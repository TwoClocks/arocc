const std = @import("std");
const Compilation = @import("Compilation.zig");
const Tree = @import("Tree.zig");
const NodeIndex = Tree.NodeIndex;
const Ir = @import("Ir.zig");
const Type = @import("Type.zig");

const GenIr = @This();

const WipSwitch = struct {
    cases: std.ArrayList(Ir.Inst.Switch.Case),
    default: ?Ir.Ref = null,
    size: u64,
};

const Symbol = struct {
    name: []const u8,
    val: union(enum) {
        arg: u32,
        local: Ir.Ref,
    },
};

pub const Error = Compilation.Error || error{IrGenFailed};

arena: std.heap.ArenaAllocator,
instructions: std.MultiArrayList(Ir.Inst) = .{},
tree: Tree,
comp: *Compilation,
node_tag: []const Tree.Tag,
node_data: []const Tree.Node.Data,
node_ty: []const Type,
wip_switch: *WipSwitch = undefined,
symbols: std.ArrayListUnmanaged(Symbol) = .{},

fn deinit(ir: *GenIr) void {
    ir.arena.deinit();
    ir.symbols.deinit(ir.comp.gpa);
    ir.instructions.deinit(ir.comp.gpa);
    ir.* = undefined;
}

fn finish(ir: GenIr) Ir {
    return .{
        .instructions = ir.instructions,
        .arena = ir.arena.state,
    };
}

fn addInst(ir: *GenIr, tag: Ir.Inst.Tag, data: Ir.Inst.Data) !Ir.Ref {
    const index = ir.instructions.len;
    try ir.instructions.append(ir.comp.gpa, .{ .tag = tag, .data = data });
    return @intToEnum(Ir.Ref, index);
}

/// Generate tree to an object file.
/// Caller is responsible for flushing and freeing the returned object.
pub fn generateTree(comp: *Compilation, tree: Tree) Compilation.Error!void {
    var ir = GenIr{
        .arena = std.heap.ArenaAllocator.init(comp.gpa),
        .tree = tree,
        .comp = comp,
        .node_tag = tree.nodes.items(.tag),
        .node_data = tree.nodes.items(.data),
        .node_ty = tree.nodes.items(.ty),
    };
    defer ir.deinit();

    const node_tags = tree.nodes.items(.tag);
    for (tree.root_decls) |decl| {
        ir.arena.deinit();
        ir.arena = std.heap.ArenaAllocator.init(comp.gpa);
        defer ir.instructions.len = 0;

        switch (node_tags[@enumToInt(decl)]) {
            // these produce no code
            .static_assert,
            .typedef,
            .struct_decl_two,
            .union_decl_two,
            .enum_decl_two,
            .struct_decl,
            .union_decl,
            .enum_decl,
            => {},

            // define symbol
            .fn_proto,
            .static_fn_proto,
            .inline_fn_proto,
            .inline_static_fn_proto,
            .noreturn_fn_proto,
            .noreturn_static_fn_proto,
            .noreturn_inline_fn_proto,
            .noreturn_inline_static_fn_proto,
            .extern_var,
            .threadlocal_extern_var,
            => {},

            // function definition
            .fn_def,
            .static_fn_def,
            .inline_fn_def,
            .inline_static_fn_def,
            .noreturn_fn_def,
            .noreturn_static_fn_def,
            .noreturn_inline_fn_def,
            .noreturn_inline_static_fn_def,
            => ir.genFn(decl) catch |err| switch (err) {
                error.FatalError => return error.FatalError,
                error.OutOfMemory => return error.OutOfMemory,
                error.IrGenFailed => continue,
            },

            .@"var",
            .static_var,
            .threadlocal_var,
            .threadlocal_static_var,
            => ir.genVar(decl) catch |err| switch (err) {
                error.FatalError => return error.FatalError,
                error.OutOfMemory => return error.OutOfMemory,
                error.IrGenFailed => continue,
            },
            else => unreachable,
        }
    }
}

fn genFn(ir: *GenIr, decl: NodeIndex) Error!void {
    const name = ir.tree.tokSlice(ir.node_data[@enumToInt(decl)].decl.name);
    const func_ty = ir.node_ty[@enumToInt(decl)].canonicalize(.standard);
    for (func_ty.data.func.params) |param, i| {
        try ir.symbols.append(ir.comp.gpa, .{
            .name = param.name,
            .val = .{ .arg = @intCast(u32, i) },
        });
    }
    _ = try ir.genNode(ir.node_data[@enumToInt(decl)].decl.node);
    const res = ir.finish();
    res.dump(name, std.io.getStdOut().writer()) catch {};
}

fn genNode(ir: *GenIr, node: NodeIndex) Error!Ir.Ref {
    std.debug.assert(node != .none);
    const data = ir.node_data[@enumToInt(node)];
    switch (ir.node_tag[@enumToInt(node)]) {
        .fn_def,
        .static_fn_def,
        .inline_fn_def,
        .inline_static_fn_def,
        .noreturn_fn_def,
        .noreturn_static_fn_def,
        .noreturn_inline_fn_def,
        .noreturn_inline_static_fn_def,
        .invalid,
        .threadlocal_var,
        .attr_arg_ident,
        .attr_params_two,
        .attr_params,
        => unreachable,
        .static_assert,
        .fn_proto,
        .static_fn_proto,
        .inline_fn_proto,
        .inline_static_fn_proto,
        .noreturn_fn_proto,
        .noreturn_static_fn_proto,
        .noreturn_inline_fn_proto,
        .noreturn_inline_static_fn_proto,
        .extern_var,
        .threadlocal_extern_var,
        .typedef,
        .struct_decl_two,
        .union_decl_two,
        .enum_decl_two,
        .struct_decl,
        .union_decl,
        .enum_decl,
        .enum_field_decl,
        .record_field_decl,
        .indirect_record_field_decl,
        .null_stmt,
        => {},
        .static_var,
        .implicit_static_var,
        .threadlocal_static_var,
        => try ir.genVar(node), // TODO
        .@"var" => {
            const ty = ir.node_ty[@enumToInt(node)];
            const size = ty.sizeof(ir.comp) orelse return error.IrGenFailed; // TODO vla
            const alloc = try ir.addInst(.alloc, .{ .alloc = size });
            try ir.symbols.append(ir.comp.gpa, .{
                .name = ir.tree.tokSlice(data.decl.name),
                .val = .{ .local = alloc },
            });
            return alloc;
        },
        .labeled_stmt => {
            _ = try ir.addInst(.label, .{ .none = {} });
            _ = try ir.genNode(data.decl.node);
        },
        .compound_stmt_two => {
            const old_sym_len = ir.symbols.items.len;
            ir.symbols.items.len = old_sym_len;

            if (data.bin.lhs != .none) _ = try ir.genNode(data.bin.lhs);
            if (data.bin.rhs != .none) _ = try ir.genNode(data.bin.rhs);
        },
        .compound_stmt => {
            const old_sym_len = ir.symbols.items.len;
            ir.symbols.items.len = old_sym_len;

            for (ir.tree.data[data.range.start..data.range.end]) |stmt| _ = try ir.genNode(stmt);
        },
        .if_then_else_stmt => {
            const cond = try ir.genNode(data.if3.cond);

            const jmp_else_index = ir.instructions.len;
            _ = try ir.addInst(.jmp_false, undefined);

            _ = try ir.genNode(ir.tree.data[data.if3.body]); // then
            const jmp_end_index = ir.instructions.len;
            _ = try ir.addInst(.jmp, undefined);

            const else_label = try ir.addInst(.label, .{ .none = {} });
            _ = try ir.genNode(ir.tree.data[data.if3.body + 1]); // else

            const end_label = try ir.addInst(.label, .{ .none = {} });

            ir.instructions.items(.data)[jmp_else_index] = .{
                .bin = .{ .lhs = cond, .rhs = else_label },
            };
            ir.instructions.items(.data)[jmp_end_index] = .{ .un = end_label };
        },
        .if_then_stmt => {
            const cond = try ir.genNode(data.bin.lhs);
            const jmp_index = ir.instructions.len;
            _ = try ir.addInst(.jmp_false, undefined);
            _ = try ir.genNode(data.bin.rhs);
            const end_label = try ir.addInst(.label, .{ .none = {} });
            ir.instructions.items(.data)[jmp_index] = .{
                .bin = .{ .lhs = cond, .rhs = end_label },
            };
        },
        .switch_stmt => {
            var wip_switch = WipSwitch{
                .cases = std.ArrayList(Ir.Inst.Switch.Case).init(ir.comp.gpa),
                .size = ir.node_ty[@enumToInt(data.bin.lhs)].sizeof(ir.comp).?,
            };
            defer wip_switch.cases.deinit();

            const old_wip_switch = ir.wip_switch;
            defer ir.wip_switch = old_wip_switch;
            ir.wip_switch = &wip_switch;

            const cond = try ir.genNode(data.bin.lhs);
            const switch_index = ir.instructions.len;
            _ = try ir.addInst(switch (wip_switch.size) {
                4 => .switch_32,
                8 => .switch_64,
                16 => .switch_128,
                else => unreachable,
            }, undefined);

            _ = try ir.genNode(data.bin.rhs); // body

            const default_ref = wip_switch.default orelse
                try ir.addInst(.label, .{ .none = {} });

            const switch_data = try ir.arena.allocator().create(Ir.Inst.Switch);
            switch_data.* = .{
                .target = cond,
                .cases = try ir.arena.allocator().dupe(Ir.Inst.Switch.Case, wip_switch.cases.items),
                .default = default_ref,
            };
            ir.instructions.items(.data)[switch_index] = .{ .@"switch" = switch_data };
        },
        .case_stmt => {
            const val = ir.tree.value_map.get(data.bin.lhs).?;
            try ir.wip_switch.cases.append(.{
                .val = switch (ir.wip_switch.size) {
                    4 => Ir.Inst.Data{ .val32 = @truncate(u32, val) },
                    8 => Ir.Inst.Data{ .val64 = val },
                    16 => unreachable, // TODO
                    else => unreachable,
                },
                .label = try ir.addInst(.label, .{ .none = {} }),
            });
            _ = try ir.genNode(data.bin.rhs);
        },
        .default_stmt => {
            ir.wip_switch.default = try ir.addInst(.label, .{ .none = {} });
            _ = try ir.genNode(data.un);
        },
        .return_stmt => {
            if (data.un == .none)
                return ir.addInst(.ret, .{ .sized = .{ .size = 0, .operand = undefined } });

            const size = ir.node_ty[@enumToInt(data.un)].bitSizeof(ir.comp).?; // cannot return a vla
            const operand = try ir.genNode(data.un);
            return ir.addInst(.ret, .{ .sized = .{ .size = @intCast(u32, size), .operand = operand } });
        },
        .comma_expr => {
            _ = try ir.genNode(data.bin.lhs);
            return ir.genNode(data.bin.rhs);
        },
        .paren_expr => return ir.genNode(data.un),
        .decl_ref_expr => {
            const size = ir.node_ty[@enumToInt(node)].bitSizeof(ir.comp).?; // arg can't be a vla
            const name = ir.tree.tokSlice(data.decl_ref);
            var i = ir.symbols.items.len;
            while (i > 0) {
                i -= 1;
                if (std.mem.eql(u8, ir.symbols.items[i].name, name)) {
                    const val = ir.symbols.items[i].val;
                    if (val == .arg) {
                        return ir.addInst(.arg, .{ .arg = .{
                            .index = val.arg,
                            .size = @intCast(u32, size),
                        } });
                    } else {
                        return val.local;
                    }
                }
            }

            return ir.addInst(.symbol, .{
                .arg = .{
                    .index = 0, // TODO reference a symbol somehow
                    .size = @intCast(u32, size),
                },
            });
        },
        .lval_to_rval => {
            const size = ir.node_ty[@enumToInt(node)].bitSizeof(ir.comp).?; // cannot load vla
            const operand = try ir.genNode(data.un);
            return ir.addInst(.load, .{ .sized = .{
                .size = @intCast(u32, size),
                .operand = operand,
            } });
        },
        .implicit_return => {
            _ = try ir.addInst(.ret, .{ .sized = .{ .size = 0, .operand = undefined } });
        },
        else => {},
    }
    return @as(Ir.Ref, undefined); // statement, value is ignored
}

fn genVar(ir: *GenIr, decl: NodeIndex) Error!void {
    _ = ir;
    _ = decl;
}
