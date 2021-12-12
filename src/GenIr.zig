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
    val: Ir.Ref,
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
breaks: std.ArrayListUnmanaged(u32) = .{},
continues: std.ArrayListUnmanaged(u32) = .{},
body: std.ArrayListUnmanaged(Ir.Ref) = .{},
last_alloc_index: u32 = 0,

fn deinit(ir: *GenIr) void {
    ir.arena.deinit();
    ir.symbols.deinit(ir.comp.gpa);
    ir.breaks.deinit(ir.comp.gpa);
    ir.continues.deinit(ir.comp.gpa);
    ir.instructions.deinit(ir.comp.gpa);
    ir.body.deinit(ir.comp.gpa);
    ir.* = undefined;
}

fn finish(ir: GenIr) Ir {
    return .{
        .instructions = ir.instructions,
        .arena = ir.arena.state,
        .body = ir.body,
    };
}

fn addInst(ir: *GenIr, tag: Ir.Inst.Tag, src: NodeIndex, data: Ir.Inst.Data) !Ir.Ref {
    const ref = @intToEnum(Ir.Ref, ir.instructions.len);
    try ir.instructions.append(ir.comp.gpa, .{ .tag = tag, .data = data, .src = src });
    if (tag == .alloc) {
        try ir.body.insert(ir.comp.gpa, ir.last_alloc_index, ref);
        ir.last_alloc_index = 0;
    } else {
        try ir.body.append(ir.comp.gpa, ref);
    }
    return ref;
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
        ir.instructions.len = 0;
        ir.body.items.len = 0;
        ir.last_alloc_index = 0;

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
        const alloc = @intToEnum(Ir.Ref, ir.instructions.len);
        try ir.instructions.append(
            ir.comp.gpa,
            .{ .tag = .arg, .data = .{ .arg = @intCast(u32, i) }, .src = .none },
        );
        try ir.symbols.append(ir.comp.gpa, .{ .name = param.name, .val = alloc });
    }
    _ = try ir.genNode(ir.node_data[@enumToInt(decl)].decl.node);
    var res = ir.finish();
    res.dump(name, std.io.getStdOut().writer()) catch {};
}

fn genNode(ir: *GenIr, node: NodeIndex) Error!Ir.Ref {
    std.debug.assert(node != .none);
    if (ir.tree.value_map.get(node)) |some| {
        return ir.addInst(.const_int, node, .{ .int = some });
    }
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
            const alloc = try ir.addInst(.alloc, node, .{ .alloc = size });
            try ir.symbols.append(ir.comp.gpa, .{ .name = ir.tree.tokSlice(data.decl.name), .val = alloc });
            if (data.decl.node != .none) {
                const res = try ir.genNode(data.decl.node);
                _ = try ir.addInst(.store, data.decl.node, .{ .bin = .{ .lhs = alloc, .rhs = res } });
            }
            return alloc;
        },
        .labeled_stmt => {
            _ = try ir.addInst(.label, node, .{ .none = {} });
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
            _ = try ir.addInst(.jmp_false, node, undefined);

            _ = try ir.genNode(ir.tree.data[data.if3.body]); // then
            const jmp_end_index = ir.instructions.len;
            _ = try ir.addInst(.jmp, node, undefined);

            const else_label = try ir.addInst(.label, node, .{ .none = {} });
            _ = try ir.genNode(ir.tree.data[data.if3.body + 1]); // else

            const end_label = try ir.addInst(.label, node, .{ .none = {} });

            ir.instructions.items(.data)[jmp_else_index] = .{
                .bin = .{ .lhs = cond, .rhs = else_label },
            };
            ir.instructions.items(.data)[jmp_end_index] = .{ .un = end_label };
        },
        .if_then_stmt => {
            const cond = try ir.genNode(data.bin.lhs);
            const jmp_index = ir.instructions.len;
            _ = try ir.addInst(.jmp_false, node, undefined);
            _ = try ir.genNode(data.bin.rhs);
            const end_label = try ir.addInst(.label, node, .{ .none = {} });
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

            const old_breaks = ir.breaks.items.len;
            defer ir.breaks.items.len = old_breaks;

            const cond = try ir.genNode(data.bin.lhs);
            const switch_index = ir.instructions.len;
            _ = try ir.addInst(.@"switch", node, undefined);

            _ = try ir.genNode(data.bin.rhs); // body

            const end_ref = try ir.addInst(.label, node, .{ .none = {} });
            const default_ref = wip_switch.default orelse end_ref;

            const inst_data = ir.instructions.items(.data);
            for (ir.breaks.items[old_breaks..]) |break_index| {
                inst_data[break_index] = .{ .un = end_ref };
            }

            const switch_data = try ir.arena.allocator().create(Ir.Inst.Switch);
            switch_data.* = .{
                .target = cond,
                .cases = try ir.arena.allocator().dupe(Ir.Inst.Switch.Case, wip_switch.cases.items),
                .default = default_ref,
            };
            inst_data[switch_index] = .{ .@"switch" = switch_data };
        },
        .case_stmt => {
            try ir.wip_switch.cases.append(.{
                .val = .{ .int = ir.tree.value_map.get(data.bin.lhs).? },
                .label = try ir.addInst(.label, node, .{ .none = {} }),
            });
            _ = try ir.genNode(data.bin.rhs);
        },
        .default_stmt => {
            ir.wip_switch.default = try ir.addInst(.label, node, .{ .none = {} });
            _ = try ir.genNode(data.un);
        },
        .while_stmt => {
            const old_breaks = ir.breaks.items.len;
            defer ir.breaks.items.len = old_breaks;
            const old_continues = ir.continues.items.len;
            defer ir.continues.items.len = old_continues;

            const start_ref = try ir.addInst(.label, node, .{ .none = {} });
            const cond = try ir.genNode(data.bin.lhs);
            const jmp_index = ir.instructions.len;
            _ = try ir.addInst(.jmp_false, node, undefined);
            _ = try ir.genNode(data.bin.rhs);
            const end_ref = try ir.addInst(.label, node, .{ .none = {} });

            const inst_data = ir.instructions.items(.data);
            for (ir.breaks.items[old_breaks..]) |break_index| {
                inst_data[break_index] = .{ .un = end_ref };
            }
            inst_data[jmp_index] = .{ .bin = .{ .lhs = cond, .rhs = end_ref } };
            for (ir.continues.items[old_continues..]) |continue_index| {
                inst_data[continue_index] = .{ .un = start_ref };
            }
        },
        .do_while_stmt => {
            const old_breaks = ir.breaks.items.len;
            defer ir.breaks.items.len = old_breaks;
            const old_continues = ir.continues.items.len;
            defer ir.continues.items.len = old_continues;

            const start_ref = try ir.addInst(.label, node, .{ .none = {} });
            _ = try ir.genNode(data.bin.rhs);

            const cond_ref = try ir.addInst(.label, node, .{ .none = {} });
            const cond = try ir.genNode(data.bin.lhs);
            const jmp_index = ir.instructions.len;
            _ = try ir.addInst(.jmp_true, node, undefined);
            const end_ref = try ir.addInst(.label, node, .{ .none = {} });

            const inst_data = ir.instructions.items(.data);
            for (ir.breaks.items[old_breaks..]) |break_index| {
                inst_data[break_index] = .{ .un = end_ref };
            }
            inst_data[jmp_index] = .{ .bin = .{ .lhs = cond, .rhs = start_ref } };
            for (ir.continues.items[old_continues..]) |continue_index| {
                inst_data[continue_index] = .{ .un = cond_ref };
            }
        },
        .for_decl_stmt => {
            const old_breaks = ir.breaks.items.len;
            defer ir.breaks.items.len = old_breaks;
            const old_continues = ir.continues.items.len;
            defer ir.continues.items.len = old_continues;

            const for_decl = data.forDecl(ir.tree);
            for (for_decl.decls) |decl| _ = try ir.genNode(decl);

            const start_ref = try ir.addInst(.label, node, .{ .none = {} });

            const jmp_index = ir.instructions.len;
            var cond: ?Ir.Ref = null;
            if (for_decl.cond != .none) {
                cond = try ir.genNode(for_decl.cond);
                _ = try ir.addInst(.jmp_false, node, undefined);
            }

            _ = try ir.genNode(for_decl.body);

            const continue_ref = try ir.addInst(.label, node, .{ .none = {} });
            if (for_decl.incr != .none) {
                _ = try ir.genNode(for_decl.incr);
            }
            _ = try ir.addInst(.jmp, node, .{ .un = start_ref });

            const end_ref = try ir.addInst(.label, node, .{ .none = {} });

            const inst_data = ir.instructions.items(.data);
            for (ir.breaks.items[old_breaks..]) |break_index| {
                inst_data[break_index] = .{ .un = end_ref };
            }
            if (cond) |some| {
                inst_data[jmp_index] = .{ .bin = .{ .lhs = some, .rhs = end_ref } };
            }
            for (ir.continues.items[old_continues..]) |continue_index| {
                inst_data[continue_index] = .{ .un = continue_ref };
            }
        },
        .forever_stmt => {
            const old_breaks = ir.breaks.items.len;
            defer ir.breaks.items.len = old_breaks;
            const old_continues = ir.continues.items.len;
            defer ir.continues.items.len = old_continues;

            const start_ref = try ir.addInst(.label, node, .{ .none = {} });
            _ = try ir.genNode(data.un);
            const end_ref = try ir.addInst(.label, node, .{ .none = {} });

            const inst_data = ir.instructions.items(.data);
            for (ir.breaks.items[old_breaks..]) |break_index| {
                inst_data[break_index] = .{ .un = end_ref };
            }
            for (ir.continues.items[old_continues..]) |continue_index| {
                inst_data[continue_index] = .{ .un = start_ref };
            }
        },
        .for_stmt => {
            const old_breaks = ir.breaks.items.len;
            defer ir.breaks.items.len = old_breaks;
            const old_continues = ir.continues.items.len;
            defer ir.continues.items.len = old_continues;

            const for_stmt = data.forStmt(ir.tree);
            if (for_stmt.init != .none) _ = try ir.genNode(for_stmt.init);

            const start_ref = try ir.addInst(.label, node, .{ .none = {} });

            const jmp_index = ir.instructions.len;
            var cond: ?Ir.Ref = null;
            if (for_stmt.cond != .none) {
                cond = try ir.genNode(for_stmt.cond);
                _ = try ir.addInst(.jmp_false, node, undefined);
            }

            _ = try ir.genNode(for_stmt.body);

            const continue_ref = try ir.addInst(.label, node, .{ .none = {} });
            if (for_stmt.incr != .none) {
                _ = try ir.genNode(for_stmt.incr);
            }
            _ = try ir.addInst(.jmp, node, .{ .un = start_ref });

            const end_ref = try ir.addInst(.label, node, .{ .none = {} });

            const inst_data = ir.instructions.items(.data);
            for (ir.breaks.items[old_breaks..]) |break_index| {
                inst_data[break_index] = .{ .un = end_ref };
            }
            if (cond) |some| {
                inst_data[jmp_index] = .{ .bin = .{ .lhs = some, .rhs = end_ref } };
            }
            for (ir.continues.items[old_continues..]) |continue_index| {
                inst_data[continue_index] = .{ .un = continue_ref };
            }
        },
        .continue_stmt => {
            try ir.continues.append(ir.comp.gpa, @intCast(u32, ir.instructions.len));
            _ = try ir.addInst(.jmp, node, undefined);
        },
        .break_stmt => {
            try ir.breaks.append(ir.comp.gpa, @intCast(u32, ir.instructions.len));
            _ = try ir.addInst(.jmp, node, undefined);
        },
        .return_stmt => {
            if (data.un == .none)
                return ir.addInst(.ret_void, node, .{ .none = {} });

            const operand = try ir.genNode(data.un);
            return ir.addInst(.ret, node, .{ .un = operand });
        },
        .comma_expr => {
            _ = try ir.genNode(data.bin.lhs);
            return ir.genNode(data.bin.rhs);
        },
        .assign_expr => {
            const rhs = try ir.genNode(data.bin.rhs);
            const lhs = try ir.genNode(data.bin.lhs);
            _ = try ir.addInst(.store, node, .{ .bin = .{ .lhs = lhs, .rhs = rhs } });
            return rhs;
        },
        .mul_assign_expr => return ir.genCompoundAssign(node, .mul),
        .div_assign_expr => return ir.genCompoundAssign(node, .div),
        .mod_assign_expr => return ir.genCompoundAssign(node, .mod),
        .add_assign_expr => return ir.genCompoundAssign(node, .add),
        .sub_assign_expr => return ir.genCompoundAssign(node, .sub),
        .shl_assign_expr => return ir.genCompoundAssign(node, .bit_shl),
        .shr_assign_expr => return ir.genCompoundAssign(node, .bit_shr),
        .bit_and_assign_expr => return ir.genCompoundAssign(node, .bit_and),
        .bit_xor_assign_expr => return ir.genCompoundAssign(node, .bit_xor),
        .bit_or_assign_expr => return ir.genCompoundAssign(node, .bit_or),
        .bit_or_expr => return ir.genBinOp(node, .bit_or),
        .bit_xor_expr => return ir.genBinOp(node, .bit_xor),
        .bit_and_expr => return ir.genBinOp(node, .bit_and),
        .equal_expr => return ir.genBinOp(node, .cmp_eql),
        .not_equal_expr => return ir.genBinOp(node, .cmp_not_eql),
        .less_than_expr => return ir.genBinOp(node, .cmp_lt),
        .less_than_equal_expr => return ir.genBinOp(node, .cmp_lte),
        .greater_than_expr => return ir.genBinOp(node, .cmp_gt),
        .greater_than_equal_expr => return ir.genBinOp(node, .cmp_gte),
        .shl_expr => return ir.genBinOp(node, .bit_shl),
        .shr_expr => return ir.genBinOp(node, .bit_shr),
        .add_expr => return ir.genBinOp(node, .add),
        .sub_expr => return ir.genBinOp(node, .sub),
        .mul_expr => return ir.genBinOp(node, .mul),
        .div_expr => return ir.genBinOp(node, .div),
        .mod_expr => return ir.genBinOp(node, .mod),
        .addr_of_expr => return try ir.genNode(data.un),
        .deref_expr => {
            const operand = try ir.genNode(data.un);
            return ir.addInst(.load, node, .{ .un = operand });
        },
        .plus_expr => return ir.genNode(data.un),
        .negate_expr => {
            const zero = try ir.addInst(.const_int, node, .{ .int = 0 });
            const operand = try ir.genNode(data.un);
            return ir.addInst(.sub, node, .{ .bin = .{ .lhs = zero, .rhs = operand } });
        },
        .bit_not_expr => {
            const operand = try ir.genNode(data.un);
            return ir.addInst(.bit_not, node, .{ .un = operand });
        },
        .bool_not_expr => {
            const zero = try ir.addInst(.const_int, node, .{ .int = 0 });
            const operand = try ir.genNode(data.un);
            return ir.addInst(.cmp_not_eql, node, .{ .bin = .{ .lhs = zero, .rhs = operand } });
        },
        .pre_inc_expr => {
            const operand = try ir.genNode(data.un);
            const val = try ir.addInst(.load, node, .{ .un = operand });
            const one = try ir.addInst(.const_int, node, .{ .int = 1 });
            const plus_one = try ir.addInst(.add, node, .{ .bin = .{ .lhs = val, .rhs = one } });
            _ = try ir.addInst(.store, node, .{ .bin = .{ .lhs = operand, .rhs = plus_one } });
            return plus_one;
        },
        .pre_dec_expr => {
            const operand = try ir.genNode(data.un);
            const val = try ir.addInst(.load, node, .{ .un = operand });
            const one = try ir.addInst(.const_int, node, .{ .int = 1 });
            const plus_one = try ir.addInst(.sub, node, .{ .bin = .{ .lhs = val, .rhs = one } });
            _ = try ir.addInst(.store, node, .{ .bin = .{ .lhs = operand, .rhs = plus_one } });
            return plus_one;
        },
        .post_inc_expr => {
            const operand = try ir.genNode(data.un);
            const val = try ir.addInst(.load, node, .{ .un = operand });
            const one = try ir.addInst(.const_int, node, .{ .int = 1 });
            const plus_one = try ir.addInst(.add, node, .{ .bin = .{ .lhs = val, .rhs = one } });
            _ = try ir.addInst(.store, node, .{ .bin = .{ .lhs = operand, .rhs = plus_one } });
            return val;
        },
        .post_dec_expr => {
            const operand = try ir.genNode(data.un);
            const val = try ir.addInst(.load, node, .{ .un = operand });
            const one = try ir.addInst(.const_int, node, .{ .int = 1 });
            const plus_one = try ir.addInst(.sub, node, .{ .bin = .{ .lhs = val, .rhs = one } });
            _ = try ir.addInst(.store, node, .{ .bin = .{ .lhs = operand, .rhs = plus_one } });
            return val;
        },
        .paren_expr => return ir.genNode(data.un),
        .decl_ref_expr => {
            const name = ir.tree.tokSlice(data.decl_ref);
            var i = ir.symbols.items.len;
            while (i > 0) {
                i -= 1;
                if (std.mem.eql(u8, ir.symbols.items[i].name, name)) {
                    return ir.symbols.items[i].val;
                }
            }

            return ir.addInst(.symbol, node, .{ .arg = 0 });
        },
        .int_literal => {
            return ir.addInst(.const_int, node, .{ .int = data.int });
        },
        .lval_to_rval => {
            const operand = try ir.genNode(data.un);
            return ir.addInst(.load, node, .{ .un = operand });
        },
        .implicit_return => {
            if (ir.node_ty[@enumToInt(node)].get(.void)) |_| {
                _ = try ir.addInst(.ret_void, node, .{ .none = {} });
            } else {
                const zero = try ir.addInst(.const_int, node, .{ .int = 0 });
                _ = try ir.addInst(.ret, node, .{ .un = zero });
            }
        },
        else => {},
    }
    return @as(Ir.Ref, undefined); // statement, value is ignored
}

fn genCompoundAssign(ir: *GenIr, node: NodeIndex, tag: Ir.Inst.Tag) Error!Ir.Ref {
    const bin = ir.node_data[@enumToInt(node)].bin;
    const rhs = try ir.genNode(bin.rhs);
    const lhs = try ir.genNode(bin.lhs);
    const res = try ir.addInst(tag, node, .{ .bin = .{ .lhs = lhs, .rhs = rhs } });
    _ = try ir.addInst(.store, node, .{ .bin = .{ .lhs = lhs, .rhs = res } });
    return res;
}

fn genBinOp(ir: *GenIr, node: NodeIndex, tag: Ir.Inst.Tag) Error!Ir.Ref {
    const bin = ir.node_data[@enumToInt(node)].bin;
    const lhs = try ir.genNode(bin.lhs);
    const rhs = try ir.genNode(bin.rhs);
    return ir.addInst(tag, node, .{ .bin = .{ .lhs = lhs, .rhs = rhs } });
}

fn genVar(ir: *GenIr, decl: NodeIndex) Error!void {
    _ = ir;
    _ = decl;
}
