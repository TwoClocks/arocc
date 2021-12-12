const std = @import("std");
const NodeIndex = @import("Tree.zig").NodeIndex;

const Ir = @This();

instructions: std.MultiArrayList(Inst),
body: std.ArrayListUnmanaged(Ref) = .{},
arena: std.heap.ArenaAllocator.State,

pub const Ref = enum(u32) { _ };

pub const Inst = struct {
    tag: Tag,
    data: Data,
    src: NodeIndex,

    pub const Tag = enum {
        // data.none
        label,

        // data.un
        label_val,

        // data.switch
        @"switch",

        // data.un
        jmp,

        // data.bin
        jmp_false,
        jmp_true,
        jmp_val,

        // data.call
        call,

        // data.arg
        arg,
        symbol,

        // data.alloc
        alloc,

        // data.bin
        store,
        bit_or,
        bit_xor,
        bit_and,
        bit_shl,
        bit_shr,
        cmp_eql,
        cmp_not_eql,
        cmp_lt,
        cmp_lte,
        cmp_gt,
        cmp_gte,
        add,
        sub,
        mul,
        div,
        mod,

        // data.un
        ret,
        load,
        bit_not,
        negate,

        // data.none
        ret_void,

        const_int,
        const_f32,
        const_f64,
        const_f80,
        const_f128,
    };

    pub const Data = union {
        none: void,
        bin: struct {
            lhs: Ref,
            rhs: Ref,
        },
        un: Ref,
        arg: u32,
        alloc: u64,
        int: u64,
        int128: *i128,
        f32: f32,
        f64: f64,
        f128: *f128,
        label: Ref,
        @"switch": *Switch,
        @"call": *Call,
    };

    pub const Switch = struct {
        target: Ref,
        default: Ref,
        cases: []Case,

        pub const Case = struct {
            val: Data,
            label: Ref,
        };
    };

    pub const Call = struct {
        func: Ref,
        args: []Ref,
    };
};

pub fn deinit(ir: *Ir, gpa: std.mem.Allocator) void {
    ir.arena.promote(gpa).deinit();
    ir.instructions.deinit(gpa);
    ir.* = undefined;
}

pub fn dump(ir: Ir, name: []const u8, w: anytype) !void {
    const tags = ir.instructions.items(.tag);
    const data = ir.instructions.items(.data);

    try w.print("{s}(", .{name});
    for (tags) |tag, i| {
        if (tag != .arg) break;
        if (i != 0) try w.writeAll(", ");
        try w.print("%{d}", .{i});
    }
    try w.writeAll(") {\n");

    for (ir.body.items) |ref| {
        const i = @enumToInt(ref);
        const tag = tags[i];
        switch (tag) {
            .arg => unreachable,
            .label => try w.print("label.{d}:\n", .{i}),
            .label_val => {
                const un = data[i].un;
                try w.print("    %{d} = label.{d}\n", .{ i, @enumToInt(un) });
            },
            .jmp => {
                const un = data[i].un;
                try w.print("    jmp label.{d}\n", .{@enumToInt(un)});
            },
            .jmp_false, .jmp_true, .jmp_val => {
                const bin = data[i].bin;
                try w.print("    %{s} %{d} label.{d}\n", .{ @tagName(tag), @enumToInt(bin.lhs), @enumToInt(bin.rhs) });
            },
            .@"switch" => {
                const @"switch" = data[i].@"switch";
                try w.print("    {s} %{d} {{\n", .{ @tagName(tag), @enumToInt(@"switch".target) });
                for (@"switch".cases) |case| {
                    try w.writeAll("        ");
                    try dumpVal(.const_int, case.val, w);
                    try w.print(" label.{d}\n", .{@enumToInt(case.label)});
                }
                try w.print("        default label.{d}\n    }}\n", .{@enumToInt(@"switch".default)});
            },
            .call => {
                const call = data[i].call;
                try w.print("    %{d} = call {d} (", .{ i, @enumToInt(call.func) });
                for (call.args) |arg, arg_i| {
                    if (arg_i != 0) try w.writeAll(", ");
                    try w.print("%{d}", .{@enumToInt(arg)});
                }
                try w.writeAll(")\n");
            },
            .symbol => {
                try w.print("    %{d} = symbol\n", .{i});
            },
            .alloc => {
                const size = data[i].alloc;
                try w.print("    %{d} = alloc {d}\n", .{ i, size });
            },
            .store => {
                const bin = data[i].bin;
                try w.print("    store %{d}, %{d}\n", .{ @enumToInt(bin.lhs), @enumToInt(bin.rhs) });
            },
            .ret => {
                try w.print("    ret %{d}\n", .{@enumToInt(data[i].un)});
            },
            .ret_void => {
                try w.writeAll("    ret\n");
            },
            .load => {
                try w.print("    %{d} = load %{d}\n", .{ i, @enumToInt(data[i].un) });
            },
            .bit_or,
            .bit_xor,
            .bit_and,
            .bit_shl,
            .bit_shr,
            .cmp_eql,
            .cmp_not_eql,
            .cmp_lt,
            .cmp_lte,
            .cmp_gt,
            .cmp_gte,
            .add,
            .sub,
            .mul,
            .div,
            .mod,
            => {
                const bin = data[i].bin;
                try w.print(
                    "    %{d} = {s} %{d}, %{d}\n",
                    .{ i, @tagName(tag), @enumToInt(bin.lhs), @enumToInt(bin.rhs) },
                );
            },
            .bit_not,
            .negate,
            => {
                const un = data[i].un;
                try w.print("    %{d} = {s} %{d}\n", .{ i, @tagName(tag), @enumToInt(un) });
            },
            .const_int,
            .const_f32,
            .const_f64,
            .const_f80,
            .const_f128,
            => {
                try w.print("    %{d} = {s} ", .{ i, @tagName(tag) });
                try dumpVal(tag, data[i], w);
                try w.writeByte('\n');
            },
        }
    }
    try w.print("}} // {s}\n\n", .{name});
}

fn dumpVal(tag: Inst.Tag, val: Inst.Data, w: anytype) !void {
    switch (tag) {
        .const_int => try w.print("0x{X}", .{val.int}),
        .const_f32 => try w.print("{d}", .{val.f32}),
        .const_f64 => try w.print("{d}", .{val.f64}),
        .const_f80, .const_f128 => try w.print("{X}", .{@bitCast(i128, val.f128.*)}),
        else => unreachable,
    }
}
