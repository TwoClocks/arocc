const std = @import("std");

const Ir = @This();

instructions: std.MultiArrayList(Inst),
arena: std.heap.ArenaAllocator.State,

pub const Ref = enum(u32) { _ };

pub const Inst = struct {
    tag: Tag,
    data: Data,

    pub const Tag = enum {
        // data.none
        label,

        // data.un
        label_val,

        // data.switch
        switch_32,
        switch_64,
        switch_128,

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

        // data.sized
        ret,
        load,
        store,

        // data.bin
        or_i32,
        or_i64,
        or_i128,
        xor_i32,
        xor_i64,
        xor_i128,
        and_i32,
        and_i64,
        and_i128,
        shl_i32,
        shl_i64,
        shl_i128,
        shr_i32,
        shr_i64,
        shr_i128,
        cmp_eql_i32,
        cmp_eql_i64,
        cmp_eql_i128,
        cmp_eql_f32,
        cmp_eql_f64,
        cmp_eql_f80,
        cmp_eql_f128,
        cmp_not_eql_i32,
        cmp_not_eql_i64,
        cmp_not_eql_i128,
        cmp_not_eqf_f32,
        cmp_not_eqf_f64,
        cmp_not_eql_f80,
        cmp_not_eql_f128,
        cmp_lt_i32,
        cmp_lt_i64,
        cmp_lt_i128,
        cmp_lt_f32,
        cmp_lt_f64,
        cmp_lt_f80,
        cmp_lt_f128,
        cmp_lte_i32,
        cmp_lte_i64,
        cmp_lte_i128,
        cmp_lte_f32,
        cmp_lte_f64,
        cmp_lte_f80,
        cmp_lte_f128,
        cmp_gt_i32,
        cmp_gt_i64,
        cmp_gt_i128,
        cmp_gt_f32,
        cmp_gt_f64,
        cmp_gt_f80,
        cmp_gt_f128,
        cmp_gte_i32,
        cmp_gte_i64,
        cmp_gte_i128,
        cmp_gte_f32,
        cmp_gte_f64,
        cmp_gte_f80,
        cmp_gte_f128,
        add_i32,
        add_i64,
        add_i128,
        add_f32,
        add_f64,
        add_f80,
        add_f128,
        sub_i32,
        sub_i64,
        sub_i128,
        sub_f32,
        sub_f64,
        sub_f80,
        sub_f128,
        mul_i32,
        mul_i64,
        mul_i128,
        mul_f32,
        mul_f64,
        mul_f80,
        mul_f128,
        div_i32,
        div_i64,
        div_i128,
        div_f32,
        div_f64,
        div_f80,
        div_f128,
        mod_i32,
        mod_i64,
        mod_i128,
        mod_f32,
        mod_f64,
        mod_f80,
        mod_f128,

        // data.un
        bit_not_i32,
        bit_not_i64,
        bit_not_i128,
        negate_i32,
        negate_i64,
        negate_i128,
        negate_f32,
        negate_f64,
        negate_f80,
        negate_f128,
        bool_not_i32,
        bool_not_i64,
        bool_not_i128,
        bool_not_f32,
        bool_not_f64,
        bool_not_f80,
        bool_not_f128,

        // data.val32
        const_i32,
        const_f32,
        // data.val64
        const_i64,
        const_f64,
        // data.val128
        const_i128,
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
        sized: struct {
            operand: Ref,
            size: u32,
        },
        arg: struct {
            index: u32,
            size: u32,
        },
        alloc: u64,
        val32: u32,
        val64: u64,
        val128: *u128,
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
        args: []Arg,
        // number of non variadic arguments
        variadic: u32,

        pub const Arg = struct {
            val: Ref,
            size: u32,
        };
    };
};

pub fn deinit(ir: *Ir, gpa: std.mem.Allocator) void {
    ir.arena.promote(gpa).deinit();
    ir.instructions.deinit(gpa);
    ir.* = undefined;
}

pub fn dump(ir: Ir, name: []const u8, w: anytype) !void {
    try w.print("{s} {{\n", .{name});

    const data = ir.instructions.items(.data);
    for (ir.instructions.items(.tag)) |tag, i| switch (tag) {
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
        .switch_32,
        .switch_64,
        .switch_128,
        => {
            const @"switch" = data[i].@"switch";
            const val_tag: Inst.Tag = switch (tag) {
                .switch_32 => .const_i32,
                .switch_64 => .const_i64,
                .switch_128 => .const_i128,
                else => unreachable,
            };
            try w.print("    {s} %{d} {{\n", .{ @tagName(tag), @enumToInt(@"switch".target) });
            for (@"switch".cases) |case| {
                try w.writeAll("        ");
                try dumpVal(val_tag, case.val, w);
                try w.print(" label.{d}\n", .{@enumToInt(case.label)});
            }
            try w.print("        default label.{d}\n    }}\n", .{@enumToInt(@"switch".default)});
        },
        .call => {
            const call = data[i].call;
            try w.print("    %{d} = call {d} (", .{ i, @enumToInt(call.func) });
            for (call.args) |arg, arg_i| {
                if (arg_i != 0) try w.writeAll(", ");
                if (arg_i == call.variadic) try w.writeAll("{ ");
                try w.print("{d} %{d}", .{ arg.size, @enumToInt(arg.val) });
            }
            if (call.variadic != call.args.len) try w.writeByte('}');
            try w.writeAll(")\n");
        },
        .arg => {
            const arg = data[i].arg;
            try w.print("    %{d} = arg_{d}[{d}]\n", .{ i, arg.size, arg.index });
        },
        .symbol => {
            const sym = data[i].arg;
            try w.print("    %{d} = symbol_{d}\n", .{ i, sym.size });
        },
        .alloc => {
            const size = data[i].alloc;
            try w.print("    %{d} = alloc {d}\n", .{ i, size });
        },
        .ret, .store => {
            const sized = data[i].sized;
            if (sized.size == 0) {
                try w.print("    {s}\n", .{@tagName(tag)});
            } else {
                try w.print("    {s}.{d} %{d}\n", .{ @tagName(tag), sized.size, @enumToInt(sized.operand) });
            }
        },
        .load => {
            const sized = data[i].sized;
            try w.print("    %{d} = load_{d} %{d}\n", .{ i, sized.size, @enumToInt(sized.operand) });
        },
        .or_i32,
        .or_i64,
        .or_i128,
        .xor_i32,
        .xor_i64,
        .xor_i128,
        .and_i32,
        .and_i64,
        .and_i128,
        .shl_i32,
        .shl_i64,
        .shl_i128,
        .shr_i32,
        .shr_i64,
        .shr_i128,
        .cmp_eql_i32,
        .cmp_eql_i64,
        .cmp_eql_i128,
        .cmp_eql_f32,
        .cmp_eql_f64,
        .cmp_eql_f80,
        .cmp_eql_f128,
        .cmp_not_eql_i32,
        .cmp_not_eql_i64,
        .cmp_not_eql_i128,
        .cmp_not_eqf_f32,
        .cmp_not_eqf_f64,
        .cmp_not_eql_f80,
        .cmp_not_eql_f128,
        .cmp_lt_i32,
        .cmp_lt_i64,
        .cmp_lt_i128,
        .cmp_lt_f32,
        .cmp_lt_f64,
        .cmp_lt_f80,
        .cmp_lt_f128,
        .cmp_lte_i32,
        .cmp_lte_i64,
        .cmp_lte_i128,
        .cmp_lte_f32,
        .cmp_lte_f64,
        .cmp_lte_f80,
        .cmp_lte_f128,
        .cmp_gt_i32,
        .cmp_gt_i64,
        .cmp_gt_i128,
        .cmp_gt_f32,
        .cmp_gt_f64,
        .cmp_gt_f80,
        .cmp_gt_f128,
        .cmp_gte_i32,
        .cmp_gte_i64,
        .cmp_gte_i128,
        .cmp_gte_f32,
        .cmp_gte_f64,
        .cmp_gte_f80,
        .cmp_gte_f128,
        .add_i32,
        .add_i64,
        .add_i128,
        .add_f32,
        .add_f64,
        .add_f80,
        .add_f128,
        .sub_i32,
        .sub_i64,
        .sub_i128,
        .sub_f32,
        .sub_f64,
        .sub_f80,
        .sub_f128,
        .mul_i32,
        .mul_i64,
        .mul_i128,
        .mul_f32,
        .mul_f64,
        .mul_f80,
        .mul_f128,
        .div_i32,
        .div_i64,
        .div_i128,
        .div_f32,
        .div_f64,
        .div_f80,
        .div_f128,
        .mod_i32,
        .mod_i64,
        .mod_i128,
        .mod_f32,
        .mod_f64,
        .mod_f80,
        .mod_f128,
        => {
            const bin = data[i].bin;
            try w.print(
                "    %{d} = {s} %{d}, %{d}\n",
                .{ i, @tagName(tag), @enumToInt(bin.lhs), @enumToInt(bin.rhs) },
            );
        },
        .bit_not_i32,
        .bit_not_i64,
        .bit_not_i128,
        .negate_i32,
        .negate_i64,
        .negate_i128,
        .negate_f32,
        .negate_f64,
        .negate_f80,
        .negate_f128,
        .bool_not_i32,
        .bool_not_i64,
        .bool_not_i128,
        .bool_not_f32,
        .bool_not_f64,
        .bool_not_f80,
        .bool_not_f128,
        => {
            const un = data[i].un;
            try w.print("    %{d} = {s} %{d}\n", .{ i, @tagName(tag), @enumToInt(un) });
        },
        .const_i32,
        .const_i64,
        .const_i128,
        .const_f32,
        .const_f64,
        .const_f80,
        .const_f128,
        => {
            try w.print("    %{d} = {s} ", .{ i, @tagName(tag) });
            try dumpVal(tag, data[i], w);
            try w.writeByte('\n');
        },
    };
    try w.print("}} // {s}\n\n", .{name});
}

fn dumpVal(tag: Inst.Tag, val: Inst.Data, w: anytype) !void {
    switch (tag) {
        .const_i32 => try w.print("0x{X}", .{val.val32}),
        .const_i64 => try w.print("0x{X}", .{val.val64}),
        .const_i128 => try w.print("0x{X}", .{val.val128.*}),
        .const_f32 => try w.print("{d}", .{@bitCast(f32, val.val32)}),
        .const_f64 => try w.print("{d}", .{@bitCast(f64, val.val64)}),
        .const_f80, .const_f128 => try w.print("{X}", .{val.val128.*}),
        else => unreachable,
    }
}
