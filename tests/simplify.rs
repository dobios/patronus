// Copyright 2024 Cornell University
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cornell.edu>

use patronus::expr::*;

/// test a simplification
fn ts(inp: &str, expect: &str) {
    let mut ctx = Context::default();
    let input = parse_expr(&mut ctx, inp);
    let expected = parse_expr(&mut ctx, expect);
    let simplified = simplify_single_expression(&mut ctx, input);
    assert_eq!(
        simplified,
        expected,
        "simplify({}) = {}\nExpected: {}",
        input.serialize_to_str(&ctx),
        simplified.serialize_to_str(&ctx),
        expected.serialize_to_str(&ctx)
    );
}

#[test]
fn test_simplify_and() {
    ts("true", "true");
    ts("false", "false");
    ts("and(true, false)", "false");
    ts("and(true, true)", "true");
    ts("and(a : bv<1>, true)", "a : bv<1>");
    ts("and(a : bv<3>, 3'b111)", "a : bv<3>");
    ts("and(a : bv<1>, false)", "false");
    ts("and(a : bv<3>, 3'b000)", "3'b000");
    ts("and(a : bv<1>, not(a))", "false");
    ts("and(not(a : bv<1>), a)", "false");
}

#[test]
fn test_simplify_or() {
    ts("or(false, true)", "true");
    ts("or(false, false)", "false");
    ts("or(a : bv<1>, true)", "true");
    ts("or(a : bv<3>, 3'b111)", "3'b111");
    ts("or(a : bv<1>, false)", "a : bv<1>");
    ts("or(a : bv<3>, 3'b000)", "a : bv<3>");
    ts("or(a : bv<1>, not(a))", "true");
    ts("or(not(a : bv<1>), a)", "true");
}

#[test]
fn test_simplify_xor() {
    ts("xor(false, true)", "true");
    ts("xor(false, false)", "false");
    ts("xor(true, true)", "false");
    ts("xor(a : bv<1>, a)", "false");
    ts("xor(a : bv<1>, not(a))", "true");
    ts("xor(not(a : bv<1>), a)", "true");
}

#[test]
fn test_simplify_not() {
    ts("not(false)", "true");
    ts("not(true)", "false");
    ts("not(a: bv<1>)", "not(a: bv<1>)");
    ts("not(not(a: bv<1>))", "a: bv<1>");
    ts("not(not(not(a: bv<1>)))", "not(a: bv<1>)");
    ts("not(not(not(not(a: bv<1>))))", "a: bv<1>");
}

#[test]
fn test_simplify_zero_extend() {
    ts("zext(false, 1)", "2'b00");
    ts("zext(true, 1)", "2'b01");
    ts("zext(true, 0)", "true");
    // zero extends always get normalized to a concat with zero
    ts("zext(a: bv<2>, 4)", "concat(4'd0, a: bv<2>)");
    ts("zext(zext(a: bv<2>, 4), 3)", "concat(7'd0, a: bv<2>)");
}

#[test]
fn test_simplify_sign_extend() {
    ts("sext(false, 1)", "2'b00");
    ts("sext(true, 1)", "2'b11");
    ts("sext(true, 0)", "true");
    // combine sign extensions
    ts("sext(sext(a: bv<2>, 4), 3)", "sext(a : bv<2>, 7)");
}

#[test]
fn test_simplify_ite() {
    // outcome is always the same
    ts("ite(c : bv<1>, a: bv<10>, a)", "a : bv<10>");

    // constant condition
    ts("ite(true, a: bv<10>, b: bv<10>)", "a : bv<10>");
    ts("ite(false, a: bv<10>, b: bv<10>)", "b : bv<10>");

    // both true and false value are boolean constants
    ts("ite(c : bv<1>, true, false)", "c : bv<1>");
    ts("ite(c : bv<1>, true, true)", "true");
    ts("ite(c : bv<1>, false, true)", "not(c : bv<1>)");
    ts("ite(c : bv<1>, false, false)", "false");
}

#[test]
fn test_simplify_slice() {
    // slice a constant
    ts("3'b110[2]", "true");
    ts("3'b110[1]", "true");
    ts("3'b110[0]", "false");
    ts("4'b1100[3:2]", "2'b11");
    ts("4'b1100[2:1]", "2'b10");
    ts("4'b1100[1:0]", "2'b00");

    // nested slices
    ts("a : bv<10>[6:3][1]", "a : bv<10>[4]");
}

#[test]
fn test_simplify_shift_left() {
    // shift a constant by a constant
    ts("shift_left(3'b011, 3'd0)", "3'b011");
    ts("shift_left(3'b011, 3'd1)", "3'b110");
    ts("shift_left(3'b011, 3'd2)", "3'b100");
    ts("shift_left(3'b011, 3'd3)", "3'b000");

    // shift by a constant
    ts("shift_left(a : bv<3>, 3'd0)", "a : bv<3>");
    ts(
        "shift_left(a : bv<3>, 3'd1)",
        "concat(a : bv<3>[1:0], 1'b0)",
    );
    ts("shift_left(a : bv<3>, 3'd2)", "concat(a : bv<3>[0], 2'b00)");
    ts("shift_left(a : bv<3>, 3'd3)", "3'b000");

    // more shift by constant tests
    ts("shift_left(a:bv<32>, 32'd0)", "a : bv<32>");
    ts(
        "shift_left(a:bv<32>, 32'd4)",
        "concat(a:bv<32>[27:0], 4'd0)",
    );
}

#[test]
fn test_simplify_shift_right() {
    // shift a constant by a constant
    ts("shift_right(3'b101, 3'd0)", "3'b101");
    ts("shift_right(3'b101, 3'd1)", "3'b010");
    ts("shift_right(3'b101, 3'd2)", "3'b001");
    ts("shift_right(3'b101, 3'd3)", "3'b000");

    // shift by a constant
    ts("shift_right(a : bv<3>, 3'd0)", "a : bv<3>");
    ts(
        "shift_right(a : bv<3>, 3'd1)",
        "concat(1'd0, a : bv<3>[2:1])",
    );
    ts("shift_right(a : bv<3>, 3'd2)", "concat(2'd0, a : bv<3>[2])");
    ts("shift_right(a : bv<3>, 3'd3)", "3'b000");

    // more shift by constant tests
    ts("shift_right(a:bv<32>, 32'd0)", "a : bv<32>");
    ts(
        "shift_right(a:bv<32>, 32'd4)",
        "concat(4'd0, a:bv<32>[31:4])",
    );
}

#[test]
fn test_simplify_arithmetic_shift_right() {
    // shift a constant by a constant
    ts("arithmetic_shift_right(3'b101, 3'd0)", "3'b101");
    ts("arithmetic_shift_right(3'b101, 3'd1)", "3'b110");
    ts("arithmetic_shift_right(3'b101, 3'd2)", "3'b111");
    ts("arithmetic_shift_right(3'b101, 3'd3)", "3'b111");

    // shift by a constant
    ts("arithmetic_shift_right(a : bv<3>, 3'd0)", "a : bv<3>");
    ts(
        "arithmetic_shift_right(a : bv<3>, 3'd1)",
        "sext(a : bv<3>[2:1], 1)",
    );
    ts(
        "arithmetic_shift_right(a : bv<3>, 3'd2)",
        "sext(a : bv<3>[2], 2)",
    );
    ts(
        "arithmetic_shift_right(a : bv<3>, 3'd3)",
        "sext(a : bv<3>[2], 2)",
    );
}

#[test]
fn test_simplify_add() {
    // add constants
    ts("add(true, true)", "false");
    ts("add(true, false)", "true");
    ts("add(false, false)", "false");
    ts("add(15'd123, 15'd321)", "15'd444");

    // add zero
    ts("add(a : bv<4>, 4'd0)", "a : bv<4>");
    ts("add(4'd0, a : bv<4>)", "a : bv<4>");
}

#[test]
fn test_simplify_mul() {
    // multiply constants
    ts("mul(true, true)", "true");
    ts("mul(true, false)", "false");
    ts("mul(false, false)", "false");
    ts("mul(17'd123, 17'd321)", "17'd39483");

    // multiply with zero
    ts("mul(a : bv<4>, 4'd0)", "4'd0");
    ts("mul(4'd0, a : bv<4>)", "4'd0");

    // multiply with one
    ts("mul(a : bv<4>, 4'd1)", "a : bv<4>");
    ts("mul(4'd1, a : bv<4>)", "a : bv<4>");

    // multiply with power of two (this includes a simplification of the left shift)
    ts("mul(a : bv<4>, 4'd2)", "concat(a : bv<4>[2:0],  1'b0)");
    ts("mul(a : bv<4>, 4'd4)", "concat(a : bv<4>[1:0], 2'b00)");
    ts("mul(a : bv<4>, 4'd8)", "concat(a : bv<4>[0],  3'b000)");
}

#[test]
fn test_simplify_concat() {
    // normalize concats
    ts(
        "concat(concat(a : bv<1>, b:bv<1>), c:bv<1>)",
        "concat(a : bv<1>, concat(b:bv<1>, c:bv<1>))",
    );

    // concat constants
    ts("concat(3'b110, 2'b01)", "5'b11001");
    ts("concat(3'b110, concat(false, true))", "5'b11001");
    ts("concat(concat(3'b110, false), true)", "5'b11001");

    // concat constants in the presence of other expressions
    ts(
        "concat(a : bv<3>, concat(false, true))",
        "concat(a:bv<3>, 2'b01)",
    );
    ts(
        "concat(concat(a : bv<3>, false), true)",
        "concat(a:bv<3>, 2'b01)",
    );
    ts(
        "concat(true, concat(false, a : bv<3>))",
        "concat(2'b10, a:bv<3>)",
    );
    ts(
        "concat(concat(true, false), a : bv<3>)",
        "concat(2'b10, a:bv<3>)",
    );
    ts(
        "concat(3'b101, concat(true, concat(false, a : bv<3>)))",
        "concat(5'b10110, a:bv<3>)",
    );
}

// from maltese-smt:
// https://github.com/ucb-bar/maltese-smt/blob/main/test/maltese/smt/SMTSimplifierSpec.scala
#[test]
fn test_simplify_bool_equality() {
    ts("eq(b : bv<1>, true)", "b : bv<1>");
    ts("eq(b : bv<1>, false)", "not(b : bv<1>)");
    ts("eq(false, b : bv<1>)", "not(b : bv<1>)");
}

// from maltese-smt
#[test]
fn test_simplify_comparison_to_concat() {
    // eq over concat should be split up
    ts(
        "eq(c:bv<5>, concat(a:bv<2>, b:bv<3>))",
        "and(eq(a:bv<2>, c:bv<5>[4:3]), eq(b:bv<3>,c[2:0]))",
    );
    ts(
        "eq(concat(a:bv<2>, b:bv<3>), c:bv<5>)",
        "and(eq(a:bv<2>, c:bv<5>[4:3]), eq(b:bv<3>,c[2:0]))",
    );

    // now with nested concats
    ts(
        "eq(c:bv<5>, concat(concat(a1:bv<1>, a0:bv<1>), b: bv<3>))",
        "and(eq(a1:bv<1>, c:bv<5>[4]), and(eq(a0:bv<1>, c[3]), eq(b:bv<3>, c[2:0])))",
    );
}

#[test]
fn test_simplify_comparison_to_zero_extend() {
    ts("eq(4'd0, zext(a:bv<5>, 4)[8:5])", "true");
    ts("eq(4'd1, zext(a:bv<5>, 4)[8:5])", "false");
    ts("eq(2'b10, zext(a:bv<1>, 1))", "false");
    ts("eq(concat(4'd0, a:bv<5>), zext(a:bv<5>, 4))", "true");
}

// from maltese-smt
#[test]
fn test_simplify_bit_masks() {
    ts(
        "and(concat(a: bv<2>, b: bv<3>), 5'b11000",
        "concat(a:bv<2>, 3'd0)",
    );
    ts(
        "and(concat(a: bv<2>, b: bv<3>), 5'b10000",
        "concat(a:bv<2>[1], 4'd0)",
    );
    ts(
        "and(concat(a: bv<2>, b: bv<3>), 5'b01000",
        "concat(concat(1'd0, a:bv<2>[0]), 3'd0)",
    );
    ts(
        "and(concat(a: bv<2>, b: bv<3>), 5'b00100",
        "concat(concat(2'd0, b:bv<3>[2]), 2'd0)",
    );
    ts(
        "and(concat(a: bv<2>, b: bv<3>), 5'b00010",
        "concat(concat(3'd0, b:bv<3>[1]), 1'd0)",
    );
    ts(
        "and(concat(a: bv<2>, b: bv<3>), 5'b00001",
        "concat(4'd0, b:bv<3>[0])",
    );
}

// from maltese-smt
#[test]
fn test_simplify_slice_on_sign_extension() {
    // sext is essentially like a concat and thus we want to push the slice into it
    ts("sext(a:bv<4>, 2)[3:0]", "a:bv<4>");
    ts("sext(a:bv<4>, 2)[3:1]", "a:bv<4>[3:1]");
    ts("sext(a:bv<4>, 2)[2:1]", "a:bv<4>[2:1]");
    ts("sext(a:bv<4>, 2)[4:0]", "sext(a:bv<4>, 1)");
    ts("sext(a:bv<4>, 2)[5:0]", "sext(a:bv<4>, 2)");
    ts("sext(a:bv<4>, 2)[4:1]", "sext(a:bv<4>[3:1], 1)");
}

// TODO: add slice simplifications: https://github.com/ekiwi/maltese-private/blob/main/test/maltese/smt/SMTSimplifierSliceSpec.scala

// TODO: add missing literals simplifications: https://github.com/ekiwi/maltese-private/blob/main/test/maltese/smt/SMTSimplifierLiteralsSpec.scala
