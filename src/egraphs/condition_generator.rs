// Copyright 2024 Cornell University
// released under BSD 3-Clause License
// author: Amelia Dobis <amelia.dobis@princeton.edu>
// author: Mohanna Shahrad <mohanna@princeton.edu>

use crate::expr::*;
use crate::egraphs::*;
use clap::builder::StyledStr;
use egg::Language;
use std::cmp::Ordering;
use std::fmt::{Display, Formatter};
use rustlearn::prelude::*;
use rustlearn::trees::decision_tree::Hyperparameters;


// Goal: Prove the correctness of the following example
// module spec (A, B ,M, N, O);
//     input [15:0] A, B;
//     input [3:0] M, N;
//     output [62:0] O;
//     wire [30:0] D;
//     wire [30:0] E ;
//     assign D = A << M;
//     assign E = B << N;
//     assign O = D * E ;
// endmodule
// ========================
// module impl (A, B, M, N, O);
//     input [15:0] A, B;
//     input [3:0] M, N;
//     output [62:0] O;
//     wire [31:0] C;
//     wire [4:0] P;
//     assign C = A * B;
//     assign P = M + N;
//     assign O = C << P;
// endmodule
// ========================
// To do this we must generate the conditions for the following rewrites:
// 1. a << (b + c) -> (a << b) << c
// 2. a * (b << c) -> (a * b) << c
// 3. a << const -> a * 2^const
// 4. a * 2 -> a + a

// Associates a sign to a width
struct SignedWidth {
    s: bool,
    w: u32,
    sym: &'static str
}

// Set of parameters to a condtion
struct ConditionParam {
    wr: u32,
    params: Vec<SignedWidth>
}

struct BooleanFeature<'a> {
    param: &'a ConditionParam,
    features: Vec<(String, bool)>,
}

// Condition generation for the following rewrite rule
// 1. a << (b + c) -> (a << b) << c
// @param w_max: the max width we support in the condition
// @returns: string version of the condition
// e.g. "(| (& ?w0 (! ?w1)) (!w0))"
pub fn gen_condition1(w_max: u32) -> String {
    // Store check result in lut: ([wi si] -> bool)
    let mut lut: Vec<(ConditionParam, bool)> = Vec::new();

    // Loop over all inputs and concretize the values
    for wr in 0..w_max {
        for wa in 0..w_max {
            for wb in 0..w_max {
                for wc in 0..w_max {
                    for wbc in 0..w_max {
                        for wab in 0..w_max {
                            for sa in 0..1 {
                                for sb in 0..1 {
                                    for sc in 0..1 {
                                        for sbc in 0..1 {
                                            for sab in 0..1 {
                                                // Check if the concrete rewrite is legal
                                                let check = check_cond1(
                                                    wr, wa, wb, wc, wbc, wab, 
                                                    sa == 1, sb == 1, sc == 1, sbc == 1, sab == 1
                                                );
                                                
                                                // Only add the params to the lut if the check returned
                                                if let Some(c) = check {
                                                    lut.push(
                                                        (ConditionParam {
                                                            wr,
                                                            params: vec![
                                                                SignedWidth { sym: "wa", w: wa, s: sa == 1 },
                                                                SignedWidth { sym: "wb", w: wb, s: sb == 1 },
                                                                SignedWidth { sym: "wc", w: wc, s: sc == 1 },
                                                                SignedWidth { sym: "wbc", w: wbc, s: sbc == 1 },
                                                                SignedWidth { sym: "wab", w: wab, s: sab == 1 }
                                                            ]
                                                        }, c)
                                                    );
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
    }
    // TODO: Construct the training data using the LUT and a predefined set of boolean features
    todo!();
}

// Generates condition 1 as an artih expression
// Converts this expression to btor2
// Checks the btor2 version of the expression using bitwuzla
// if unsat -> true
// if sat -> false
// if error -> skip
// rewrite rule: a << (b + c) -> (a << b) << c
pub fn check_cond1(
    wr: u32, wa: u32, wb: u32, wc: u32,
    wbc: u32, wab: u32, sa: bool, sb: bool,
    sc: bool, sbc: bool, sab: bool 
) -> Option<bool> { 
    // Encode rewrite rule
    let mut ctx = Context::default();
    let a = ctx.bv_symbol("A", wa);
    let b = ctx.bv_symbol("B", wb);
    let c = ctx.bv_symbol("C", wc);
    // lhs: a << (b + c)
    let lhs = ctx.build(|cx| {
        let sr = sa & sb & sc;
        cx.apply_sign(
            cx.shift_left(
                cx.apply_sign(a, wa, sa),
                cx.apply_sign(   
                    cx.add( 
                        cx.apply_sign(b, wb, sb),
                        cx.apply_sign(c, wc, sc)
                    ), wbc, sbc
                )
            ), wr, sr
        )
    });
    // rhs: (a << b) << c
    let rhs = ctx.build(|cx| {
        let sr = sa & sb & sc;
        cx.apply_sign(
            cx.shift_left(
                cx.apply_sign(
                    cx.shift_left( 
                        cx.apply_sign(a, wa, sa),
                        cx.apply_sign(b, wb, sb)
                    ), wab, sab
                ),
                cx.apply_sign(c, wc, sc)
            ), wr, sr
        )
    });
    // check validity of the rewrite
    let miter = ctx.build(|cx| {
        cx.not(cx.bv_equal(lhs, rhs))
    });
    // TODO: Call SMT solver to check the miter and return result
    todo!();
 }


  // Given the LUT, generates the boolean features (for classifier fitting).
 // Input: LUT generated for each condition
 // Output: Vector of Boolean Features (for each ConditionParam, a vector of (String, bool) that represents the boolean feature)
 // TODO: maybe we wnat selective inclusion of the features, right now all of them are included
 pub fn gen_boolean_features(lut: &Vec<(ConditionParam, bool)>) -> Vec<BooleanFeature> {

    let mut features = Vec::new();

    // For demonstration: printing out the vector content
    for (param, flag) in lut {

        let mut feature_list = Vec::new();

        // Sign feature -> forall i: si == unsigned
        for sw in &param.params {

            let feature_name = format!("s_{}", sw.sym); 
            let feature_value = !sw.s; 
            feature_list.push((feature_name, feature_value));

        }

        // Width Equality and Inequality Features (features 14 - 15 - 16 in the paper)
        for i in 0..param.params.len() {
            for j in i + 1..param.params.len() {
                let sw1 = &param.params[i];
                let sw2 = &param.params[j];
                
                // Create the feature name in the form "w_<sym1> == w_<sym2>"
                let feature_width_eq = format!("w_{} == w_{}", sw1.sym, sw2.sym);
                let feature_width_neq = format!("w_{} < w_{}", sw1.sym, sw2.sym);
                let feature_width_increment = format!("w_{} + 1 < w_{}", sw1.sym, sw2.sym);
                let feature_width_decrement = format!("w_{} - 1 < w_{}", sw1.sym, sw2.sym);
                
                // The value of the feature is true if the widths are equal, false otherwise
                let width_eq_value = sw1.w == sw2.w;
                let width_neq_value = sw1.w < sw2.w;
                let width_increment_value = sw1.w + 1 < sw2.w;
                let width_decrement_value = sw1.w - 1 < sw2.w;

                feature_list.push((feature_width_eq, width_eq_value));
                feature_list.push((feature_width_neq, width_neq_value));
                feature_list.push((feature_width_increment, width_increment_value));
                feature_list.push((feature_width_decrement, width_decrement_value));
            }
        }

        // Sum and Shift Boolean Features (features 17 - 18 in the paper)
        for i in 0..param.params.len() {
            for j in 0..param.params.len() {
                for k in 0..param.params.len() {
                    if i != j && j != k && i != k {
                        let sw1 = &param.params[i];
                        let sw2 = &param.params[j];
                        let sw3 = &param.params[k];
                        
                        // Create the feature name in the form "w_<sym1> == w_<sym2>"
                        let feature_sum = format!("w_{} + w_{} < w_{}", sw1.sym, sw2.sym, sw3.sym);
                        let feature_shift = format!("w_{} + 2^w_{} < w_{}", sw1.sym, sw2.sym, sw3.sym);

                        // The value of the feature is true if the widths are equal, false otherwise
                        let width_sum_value = sw1.w + sw2.w < sw3.w;
                        let width_shift_value = sw1.w + 2u32.pow(sw2.w) < sw3.w;

                        feature_list.push((feature_sum, width_sum_value));
                        feature_list.push((feature_shift, width_shift_value));
                    }
                }
            }
        }

        let boolean_feature = BooleanFeature {
            param: param,       // we are borrowing the param instead of cloning
            features: feature_list,
        };

        features.push(boolean_feature);
    }

    features
}