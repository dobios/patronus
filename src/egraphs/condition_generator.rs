// Copyright 2024 Cornell University
// released under BSD 3-Clause License
// author: Amelia Dobis <amelia.dobis@princeton.edu>
// author: Mohanna Shahrad <mohanna@princeton.edu>

use crate::{expr::*, mc::{check_assuming, BITWUZLA_CMD}, smt::convert_expr};
use easy_smt::Response;
use linfa::dataset::Dataset;
use linfa::prelude::*;
use linfa_trees::DecisionTree;
use ndarray::{Array2, Array1};

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
pub struct SignedWidth {
    s: bool,
    w: u32,
    sym: &'static str
}

// Set of parameters to a condtion
pub struct ConditionParam {
    wr: u32,
    params: Vec<SignedWidth>
}

pub struct BooleanFeature<'a> {
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
    for wr in 1..w_max {
        for wa in 1..w_max {
            for wb in 1..w_max {
                for wc in 1..w_max {
                    for wbc in 1..w_max {
                        for wab in 1..w_max {
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
    let cond = fit_decision_classifier(&lut);
    
    cond
}

// Generates condition 1 as an artih expression
// Converts this expression to btor2
// Checks the btor2 version of the expression using bitwuzla
// rewrite rule: a << (b + c) -> (a << b) << c
pub fn check_cond1(
    wr: u32, wa: u32, wb: u32, wc: u32,
    wbc: u32, wab: u32, sa: bool, sb: bool,
    sc: bool, sbc: bool, sab: bool 
) -> Option<bool> { 
    // Encode rewrite rule
    let mut ctx = Context::default();
    println!("**********************");
    println!("{}", wa);
    println!("**********************");
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
    
    // Check validity of the rewrite
    check(&mut ctx, lhs, rhs)
}

// Checks the validity of a rewrite rule using bitwuzla
// returns Some(true) if unsat
//         Some(false) if sat
//         None if error
pub fn check(ctx: &mut Context, lhs: ExprRef, rhs: ExprRef) -> Option<bool> {
    // Build out miter for EC
    let miter = ctx.build(|cx| {
        cx.not(cx.bv_equal(lhs, rhs))
    });
    // Create a solver instance
    let solver = BITWUZLA_CMD;
    let mut smt_ctx = easy_smt::ContextBuilder::new()
            .solver(solver.name, solver.args)
            .build().unwrap();
    smt_ctx.set_logic("QF_ABV").unwrap();

    let smt_expr = convert_expr(
        &smt_ctx, &ctx,
        miter, &|_| None
    );

    // Call the solver to check the result
    let resp = check_assuming(
        &mut smt_ctx, smt_expr, &solver
    ).unwrap();
    if resp == Response::Unknown {
        return None
    }
    Some(resp == Response::Unsat)
}


// Given the LUT, fit the data in a DecisionClassifier
// TODO: the return value of this function should be a string of the final formula
pub fn fit_decision_classifier<'a>(lut: &'a Vec<(ConditionParam, bool)>) -> String{
    
    let mut features = Vec::with_capacity(lut.len());
    let mut labels = Vec::with_capacity(lut.len());

    for (param, eq_result) in lut {
        let feature_list = gen_boolean_features(param);
        features.push(BooleanFeature {
            param,
            features: feature_list,
        });

        // Add label (convert bool to 1 or 0)
        labels.push(if *eq_result { 1 } else { 0 });
    }

    let feature_vectors = features.iter()
        .map(|feature| feature.features.iter()
            .map(|(_, value)| if *value { 1.0 } else { 0.0 })
            .collect::<Vec<_>>())
        .collect::<Vec<_>>();

    let num_rows = feature_vectors.len();
    let num_cols = feature_vectors[0].len();

    let features_array = Array2::from_shape_vec(
        (num_rows, num_cols),
        feature_vectors.into_iter().flatten().collect()).unwrap();

    let labels_array: Array1<i32> = Array1::from(labels);
    let labels_usize: Array1<usize> = labels_array.mapv(|x| x as usize);

    // Make the dataset: labels are the result of the EC check, features are the Boolean Features extracted
    let dataset = Dataset::new(features_array, labels_usize);

    // Build the DecisionTreeClassifier
    let model = DecisionTree::params()
        .max_depth(Some(5)) // Max depth for the decision tree
        .fit(&dataset)   
        .unwrap();

    let accuracy = model.predict(&dataset)
        .confusion_matrix(&dataset)
        .unwrap()
        .accuracy();

    println!("Trained decision tree accuracy:\n{:?}", accuracy);
    println!("Model:\n{:?}", model);

    // TODO: build a string-formatted condition based on the model
    // for now return dummy string
    let output = String::from("condition");
    output
    
}

// Given a single ConditionParam from the LUT, generates the boolean features
pub fn gen_boolean_features(param: &ConditionParam) -> Vec<(String, bool)> {
    let mut feature_list = Vec::new();

    // Generate Sign features
    for sw in &param.params {
        let feature_name = format!("s_{}", sw.sym);
        let feature_value = !sw.s; // Negate the sign
        feature_list.push((feature_name, feature_value));
    }

    // Generate Width Equality and Inequality features
    for i in 0..param.params.len() {
        for j in i + 1..param.params.len() {
            let sw1 = &param.params[i];
            let sw2 = &param.params[j];
            feature_list.push((
                format!("w_{} == w_{}", sw1.sym, sw2.sym),
                sw1.w == sw2.w,
            ));
            feature_list.push((
                format!("w_{} < w_{}", sw1.sym, sw2.sym),
                sw1.w < sw2.w,
            ));
        }
    }

    // Generate Sum and Shift Boolean Features
    for i in 0..param.params.len() {
        for j in 0..param.params.len() {
            for k in 0..param.params.len() {
                if i != j && j != k && i != k {
                    let sw1 = &param.params[i];
                    let sw2 = &param.params[j];
                    let sw3 = &param.params[k];
                    feature_list.push((
                        format!("w_{} + w_{} < w_{}", sw1.sym, sw2.sym, sw3.sym),
                        sw1.w + sw2.w < sw3.w,
                    ));
                    feature_list.push((
                        format!("w_{} + 2^w_{} < w_{}", sw1.sym, sw2.sym, sw3.sym),
                        sw1.w + 2u32.pow(sw2.w) < sw3.w,
                    ));
                }
            }
        }
    }

    feature_list
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_shift_rewrite() {
        let resString = gen_condition1(2);
        println!("{}", resString);
    }
}