// Copyright 2024 Cornell University
// released under BSD 3-Clause License
// author: Amelia Dobis <amelia.dobis@princeton.edu>
// author: Mohanne Shahrad <mohanna@princeton.edu>

use crate::expr::*;
use crate::egraphs::*;
use egg::Language;
use std::cmp::Ordering;
use std::fmt::{Display, Formatter};


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
    w: u32
}

// Set of parameters to a condtion
struct ConditionParam {
    wr: u32,
    params: Vec<SignedWidth>
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
                                                                SignedWidth { w: wa, s: sa == 1 },
                                                                SignedWidth { w: wb, s: sb == 1 },
                                                                SignedWidth { w: wc, s: sc == 1 },
                                                                SignedWidth { w: wbc, s: sbc == 1 },
                                                                SignedWidth { w: wab, s: sab == 1}
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
    return "".to_string();
}

// Generates condition 1 as an artih expression
// Converts this expression to btor2
// Checks the btor2 version of the expression using bitwuzla
// if unsat -> true
// if sat -> false
// if error -> skip
pub fn check_cond1(
    wr: u32, wa: u32, wb: u32, wc: u32,
    wbc: u32, wab: u32, sa: bool, sb: bool,
    sc: bool, sbc: bool, sab: bool 
) -> Option<bool> { todo!(); }