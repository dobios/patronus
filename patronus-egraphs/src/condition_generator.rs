// Copyright 2024 Cornell University
// released under BSD 3-Clause License
// author: Amelia Dobis <amelia.dobis@princeton.edu>
// author: Mohanna Shahrad <mohanna@princeton.edu>

static TRAINING_DATA_PATH: &str = "./src/egraphs/train_data.csv";
static CONFLICT_RESOLVED_TRAINING_DATA: &str = "./src/egraphs/train_data_modified.csv";

use crate::trees::Branch;
use easy_smt::*;
use csv::ReaderBuilder;
use csv::Writer;
use patronus::expr::*;
use patronus::mc::*;
use patronus::smt::*;
use std::cmp;
use std::fs::File;
use std::error::Error;
use std::collections::VecDeque;
use std::collections::{HashMap, HashSet};

// for now I'm changing the source code of rustrees locally 
use super::trees::{DecisionTree, Tree, Node};
use super::dataset::Dataset;
use super::utils::accuracy;
// use rustrees::{DecisionTree, Tree, Dataset, accuracy};

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

#[derive(Debug)]
pub struct SignedWidth {
    s: bool,
    w: u32,
    sym: &'static str
}

// Set of parameters to a condtion
#[derive(Debug)]
pub struct ConditionParam {
    wr: u32,
    params: Vec<SignedWidth>
}

#[derive(Debug)]
struct ParameterMap {
    parameters: Vec<String>,
    label: String,    
    line_number: usize,
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
    let mut ctx = patronus::expr::Context::default();
    let a = ctx.bv_symbol("A", wa);
    let b = ctx.bv_symbol("B", wb);
    let c = ctx.bv_symbol("C", wc);
    // lhs: a << (b + c)
    let lhs = ctx.build(|cx| {
        let w_in_bc = cmp::max(wb, wc) + 1;
        cx.shift_left(a, 
            cx.apply_sign(
                cx.add(b, c), 
                w_in_bc, wbc, sbc)
        )
    });

    // rhs: (a << b) << c
    let rhs = ctx.build(|cx| {
        // left shift is unsigned so we ignore it here
        cx.shift_left(
            cx.shift_left(a,b),
            c
        )
    });
    
    // Check validity of the rewrite
    check(&mut ctx, lhs, rhs)
}

// Checks the validity of a rewrite rule using bitwuzla
// returns Some(true) if unsat
//         Some(false) if sat
//         None if error
pub fn check(ctx: &mut patronus::expr::Context, lhs: ExprRef, rhs: ExprRef) -> Option<bool> {

    // Build out miter for EC
    let miter = ctx.build(|cx| {
        cx.not(cx.equal(lhs, rhs))
    });
    // Create a solver instance
    let solver: SmtSolverCmd = BITWUZLA_CMD;
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
pub fn fit_decision_classifier<'a>(lut: &'a Vec<(ConditionParam, bool)>) -> String{

    let mut all_rows: Vec<Vec<String>> = Vec::new();

    // Add headers as the first row
    let mut headers: Vec<String> = Vec::new();
    
    if let Some((param, _)) = lut.get(0) {
        let feature_list = gen_boolean_features(param);
        for (feature_name, _) in feature_list {
            headers.push(feature_name);
        }
    }
    // Add the "eq_check" column as the label of the data
    headers.push("eq_check".to_string());
    
    all_rows.push(headers);  

    // Iterate through each example in the lookup table (lut)
    for (param, eq_result) in lut {
        let feature_list = gen_boolean_features(param);

        // Create a row of features 
        let mut row = Vec::new();
        
        for (_, value) in feature_list {
            row.push(if value { "1".to_string() } else { "0".to_string() });
        }

        // Finally add the label / eq_result to the row
        row.push(if *eq_result { "1".to_string() } else { "0".to_string() }); 

        all_rows.push(row); 
    }

    let mut wtr = Writer::from_path(TRAINING_DATA_PATH).unwrap();
    for row in all_rows.iter() {
        wtr.write_record(row).unwrap();
    }
    wtr.flush().unwrap();

    // Start fitting data on the decision classifier
    let dataset = Dataset::read_csv(TRAINING_DATA_PATH, ",");

    let dt = DecisionTree::train_clf(
    &dataset, 
    Some(15), 
    Some(1),  
    None,     
    Some(42), 
    );
 
    let pred = dt.predict(&dataset);
    let acc = accuracy(&dataset.target_vector, &pred);
    
    println!("Accuracy: {}", acc);

    if acc == 1.0 {
        // Generate Condition based on the tree
        let mut paths = Vec::new();
        let mut path = VecDeque::new();
        traverse_and_find_paths(&dt.tree, &(dt.tree.nodes[dt.tree.root]), &mut path, &mut paths);

        let inner_conditions: Vec<String> = paths.iter().map(|inner| {
            format!("({})", inner.join(" AND "))
        }).collect();
    
        return inner_conditions.join(" OR ")
    }

    else {
        // There are some conflicts in our data 
        println!("Remove Conflict in the Data");
        let lines_to_discard = check_contradictions(TRAINING_DATA_PATH).unwrap();

        for &index in &lines_to_discard {
            if let Some(row) = all_rows.get_mut(index-1) {
                // Update the last column (the last element in the row)
                if let Some(last_column) = row.last_mut() {
                    *last_column = "0".to_string().clone();
                }
            }
        }

        let mut wtr = Writer::from_path(CONFLICT_RESOLVED_TRAINING_DATA).unwrap();
        for row in &all_rows {
            wtr.write_record(row).unwrap();
        }
        wtr.flush().unwrap();

        // Now re-train
        let dataset = Dataset::read_csv(CONFLICT_RESOLVED_TRAINING_DATA, ",");
 
        let dt = DecisionTree::train_clf(
        &dataset, 
        Some(15),        
        Some(1),  
        None,     
        Some(42), 
        );
    
        let pred = dt.predict(&dataset);
        let new_acc = accuracy(&dataset.target_vector, &pred);
        
        println!("Accuracy after resolving conflict: {}", new_acc);
        let mut paths = Vec::new();
        let mut path = VecDeque::new();
        traverse_and_find_paths(&dt.tree, &(dt.tree.nodes[dt.tree.root]), &mut path, &mut paths);

        // println!("************************");
        // println!("{:?}", paths );
        // println!("************************");

        let inner_conditions: Vec<String> = paths.iter().map(|inner| {
            format!("({})", inner.join(" AND "))
        }).collect();
    
        return inner_conditions.join(" OR ")
    }
    
}

// Given a single ConditionParam from the LUT, generates the boolean features
pub fn gen_boolean_features(param: &ConditionParam) -> Vec<(String, bool)> {
    let mut feature_list = Vec::new();

    // Generate Sign features
    for sw in &param.params {
        let feature_name = format!("s_{} == u", sw.sym);
        let feature_value = !sw.s; // Negate the sign
        feature_list.push((feature_name, feature_value));

        // println!("Feature: {}, Value: {}", format!("s_{}", sw.sym), !sw.s);
    }

    // Before adding the width constraints consider the union of (param.params and param.wr)
    let result: SignedWidth =  SignedWidth { sym: "wr", w: param.wr, s: true };
    let mut allWidths: Vec<&SignedWidth> = Vec::new();
    for i in 0..param.params.len() {
        allWidths.push(&param.params[i]);
    }
    allWidths.push(&result);
    

    // Generate Width Equality and Inequality features

    for i in 0..allWidths.len() {
        for j in i+1..allWidths.len() {
            let sw1 = allWidths[i];
            let sw2 = allWidths[j];
            feature_list.push((
                format!("w_{} == w_{}", sw1.sym, sw2.sym),
                sw1.w == sw2.w,
            ));
            // println!("Feature: {}, Value: {}", format!("w_{} == w_{}", sw1.sym, sw2.sym), sw1.w == sw2.w);
        }
    }

    for i in 0..allWidths.len() {
        for j in 0..allWidths.len() {
            if i != j {
                let sw1 = allWidths[i];
                let sw2 = allWidths[j];
                
                feature_list.push((
                    format!("w_{} < w_{}", sw1.sym, sw2.sym),
                    sw1.w < sw2.w,
                ));

                feature_list.push((
                    format!("w_{} + 1 < w_{}", sw1.sym, sw2.sym),
                    sw1.w + 1 < sw2.w,
                ));

                feature_list.push((
                    format!("w_{} - 1 < w_{}", sw1.sym, sw2.sym),
                    sw1.w - 1 < sw2.w,
                ));
                // println!("Feature: {}, Value: {}", format!("w_{} < w_{}", sw1.sym, sw2.sym), sw1.w < sw2.w);
            }
        }
    }

    // Generate Sum and Shift Boolean Features
    for i in 0..allWidths.len() {
        for j in 0..allWidths.len() {
            for k in 0..allWidths.len() {
                if i != j && j != k && i != k {
                    let sw1 = allWidths[i];
                    let sw2 = allWidths[j];
                    let sw3 = allWidths[k];
                    feature_list.push((
                        format!("w_{} + w_{} < w_{}", sw1.sym, sw2.sym, sw3.sym),
                        sw1.w + sw2.w < sw3.w,
                    ));
                    // println!("Feature: {}, Value: {}", format!("w_{} + w_{} < w_{}", sw1.sym, sw2.sym, sw3.sym),  sw1.w + sw2.w < sw3.w);
                    feature_list.push((
                        format!("w_{} + 2^w_{} < w_{}", sw1.sym, sw2.sym, sw3.sym),
                        sw1.w + 2u32.pow(sw2.w) < sw3.w,
                    ));
                    // println!("Feature: {}, Value: {}", format!("w_{} + 2^w_{} < w_{}", sw1.sym, sw2.sym, sw3.sym), sw1.w + 2u32.pow(sw2.w) < sw3.w);
                }
            }
        }
    }

    feature_list
}

// This function will recursively traverse the tree from the root to find leaves with prediction = 1
fn traverse_and_find_paths(
    model: &Tree, 
    node: &Node,
    path: &mut VecDeque<String>,
    paths: &mut Vec<Vec<String>>,
) {

    match &node {
        Node::Leaf(l) => {
            if l.prediction == 1.0 {
                paths.push(path.iter().cloned().collect());
            }
        }

        // If the node is a branch then traverse
        Node::Branch(b) => {
            if b.prediction == 1.0 {
                paths.push(path.iter().cloned().collect());
            } else { 
                // On the left the features are not met
                path.push_back( format!("!({})", model.feature_names[b.feature].clone()) );
                traverse_and_find_paths(model, &(model.nodes[b.left]), path, paths);
                path.pop_back();

                // On the right the features are met
                path.push_back( model.feature_names[b.feature].clone());
                traverse_and_find_paths(model, &( model.nodes[b.right]), path, paths);
                path.pop_back();
            }
        }
    }

}

fn check_contradictions(csv_file: &str) -> Result<Vec<usize>, Box<dyn Error>> {
    let mut rdr = ReaderBuilder::new().has_headers(true).from_path(csv_file)?;

    let mut records: Vec<ParameterMap> = Vec::new();
    for (line_number, result) in rdr.records().enumerate() {
        let record = result?;
        let parameters: Vec<String> = record.iter().take(record.len() - 1).map(|s| s.to_string()).collect();
        let label = record.get(record.len() - 1).unwrap_or_default().to_string();

        records.push(ParameterMap {
            parameters,
            label,
            line_number: line_number + 2, // Toaccount for header and 1-based indexing
        });

    }
    // Group records by parameters (excluding the last column)
    let mut parameter_dict: HashMap<Vec<String>, Vec<(String, usize)>> = HashMap::new();

    for record in records {
        parameter_dict
            .entry(record.parameters)
            .or_insert_with(Vec::new)
            .push((record.label, record.line_number));
    }

    // Find contradictions (rows with same parameters but different labels)
    let mut contradictory_lines: Vec<usize> = Vec::new();
    for (parameters, label_line_pairs) in parameter_dict {
        let mut labels: HashSet<String> = HashSet::new();
        let mut line_numbers: Vec<usize> = Vec::new();

        for (label, line_number) in &label_line_pairs {
            labels.insert(label.clone());
            line_numbers.push(*line_number);
        }

        // If there are multiple unique labels for these parameters, there is a contradiction
        if labels.len() > 1 {
            for (label, line_number) in label_line_pairs {
                // If label is "True", we disable rewrite for them
                if label == "1" {
                    contradictory_lines.push(line_number);
                }
            }
        }
    }

    // Return the list of lines that should be discarded (those with contradictions)
    Ok(contradictory_lines)
}

// note that here if the sign is "signed" the value of the "s" is 1
fn parse_condition_param(
    w: Vec<u32>,    
    s: Vec<&str>,   //(signed/unsigned)
) -> ConditionParam {
    ConditionParam {
        wr: w[2],  // `w6` is wr
        params: vec![
            SignedWidth { sym: "w1", w: w[0], s: s[0] == "signed" },
            SignedWidth { sym: "w2", w: w[1], s: s[1] == "signed" },
            // SignedWidth { sym: "w3", w: w[2], s: s[2] == "signed" },
            // SignedWidth { sym: "w4", w: w[3], s: s[3] == "signed" },
            // SignedWidth { sym: "w5", w: w[4], s: s[4] == "signed" },
        ],
    }
}

fn read_and_populate_lut(file_path: &str) -> Result<Vec<(ConditionParam, bool)>, Box<dyn Error>> {
    let file = File::open(file_path)?;
    let mut rdr = ReaderBuilder::new().has_headers(true).from_reader(file); // Automatically skip header row
    let mut lut: Vec<(ConditionParam, bool)> = Vec::new();

    for result in rdr.records() {
        let record = result?;

        let w: Vec<u32> = record.iter().take(3).map(|field| field.parse().unwrap_or(0)).collect();
        let s: Vec<&str> = record.iter().skip(3).take(2).collect();
        let eq_check: bool = record.get(5).unwrap_or("False") == "True";

        // Create the ConditionParam and push it into the LUT
        let condition_param = parse_condition_param(w, s);
        lut.push((condition_param, eq_check));
    }

    Ok(lut)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_shift_rewrite() {
        // let resString = gen_condition1(2);
        // println!("{}", resString);

        let lut = read_and_populate_lut("./src/egraphs/input.csv").unwrap();

        // Print the LUT to verify it's populated correctly
        // for (condition_param, bool_val) in &lut {
        //     println!("{:?} => {}", condition_param.params, bool_val);
        // }

        let condition = fit_decision_classifier(&lut);
    
        // Print or use the model output
        println!("Condition is: {}", condition);
    }
}