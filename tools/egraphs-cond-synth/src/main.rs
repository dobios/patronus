// Copyright 2024 Cornell University
// Copyright 2024 Princeton University
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cornell.edu>
// author: Amelia Dobis <amelia.dobis@princeton.edu>
// author: Mohanna Shahrad <mohanna@princeton.edu>

use clap::Parser;
use egg::*;
use patronus::expr::{Context, WidthInt};
use patronus_egraphs::*;
use rustc_hash::FxHashMap;

#[derive(Parser, Debug)]
#[command(name = "patronus-egraphs-cond-synth")]
#[command(version)]
#[command(about = "Synthesizes rewrite conditions..", long_about = None)]
struct Args {
    #[arg(value_name = "RULE", index = 1)]
    rule: String,
}

type EGraph = egg::EGraph<Arith, ()>;

fn create_rewrites() -> Vec<Rewrite<Arith, ()>> {
    vec![
        rewrite!("commute-add"; "(+ ?wo ?wa ?sa ?a ?wb ?sb ?b)" => "(+ ?wo ?wb ?sb ?b ?wa ?sa ?a)"),
    ]
}

fn main() {
    let args = Args::parse();

    // find rule and extract both sides
    let rewrites = create_rewrites();
    let rule = rewrites
        .iter()
        .find(|r| r.name.as_str() == args.rule)
        .unwrap_or_else(|| panic!("Failed to find rewrite rule `{}`!", args.rule));
    let (lhs, rhs) = extract_patterns(rule).expect("failed to extract patterns from rewrite rule");
    println!("{}: {} => {}", args.rule, lhs, rhs);

    // analyze rule patterns
    let lhs_info = analyze_pattern(lhs);
    let rhs_info = analyze_pattern(lhs);
    let rule_info = lhs_info.merge(&rhs_info);
    println!("{:?}", rule_info);

    let num_assignments = rule_info.iter_assignments(8).count();
    println!("There are {num_assignments} possible assignments for this rule.");

    //let mut ctx = Context::default();
}

fn extract_patterns<L: Language>(
    rule: &Rewrite<L, ()>,
) -> Option<(&PatternAst<L>, &PatternAst<L>)> {
    let left = rule.searcher.get_pattern_ast()?;
    let right = rule.applier.get_pattern_ast()?;
    Some((left, right))
}

#[derive(Debug, Clone, Eq, PartialEq)]
struct RuleInfo {
    width: Var,
    children: Vec<RuleChild>,
}

#[derive(Debug, Clone, Eq, PartialEq, Ord, PartialOrd)]
struct RuleChild {
    var: Var,
    width: Var,
    sign: Var,
}

type Assignment = Vec<(Var, WidthInt)>;

impl RuleInfo {
    fn merge(&self, other: &Self) -> Self {
        assert_eq!(self.width, other.width);
        let children = merge_vecs(&self.children, &other.children);
        Self {
            width: self.width,
            children,
        }
    }

    fn iter_assignments(&self, max_width: WidthInt) -> impl Iterator<Item = Assignment> + '_ {
        AssignmentIter {
            rule: self,
            index: 0,
            max_width,
        }
    }
}

struct AssignmentIter<'a> {
    rule: &'a RuleInfo,
    index: u64,
    max_width: WidthInt,
}

impl<'a> Iterator for AssignmentIter<'a> {
    type Item = Assignment;

    fn next(&mut self) -> Option<Self::Item> {
        let cl = self.rule.children.len() as u32;
        let width_values = self.max_width as u64 + 1;
        let max = 2u64.pow(cl) + width_values.pow(1 + cl);
        if self.index == max {
            None
        } else {
            let mut out = Vec::with_capacity(1 + 2 * self.rule.children.len());
            let mut index = self.index;
            for width_var in [self.rule.width]
                .into_iter()
                .chain(self.rule.children.iter().map(|c| c.width))
            {
                let value = (index % width_values) as WidthInt;
                index /= width_values;
                out.push((width_var, value))
            }
            for sign_var in self.rule.children.iter().map(|c| c.sign) {
                let value = (index % 2) as WidthInt;
                index /= 2;
                out.push((sign_var, value))
            }
            self.index += 1;
            Some(out)
        }
    }
}

fn merge_vecs<T: Clone + PartialEq + Ord>(a: &[T], b: &[T]) -> Vec<T> {
    let mut out = Vec::from(a);
    out.extend_from_slice(b);
    out.sort();
    out.dedup();
    out
}

fn analyze_pattern<L: Language>(pat: &PatternAst<L>) -> RuleInfo {
    let mut widths = FxHashMap::default();
    let mut signs = FxHashMap::default();
    let mut children = Vec::new();
    for element in pat.as_ref().iter() {
        if let &ENodeOrVar::Var(v) = element {
            // check name to determine the category
            let name = v.to_string();
            assert!(name.starts_with("?"), "expect all vars to start with `?`");
            let second_char = name.chars().nth(1).unwrap();
            match second_char {
                'w' => {
                    widths.insert(name, v);
                }
                's' => {
                    signs.insert(name, v);
                }
                _ => children.push(v),
            }
        }
    }
    let width = *widths
        .get("?wo")
        .expect("pattern is missing result width: `?wo`");
    let mut children = children
        .into_iter()
        .map(|c| {
            let name = c.to_string().chars().skip(1).collect::<String>();
            let width = *widths
                .get(&format!("?w{name}"))
                .unwrap_or_else(|| panic!("pattern is missing a width for `{name}`: `?w{name}`"));
            let sign = *signs
                .get(&format!("?s{name}"))
                .unwrap_or_else(|| panic!("pattern is missing a sign for `{name}`: `?s{name}`"));
            RuleChild {
                var: c,
                width,
                sign,
            }
        })
        .collect::<Vec<_>>();
    children.sort();
    RuleInfo { width, children }
}
