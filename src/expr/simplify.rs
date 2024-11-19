// Copyright 2023 The Regents of the University of California
// Copyright 2024 Cornell University
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cornell.edu>

use super::{
    do_transform_expr, BVLitValue, Context, Expr, ExprMetaData, ExprRef, TypeCheck, WidthInt,
};
use baa::BitVecOps;

/// Performs simplification and canonicalization on expressions and caches the results.
pub struct Simplifier<T: ExprMetaData<Option<ExprRef>>> {
    cache: T,
}

impl<T: ExprMetaData<Option<ExprRef>>> Simplifier<T> {
    pub fn new(cache: T) -> Self {
        Self { cache }
    }

    pub fn simplify(&mut self, ctx: &mut Context, e: ExprRef) -> ExprRef {
        do_transform_expr(ctx, &mut self.cache, vec![e], simplify);
        self.cache[e].unwrap()
    }
}

/// Simplifies one expression (not its children)
pub(crate) fn simplify(ctx: &mut Context, expr: ExprRef, children: &[ExprRef]) -> Option<ExprRef> {
    match (ctx.get(expr).clone(), children) {
        (Expr::BVNot(_, _), [e]) => simplify_bv_not(ctx, *e),
        (Expr::BVZeroExt { by, .. }, [e]) => simplify_bv_zero_ext(ctx, *e, by),
        (Expr::BVSlice { lo, hi, .. }, [e]) => simplify_bv_slice(ctx, *e, lo, hi),
        (Expr::BVIte { .. }, [cond, tru, fals]) => simplify_ite(ctx, *cond, *tru, *fals),
        (Expr::BVAnd(..), [a, b]) => simplify_bv_and(ctx, *a, *b),
        (Expr::BVOr(..), [a, b]) => simplify_bv_or(ctx, *a, *b),
        (Expr::BVXor(..), [a, b]) => simplify_bv_xor(ctx, *a, *b),

        _ => None,
    }
}

fn simplify_ite(ctx: &mut Context, cond: ExprRef, tru: ExprRef, fals: ExprRef) -> Option<ExprRef> {
    // ite(_, a, a) -> a
    if tru == fals {
        return Some(tru);
    }

    // constant condition
    if let Expr::BVLiteral(value) = ctx.get(cond) {
        if value.get(ctx).is_fals() {
            // ite(false, a, b) -> b
            return Some(fals);
        } else {
            // ite(true,  a, b) -> a
            return Some(tru);
        }
    }

    // boolean return type
    let value_width = ctx.get(tru).get_bv_type(ctx).unwrap();
    debug_assert_eq!(
        ctx.get(fals).get_bv_type(ctx),
        ctx.get(tru).get_bv_type(ctx)
    );
    if value_width == 1 {
        if let (Expr::BVLiteral(vt), Expr::BVLiteral(vf)) = (ctx.get(tru), ctx.get(fals)) {
            let res = match (
                vt.get(ctx).to_bool().unwrap(),
                vf.get(ctx).to_bool().unwrap(),
            ) {
                // ite(cond, true, false) -> cond
                (true, false) => cond,
                // ite(cond, false, true) -> !cond
                (false, true) => ctx.not(cond),
                _ => unreachable!(
                    "both arguments are the same, this should have been handled earlier"
                ),
            };
            return Some(res);
        }
    }
    None
}

enum Lits {
    Two(BVLitValue, BVLitValue),
    One((BVLitValue, ExprRef), ExprRef),
    None(ExprRef, ExprRef),
}

/// Finds the maximum number of literals. Only works on commutative operations.
#[inline]
fn find_lits_commutative(ctx: &Context, a: ExprRef, b: ExprRef) -> Lits {
    match (ctx.get(a), ctx.get(b)) {
        (Expr::BVLiteral(va), Expr::BVLiteral(vb)) => Lits::Two(*va, *vb),
        (Expr::BVLiteral(va), _) => Lits::One((*va, a), b),
        (_, Expr::BVLiteral(vb)) => Lits::One((*vb, b), a),
        (_, _) => Lits::None(a, b),
    }
}

fn simplify_bv_and(ctx: &mut Context, a: ExprRef, b: ExprRef) -> Option<ExprRef> {
    // a & a -> a
    if a == b {
        return Some(a);
    }

    // other simplifications depend on whether one or two of the values are a constant
    match find_lits_commutative(ctx, a, b) {
        Lits::Two(va, vb) => {
            // concretely evaluate
            Some(ctx.bv_lit(&va.get(ctx).and(&vb.get(ctx))))
        }
        Lits::One((lit, lit_expr), expr) => {
            if lit.get(ctx).is_zero() {
                // a & 0 -> 0
                Some(lit_expr)
            } else if lit.get(ctx).is_all_ones() {
                // a & 1 -> a
                Some(expr)
            } else {
                // TODO: deal with partial masks, like: a & 0xf0 -> a[7:4] # 4'd0
                None
            }
        }
        Lits::None(_, _) => {
            match (ctx.get(a), ctx.get(b)) {
                // a & !a -> 0
                (Expr::BVNot(inner, w), _) if *inner == b => Some(ctx.zero(*w)),
                (_, Expr::BVNot(inner, w)) if *inner == b => Some(ctx.zero(*w)),
                _ => None,
            }
        }
    }
}

fn simplify_bv_or(ctx: &mut Context, a: ExprRef, b: ExprRef) -> Option<ExprRef> {
    // a | a -> a
    if a == b {
        return Some(a);
    }

    // other simplifications depend on whether one or two of the values are a constant
    match find_lits_commutative(ctx, a, b) {
        Lits::Two(va, vb) => {
            // concretely evaluate
            Some(ctx.bv_lit(&va.get(ctx).or(&vb.get(ctx))))
        }
        Lits::One((lit, lit_expr), expr) => {
            if lit.get(ctx).is_zero() {
                // a | 0 -> a
                Some(expr)
            } else if lit.get(ctx).is_all_ones() {
                // a | 1 -> 1
                Some(lit_expr)
            } else {
                None
            }
        }
        Lits::None(_, _) => {
            match (ctx.get(a), ctx.get(b)) {
                // a | !a -> 1
                (Expr::BVNot(inner, w), _) if *inner == b => Some(ctx.ones(*w)),
                (_, Expr::BVNot(inner, w)) if *inner == b => Some(ctx.ones(*w)),
                _ => None,
            }
        }
    }
}

fn simplify_bv_xor(ctx: &mut Context, a: ExprRef, b: ExprRef) -> Option<ExprRef> {
    // a xor a -> 0
    if a == b {
        let width = ctx.get(a).get_bv_type(ctx).unwrap();
        return Some(ctx.zero(width));
    }

    // other simplifications depend on whether one or two of the values are a constant
    match find_lits_commutative(ctx, a, b) {
        Lits::Two(va, vb) => {
            // concretely evaluate
            Some(ctx.bv_lit(&va.get(ctx).xor(&vb.get(ctx))))
        }
        Lits::One((lit, _), expr) => {
            if lit.get(ctx).is_zero() {
                // a xor 0 -> a
                Some(expr)
            } else if lit.get(ctx).is_all_ones() {
                // a xor 1 -> !a
                Some(ctx.not(expr))
            } else {
                None
            }
        }
        Lits::None(_, _) => {
            match (ctx.get(a), ctx.get(b)) {
                // a xor !a -> 1
                (Expr::BVNot(inner, w), _) if *inner == b => Some(ctx.ones(*w)),
                (_, Expr::BVNot(inner, w)) if *inner == b => Some(ctx.ones(*w)),
                _ => None,
            }
        }
    }
}

fn simplify_bv_not(ctx: &mut Context, e: ExprRef) -> Option<ExprRef> {
    match ctx.get(e) {
        Expr::BVNot(inner, _) => Some(*inner), // double negation
        Expr::BVLiteral(value) => Some(ctx.bv_lit(&value.get(ctx).not())),
        _ => None,
    }
}

fn simplify_bv_zero_ext(ctx: &mut Context, e: ExprRef, by: WidthInt) -> Option<ExprRef> {
    match ctx.get(e) {
        // zero extend constant
        Expr::BVLiteral(value) => Some(ctx.bv_lit(&value.get(ctx).zero_extend(by))),
        _ => None,
    }
}

fn simplify_bv_slice(ctx: &mut Context, e: ExprRef, hi: WidthInt, lo: WidthInt) -> Option<ExprRef> {
    match ctx.get(e) {
        // combine slices
        Expr::BVSlice {
            lo: inner_lo,
            e: inner_e,
            ..
        } => Some(ctx.slice(*inner_e, hi + inner_lo, lo + inner_lo)),
        // slice constant
        Expr::BVLiteral(value) => Some(ctx.bv_lit(&value.get(ctx).slice(hi, lo))),
        _ => None,
    }
}
