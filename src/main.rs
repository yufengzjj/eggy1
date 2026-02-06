mod expr_convert;

use clap::Parser;
use egg::{rewrite as rw, *};
define_language! {
    enum OperatorLanguage {
        Num(i32),
        "+" = Add([Id; 2]),
        "-" = Sub([Id; 2]),
        "*" = Mul([Id; 2]),
        "/" = Div([Id; 2]),
        "%" = Mod([Id; 2]),
        "<<" = Lsl([Id; 2]),
        ">>" = Lsr([Id; 2]),
        "&" = And([Id; 2]),
        "^" = Xor([Id; 2]),
        "|" = Or([Id; 2]),
        "~" = Not([Id; 1]),
        "-" = Neg([Id; 1]),
         Symbol(Symbol),
    }
}

#[derive(Default, Clone)]
struct ConstantFolding;

impl Analysis<OperatorLanguage> for ConstantFolding {
    type Data = Option<i32>;

    fn make(
        egraph: &mut EGraph<OperatorLanguage, Self>,
        enode: &OperatorLanguage,
        _id: Id,
    ) -> Self::Data {
        let x = |i: &Id| egraph[*i].data;
        match enode {
            OperatorLanguage::Num(n) => Some(*n),
            OperatorLanguage::Add([a, b]) => Some(x(a)?.wrapping_add(x(b)?)),
            OperatorLanguage::Sub([a, b]) => Some(x(a)?.wrapping_sub(x(b)?)),
            OperatorLanguage::Mul([a, b]) => Some(x(a)?.wrapping_mul(x(b)?)),
            OperatorLanguage::Div([a, b]) => Some(x(a)?.wrapping_div(x(b)?)),
            OperatorLanguage::Mod([a, b]) => Some(x(a)?.wrapping_rem(x(b)?)),
            OperatorLanguage::And([a, b]) => Some(x(a)? & x(b)?),
            OperatorLanguage::Or([a, b]) => Some(x(a)? | x(b)?),
            OperatorLanguage::Xor([a, b]) => Some(x(a)? ^ x(b)?),
            OperatorLanguage::Lsl([a, b]) => Some(x(a)?.wrapping_shl(x(b)? as u32)),
            OperatorLanguage::Lsr([a, b]) => Some(x(a)?.wrapping_shr(x(b)? as u32)),
            OperatorLanguage::Neg([a]) => Some(x(a)?.wrapping_neg()),
            OperatorLanguage::Not([a]) => Some(!x(a)?),
            OperatorLanguage::Symbol(_) => None,
        }
    }
    fn merge(&mut self, to: &mut Self::Data, from: Self::Data) -> DidMerge {
        match (*to, from) {
            (Some(x), Some(y)) if x == y => DidMerge(false, false),
            (Some(x), Some(y)) => {
                eprintln!("Constant conflict: {} vs {} in e-class", x, y);
                panic!("Constant folding conflict detected");
            }
            (None, Some(y)) => {
                *to = Some(y);
                DidMerge(true, false)
            }
            (Some(_), None) | (None, None) => DidMerge(false, false),
        }
    }
    fn modify(egraph: &mut EGraph<OperatorLanguage, Self>, id: Id) {
        if let Some(i) = egraph[id].data {
            let added = egraph.add(OperatorLanguage::Num(i));
            egraph.union(id, added);
        }
    }
}

fn make_rules<A: Analysis<OperatorLanguage> + Clone>() -> Vec<Rewrite<OperatorLanguage, A>> {
    let mut rules = vec![
        rw!("commute-add"; "(+ ?a ?b)" => "(+ ?b ?a)"),
        rw!("commute-mul"; "(* ?a ?b)" => "(* ?b ?a)"),
        rw!("commute-and"; "(& ?a ?b)" => "(& ?b ?a)"),
        rw!("commute-xor"; "(^ ?a ?b)" => "(^ ?b ?a)"),
        rw!("commute-or"; "(| ?a ?b)" => "(| ?b ?a)"),
        rw!("add-0"; "(+ ?a 0)" => "?a"),
        rw!("sub-0"; "(- ?a 0)" => "?a"),
        rw!("sub-n0"; "(- 0 ?a)" => "(- ?a)"),
        rw!("mul-0"; "(* ?a 0)" => "0"),
        rw!("mul-1"; "(* ?a 1)" => "?a"),
        rw!("dev-1"; "(/ ?a 1)" => "?a"),
        rw!("div-0"; "(/ 0 ?a)" => "0"),
        rw!("lsl-1"; "(<< ?a 1)" => "(* ?a 2)"),
        rw!("assoc-mul"; "(* ?a (* ?b ?c))" => "(* (* ?a ?b) ?c)"),
        rw!("assoc-add"; "(+ ?a (+ ?b ?c))" => "(+ (+ ?a ?b) ?c)"),
        rw!("assoc-and"; "(& ?a (& ?b ?c))" => "(& (& ?a ?b) ?c)"),
        rw!("assoc-xor"; "(^ ?a (^ ?b ?c))" => "(^ (^ ?a ?b) ?c)"),
        rw!("assoc-or"; "(| ?a (| ?b ?c))" => "(| (| ?a ?b) ?c)"),
    ];
    rules.extend(
        vec![
            rw!("not-mul"; "(~ (* ?a ?b))" <=> "(+ (* (~ ?a) ?b) (- ?b 1))"),
            rw!("not-add"; "(~ (+ ?a ?b))" <=> "(+ (~ ?a) (+ (~ ?b) 1))"),
            rw!("not-sub"; "(~ (- ?a ?b))" <=> "(- (~ ?a) (+ (~ ?b) 1))"),
            rw!("not-and"; "(~ (& ?a ?b))" <=> "(| (~ ?a) (~ ?b))"),
            rw!("not-xor"; "(~ (^ ?a ?b))" <=> "(| (& ?a ?b) (~ (| ?a ?b)))"),
            rw!("not-or"; "(~ (| ?a ?b))" <=> "(& (~ ?a) (~ ?b))"),
            rw!("neg-mul"; "(- (* ?a ?b))" <=> "(* (- ?a) ?b)"),
            rw!("sub-to-add-neg"; "(- ?a ?b)" <=> "(+ ?a (- ?b))"),
            rw!("neg-to-not-plus-one"; "(- ?a)" <=> "(+ (~ ?a) 1)"),
            rw!("distribute-mul-add"; "(* (+ ?a ?b) ?c)" <=> "(+ (* ?a ?c) (* ?b ?c))"),
            rw!("distribute-mul-sub"; "(* (- ?a ?b) ?c)" <=> "(- (* ?a ?c) (* ?b ?c))"),
            rw!("factor-mul-add"; "(+ (* ?a ?b) (* ?a ?c))" <=> "(* ?a (+ ?b ?c))"),
            rw!("factor-mul-sub"; "(- (* ?a ?b) (* ?a ?c))" <=> "(* ?a (- ?b ?c))"),
            rw!("factor-add-mul"; "(+ (* ?a ?b) ?b)" <=> "(* (+ ?a 1) ?b)"),
            rw!("double-to-mul"; "(+ ?a ?a)" <=> "(* 2 ?a)"),
            rw!("neg-add"; "(- (+ ?a ?b))" <=> "(+ (- ?a) (- ?b))"),
        ]
        .concat(),
    );
    rules
}

fn simplify(s: &str) -> String {
    // parse the expression, the type annotation tells it which Language to use
    let expr: RecExpr<OperatorLanguage> = s.parse().unwrap();

    // simplify the expression using a Runner, which creates an e-graph with
    // the given expression and runs the given rules over it
    let runner: Runner<OperatorLanguage, ConstantFolding, ()> = Runner::new(ConstantFolding)
        .with_expr(&expr)
        .run(&make_rules::<ConstantFolding>());

    // the Runner knows which e-class the expression given with `with_expr` is in
    let root = runner.roots[0];

    // use an Extractor to pick the best element of the root eclass
    let extractor = Extractor::new(&runner.egraph, AstSize);
    let (best_cost, best) = extractor.find_best(root);
    println!(
        "simplified {} to {} with cost {} reason {}",
        expr,
        best,
        best_cost,
        if let Some(reason) = runner.stop_reason {
            format!("{:?}", reason)
        } else {
            "no".to_string()
        },
    );
    best.to_string()
}

#[derive(Parser)]
#[command(version, about, long_about = None)]
struct Cli {
    expr: String,
}
fn main() {
    let cli = Cli::parse();
    if cli.expr.is_empty() {
        println!("please enter a expression");
        return;
    }
    let prefix_expr = expr_convert::infix_to_prefix(&cli.expr);
    if prefix_expr.is_empty() {
        println!("please enter a valid expression");
        return;
    }
    println!(
        "\n{}",
        expr_convert::prefix_to_infix(&simplify(&prefix_expr))
    );
}
