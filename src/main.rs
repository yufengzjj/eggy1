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

fn make_rules() -> Vec<Rewrite<OperatorLanguage, ()>> {
    let mut rules = vec![
        rw!("commute-add"; "(+ ?a ?b)" => "(+ ?b ?a)"),
        rw!("commute-mul"; "(* ?a ?b)" => "(* ?b ?a)"),
        rw!("commute-and"; "(& ?a ?b)" => "(& ?b ?a)"),
        rw!("commute-xor"; "(^ ?a ?b)" => "(^ ?b ?a)"),
        rw!("commute-or"; "(| ?a ?b)" => "(| ?b ?a)"),
        rw!("add-0"; "(+ ?a 0)" => "?a"),
        rw!("sub-0"; "(- ?a 0)" => "?a"),
        rw!("mul-0"; "(* ?a 0)" => "0"),
        rw!("mul-1"; "(* ?a 1)" => "?a"),
        rw!("dev-1"; "(/ ?a 1)" => "?a"),
        rw!("div-0"; "(/ 0 ?a)" => "0"),
        rw!("assoc-mul"; "(* ?x (* ?y ?z))" => "(* (* ?x ?y) ?z)"),
        rw!("assoc-add"; "(+ ?x (+ ?y ?z))" => "(+ (+ ?x ?y) ?z)"),
        rw!("assoc-and"; "(& ?x (& ?y ?z))" => "(& (& ?x ?y) ?z)"),
        rw!("assoc-xor"; "(^ ?x (^ ?y ?z))" => "(^ (^ ?x ?y) ?z)"),
        rw!("assoc-or"; "(| ?x (| ?y ?z))" => "(| (| ?x ?y) ?z)"),
    ];
    rules.extend(
        vec![
            rw!("not-mul"; "(~ (* ?x ?y))" <=> "(+ (* (~ ?x) ?y) (- ?y 1))"),
            rw!("not-add"; "(~ (+ ?x ?y))" <=> "(+ (~ ?x) (+ (~ ?y) 1))"),
            rw!("not-sub"; "(~ (- ?x ?y))" <=> "(- (~ ?x) (+ (~ ?y) 1))"),
            rw!("not-and"; "(~ (& ?x ?y))" <=> "(| (~ ?x) (~ ?y))"),
            rw!("not-xor"; "(~ (^ ?x ?y))" <=> "(| (& ?x ?y) (~ (| ?x ?y)))"),
            rw!("not-or"; "(~ (| ?x ?y))" <=> "(& (~ ?x) (~ ?y))"),
            rw!("neg-mul"; "(- (* ?x ?y))" <=> "(* (- ?x) ?y)"),
            rw!("sub-to-add-neg"; "(- ?x ?y)" <=> "(+ ?x (- ?y))"),
            rw!("neg-to-not-plus-one"; "(- ?x)" <=> "(+ (~ ?x) 1)"),
            rw!("distribute-mul-add"; "(* (+ ?x ?y) ?z)" <=> "(+ (* ?x ?z) (* ?y ?z))"),
            rw!("distribute-mul-sub"; "(* (- ?x ?y) ?z)" <=> "(- (* ?x ?z) (* ?y ?z))"),
            rw!("factor-mul-add"; "(+ (* ?x ?y) (* ?x ?z))" <=> "(* ?x (+ ?y ?z))"),
            rw!("factor-mul-sub"; "(- (* ?x ?y) (* ?x ?z))" <=> "(* ?x (- ?y ?z))"),
            rw!("factor-add-mul"; "(+ (* ?x ?y) ?y)" <=> "(* (+ ?x 1) ?y)"),
            rw!("double-to-mul"; "(+ ?x ?x)" <=> "(* 2 ?x)"),
            rw!("neg-add"; "(- (+ ?x ?y))" <=> "(+ (- ?x) (- ?y))"),
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
    let runner = Runner::default().with_expr(&expr).run(&make_rules());

    // the Runner knows which e-class the expression given with `with_expr` is in
    let root = runner.roots[0];

    // use an Extractor to pick the best element of the root eclass
    let extractor = Extractor::new(&runner.egraph, AstSize);
    let (best_cost, best) = extractor.find_best(root);
    println!("Simplified {} to {} with cost {}", expr, best, best_cost);
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
