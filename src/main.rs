use clap::Parser;
use eggy1::expr_convert::infix_to_egglog;
use eggy1::{simplify, Cli};

fn main() {
    let cli = Cli::parse();
    if cli.expr.is_empty() {
        println!("please enter a expression");
        return;
    }
    if cli.rule_compile {
        println!("{}", infix_to_egglog(&cli.expr, false));
        return;
    }
    if cli.expr_compile {
        println!("{}", infix_to_egglog(&cli.expr, true));
        return;
    }
    let egg_expr = infix_to_egglog(&cli.expr, true);
    if egg_expr.is_empty() {
        println!("please enter a valid expression");
        return;
    }
    let result = simplify(&egg_expr, &cli);
    if let Ok(v) = result {
        println!("\n{}", v);
    } else if let Err(v) = result {
        println!("\nerror:{}", v);
    }
}
