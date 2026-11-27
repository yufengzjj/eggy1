use clap::{CommandFactory, FromArgMatches};
use eggy1::expr_convert::infix_to_egglog;
use eggy1::{simplify, Cli};

fn main() {
    let matches = Cli::command().get_matches();
    let cli = Cli::from_arg_matches(&matches).unwrap_or_else(|e| e.exit());
    if let Some(spec) = matches.get_raw("passes").and_then(|mut v| v.next()) {
        for w in eggy1::sched::Passes::parse_noting(&spec.to_string_lossy()).map(|(_, w)| w).unwrap_or_default() {
            eprintln!("--passes: warning: {w}");
        }
    }
    if cli.show_builtins {
        print!("{}", eggy1::builtins::listing());
        if !cli.passes.defs.is_empty() {
            println!("\n# --- defined by def in --passes, runs of their own on the whole list (group -> group)");
            for d in &cli.passes.defs {
                println!("{}", eggy1::pipe_lang::def_sig(&d.name, &d.params));
            }
        }
        return;
    }
    if cli.show_passes {
        println!("{}", cli.passes.show_run(cli.max_restarts, cli.iter_limit));
        return;
    }
    if cli.expr.is_empty() {
        println!("please enter a expression");
        return;
    }
    let egg_expr = infix_to_egglog(&cli.expr, true);
    if egg_expr.is_empty() {
        println!("please enter a valid expression");
        return;
    }
    if cli.stats {
        eggy1::stats::enable();
    }
    let result = simplify(&egg_expr, &cli);
    if eggy1::last_run_cut() {
        eprintln!("time limit reached: the result is the smallest form found by then");
    }
    if cli.stats {
        eprint!("{}", eggy1::stats::report(&eggy1::stats::take()));
    }
    if let Ok(v) = result {
        println!("\n{}", v);
    } else if let Err(v) = result {
        println!("\nerror:{}", v);
    }
}
