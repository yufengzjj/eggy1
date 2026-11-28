use clap::{CommandFactory, FromArgMatches};
use eggy1::{Cli, cli, lang};

fn main() {
    let matches = Cli::command().get_matches();
    let cli = Cli::from_arg_matches(&matches).unwrap_or_else(|e| e.exit());
    let given = matches.value_source("passes") == Some(clap::parser::ValueSource::CommandLine);
    let runs = !(cli.show_builtins || cli.show_passes || cli.expr.trim().is_empty());
    let statement = runs.then(|| cli::statement(&cli.expr, true));
    let (passes, warnings, text) = cli::parse(&cli, statement.as_deref()).unwrap_or_else(|e| {
        eprintln!("error: invalid value '{}' for '--passes <PASSES>': {e}\n\nFor more information, try '--help'.", cli.passes);
        std::process::exit(2)
    });
    if given {
        for w in warnings {
            eprintln!("--passes: warning: {w}");
        }
    }
    if cli.show_builtins {
        print!("{}", cli::listing());
        let (default, spec) = passes.defs.split_at(passes.default_defs);
        for (from, defs) in [("src/default.pipe", default), ("--passes", spec)] {
            if !defs.is_empty() {
                println!("\n# --- defined by def in {from}");
                for d in defs {
                    println!("{}", lang::defs::sig_of(d));
                }
            }
        }
        return;
    }
    if cli.show_passes {
        println!("# The program: {}\n{passes:#}", cli::one_line(&format!("{text}{}", cli::statement("EXPR", true))));
        return;
    }
    if cli.expr.is_empty() {
        println!("please enter a expression");
        return;
    }
    if !runs {
        println!("please enter a valid expression");
        return;
    }
    if cli.stats {
        eggy1::stats::enable();
    }
    let result = lang::execute(&passes, &[]);
    if cli.stats {
        eprint!("{}", eggy1::stats::report(&eggy1::stats::take()));
    }
    match result {
        Ok(Some(lang::Value::Text(v))) => println!("\n{v}"),
        Ok(_) => {
            eprintln!("error: the program gave no text");
            std::process::exit(1)
        }
        Err(v) => {
            eprintln!("error: {v}");
            std::process::exit(1)
        }
    }
}
