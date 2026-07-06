//! Module for converting infix arithmetic expressions to prefix notation.
//! Supports operators: +, -, *, / and parentheses.
//! Variables consist of letters, numbers consist of digits.

use crate::expr_convert::Token::RParen;

#[derive(Debug, Clone, PartialEq)]
enum Token {
    Num(u64),
    Operand(String),
    Operator(String),
    LParen,
    RParen,
    Comma,
}

/// Tokenize an infix expression string into a vector of Tokens.
/// Assumes valid characters: letters (variables), digits (numbers), operators, parentheses.
fn tokenize(expr: &str) -> Vec<Token> {
    let mut tokens = Vec::new();
    let mut chars = expr.chars().peekable();

    while let Some(&c) = chars.peek() {
        match c {
            ' ' | '"' => {
                chars.next();
            }
            '(' => {
                tokens.push(Token::LParen);
                chars.next();
            }
            ')' => {
                tokens.push(RParen);
                chars.next();
            }
            ',' => {
                tokens.push(Token::Comma);
                chars.next();
            }
            '+' | '-' | '*' | '/' | '%' | '&' | '|' | '^' | '~' => {
                tokens.push(Token::Operator(c.to_string()));
                chars.next();
            }
            '<' => {
                chars.next();
                if let Some(&'<') = chars.peek() {
                    chars.next();
                    tokens.push(Token::Operator("<<".to_string()));
                } else {
                    break;
                }
            }
            '>' => {
                chars.next();
                if let Some(&'>') = chars.peek() {
                    chars.next();
                    tokens.push(Token::Operator(">>".to_string()));
                } else {
                    break;
                }
            }
            _ if c == '_' || c.is_ascii_alphabetic() => {
                let mut ident = String::new();
                while let Some(&ch) = chars.peek() {
                    if ch == '_' || ch.is_ascii_alphanumeric() {
                        ident.push(ch);
                        chars.next();
                    } else {
                        break;
                    }
                }
                let sym_op = egg2sym_op(&ident);
                if sym_op == "_" {
                    tokens.push(Token::Operand(ident));
                } else {
                    tokens.push(Token::Operator(sym_op.to_string()));
                }
            }
            _ if c.is_ascii_digit() => {
                let mut num = String::new();
                let mut count = 0;
                let mut first = '_';
                while let Some(&ch) = chars.peek() {
                    if (count == 1 && first == '0' && ch == 'x')
                        || ch.is_ascii_digit()
                        || (num.starts_with("0x") && ch.is_ascii_hexdigit())
                    {
                        num.push(ch);
                        if count == 0 {
                            first = ch;
                        }
                        chars.next();
                    } else {
                        break;
                    }
                    count += 1;
                }
                if num.starts_with("0x") {
                    tokens.push(Token::Num(
                        u64::from_str_radix(&num[2..], 16)
                            .expect(&format!("fail to parse num:{}", num)),
                    ));
                } else {
                    tokens.push(Token::Num(
                        u64::from_str_radix(&num, 10).expect(&format!("fail to parse num:{}", num)),
                    ));
                }
            }
            _ => {
                chars.next();
            }
        }
    }
    tokens
}

#[derive(Debug)]
enum Ast {
    Num(u64),
    Operand(String),
    BinaryOp(String, Box<Ast>, Box<Ast>),
    UnaryOp(String, Box<Ast>),
}

/// Returns precedence of operator: higher number = higher precedence.
fn precedence(op: &str) -> u8 {
    match op {
        "*" | "/" | "%" => 5,
        "+" | "-" => 4,
        "<<" | ">>" => 3,
        "&" => 2,
        "^" => 1,
        "|" => 0,
        _ => 0, // unknown operator (including single '<' and '>')
    }
}

/// Whether operator is left‑associative (all our operators are).
fn is_left_associative(_op: &str) -> bool {
    true
}

/// Parse tokens using a recursive descent Pratt parser.
/// Returns (parsed AST, remaining tokens).
fn parse_infix_expr(tokens: &[Token], min_prec: u8) -> (Ast, &[Token]) {
    let (mut left, mut rest) = parse_atom(tokens);

    while let Some(&Token::Operator(ref op)) = rest.first() {
        let prec = precedence(op);
        if prec < min_prec {
            break;
        }
        let next_min_prec = if is_left_associative(op) {
            prec + 1
        } else {
            prec
        };
        rest = &rest[1..];
        let (right, remaining) = parse_infix_expr(rest, next_min_prec);
        left = Ast::BinaryOp(op.clone(), Box::new(left), Box::new(right));
        rest = remaining;
    }
    (left, rest)
}

fn is_unary_op(op: &str) -> bool {
    matches!(op, "-" | "~" | "Num")
}

fn parse_atom(tokens: &[Token]) -> (Ast, &[Token]) {
    match tokens.first() {
        Some(Token::Num(num)) => (Ast::Num(*num), &tokens[1..]),
        // Function-call syntax: currently only `mulhi(a, b)` (high half of product).
        Some(Token::Operand(s)) if matches!(tokens.get(1), Some(Token::LParen)) => {
            let (a, r1) = parse_infix_expr(&tokens[2..], 0);
            let r2 = match r1.first() {
                Some(Token::Comma) => &r1[1..],
                _ => panic!("expected ',' in call to {}", s),
            };
            let (b, r3) = parse_infix_expr(r2, 0);
            let r4 = match r3.first() {
                Some(RParen) => &r3[1..],
                _ => panic!("expected ')' in call to {}", s),
            };
            (
                Ast::BinaryOp(s.clone(), Box::new(a), Box::new(b)),
                r4,
            )
        }
        Some(Token::Operand(s)) => (Ast::Operand(s.clone()), &tokens[1..]),
        Some(Token::LParen) => {
            let (expr, rest) = parse_infix_expr(&tokens[1..], 0);
            if let Some(RParen) = rest.first() {
                (expr, &rest[1..])
            } else {
                panic!("Mismatched parentheses");
            }
        }
        Some(Token::Operator(c)) if is_unary_op(c) => {
            let (operand, rest) = parse_atom(&tokens[1..]);
            (Ast::UnaryOp(c.clone(), Box::new(operand)), rest)
        }
        _ => panic!("Unexpected token at atom"),
    }
}

/// Canonical form modulo associativity/commutativity of + * & | ^ :
/// same-operator chains are flattened and operands sorted, so two
/// AC-equivalent expressions produce identical strings.
#[allow(dead_code)]
pub fn ac_canon_infix(expr: &str) -> String {
    let tokens = tokenize(expr);
    let (ast, rest) = parse_infix_expr(&tokens, 0);
    assert!(rest.is_empty(), "Unconsumed tokens: {:?}", rest);
    ac_canon(&ast)
}

#[allow(dead_code)]
fn ac_canon(ast: &Ast) -> String {
    match ast {
        Ast::Num(n) => format!("#{}", *n as i64),
        Ast::Operand(s) => s.clone(),
        Ast::UnaryOp(op, a) => format!("({} {})", op, ac_canon(a)),
        Ast::BinaryOp(op, l, r) => {
            if matches!(op.as_str(), "+" | "*" | "&" | "|" | "^") {
                let mut parts = Vec::new();
                ac_flatten(op, l, &mut parts);
                ac_flatten(op, r, &mut parts);
                parts.sort();
                format!("({} {})", op, parts.join(" "))
            } else {
                format!("({} {} {})", op, ac_canon(l), ac_canon(r))
            }
        }
    }
}

#[allow(dead_code)]
fn ac_flatten(op: &str, ast: &Ast, out: &mut Vec<String>) {
    if let Ast::BinaryOp(o, l, r) = ast {
        if o == op {
            ac_flatten(op, l, out);
            ac_flatten(op, r, out);
            return;
        }
    }
    out.push(ac_canon(ast));
}

pub fn infix_to_prefix(expr: &str) -> String {
    let tokens = tokenize(expr);
    let (ast, rest) = parse_infix_expr(&tokens, 0);
    assert!(rest.is_empty(), "Unconsumed tokens: {:?}", rest);
    ast_to_prefix(&ast)
}
#[allow(dead_code)]
pub fn prefix_to_infix(expr: &str) -> String {
    let tokens = tokenize(expr);
    let (ast, rest) = parse_prefix_expr(&tokens, 0);
    assert!(rest.is_empty(), "Unconsumed tokens: {:?}", rest);
    ast_to_infix(&ast)
}

pub fn prefix_to_egglog(expr: &str, is_expr: bool) -> String {
    let tokens = tokenize(expr);
    let (ast, rest) = parse_prefix_expr(&tokens, 0);
    assert!(rest.is_empty(), "Unconsumed tokens: {:?}", rest);
    ast_to_egglog(&ast, is_expr)
}

pub fn infix_to_egglog(expr: &str, is_expr: bool) -> String {
    let expr = infix_to_prefix(expr);
    prefix_to_egglog(&expr, is_expr)
}
pub fn egglog_to_infix(expr: &str, norm: &impl Fn(i64) -> i64) -> String {
    let tokens = tokenize(expr);
    let (ast, rest) = parse_prefix_expr(&tokens, 0);
    assert!(rest.is_empty(), "Unconsumed tokens: {:?}", rest);
    let ast = normalize_nums(ast, norm);
    ast_to_infix(&ast)
}

/// Fold each constant through `norm` (truncation to the active numeric width)
/// so extraction ties between width-equivalent twins (e.g. 0x100 vs 0 in i8)
/// always display in canonical form. `-(Num n)` is folded as a unit to avoid
/// double negation artifacts like `--0x80`.
fn normalize_nums(ast: Ast, norm: &impl Fn(i64) -> i64) -> Ast {
    match ast {
        Ast::Num(n) => Ast::Num(norm(n as i64) as u64),
        Ast::UnaryOp(op, inner) => {
            if op == "-" {
                if let Ast::Num(n) = *inner {
                    return Ast::Num(norm((n as i64).wrapping_neg()) as u64);
                }
            }
            Ast::UnaryOp(op, Box::new(normalize_nums(*inner, norm)))
        }
        Ast::BinaryOp(op, l, r) => Ast::BinaryOp(
            op,
            Box::new(normalize_nums(*l, norm)),
            Box::new(normalize_nums(*r, norm)),
        ),
        other => other,
    }
}

fn ast_to_prefix(ast: &Ast) -> String {
    match ast {
        Ast::Num(s) => s.to_string(),
        Ast::Operand(s) => s.clone(),
        Ast::UnaryOp(op, operand) => {
            format!("({} {})", op, ast_to_prefix(operand))
        }
        Ast::BinaryOp(op, left, right) => {
            format!("({} {} {})", op, ast_to_prefix(left), ast_to_prefix(right))
        }
    }
}

fn egg2sym_op(op: &str) -> &'static str {
    match op {
        "Add" => "+",
        "Sub" => "-",
        "Mul" => "*",
        "Div" => "/",
        "Mod" => "%",
        "And" => "&",
        "Or" => "|",
        "Xor" => "^",
        "Shl" => "<<",
        "Shr" => ">>",
        "Neg" => "-",
        "Not" => "~",
        "Num" => "Num",
        _ => "_",
    }
}

fn parse_prefix_op(tokens: &[Token]) -> (Ast, &[Token]) {
    match tokens.first() {
        Some(Token::Operator(op)) => {
            let (left, rest1) = parse_prefix_expr(&tokens[1..], 0);
            match rest1.first() {
                None => {
                    panic!("Mismatched operand for operator:{}", op);
                }
                Some(v) => match v {
                    RParen => (Ast::UnaryOp(op.clone(), Box::new(left)), rest1),
                    _ => {
                        let (right, rest2) = parse_prefix_expr(rest1, 0);
                        (
                            Ast::BinaryOp(op.clone(), Box::new(left), Box::new(right)),
                            rest2,
                        )
                    }
                },
            }
        }
        Some(Token::Operand(op)) => match op.as_str() {
            "Num" | "Var" => parse_prefix_expr(&tokens[1..], 0),
            "Mulhi" | "mulhi" => {
                let (l, r1) = parse_prefix_expr(&tokens[1..], 0);
                let (r, r2) = parse_prefix_expr(r1, 0);
                (
                    Ast::BinaryOp("mulhi".to_string(), Box::new(l), Box::new(r)),
                    r2,
                )
            }
            _ => panic!("Unexpected operand {}", op),
        },
        _ => panic!("Expected binary operator, found {:?}", tokens.first()),
    }
}

fn parse_prefix_expr(tokens: &[Token], _min_prec: u8) -> (Ast, &[Token]) {
    match tokens.first() {
        Some(Token::Num(num)) => (Ast::Num(*num), &tokens[1..]),
        Some(Token::Operand(s)) => (Ast::Operand(s.clone()), &tokens[1..]),
        Some(Token::LParen) => {
            let (ast, rest) = parse_prefix_op(&tokens[1..]);
            if let Some(RParen) = rest.first() {
                (ast, &rest[1..])
            } else {
                panic!("Mismatched parentheses");
            }
        }
        Some(Token::Operator(op)) if is_unary_op(op) => {
            let (operand, rest) = parse_prefix_expr(&tokens[1..], 0);
            (Ast::UnaryOp(op.clone(), Box::new(operand)), rest)
        }
        _ => panic!(
            "Unexpected token in prefix expression: {:?}",
            tokens.first()
        ),
    }
}

fn ast_to_infix(ast: &Ast) -> String {
    match ast {
        Ast::Num(s) => {
            let n = *s as i64;
            if n > 9 {
                format!("{:#x}", n)
            } else if n < -9 {
                format!("-{:#x}", -(n as i128))
            } else {
                n.to_string()
            }
        }
        Ast::Operand(s) => s.clone(),
        Ast::UnaryOp(op, operand) => {
            let operand_str = ast_to_infix(operand);
            format!("{}{}", if op == "Num" { "" } else { op }, operand_str)
        }
        Ast::BinaryOp(op, left, right) if op == "mulhi" => {
            format!("mulhi({}, {})", ast_to_infix(left), ast_to_infix(right))
        }
        Ast::BinaryOp(op, left, right) => {
            let left_str = ast_to_infix(left);
            let right_str = ast_to_infix(right);
            let expr = format!("{} {} {}", left_str, op, right_str);
            format!("({})", expr)
        }
    }
}

fn ast_to_egglog(ast: &Ast, is_expr: bool) -> String {
    match ast {
        Ast::Num(s) => {
            format!("(Num {})", *s as i64)
        }
        Ast::Operand(s) => {
            if is_expr {
                format!("(Var \"{}\")", s)
            } else {
                s.clone()
            }
        }
        Ast::UnaryOp(op, operand) => {
            let operand_str = ast_to_egglog(operand, is_expr);
            match op.as_str() {
                "-" => {
                    if let Ast::Num(v) = operand.as_ref() {
                        format!("(Num -{})", *v)
                    } else {
                        format!("(Neg {})", operand_str)
                    }
                }
                "~" => {
                    format!("(Not {})", operand_str)
                }
                "Num" => {
                    format!("(Num {})", operand_str)
                }
                _ => panic!("Unexpected unary operator {}", op),
            }
        }
        Ast::BinaryOp(op, left, right) => {
            let left_str = ast_to_egglog(left, is_expr);
            let right_str = ast_to_egglog(right, is_expr);
            match op.as_str() {
                "mulhi" => {
                    format!("(Mulhi {} {})", left_str, right_str)
                }
                "+" => {
                    format!("(Add {} {})", left_str, right_str)
                }
                "-" => {
                    format!("(Sub {} {})", left_str, right_str)
                }
                "*" => {
                    format!("(Mul {} {})", left_str, right_str)
                }
                "/" => {
                    format!("(Div {} {})", left_str, right_str)
                }
                "%" => {
                    format!("(Mod {} {})", left_str, right_str)
                }
                "&" => {
                    format!("(And {} {})", left_str, right_str)
                }
                "|" => {
                    format!("(Or {} {})", left_str, right_str)
                }
                "^" => {
                    format!("(Xor {} {})", left_str, right_str)
                }
                "<<" => {
                    format!("(Shl {} {})", left_str, right_str)
                }
                ">>" => {
                    format!("(Shr {} {})", left_str, right_str)
                }
                _ => panic!("Unexpected binary operator {}", op),
            }
        }
    }
}
