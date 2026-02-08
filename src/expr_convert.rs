//! Module for converting infix arithmetic expressions to prefix notation.
//! Supports operators: +, -, *, / and parentheses.
//! Variables consist of letters, numbers consist of digits.

use crate::expr_convert::Token::RParen;

#[derive(Debug, Clone, PartialEq)]
enum Token {
    Num(String),
    Operand(String),
    Operator(String),
    LParen,
    RParen,
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
                tokens.push(Token::RParen);
                chars.next();
            }
            '+' | '-' | '*' | '/' | '%' | '&' | '|' | '^' | '~' => {
                tokens.push(Token::Operator(c.to_string()));
                chars.next();
            }
            '<' => {
                chars.next(); // consume '<'
                if let Some(&'<') = chars.peek() {
                    chars.next(); // consume second '<'
                    tokens.push(Token::Operator("<<".to_string()));
                } else {
                    break;
                }
            }
            '>' => {
                chars.next(); // consume '>'
                if let Some(&'>') = chars.peek() {
                    chars.next(); // consume second '>'
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
                            .expect(&format!("fail to parse num:{}", num))
                            .to_string(),
                    ));
                } else {
                    tokens.push(Token::Num(num));
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
    Num(String),
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
        Some(Token::Num(num)) => (Ast::Operand(num.clone()), &tokens[1..]),
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
pub fn egglog_to_infix(expr: &str) -> String {
    let tokens = tokenize(expr);
    let (ast, rest) = parse_prefix_expr(&tokens, 0);
    assert!(rest.is_empty(), "Unconsumed tokens: {:?}", rest);
    ast_to_infix(&ast)
}

fn ast_to_prefix(ast: &Ast) -> String {
    match ast {
        Ast::Num(s) => s.clone(),
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
            _ => panic!("Unexpected operand {}", op),
        },
        _ => panic!("Expected binary operator, found {:?}", tokens.first()),
    }
}

fn parse_prefix_expr(tokens: &[Token], _min_prec: u8) -> (Ast, &[Token]) {
    match tokens.first() {
        Some(Token::Num(num)) => (Ast::Num(num.clone()), &tokens[1..]),
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
        Ast::Num(s) => s.clone(),
        Ast::Operand(s) => s.clone(),
        Ast::UnaryOp(op, operand) => {
            let operand_str = ast_to_infix(operand);
            format!("{}{}", if op == "Num" { "" } else { op }, operand_str)
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
            format!("(Num {})", s)
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
                    format!("(Neg {})", operand_str)
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_simple() {
        assert_eq!(infix_to_prefix("a + b"), "(+ a b)");
        assert_eq!(infix_to_prefix("a - b"), "(- a b)");
        assert_eq!(infix_to_prefix("a * b"), "(* a b)");
        assert_eq!(infix_to_prefix("a / b"), "(/ a b)");
        assert_eq!(infix_to_prefix("a % b"), "(% a b)");
    }

    #[test]
    fn test_precedence() {
        assert_eq!(infix_to_prefix("a + b + c"), "(+ (+ a b) c)");
        assert_eq!(infix_to_prefix("a + b * c"), "(+ a (* b c))");
        assert_eq!(infix_to_prefix("a * b + c"), "(+ (* a b) c)");
        assert_eq!(infix_to_prefix("a * b * c"), "(* (* a b) c)");
    }

    #[test]
    fn test_parentheses() {
        assert_eq!(infix_to_prefix("(a + b)"), "(+ a b)");
        assert_eq!(infix_to_prefix("(a + b) * c"), "(* (+ a b) c)");
        assert_eq!(infix_to_prefix("a * (b + c)"), "(* a (+ b c))");
        assert_eq!(infix_to_prefix("(a + b) * (c - d)"), "(* (+ a b) (- c d))");
    }

    #[test]
    fn test_complex() {
        assert_eq!(
            infix_to_prefix("(a + b) * (c - d) / e"),
            "(/ (* (+ a b) (- c d)) e)"
        );
        assert_eq!(
            infix_to_prefix("a + b * c - d / e"),
            "(- (+ a (* b c)) (/ d e))"
        );
    }

    #[test]
    fn test_variables() {
        assert_eq!(infix_to_prefix("x1 + y2"), "(+ x1 y2)");
        assert_eq!(infix_to_prefix("alpha * beta"), "(* alpha beta)");
    }

    #[test]
    fn test_numbers() {
        assert_eq!(infix_to_prefix("42 + 13"), "(+ 42 13)");
        assert_eq!(infix_to_prefix("2 * (3 + 4)"), "(* 2 (+ 3 4))");
    }

    #[test]
    fn test_new_operators() {
        assert_eq!(infix_to_prefix("a & b"), "(& a b)");
        assert_eq!(infix_to_prefix("a | b"), "(| a b)");
        assert_eq!(infix_to_prefix("a ^ b"), "(^ a b)");
        assert_eq!(infix_to_prefix("a % b"), "(% a b)");

        assert_eq!(infix_to_prefix("a & b | c"), "(| (& a b) c)");
        assert_eq!(infix_to_prefix("a | b & c"), "(| a (& b c))");
        assert_eq!(infix_to_prefix("a ^ b & c"), "(^ a (& b c))");
        assert_eq!(infix_to_prefix("a & b % c"), "(& a (% b c))");

        assert_eq!(infix_to_prefix("a + b & c"), "(& (+ a b) c)");
        assert_eq!(infix_to_prefix("a & b * c"), "(& a (* b c))");

        assert_eq!(infix_to_prefix("-a"), "(- a)");
        assert_eq!(infix_to_prefix("~a"), "(~ a)");

        assert_eq!(infix_to_prefix("-a + b"), "(+ (- a) b)");

        assert_eq!(infix_to_prefix("-(a + b)"), "(- (+ a b))");

        assert_eq!(infix_to_prefix("~-a"), "(~ (- a))");
        assert_eq!(infix_to_prefix("-~a"), "(- (~ a))");
        assert_eq!(infix_to_prefix("~~a"), "(~ (~ a))");

        assert_eq!(infix_to_prefix("~a + b"), "(+ (~ a) b)");
        assert_eq!(infix_to_prefix("a & ~b"), "(& a (~ b))");

        assert_eq!(infix_to_prefix("~(a + b)"), "(~ (+ a b))");
        assert_eq!(infix_to_prefix("~(a & b)"), "(~ (& a b))");
    }

    #[test]
    fn test_prefix_to_infix_simple() {
        assert_eq!(prefix_to_infix("(+ a b)"), "(a + b)");
        assert_eq!(prefix_to_infix("(- a b)"), "(a - b)");
        assert_eq!(prefix_to_infix("(* a b)"), "(a * b)");
        assert_eq!(prefix_to_infix("(/ a b)"), "(a / b)");
    }

    #[test]
    fn test_prefix_to_infix_precedence() {
        assert_eq!(prefix_to_infix("(+ (+ a b) c)"), "((a + b) + c)");
        assert_eq!(prefix_to_infix("(+ a (* b c))"), "(a + (b * c))");
        assert_eq!(prefix_to_infix("(+ (* a b) c)"), "((a * b) + c)");
        assert_eq!(prefix_to_infix("(* (* a b) c)"), "((a * b) * c)");
    }

    #[test]
    fn test_prefix_to_infix_parentheses() {
        assert_eq!(prefix_to_infix("(+ a b)"), "(a + b)");
        assert_eq!(prefix_to_infix("(* (+ a b) c)"), "((a + b) * c)");
        assert_eq!(prefix_to_infix("(* a (+ b c))"), "(a * (b + c))");
        assert_eq!(
            prefix_to_infix("(* (+ a b) (- c d))"),
            "((a + b) * (c - d))"
        );
    }

    #[test]
    fn test_prefix_to_infix_complex() {
        assert_eq!(
            prefix_to_infix("(/ (* (+ a b) (- c d)) e)"),
            "(((a + b) * (c - d)) / e)"
        );
        assert_eq!(
            prefix_to_infix("(- (+ a (* b c)) (/ d e))"),
            "((a + (b * c)) - (d / e))"
        );
    }

    #[test]
    fn test_prefix_to_infix_unary() {
        assert_eq!(prefix_to_infix("-a"), "-a");
        assert_eq!(prefix_to_infix("~a"), "~a");
        assert_eq!(prefix_to_infix("-(+ a b)"), "-(a + b)");
        assert_eq!(prefix_to_infix("~(+ a b)"), "~(a + b)");
        assert_eq!(prefix_to_infix("~(& a b)"), "~(a & b)");
        assert_eq!(prefix_to_infix("(+ -a b)"), "(-a + b)");
        assert_eq!(prefix_to_infix("(+ ~a b)"), "(~a + b)");
        assert_eq!(prefix_to_infix("(& a ~b)"), "(a & ~b)");
    }

    #[test]
    fn test_prefix_to_infix_new_operators() {
        assert_eq!(prefix_to_infix("(& a b)"), "(a & b)");
        assert_eq!(prefix_to_infix("(| a b)"), "(a | b)");
        assert_eq!(prefix_to_infix("(^ a b)"), "(a ^ b)");
        assert_eq!(prefix_to_infix("(% a b)"), "(a % b)");
        assert_eq!(prefix_to_infix("(| (& a b) c)"), "((a & b) | c)");
        assert_eq!(prefix_to_infix("(| a (& b c))"), "(a | (b & c))");
        assert_eq!(prefix_to_infix("(^ a (& b c))"), "(a ^ (b & c))");
        assert_eq!(prefix_to_infix("(& a (% b c))"), "(a & (b % c))");
        assert_eq!(prefix_to_infix("(& (+ a b) c)"), "((a + b) & c)");
        assert_eq!(prefix_to_infix("(& a (* b c))"), "(a & (b * c))");
    }

    #[test]
    fn test_prefix_to_infix_roundtrip() {
        let cases = [
            "(a + b)",
            "((a * b) + c)",
            "((a + b) * c)",
            "(a * (b + c))",
            "((a + (b * c)) - (d / e))",
            "-a",
            "~(a + b)",
            "((a & b) | c)",
        ];
        for case in cases {
            let prefix = infix_to_prefix(case);
            let infix = prefix_to_infix(&prefix);
            assert_eq!(infix, case, "Roundtrip failed for case: {}", case);
        }
    }

    #[test]
    fn test_shift_operators() {
        // 基本位移运算
        assert_eq!(infix_to_prefix("a << b"), "(<< a b)");
        assert_eq!(infix_to_prefix("a >> b"), "(>> a b)");
        assert_eq!(prefix_to_infix("(<< a b)"), "(a << b)");
        assert_eq!(prefix_to_infix("(>> a b)"), "(a >> b)");

        // 位移运算符的优先级（低于 + - * / %）
        assert_eq!(infix_to_prefix("a << b + c"), "(<< a (+ b c))");
        assert_eq!(infix_to_prefix("a + b << c"), "(<< (+ a b) c)");
        assert_eq!(infix_to_prefix("a * b << c"), "(<< (* a b) c)");
        assert_eq!(infix_to_prefix("a << b * c"), "(<< a (* b c))");

        // 位移运算符的结合性（左结合）
        assert_eq!(infix_to_prefix("a << b >> c"), "(>> (<< a b) c)");

        // 与其他位运算符的优先级（高于 & ^ |）
        assert_eq!(infix_to_prefix("a << b & c"), "(& (<< a b) c)");
        assert_eq!(infix_to_prefix("a & b << c"), "(& a (<< b c))");
        assert_eq!(infix_to_prefix("a << b ^ c"), "(^ (<< a b) c)");
        assert_eq!(infix_to_prefix("a << b | c"), "(| (<< a b) c)");
    }

    #[test]
    fn test_complex_nested_expressions() {
        // 深度嵌套括号
        assert_eq!(
            prefix_to_infix("(/ (- (* (+ a b) c) d) e)"),
            "((((a + b) * c) - d) / e)"
        );
        assert_eq!(
            infix_to_prefix("((((a + b) * c) - d) / e)"),
            "(/ (- (* (+ a b) c) d) e)"
        );

        // 多重嵌套混合操作符
        assert_eq!(
            prefix_to_infix("(+ a (* b (- c (/ d (+ e f)))))"),
            "(a + (b * (c - (d / (e + f)))))"
        );
        assert_eq!(
            infix_to_prefix("(a + (b * (c - (d / (e + f)))))"),
            "(+ a (* b (- c (/ d (+ e f)))))"
        );

        // 一元操作符嵌套（移除 ! 的支持）
        assert_eq!(
            prefix_to_infix("(+ -(& a b) ~(* c d))"),
            "(-(a & b) + ~(c * d))"
        );
        assert_eq!(
            infix_to_prefix("(-(a & b) + ~(c * d))"),
            "(+ (- (& a b)) (~ (* c d)))"
        );

        // 深度嵌套表达式（与多重嵌套相同，已包含）

        // 复杂混合表达式（包含位操作符）
        assert_eq!(
            prefix_to_infix("(| (& a b) (% (* (+ c d) (^ e f)) g))"),
            "((a & b) | (((c + d) * (e ^ f)) % g))"
        );
        assert_eq!(
            infix_to_prefix("(((a & b) | (((c + d) * (e ^ f)) % g)))"),
            "(| (& a b) (% (* (+ c d) (^ e f)) g))"
        );

        // 多重一元操作符（移除 ! 的支持）
        assert_eq!(prefix_to_infix("(+ ~-a -~b)"), "(~-a + -~b)");
        assert_eq!(infix_to_prefix("(~-a + -~b)"), "(+ (~ (- a)) (- (~ b)))");

        // 嵌套括号和优先级
        assert_eq!(
            prefix_to_infix("(* (+ a b) (- c (/ d (* e f))))"),
            "((a + b) * (c - (d / (e * f))))"
        );
        assert_eq!(
            infix_to_prefix("(((a + b) * (c - (d / (e * f)))))"),
            "(* (+ a b) (- c (/ d (* e f))))"
        );

        // 往返测试确保一致性
        let complex_cases = [
            "((((a + b) * c) - d) / e)",
            "(a + (b * (c - (d / (e + f)))))",
            "(-(a & b) + ~(c * d))",
            "((a & b) | (((c + d) * (e ^ f)) % g))",
            "(~-a + -~b)",
            "((a + b) * (c - (d / (e * f))))",
            "(((((a + b) * c) - d) / e) + f)",
            "(a * (b + (c * (d - (e / f)))))",
        ];
        for case in complex_cases {
            let prefix = infix_to_prefix(case);
            let infix = prefix_to_infix(&prefix);
            assert_eq!(infix, case, "Roundtrip failed for complex case: {}", case);
        }
    }
}
