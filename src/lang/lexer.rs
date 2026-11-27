//! The tokens of the pipeline language and the helpers that read source text by them: string
//! literals, comments and parentheses.

use super::builtins::get;
use super::host::defined_builtin;
use super::parser::known_name;
use super::types::Ty;
use super::vars::NONE;

#[derive(Clone, Debug, PartialEq)]
pub(crate) enum Tok {
    Open,
    Close,
    Bar,
    Or,
    And,
    Not,
    Cmp(&'static str),
    Arith(char),
    Num(u64),
    Name(String),
    /// A string literal, its escapes read.
    Str(String),
    Assign,
    At,
    Colon,
    Arrow,
}

pub(crate) fn name_start(c: char) -> bool {
    c.is_ascii_alphabetic() || c == '_'
}

pub(crate) fn name_char(c: char) -> bool {
    c.is_ascii_alphanumeric() || c == '_'
}

/// The error for `w`, a word `a/b` written without spaces, when it is an old name with `/`:
/// a one-name function or macro written `save/t`, or a name known with `_` (`polish/factor`).
pub fn slash_name(w: &str) -> Option<String> {
    let (h, r) = w.split_once('/')?;
    let one_name = |h: &str| get(h).is_some_and(|s| matches!(s.params.as_slice(), [p] if matches!(p.ty, Ty::Group | Ty::Name)));
    if !r.is_empty() && !r.contains('/') && (one_name(h) || h == "on" || h == "off") {
        return Some(format!("write {w} as ({h} {r})"));
    }
    let joined = w.replace('/', "_");
    let known = known_name(&joined) || defined_builtin(&joined) || joined.starts_with("sub_");
    known.then(|| format!("names cannot contain '/': write {joined}"))
}

pub(crate) fn lex(s: &str) -> Result<Vec<Tok>, String> {
    let cs: Vec<char> = s.chars().collect();
    let mut out = Vec::new();
    let mut i = 0;
    while i < cs.len() {
        let c = cs[i];
        let next = cs.get(i + 1).copied();
        let two = |a: char| next == Some(a);
        let (tok, len) = match c {
            '#' => {
                while i < cs.len() && cs[i] != '\n' {
                    i += 1;
                }
                continue;
            }
            c if c.is_whitespace() => {
                i += 1;
                continue;
            }
            '"' => {
                let (text, len) = string_at(&cs[i..])?;
                (Tok::Str(text), len)
            }
            '(' => (Tok::Open, 1),
            ')' => (Tok::Close, 1),
            '|' if two('|') => (Tok::Or, 2),
            '|' => (Tok::Bar, 1),
            '&' if two('&') => (Tok::And, 2),
            '!' if two('=') => (Tok::Cmp("!="), 2),
            '!' => (Tok::Not, 1),
            '<' if two('=') => (Tok::Cmp("<="), 2),
            '<' => (Tok::Cmp("<"), 1),
            '>' if two('=') => (Tok::Cmp(">="), 2),
            '>' => (Tok::Cmp(">"), 1),
            '=' if two('=') => (Tok::Cmp("=="), 2),
            '=' => (Tok::Assign, 1),
            '@' => (Tok::At, 1),
            ':' => (Tok::Colon, 1),
            '-' if two('>') => (Tok::Arrow, 2),
            '+' | '-' | '*' | '/' => (Tok::Arith(c), 1),
            c if c.is_ascii_digit() => {
                let n: String = cs[i..].iter().take_while(|c| c.is_ascii_digit()).collect();
                let len = n.len();
                let v = n.parse().ok().filter(|v| *v != NONE).ok_or_else(|| format!("number too large: {n}"))?;
                (Tok::Num(v), len)
            }
            c if name_start(c) => {
                let len = cs[i..].iter().take_while(|c| name_char(**c)).count();
                let mut end = i + len;
                while cs.get(end) == Some(&'/') && cs.get(end + 1).is_some_and(|c| name_start(*c)) {
                    end += 1 + cs[end + 1..].iter().take_while(|c| name_char(**c)).count();
                }
                if let Some(e) = slash_name(&cs[i..end].iter().collect::<String>()) {
                    return Err(e);
                }
                (Tok::Name(cs[i..i + len].iter().collect()), len)
            }
            _ if s.contains("(extern") => return Err(NO_EXTERN.into()),
            _ => return Err(format!("unexpected character {c:?} in pipeline")),
        };
        out.push(tok);
        i += len;
    }
    Ok(out)
}

/// The string literal at the start of `cs`, a `"`, and the characters it takes: `\"` and
/// `\\` are the only escapes, and it ends on its line.
fn string_at(cs: &[char]) -> Result<(String, usize), String> {
    let mut text = String::new();
    let mut k = 1;
    loop {
        match cs.get(k) {
            None | Some('\n') => return Err(format!("unclosed string: {}", cs[..k].iter().collect::<String>())),
            Some('"') => return Ok((text, k + 1)),
            Some('\\') => match cs.get(k + 1) {
                Some(c @ ('"' | '\\')) => {
                    text.push(*c);
                    k += 2;
                }
                c => return Err(format!("unknown escape \\{} in a string: only \\\" and \\\\ are read", c.map_or(String::new(), |c| c.to_string()))),
            },
            Some(c) => {
                text.push(*c);
                k += 1;
            }
        }
    }
}

/// `s` written as a string literal that `string_at` reads back.
pub(crate) fn quoted(s: &str) -> String {
    format!("\"{}\"", s.replace('\\', "\\\\").replace('"', "\\\""))
}

/// `s` up to a `#` that starts a comment, outside string literals.
pub(crate) fn code_part(s: &str) -> &str {
    let (mut in_str, mut esc) = (false, false);
    for (i, c) in s.char_indices() {
        match c {
            _ if esc => esc = false,
            '\\' if in_str => esc = true,
            '"' => in_str = !in_str,
            '#' if !in_str => return &s[..i],
            _ => {}
        }
    }
    s
}

/// The parentheses opened less those closed in `s`, outside string literals.
pub(crate) fn depth_of(s: &str) -> i32 {
    let (mut d, mut in_str, mut esc) = (0, false, false);
    for c in s.chars() {
        match c {
            _ if esc => esc = false,
            '\\' if in_str => esc = true,
            '"' => in_str = !in_str,
            '(' if !in_str => d += 1,
            ')' if !in_str => d -= 1,
            _ => {}
        }
    }
    d
}

pub(crate) const NO_EXTERN: &str = "extern declarations are only read from src/builtins.pipe";

pub(crate) fn show_tok(t: Option<&Tok>) -> String {
    match t {
        None => "the end".into(),
        Some(t) => match t {
            Tok::Open => "(".into(),
            Tok::Close => ")".into(),
            Tok::Bar => "|".into(),
            Tok::Or => "||".into(),
            Tok::And => "&&".into(),
            Tok::Not => "!".into(),
            Tok::Cmp(c) => c.to_string(),
            Tok::Arith(c) => c.to_string(),
            Tok::Num(n) => n.to_string(),
            Tok::Name(n) => n.clone(),
            Tok::Str(t) => quoted(t),
            Tok::Assign => "=".into(),
            Tok::At => "@".into(),
            Tok::Colon => ":".into(),
            Tok::Arrow => "->".into(),
        },
    }
}

/// Whether `s` looks like the old `seq(a,b)` syntax, for an error message: a name directly
/// followed by `(`.
pub fn is_old_syntax(s: &str) -> bool {
    let cs: Vec<char> = s.chars().collect();
    cs.windows(2).any(|w| name_char(w[0]) && w[1] == '(')
}
