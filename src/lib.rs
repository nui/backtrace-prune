use std::fmt::{self, Display};

use nom::bytes::complete::{tag, take_while1};
use nom::character::complete::{multispace0, multispace1, newline, not_line_ending};
use nom::combinator::{consumed, iterator, map, not, opt, recognize, verify};
use nom::multi::{many0_count, separated_list1};
use nom::sequence::{pair, preceded, separated_pair, tuple};
use nom::IResult;
use ref_cast::{ref_cast_custom, RefCastCustom};

/// Represents a parsed stack frame.
#[derive(Debug, Clone, PartialEq)]
pub struct Frame<'a> {
    header: FrameHeader<'a>,
    symbols: &'a Symbols,
    matched: &'a str,
}

/// Represents a parsed symbol.
#[derive(Debug, Clone, PartialEq)]
pub struct Symbol<'a> {
    name: &'a str,
    location: Option<&'a str>,
    matched: &'a str,
}

/// Represents unparsed symbols.
#[derive(Debug, PartialEq, RefCastCustom)]
#[repr(transparent)]
pub struct Symbols {
    matched: str,
}

#[derive(Debug, Clone, PartialEq)]
struct FrameHeader<'a> {
    index: u64,
    // instruction pointer
    ip: &'a str,
    matched: &'a str,
}

impl Frame<'_> {
    pub fn symbols(&self) -> &Symbols {
        &self.symbols
    }
}

impl Symbol<'_> {
    pub fn name(&self) -> &str {
        self.name
    }

    pub fn location(&self) -> Option<&str> {
        self.location
    }
}

impl Symbols {
    /// Returns an iterator yields all symbols
    pub fn iter(&self) -> impl Iterator<Item=Symbol<'_>> {
        let mut input = &self.matched;
        let mut first = true;
        let mut iter = None;

        core::iter::from_fn(move || {
            if first {
                first = false;
                let (next_input, symbol) = symbol(input).ok()?;
                input = next_input;
                Some(symbol)
            } else {
                let mut it = iter.get_or_insert_with(|| iterator(input, preceded(newline, symbol)));
                it.next()
            }
        })
    }

    #[ref_cast_custom]
    pub(crate) const fn new(s: &str) -> &Self;
}

fn symbol(input: &str) -> IResult<&str, Symbol<'_>> {
    let (input, (matched, (name, location))) = consumed(tuple((
        preceded(multispace0, not_line_ending),
        opt(preceded(newline, location)),
    )))(input)?;
    Ok((
        input,
        Symbol {
            name,
            location,
            matched,
        },
    ))
}

fn symbols(input: &str) -> IResult<&str, &Symbols> {
    map(symbol_lines, |matched| Symbols::new(&matched))(input)
}

fn location(input: &str) -> IResult<&str, &str> {
    let mut parser = preceded(pair(multispace0, tag("at ")), not_line_ending);
    let (input, location) = parser(input)?;
    Ok((input, location))
}

fn frame_header(input: &str) -> IResult<&str, FrameHeader<'_>> {
    let parser = tuple((
        preceded(multispace0, nom::character::complete::u64),
        preceded(
            pair(tag(":"), multispace1),
            take_while1(|c: char| !c.is_ascii_whitespace()),
        ),
    ));
    let (input, (matched, (index, ip))) = consumed(parser)(input)?;
    Ok((input, FrameHeader { index, ip, matched }))
}

fn symbol_line(input: &str) -> IResult<&str, &str> {
    verify(not_line_ending, |line: &str| {
        not(frame_header)(line).is_ok() && !line.is_empty()
    })(input)
}

fn symbol_lines(input: &str) -> IResult<&str, &str> {
    recognize(pair(
        symbol_line,
        many0_count(preceded(newline, symbol_line)),
    ))(input)
}

fn frame(input: &str) -> IResult<&str, Frame<'_>> {
    let parser = separated_pair(frame_header, tag(" - "), symbols);
    let (input, (matched, (header, symbols))) = consumed(parser)(input)?;
    Ok((
        input,
        Frame {
            header,
            symbols,
            matched,
        },
    ))
}

// This function is public because we use it in integration test.
#[doc(hidden)]
pub fn _all_frames(input: &str) -> IResult<&str, Vec<Frame<'_>>> {
    separated_list1(newline, frame)(input)
}

/// Display a pruned backtrace
#[derive(Clone)]
pub struct BacktracePruner<BT, F> {
    backtrace: BT,
    predicate: F,
    enabled: bool,
}

impl<BT, F> BacktracePruner<BT, F>
    where
        BT: Display,
        F: Fn(&Frame<'_>) -> bool,
{
    pub fn new(backtrace: BT, predicate: F) -> Self {
        BacktracePruner {
            backtrace,
            predicate,
            enabled: true,
        }
    }

    pub fn enabled(self, enabled: bool) -> Self {
        Self { enabled, ..self }
    }
}

impl<BT, F> Display for BacktracePruner<BT, F>
    where
        BT: Display,
        F: Fn(&Frame<'_>) -> bool,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let Self {
            backtrace,
            predicate,
            enabled,
        } = self;
        if !enabled {
            return Display::fmt(backtrace, f);
        }
        let formatted = if f.alternate() {
            format!("{:#}", backtrace)
        } else {
            format!("{}", backtrace)
        };
        if let Ok((_, frames)) = _all_frames(&formatted) {
            for frame in frames {
                let keep = predicate(&frame);
                if keep {
                    writeln!(f, "{}", frame.matched)?;
                }
            }
        } else {
            // If for some reasons we can't extract frames, print the whole backtrace.
            write!(f, "{formatted}")?;
        }
        Ok(())
    }
}

impl Display for Symbols {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        Display::fmt(&self.matched, f)
    }
}

impl Display for Symbol<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        Display::fmt(&self.matched, f)
    }
}

impl Display for Frame<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        Display::fmt(&self.matched, f)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    #[ignore]
    fn playground() {
        let backtrace_content = include_str!("./test_data/anyhow_alternate_backtrace.log");
        fn predicate(frame: &'_ Frame<'_>) -> bool {
            frame
                .symbols
                .iter()
                .any(|s| s.location().map(|l| l.contains("/rust_app/")).unwrap_or_default())
        }
        let formatted = BacktracePruner::new(backtrace_content, predicate).enabled(true);
        println!("{formatted}");
    }

    #[test]
    fn test_symbol_line() {
        let input = "<unknown>\n";
        let (rest, consumed) = symbol_line(input).unwrap();
        assert_eq!(consumed, "<unknown>");
        assert_eq!(rest, "\n")
    }

    #[test]
    fn test_symbol() {
        let input = [
            "  <alloc::boxed::Box<F,A> as core::ops::function::FnOnce<Args>>::call_once::h6906883c713b69be",
            "      at /rustc/d5a82bbd26e1ad8b7401f6a718a9c57c96905483/library/alloc/src/boxed.rs:2000:9",
        ].join("\n");
        let (_, actual) = symbol(&input).unwrap();
        assert_eq!(actual.name, "<alloc::boxed::Box<F,A> as core::ops::function::FnOnce<Args>>::call_once::h6906883c713b69be");
        assert_eq!(
            actual.location,
            Some(
                "/rustc/d5a82bbd26e1ad8b7401f6a718a9c57c96905483/library/alloc/src/boxed.rs:2000:9"
            )
        );

        let input = "<unknown>";
        let (_, actual) = symbol(input).unwrap();
        assert_eq!(actual.name, input);
        assert_eq!(actual.location, None);
    }

    #[test]
    fn test_frame() {
        let inputs = [
            "35:        0x10eb35f67 -   <alloc::boxed::Box<F,A> as core::ops::function::FnOnce<Args>>::call_once::h7c8ede2e3550473e",
            "                               at /rustc/d5a82bbd26e1ad8b7401f6a718a9c57c96905483/library/alloc/src/boxed.rs:2000:9",
            "                           <alloc::boxed::Box<F,A> as core::ops::function::FnOnce<Args>>::call_once::h6906883c713b69be",
            "                               at /rustc/d5a82bbd26e1ad8b7401f6a718a9c57c96905483/library/alloc/src/boxed.rs:2000:9",
            "                           std::sys::unix::thread::Thread::new::thread_start::he272a3f7edb058e0",
            "                               at /rustc/d5a82bbd26e1ad8b7401f6a718a9c57c96905483/library/std/src/sys/unix/thread.rs:108:17",
        ];
        let input = inputs.join("\n");
        let (_, actual) = frame(&input).unwrap();
        assert_eq!(
            actual.header,
            FrameHeader {
                index: 35,
                ip: "0x10eb35f67",
                matched: "35:        0x10eb35f67",
            }
        );
        assert_eq!(actual.symbols.iter().collect::<Vec<_>>(), vec![
            Symbol {
                name: "<alloc::boxed::Box<F,A> as core::ops::function::FnOnce<Args>>::call_once::h7c8ede2e3550473e",
                location: Some("/rustc/d5a82bbd26e1ad8b7401f6a718a9c57c96905483/library/alloc/src/boxed.rs:2000:9"),
                matched: "  <alloc::boxed::Box<F,A> as core::ops::function::FnOnce<Args>>::call_once::h7c8ede2e3550473e\n                               at /rustc/d5a82bbd26e1ad8b7401f6a718a9c57c96905483/library/alloc/src/boxed.rs:2000:9",
            },
            Symbol {
                name: "<alloc::boxed::Box<F,A> as core::ops::function::FnOnce<Args>>::call_once::h6906883c713b69be",
                location: Some("/rustc/d5a82bbd26e1ad8b7401f6a718a9c57c96905483/library/alloc/src/boxed.rs:2000:9"),
                matched: &inputs[2..4].join("\n"),
            },
            Symbol {
                name: "std::sys::unix::thread::Thread::new::thread_start::he272a3f7edb058e0",
                location: Some("/rustc/d5a82bbd26e1ad8b7401f6a718a9c57c96905483/library/std/src/sys/unix/thread.rs:108:17"),
                matched: &inputs[4..6].join("\n"),
            },
        ]);
    }

    #[test]
    fn test_frame_header() {
        let input = indoc::indoc! {r###"
             38:     0x7fa2745dea00 - clone3
        "###};
        let (rest, actual) = frame_header(input).unwrap();
        assert_eq!(rest, " - clone3\n");
        assert_eq!(
            actual,
            FrameHeader {
                index: 38,
                ip: "0x7fa2745dea00",
                matched: "38:     0x7fa2745dea00",
            }
        );
    }

    #[test]
    fn test_stripped_frame() {
        let input = indoc::indoc! {r###"
            39:                0x0 - <unknown>
        "###};
        let (rest, actual) = frame(input).unwrap();
        assert_eq!(rest, "\n");
        assert_eq!(
            actual.header,
            FrameHeader {
                index: 39,
                ip: "0x0",
                matched: "39:                0x0",
            }
        );
        assert_eq!(
            actual.symbols.iter().collect::<Vec<_>>(),
            vec![Symbol {
                name: "<unknown>",
                location: None,
                matched: "<unknown>",
            }]
        );
    }

    #[test]
    fn test_frames() {
        assert!(_all_frames("").is_err())
    }
}
