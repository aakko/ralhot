//! Succinct command line parsing.
//!
//! ```rust,no_run
//! #[macro_use]
//! extern crate ralhot;
//!
//! fn main() {
//!     let options = options! {
//!         r String output, "o=FILE";
//!         i32 timeout, "=SECONDS", "?spend up to SECONDS per entry (default: 5)";
//!         String arg_file, "a=FILE", "?read arguments from FILE";
//!         flag quiet, "q", "silent", "s", "?don't print progress";
//!         :outro "Please report bugs to https://example.com/bugs";
//!     };
//!
//!     println!("I would output to {}", options.output);
//!     println!("I would time out after {}s", options.timeout.unwrap_or(5));
//!     options.arg_file.map(|af| println!("I would read arguments from {}", af));
//!     if options.quiet {
//!        println!("I would be quiet");
//!     }
//! }
//! ```
//! See [`options!`](macro.options.html) for the full details.

#![deny(missing_docs)]

#[doc(hidden)]
#[macro_export]
macro_rules! ralhot_parse {
    [$m:ident [$($args:tt)*] [$($attr:tt)*] [$($opt:tt)*]
     [ : $k:ident $v:expr ; $($tt:tt)*]] => {
        ralhot_parse![$m [$($args)*]
                      [$($attr)* [$k, $v]]
                      [$($opt)*]
                      [$($tt)*]];
    };
    [$m:ident [$($args:tt)*] [$($attr:tt)*] [$($opt:tt)*]
     [ $t:ident $n:ident $(, $v:expr)* ; $($tt:tt)*]] => {
        ralhot_parse![$m [$($args)*]
                      [$($attr)*]
                      [$($opt)* [[$t] [$n] $($v),*]]
                      [$($tt)*]];
    };
    [$m:ident [$($args:tt)*] [$($attr:tt)*] [$($opt:tt)*]
     [ r $t:ident $n:ident $(, $v:expr)* ; $($tt:tt)*]] => {
        ralhot_parse![$m [$($args)*]
                      [$($attr)*]
                      [$($opt)* [[req $t] [$n] $($v),*]]
                      [$($tt)*]];
    };
    [$m:ident [$($args:tt)*] [$($attr:tt)*] [$($opt:tt)*] []] => {
        $m![[$($args)*] [$($attr)*] [$($opt)*]];
    }
}

#[doc(hidden)]
#[macro_export]
macro_rules! ralhot_type {
    (req flag) => { bool };
    (flag) => { bool };
    (req $typ:ident) => { <$typ as $crate::OptionParser>::Parsed };
    ($typ:ident) => { Option<<$typ as $crate::OptionParser>::Parsed> };
}

#[doc(hidden)]
#[macro_export]
macro_rules! ralhot_required {
    (req flag) => {
        true
    };
    (flag) => {
        false
    };
    (req $typ:ident) => {
        true
    };
    ($typ:ident) => {
        false
    };
}

#[doc(hidden)]
#[macro_export]
macro_rules! ralhot_flag {
    (req flag) => {
        true
    };
    (flag) => {
        true
    };
    (req $typ:ident) => {
        false
    };
    ($typ:ident) => {
        false
    };
}

#[doc(hidden)]
#[macro_export]
macro_rules! ralhot_unwrap {
    ($parse:ident [req flag] $name:ident) => {
        $parse.flag[$name]
    };
    ($parse:ident [flag] $name:ident) => {
        $parse.flag[$name]
    };
    ($parse:ident [req $typ:ident] $name:ident) => {{
        use $crate::OptionParser;
        try!($typ::from_ralhot_required(&$parse, $name))
    }};
    ($parse:ident [$typ:ident] $name:ident) => {{
        use $crate::OptionParser;
        try!($typ::from_ralhot_optional(&$parse, $name))
    }};
}

#[doc(hidden)]
#[macro_export]
macro_rules! ralhot_attr {
    ($parser:ident, stopwords, $v:expr) => {
        $parser.add_stopwords(&$v)
    };
    ($parser:ident, $k:ident, $v:expr) => {
        $parser.add_attribute(stringify!($k), $v)
    }
}

#[doc(hidden)]
#[macro_export]
macro_rules! ralhot_main {
    [[$class:ident]
     [$([$k:ident, $v:expr])*]
     [$([[$($typ:tt)*] [$name:ident] $($alias:expr),*])*]] => {
        #[derive(Debug)]
        struct $class {
            leftovers: Vec<String>,
            leftovers_with_stopword: Vec<String>,
            stopword: Option<String>,
            stopword_index: Option<usize>,
            $($name: ralhot_type!($($typ)*)),*
        }

        impl $class {
            fn _parse() -> Self {
                use std;
                use std::io::Write;
                let args: Vec<String> = std::env::args().collect();
                let argsref: Vec<&str> = args.iter().map(|s| {
                    s.as_str()
                }).collect();

                match Self::parse_noexit(&argsref[..]) {
                    Ok(parse) => return parse,
                    Err($crate::ParseError::Fail(msg)) => {
                        write!(std::io::stderr(), "{}", msg).unwrap();
                        std::process::exit(1);
                    },
                    Err($crate::ParseError::Succeed(msg)) => {
                        write!(std::io::stdout(), "{}", msg).unwrap();
                        std::process::exit(0);
                    }
                }
            }

            fn parse_noexit(args: &[&str]) -> Result<Self, $crate::ParseError> {
                let mut _parser = $crate::Parser::new();
                let mut _i = 0;
                $(let $name = _i;
                  _parser
                  .add_option($crate::Opt::new(ralhot_required!($($typ)*),
                                               ralhot_flag!($($typ)*),
                                               &[stringify!($name)
                                                 $(, $alias)*]));
                  _i += 1;)*
                $(ralhot_attr!(_parser, $k, $v);)*
                let _parse = try!(_parser.parse(args));
                let leftovers_with_stopword: Vec<String> =
                    _parse.leftovers.iter().map(|&s| s.to_owned()).collect();
                let stopword_index = _parse.stopword;
                let stopword = stopword_index.map(|i| {
                    leftovers_with_stopword[i].clone()
                });
                let leftovers = match stopword_index {
                    None => leftovers_with_stopword.clone(),
                    Some(i) => {
                        let a = &leftovers_with_stopword[..i];
                        let b = &leftovers_with_stopword[(i + 1)..];
                        let mut leftovers = a.to_vec();
                        leftovers.extend_from_slice(b);
                        leftovers
                    }
                };
                Ok($class {
                    leftovers_with_stopword: leftovers_with_stopword,
                    leftovers: leftovers,
                    stopword: stopword,
                    stopword_index: stopword_index,
                    $($name: ralhot_unwrap!(_parse [$($typ)*] $name)),*
                })
            }
        }
    }
}

#[doc(hidden)]
#[macro_export]
macro_rules! ralhot_options_named {
    ($class:ident, $($tt:tt)*) => {
        ralhot_parse!(ralhot_main [$class] [] [] [$($tt)*]);
    }
}

#[doc(hidden)]
#[macro_export]
macro_rules! ralhot_no_parse {
    ($($tt:tt)*) => {
        ralhot_options_named!(Options, $($tt)*);
    }
}

/// `options!` takes as arguments a list of attributes and option
/// definitions, and produces a typed struct of parsed command line
/// options.
///
/// On failure, or on finding `--help` or `--version`, `options!` will
/// print a message and call `std::process::exit`.
///
/// # Option definitions
///
/// The format of an option definition is:
///
/// ```rust,ignore
/// r? type unquoted_alias(, "quoted-alias")*;
/// ```
///
/// The optional initial `r` marks the option as mandatory.
///
/// `type` can be any rust type that implements
/// [`OptionParser`](trait.OptionParser.html), or the special type
/// `flag`. Flags have type `bool` on the generated struct, whereas
/// rust types have type `OptionParser::Parsed` (which equals `Self` for
/// everything included in rahlot) if they are mandatory, and
/// `Option<OptionParser::Parsed>` otherwise.
///
/// `unquoted_alias` becomes the name of the option's field in the
/// generated struct.
///
/// The characters `_=?` have special significance in aliases.
///
/// Aliases starting with `_` are ignored. Underscores in other
/// positions are replaced with hyphens `-`. Both behaviors can be
/// useful on the first unquoted alias.
///
/// Aliases starting with or containing a `=` are used for argument
/// names in help messages. The half before `=` gets used as a normal
/// alias, unless it's empty as in `"=FILE"`.
///
/// Aliases starting with `?` become the option's help description.
///
/// # Attributes
///
/// The format of an attribute is
///
/// ```rust,ignore
/// :unquoted_key "quoted value";
/// ```
///
/// with the exception of `:stopwords`, which takes as its value an
/// array of strings to be added to the already loaded stopwords. The
/// available attributes are
///
/// ```rust,ignore
/// :program :version :stopwords :help :usage :intro :outro :indent
/// ```
///
/// If `:help` is set it replaces ralhot's built-in `--help` message
/// verbatim.
///
/// If `:help` is nil, the help message is a sequence of
///
/// 1. `:usage`
/// 2. `:intro`
/// 3. generated option descriptions
/// 4. `:outro`
///
/// `:usage` has a default value of `Usage: :program [OPTION]...` and
/// is a great candidate for being explicitly set. `:intro` and
/// `:outro` are nil by default.
///
/// ralhot ensures each non-nil section has at least one trailing
/// newline. Additional spacing can be added manually.
///
/// `:indent` controls the horizontal layout of option
/// descriptions. It defaults to column `"30"`.
///
/// `:program` and `:version` are taken from `argv[0]` and
/// `CARGO_PKG_NAME` if not set.
///
/// `:stopwords` defaults to `["--"]`. Custom stopwords can be added
/// but `"--"` can't be disabled as a stopword.
///
/// # Non-option structs fields
///
/// ```rust,ignore
/// leftovers: Vec<String>,
/// leftovers_with_stopword: Vec<String>,
/// stopword: Option<String>,
/// stopword_index: Option<usize>,
/// ```
///
/// Leftovers contain the "positional" command line arguments not
/// consumed by options. `leftovers` and `leftovers_with_stopword` are
/// identical when `stopword == None`, otherwise they differ by the
/// element
///
/// ```rust,ignore
/// leftovers_with_stopword[stopword_index.unwrap()] == stopword.unwrap()
/// ```
#[macro_export]
macro_rules! options {
    ($($tt:tt)*) => {{
        ralhot_no_parse!($($tt)*);
        Options::_parse()
    }}
}

#[doc(hidden)]
pub type Set<A> = std::collections::HashSet<A>;
#[doc(hidden)]
pub type Map<K, V> = std::collections::HashMap<K, V>;

#[doc(hidden)]
pub struct Opt {
    required: bool,
    name: String,
    argument: Option<String>,
    description: Option<String>,
    alias: Vec<String>,
}

fn align(s: &mut String, spaces: usize) {
    for _ in 0..spaces {
        s.push(' ');
    }
}

fn wrap_description(mut column: usize,
                    indent: usize,
                    desc: Option<&String>)
                    -> String {
    let mut s = String::new();
    if desc.is_none() {
        s.push('\n');
        return s;
    }

    let desc = desc.unwrap().trim();
    if column > indent - 2 {
        s.push('\n');
        column = 0;
    }
    if column < indent - 2 {
        align(&mut s, indent - 2 - column);
        column = indent - 2;
    }
    let indent = indent + 2;

    for word in desc.split_whitespace() {
        let len = word.chars().count();
        if 1 + column + len > 80 && column > indent {
            s.push('\n');
            align(&mut s, indent - 1);
            s.push_str(word);
            column = indent + len - 1;
        } else {
            s.push(' ');
            s.push_str(word);
            column += len + 1;
        }
    }

    s.push('\n');

    s
}

impl Opt {
    #[doc(hidden)]
    pub fn new(required: bool, flag: bool, aliases: &[&str]) -> Self {
        let aliases = aliases;
        let mut name = None;
        let mut argument = None;
        let mut description = None;
        let mut aliases_out = Vec::with_capacity(aliases.len());

        for &alias in aliases {
            let alias: String = alias.to_owned();
            match alias.chars().next() {
                None => panic!("ralhot: empty option alias"),
                Some('_') => continue,
                Some('=') => {
                    if argument.is_some() {
                        panic!("ralhot: multiple arg names: '{}'", alias);
                    }
                    argument = Some(alias[1..].to_owned());
                }
                Some('?') => {
                    if description.is_some() {
                        panic!("ralhot: multiple arg descs: '{}'", alias);
                    }
                    description = Some(alias[1..].to_owned());
                }
                _ => {
                    let eq = alias.find('=');
                    if eq.is_some() {
                        if argument.is_some() {
                            panic!("ralhot: multiple arg names: '{}'", alias);
                        }
                        argument = Some(alias[(eq.unwrap() + 1)..].to_owned());
                    }
                    let alias = match eq {
                        None => alias,
                        Some(byte) => alias[..(byte)].to_owned(),
                    };
                    let alias = alias.replace('_', "-");
                    if name.is_none() {
                        name = Some(alias.clone());
                    } else if name.as_ref().unwrap().chars().count() == 1 &&
                              alias.chars().count() > 1 {
                        name = Some(alias.clone());
                    }
                    aliases_out.push(alias)
                }
            }
        }

        if !flag && argument.is_none() {
            argument = Some("ARG".to_owned());
        }

        Opt {
            name: name.expect("ralhot: option without name"),
            required: required,
            argument: argument,
            description: description,
            alias: aliases_out,
        }
    }

    fn to_string(&self, indent: usize) -> String {
        let mut s = String::new();
        let mut short = vec![];
        let mut long = vec![];
        for alias in &self.alias {
            match alias.chars().next() {
                Some('_') | Some('=') | Some('?') => continue,
                _ => {
                    "pass";
                }
            }
            if alias.chars().count() == 1 {
                short.push(format!("-{}", alias));
            } else {
                long.push(format!("--{}", alias));
            }
        }
        let shorts = short.len();
        let longs = long.len();
        let mut combined = short;
        combined.append(&mut long);
        if shorts + longs == 0 {
            return s;
        }
        if shorts == 0 {
            s.push_str("      ");
        } else {
            s.push_str("  ");
        }
        s += combined.join(", ").as_str();
        if let Some(ref argument) = self.argument {
            if longs == 0 {
                s += format!(" {}", argument).as_str();
            } else {
                s += format!("={}", argument).as_str();
            }
        };

        let column = s.chars().count();
        let desc = self.description.as_ref();
        s.push_str(wrap_description(column, indent, desc).as_ref());

        s
    }
}

#[doc(hidden)]
pub struct Parse<'a> {
    pub flag: Vec<bool>,
    pub option: Vec<Option<&'a str>>,
    pub source: Vec<Option<String>>,
    pub leftovers: Vec<&'a str>,
    pub program: String,
    pub stopword: Option<usize>,
}

/// Implement this to extend ralhot's parsing capabilities.
pub trait OptionParser {
    /// Permits parsing the "same" type in multiple ways.
    type Parsed;

    #[doc(hidden)]
    fn from_ralhot_optional(parse: &Parse,
                            i: usize)
                            -> Result<Option<Self::Parsed>, ParseError> {
        match parse.option[i] {
            None => Ok(None),
            Some(v) => {
                Self::from_ralhot(v)
                    .map(|v| Some(v))
                    .map_err(|e| {
                        Fail(format!("{}: {}: {}\n",
                                     parse.program,
                                     parse.source[i].as_ref().unwrap(),
                                     e))
                    })
            }
        }
    }

    #[doc(hidden)]
    fn from_ralhot_required(parse: &Parse,
                            i: usize)
                            -> Result<Self::Parsed, ParseError> {
        Self::from_ralhot(parse.option[i].unwrap()).map_err(|e| {
            Fail(format!("{}: {}: {}\n",
                         parse.program,
                         parse.source[i].as_ref().unwrap(),
                         e))
        })
    }

    /// The error string will be prepended with the program name and
    /// the option and argument that caused the error.
    fn from_ralhot(&str) -> Result<Self::Parsed, String>;
}


impl OptionParser for char {
    type Parsed = char;

    fn from_ralhot(s: &str) -> Result<char, String> {
        let mut c = s.chars();
        let a = c.next();
        let b = c.next();
        match (a, b) {
            (None, None) |
            (Some(_), Some(_)) => Err("expected a single character".to_owned()),
            (Some(a), None) => Ok(a),
            (None, Some(_)) => panic!(),
        }
    }
}

macro_rules! ralhot_fromralhot {
    ($($typ:ident),*) => {$(
        impl OptionParser for $typ {
            type Parsed = $typ;

            fn from_ralhot(s: &str) -> Result<$typ, String> {
                use std::str::FromStr;
                $typ::from_str(s).map_err(|e| {
                    format!("{}", e)
                })
            }
        }
    )*}
}

use std::net::{IpAddr, Ipv4Addr, Ipv6Addr, SocketAddrV4, SocketAddrV6,
               SocketAddr};

ralhot_fromralhot!(bool,
                   f32,
                   f64,
                   isize,
                   i8,
                   i16,
                   i32,
                   i64,
                   usize,
                   u8,
                   u16,
                   u32,
                   u64,
                   String,
                   IpAddr,
                   Ipv4Addr,
                   Ipv6Addr,
                   SocketAddrV4,
                   SocketAddrV6,
                   SocketAddr);

#[doc(hidden)]
pub struct Parser {
    option: Vec<Opt>,
    index: Map<String, usize>,
    stopwords: Set<String>,
    attribute: Map<String, String>,
}

#[doc(hidden)]
#[derive(Debug, Eq, PartialEq)]
pub enum ParseError {
    Succeed(String),
    Fail(String),
}

use ParseError::*;

impl Parser {
    #[doc(hidden)]
    pub fn new() -> Self {
        let mut stopwords = Set::with_capacity(1);
        stopwords.insert("--".to_owned());
        Parser {
            option: vec![],
            index: Map::new(),
            stopwords: stopwords,
            attribute: Map::new(),
        }
    }

    #[doc(hidden)]
    pub fn add_attribute<S: Into<String>>(&mut self, k: S, v: S) {
        let k = k.into();
        match k.as_ref() {
            "help" | "usage" | "intro" | "outro" | "version" | "program" |
            "indent" => {}
            _ => panic!("ralhot: unknown attribute: {}", k),
        }
        if self.attribute.contains_key(&k) {
            panic!("ralhot: duplicate attribute: {}", k);
        }
        self.attribute.insert(k, v.into());
    }

    #[doc(hidden)]
    pub fn add_stopwords(&mut self, words: &[&str]) {
        for &word in words {
            self.stopwords.insert(word.to_owned());
        }
    }

    #[doc(hidden)]
    pub fn add_option(&mut self, opt: Opt) {
        let idx = self.option.len();
        for alias in &opt.alias {
            if self.index.contains_key(alias) {
                panic!("ralhot: duplicate option: {}", alias);
            }
            self.index.insert(alias.clone(), idx);
        }
        self.option.push(opt);
    }

    fn version(&self) -> String {
        match self.attribute.get("version") {
                Some(version) => version,
                None => {
                    option_env!("CARGO_PKG_VERSION")
                        .unwrap_or("unknown version")
                }
            }
            .to_owned()
    }

    fn program(&self) -> &str {
        match self.attribute.get("program") {
            Some(program) => program,
            None => "unknown program",
        }
    }

    fn usage(&self) -> String {
        match self.attribute.get("usage") {
            Some(usage) => usage.clone(),
            None => format!("Usage: {} [OPTION]...\n", self.program()),
        }
    }

    fn help(&self) -> String {
        fn nl(mut s: String) -> String {
            let last = s.pop();
            last.map(|c| s.push(c));
            match last {
                None | Some('\n') => {}
                Some(_) => s.push('\n'),
            };
            s
        }

        if let Some(help) = self.attribute.get("help") {
            return nl(help.clone());
        }

        let mut help = String::new();
        help.push_str(nl(self.usage()).as_ref());
        if let Some(intro) = self.attribute.get("intro") {
            help.push_str(nl(intro.clone()).as_ref());
        }

        use std::str::FromStr;
        let indent = self.attribute
            .get("indent")
            .map(|s| usize::from_str(s).unwrap())
            .unwrap_or(30);
        for option in &self.option {
            help.push_str(option.to_string(indent).as_ref());
        }
        let hv = "      --help     display this help and exit
      --version  output version information and exit\n";
        help.push_str(hv);
        if let Some(outro) = self.attribute.get("outro") {
            help.push_str(nl(outro.clone()).as_ref());
        }
        help
    }

    #[doc(hidden)]
    pub fn parse<'a>(&mut self,
                     args: &[&'a str])
                     -> Result<Parse<'a>, ParseError> {
        if !self.attribute.contains_key("program") {
            // TBD: portable path separators
            let program = args[0].split('/').last().unwrap();
            self.attribute.insert("program".to_owned(), program.to_owned());
        }

        let mut parse = Parse {
            flag: self.option.iter().map(|_| false).collect(),
            option: self.option.iter().map(|_| None).collect(),
            source: self.option.iter().map(|_| None).collect(),
            leftovers: Vec::with_capacity(args.len() - 1),
            program: self.program().to_owned(),
            stopword: None,
        };

        let args = &args[1..];
        let mut arg_iter = args.iter().enumerate();

        let fail = |msg| Err(Fail(msg));

        let doesnt_allow_arg = |opt: &str| {
            fail(format!("{}: option '{}' doesn't allow an argument\n",
                         self.program(),
                         opt))
        };

        let needs_arg = |opt: &str| {
            fail(format!("{}: option '{}' requires an argument\n",
                         self.program(),
                         opt))
        };

        let unrecognized = |opt: &str| {
            fail(format!("{}: unrecognized option '{}'\n", self.program(), opt))
        };

        let required = |opt: &str| {
            fail(format!("{}: option '{}' is required\n", self.program(), opt))
        };

        while let Some((arg_i, &arg)) = arg_iter.next() {
            if self.stopwords.contains(arg) {
                parse.stopword = Some(parse.leftovers.len());
                parse.leftovers.extend_from_slice(&args[arg_i..]);
                break;
            }

            if arg == "--help" {
                return Err(Succeed(self.help()));
            }
            if arg == "--version" {
                return Err(Succeed(format!("{}\n", self.version())));
            }

            let mut chars = arg.chars();
            let a = chars.next();
            let b = chars.next();

            match (a, b) {
                (Some('-'), Some('-')) => {
                    let eq = arg.find('=');
                    let opt = match eq {
                        None => &arg[2..],
                        Some(byte) => &arg[2..byte],
                    };

                    let i = self.index.get(opt);
                    if i.is_none() {
                        return unrecognized(opt);
                    }
                    let &i = i.unwrap();

                    if self.option[i].argument.is_none() {
                        if eq.is_some() {
                            return doesnt_allow_arg(opt);
                        } else {
                            parse.flag[i] = true;
                        }
                    } else {
                        if let Some(byte) = eq {
                            let v = &arg[(byte + 1)..];
                            parse.option[i] = Some(v);
                            parse.source[i] = Some(format!("--{}={}", opt, v));
                        } else {
                            match arg_iter.next() {
                                Some((_, v)) => {
                                    parse.option[i] = Some(v);
                                    parse.source[i] =
                                        Some(format!("--{} {}", opt, v));
                                }
                                None => return needs_arg(opt),
                            }
                        }
                    }
                }

                (Some('-'), Some(_)) => {
                    let mut chars = arg.chars();
                    chars.next();
                    while let Some(opt) = chars.next() {
                        // cross at the lowest point
                        let opt = opt.to_string();
                        let i = self.index.get(opt.as_str());
                        if i.is_none() {
                            return unrecognized(opt.as_str());
                        }
                        let &i = i.unwrap();

                        if self.option[i].argument.is_none() {
                            parse.flag[i] = true;
                            continue;
                        }

                        if chars.as_str() != "" {
                            parse.option[i] = Some(chars.as_str());
                            parse.source[i] =
                                Some(format!("-{}{}", opt, chars.as_str()));
                            break;
                        } else {
                            match arg_iter.next() {
                                Some((_, v)) => {
                                    parse.option[i] = Some(v);
                                    parse.source[i] =
                                        Some(format!("-{} {}", opt, v));
                                    break;
                                }
                                None => return needs_arg(opt.as_str()),
                            }
                        }
                    }
                }

                _ => parse.leftovers.push(arg),
            }
        }

        for i in 0..self.option.len() {
            if self.option[i].required && parse.option[i].is_none() &&
               self.option[i].argument.is_some() {
                return required(self.option[i].name.as_str());
            }
        }

        Ok(parse)
    }
}
