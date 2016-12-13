// #![feature(trace_macros)]
// trace_macros!(true);
#[macro_use]
extern crate ralhot;

#[test]
fn flag() {
    ralhot_no_parse!(r flag test;);
    let o = Options::parse_noexit(&["prog", "--test"]).unwrap();
    assert_eq!(o.test, true);
}

#[test]
fn option() {
    ralhot_no_parse!(i32 test;);
    let o = Options::parse_noexit(&["prog", "--test", "-1"]).unwrap();
    assert_eq!(o.test, Some(-1));
}

#[test]
fn required() {
    ralhot_no_parse!(r i8 test;);
    let o = Options::parse_noexit(&["prog", "--test", "-1"]).unwrap();
    assert_eq!(o.test, -1);
}

use ralhot::ParseError::*;

#[test]
fn required_missing() {
    ralhot_no_parse!(r i16 test_this;);
    let o = Options::parse_noexit(&["prog"]).unwrap_err();
    assert_eq!(o, Fail("prog: option 'test-this' is required\n".to_owned()));
}

#[test]
fn short_immediate_eq() {
    ralhot_no_parse!(r String t;);
    let o = Options::parse_noexit(&["prog", "-t=gotcha"]).unwrap();
    assert_eq!(o.t, "=gotcha");
}

#[test]
fn short_separate() {
    ralhot_no_parse!(r char t;);
    let o = Options::parse_noexit(&["prog", "-t", "-"]).unwrap();
    assert_eq!(o.t, '-');
}

#[test]
fn long_eq_empty() {
    ralhot_no_parse!(r String test;);
    let o = Options::parse_noexit(&["prog", "--test="]).unwrap();
    assert_eq!(o.test, "");
}

#[test]
fn long_stopword() {
    ralhot_no_parse!(:stopwords ["command"]; r String test;);
    let o = Options::parse_noexit(&["prog", "--test", "command"]).unwrap();
    assert_eq!(o.test, "command");
}

#[test]
fn long_unwanted_argument() {
    ralhot_no_parse!(flag test;);
    let o = Options::parse_noexit(&["prog", "--test=unwanted"]).unwrap_err();
    assert_eq!(o, Fail("prog: option 'test' doesn't allow an argument\n"
                       .to_owned()));
}

#[test]
fn short_missing_argument() {
    ralhot_no_parse!(u8 t;);
    let o = Options::parse_noexit(&["prog", "-t"]).unwrap_err();
    assert_eq!(o, Fail("prog: option 't' requires an argument\n".to_owned()));
}

#[test]
fn long_missing_argument() {
    ralhot_no_parse!(u8 test;);
    let o = Options::parse_noexit(&["prog", "--test"]).unwrap_err();
    let msg = "prog: option 'test' requires an argument\n";
    assert_eq!(o, Fail(msg.to_owned()));
}

#[test]
fn unknown_short() {
    ralhot_no_parse!();
    let o = Options::parse_noexit(&["prog", "-t"]).unwrap_err();
    assert_eq!(o, Fail("prog: unrecognized option 't'\n".to_owned()));
}

#[test]
fn unknown_long() {
    ralhot_no_parse!();
    let o = Options::parse_noexit(&["prog", "--test"]).unwrap_err();
    assert_eq!(o, Fail("prog: unrecognized option 'test'\n".to_owned()));
}

#[test]
fn version() {
    ralhot_no_parse!(:version "prog 1.0";);
    let o = Options::parse_noexit(&["prog", "--version"]).unwrap_err();
    assert_eq!(o, Succeed("prog 1.0\n".to_owned()))
}

#[test]
fn override_help() {
    ralhot_no_parse!(:help "cats dogs\n";);
    let o = Options::parse_noexit(&["prog", "--help"]).unwrap_err();
    assert_eq!(o, Succeed("cats dogs\n".to_owned()))
}

#[test]
fn help() {
    ralhot_no_parse!(u8 t, "test=this"; String o, "output"; u8 a, "b", "c";
             u8 really_long_option, "=COMPLEX-VALUE", "?help message";
    flag s, "?help message";);
    let o = Options::parse_noexit(&["prog", "--help"]).unwrap_err();
    let help = "Usage: prog [OPTION]...
  -t, --test=this
  -o, --output=ARG
  -a, -b, -c ARG
      --really-long-option=COMPLEX-VALUE
                             help message
  -s                         help message
      --help     display this help and exit
      --version  output version information and exit\n";
    assert_eq!(o, Succeed(help.to_owned()));
}

#[test]
fn help_wrap() {
    ralhot_no_parse!(flag a, "?A A A A A A A A A A A A A A A A A A A A A A
A A A A A A A A A A A A A A A A A A A A A A
A A A A A A A A A A A A A A A A A A A A A A
A A A A A A A A A A A A A A A A A A A A A A";
             flag b, "?A A A A A A A A A A A A A A A A A A A A A A
A A A A A A A A A A A A A A A A A A A A A A
A A A A A A A A A A A A A A A A A A A A A A
A A A A A A A A A A A A A A A A A A A A A A";);
    let help = "Usage: prog [OPTION]...
  -a                         A A A A A A A A A A A A A A A A A A A A A A A A A A
                               A A A A A A A A A A A A A A A A A A A A A A A A A
                               A A A A A A A A A A A A A A A A A A A A A A A A A
                               A A A A A A A A A A A A
  -b                         A A A A A A A A A A A A A A A A A A A A A A A A A A
                               A A A A A A A A A A A A A A A A A A A A A A A A A
                               A A A A A A A A A A A A A A A A A A A A A A A A A
                               A A A A A A A A A A A A
      --help     display this help and exit
      --version  output version information and exit\n";
    let o = Options::parse_noexit(&["prog", "--help"]).unwrap_err();
    assert_eq!(o, Succeed(help.to_owned()));
}

#[test]
fn help_indent() {
    ralhot_no_parse!(flag a, "?A A A A A A A A A A A A A A A A A A A A A A
A A A A A A A A A A A A A A A A A A A A A A
A A A A A A A A A A A A A A A A A A A A A A
A A A A A A A A A A A A A A A A A A A A A A";
             flag b, "?A A A A A A A A A A A A A A A A A A A A A A
A A A A A A A A A A A A A A A A A A A A A A
A A A A A A A A A A A A A A A A A A A A A A
A A A A A A A A A A A A A A A A A A A A A A"; :indent "6";);
    let help = "Usage: prog [OPTION]...
  -a A A A A A A A A A A A A A A A A A A A A A A A A A A A A A A A A A A A A A A
       A A A A A A A A A A A A A A A A A A A A A A A A A A A A A A A A A A A A A
       A A A A A A A A A A A A A
  -b A A A A A A A A A A A A A A A A A A A A A A A A A A A A A A A A A A A A A A
       A A A A A A A A A A A A A A A A A A A A A A A A A A A A A A A A A A A A A
       A A A A A A A A A A A A A
      --help     display this help and exit
      --version  output version information and exit\n";
    let o = Options::parse_noexit(&["prog", "--help"]).unwrap_err();
    assert_eq!(o, Succeed(help.to_owned()));
}

#[test]
#[should_panic(expected = "unknown attribute")]
fn unknown_attr() {
    options!(:strange "unknown";);
}

#[test]
fn program_path() {
    ralhot_no_parse!();
    let o = Options::parse_noexit(&["/usr/bin/prog", "--help"]).unwrap_err();
    assert_eq!(o, Succeed("Usage: prog [OPTION]...
      --help     display this help and exit
      --version  output version information and exit\n".to_owned()));
}

#[test]
fn usage_intro_outro() {
    ralhot_no_parse!(:usage "usage";
             :intro "intro";
             :outro "outro";); // newlines should be added
    let o = Options::parse_noexit(&["prog", "--help"]).unwrap_err();
    assert_eq!(o, Succeed("usage
intro
      --help     display this help and exit
      --version  output version information and exit
outro\n".to_owned()));
}

#[test]
fn double_char_short_immediate() {
    ralhot_no_parse!(char c; flag f;);
    let o = Options::parse_noexit(&["prog", "-fcdd"]).unwrap_err();
    assert_eq!(o, Fail("prog: -cdd: expected a single character\n".to_owned()))
}

#[test]
fn empty_char_short_separate() {
    ralhot_no_parse!(char c; flag f;);
    let o = Options::parse_noexit(&["prog", "-fc", ""]).unwrap_err();
    // this isn't model behavior
    assert_eq!(o, Fail("prog: -c : expected a single character\n".to_owned()));
}

#[test]
fn double_char_long_eq() {
    ralhot_no_parse!(char ch; flag f;);
    let o = Options::parse_noexit(&["prog", "-f", "--ch=dd"]).unwrap_err();
    assert_eq!(o, Fail("prog: --ch=dd: expected a single character\n"
                       .to_owned()))
}

#[test]
fn double_char_long_separate() {
    ralhot_no_parse!(char ch; flag f;);
    let o = Options::parse_noexit(&["prog", "-f", "--ch", "dd"]).unwrap_err();
    assert_eq!(o, Fail("prog: --ch dd: expected a single character\n"
                       .to_owned()))
}

#[test]
fn stopword() {
    ralhot_no_parse!(:stopwords ["abc", "def", "ghi"]; flag u; flag s;);
    let o = Options::parse_noexit(&["prog", "-s", "def", "-u", "ghi"]).unwrap();
    assert_eq!(o.u, false);
    assert_eq!(o.s, true);
    assert_eq!(o.leftovers, vec!["-u", "ghi"]);
    assert_eq!(o.leftovers_with_stopword, vec!["def", "-u", "ghi"]);
    assert_eq!(o.stopword_index, Some(0));
    assert_eq!(o.stopword, Some("def".to_owned()));
}

#[test]
fn overwrite() {
    ralhot_no_parse!(r u8 old, "new";);
    let o = Options::parse_noexit(&["prog", "--old=0", "--new=1"]).unwrap();
    assert_eq!(o.old, 1);
}
