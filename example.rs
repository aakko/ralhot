#[macro_use]
extern crate ralhot;

fn main() {
    let options = options! {
        r String output, "o=FILE";
        i32 timeout, "=SECONDS", "?spend up to SECONDS per entry (default: 5)";
        String arg_file, "a=FILE", "?read arguments from FILE";
        flag quiet, "q", "silent", "s", "?don't print progress";
        :outro "Please report bugs to https://example.com/bugs";
    };

    println!("I would output to {}", options.output);
    println!("I would time out after {}s", options.timeout.unwrap_or(5));
    options.arg_file.map(|af| println!("I would read arguments from {}", af));
    if options.quiet {
        println!("I would be quiet");
    }
}
