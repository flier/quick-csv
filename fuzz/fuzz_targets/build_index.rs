#![no_main]
#[macro_use] extern crate libfuzzer_sys;
extern crate quick_csv;

fuzz_target!(|data: &[u8]| {
    let _ = quick_csv::build(data);
});
