#[macro_use]
extern crate criterion;

use std::fs;
use std::io;
use std::path::Path;

use criterion::{Criterion, ParameterizedBenchmark, Throughput};

fn read_data(filename: &str) -> io::Result<Vec<u8>> {
    fs::read(
        Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("data/bench")
            .join(filename),
    )
}

fn parse_benchmark(c: &mut Criterion) {
    c.bench(
        "parse",
        ParameterizedBenchmark::new(
            "quick_csv::parse",
            |b, &&(filename, records, fields)| {
                let data = read_data(filename).unwrap();

                b.iter(|| {
                    let csv = quick_csv::parse(data.as_slice());

                    let mut count_fields = 0;
                    let mut count_records = 0;

                    for record in csv {
                        count_records += 1;
                        count_fields += record.records().count();
                    }

                    assert_eq!(
                        count_records, records,
                        "{} should has {} records",
                        filename, records
                    );
                    assert_eq!(
                        count_fields, fields,
                        "{} should has {} fields",
                        filename, records
                    );
                })
            },
            &[
                ("game.csv", 100000, 600000),
                ("gtfs-mbta-stop-times.csv", 0, 0),
                ("nfl.csv", 0, 0),
                ("worldcitiespop.csv", 0, 0),
            ],
        )
        .with_function(
            "csv_core::read_field_dfa",
            move |b, &&(filename, records, fields)| {
                use csv_core::*;

                let data = read_data(filename).unwrap();
                let mut reader = Reader::new();
                let mut bytes = data.as_slice();
                let mut data = [0; 1024];

                b.iter(|| {
                    reader.reset();

                    let mut count_fields = 0;
                    let mut count_records = 0;

                    loop {
                        let (res, len, _) = reader.read_field(bytes, &mut data);

                        bytes = &bytes[len..];

                        match res {
                            ReadFieldResult::InputEmpty => {}
                            ReadFieldResult::OutputFull => panic!("field too large"),
                            ReadFieldResult::Field { record_end } => {
                                count_fields += 1;
                                if record_end {
                                    count_records += 1;
                                }
                            }
                            ReadFieldResult::End => break,
                        }
                    }

                    assert_eq!(
                        count_records, records,
                        "{} should has {} records",
                        filename, records
                    );
                    assert_eq!(
                        count_fields, fields,
                        "{} should has {} fields",
                        filename, records
                    );
                });
            },
        )
        .with_function(
            "csv_core::read_field_nfa",
            move |b, &&(filename, records, fields)| {
                use csv_core::*;

                let data = read_data(filename).unwrap();
                let mut builder = ReaderBuilder::new();
                builder.nfa(true);
                let mut reader = builder.build();
                let mut bytes = data.as_slice();
                let mut data = [0; 1024];

                b.iter(|| {
                    reader.reset();

                    let mut count_fields = 0;
                    let mut count_records = 0;

                    loop {
                        let (res, len, _) = reader.read_field(bytes, &mut data);

                        bytes = &bytes[len..];

                        match res {
                            ReadFieldResult::InputEmpty => {}
                            ReadFieldResult::OutputFull => panic!("field too large"),
                            ReadFieldResult::Field { record_end } => {
                                count_fields += 1;
                                if record_end {
                                    count_records += 1;
                                }
                            }
                            ReadFieldResult::End => break,
                        }
                    }

                    assert_eq!(
                        count_records, records,
                        "{} should has {} records",
                        filename, records
                    );
                    assert_eq!(
                        count_fields, fields,
                        "{} should has {} fields",
                        filename, records
                    );
                });
            },
        )
        .throughput(|&(filename, _, _)| {
            Throughput::Bytes(
                fs::metadata(
                    Path::new(env!("CARGO_MANIFEST_DIR"))
                        .join("data/bench")
                        .join(filename),
                )
                .unwrap()
                .len() as u32,
            )
        }),
    );
}

criterion_group!(benches, parse_benchmark);
criterion_main!(benches);
