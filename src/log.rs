use std::fs::File;
use std::ops::Deref;
use std::path::Path;
use std::sync::Mutex;
use log::{Level, LevelFilter, Metadata, Record};

static MY_LOGGER: Logger = Logger { level: Level::Trace, file: Mutex::new(None) };

struct Logger {
    level: Level,
    file: Mutex<Option<File>>
}

impl log::Log for Logger {
    fn enabled(&self, metadata: &Metadata) -> bool {
        metadata.level() <= self.level
    }

    fn log(&self, record: &Record) {
        if self.enabled(record.metadata()) {
            println!("{:5} - {}", record.level(), record.args());
        }
    }

    fn flush(&self) {}
}

pub fn enable_logging(log_file: Option<&Path>) {
    *MY_LOGGER.file.lock().unwrap() = log_file.map(|p| File::open(p).unwrap());
    log::set_logger(&MY_LOGGER).unwrap();
    log::set_max_level(LevelFilter::Trace);
}