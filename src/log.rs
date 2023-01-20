use log::{Level, LevelFilter, Metadata, Record};

static MY_LOGGER: Logger = Logger { level: Level::Trace };

struct Logger {
    level: Level
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

pub fn enable_logging() {
    log::set_logger(&MY_LOGGER).unwrap();
    log::set_max_level(LevelFilter::Trace);
}