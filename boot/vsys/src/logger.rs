use log::{Level, Metadata, Record};

use astd::io::Write;

static LOGGER: Logger = Logger;

pub fn init_logging() {
    init_logging_with_level(Level::Trace);
}

pub fn init_logging_with_level(level: Level) {
    log::set_logger(&LOGGER)
        .map(|_| log::set_max_level(level.to_level_filter()))
        .unwrap();
}

pub struct Logger;

impl log::Log for Logger {
    fn enabled(&self, _metadata: &Metadata) -> bool {
        true
    }

    fn log(&self, record: &Record) {
        let mut buffer: [u8; 1024] = [0u8; 1024];
        let mut writer = buffer.as_mut_slice();

        let _ = writer.write_fmt(*record.args());
        let remaining = writer.len();
        let written = buffer.len() - remaining;

        unsafe {
            crate::sys_debug_print(buffer.as_ptr(), written);
        }
    }

    fn flush(&self) {}
}
