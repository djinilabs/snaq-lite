//! Granular dates: temporal intervals with an explicit grain (Year, Month, Day, Hour, Minute, Second).
//! Stored as anchor (start of interval) in Unix time (UTC) plus grain; bounds are computed for comparison.

#![allow(deprecated)] // chrono NaiveDateTime::from_timestamp_opt / .timestamp() until we switch to DateTime<Utc>

use chrono::{Datelike, NaiveDate, NaiveDateTime, Timelike};
use std::fmt;

/// Fineness of a date literal; ordering: Year < Month < Day < Hour < Minute < Second.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum Grain {
    Year,
    Month,
    Day,
    Hour,
    Minute,
    Second,
}

impl Grain {
    /// Ordering for grain strictness: 0 = Year (coarsest), 5 = Second (finest).
    pub fn strictness(self) -> u8 {
        match self {
            Grain::Year => 0,
            Grain::Month => 1,
            Grain::Day => 2,
            Grain::Hour => 3,
            Grain::Minute => 4,
            Grain::Second => 5,
        }
    }

    /// True if `self` is at least as fine as `other` (can accept duration at `other` or coarser).
    pub fn at_least_as_fine_as(self, other: Grain) -> bool {
        self.strictness() >= other.strictness()
    }
}

impl PartialOrd for Grain {
    fn partial_cmp(&self, other: &Grain) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Grain {
    fn cmp(&self, other: &Grain) -> std::cmp::Ordering {
        self.strictness().cmp(&other.strictness())
    }
}

/// Map a Time unit name (as in the unit registry) to a Grain. Returns None for non-time units.
pub fn grain_for_time_unit_name(name: &str) -> Option<Grain> {
    match name {
        "s" | "second" | "seconds" => Some(Grain::Second),
        "minute" | "minutes" => Some(Grain::Minute),
        "hour" | "hours" => Some(Grain::Hour),
        "day" | "days" => Some(Grain::Day),
        "month" | "months" => Some(Grain::Month),
        "year" | "years" => Some(Grain::Year),
        "week" | "weeks" => Some(Grain::Day), // week is coarser than day, treat as day for grain
        "quarter" | "quarters" => Some(Grain::Month),
        "decade" | "decades" => Some(Grain::Year),
        "century" | "centuries" => Some(Grain::Year),
        "millennium" | "millenniums" => Some(Grain::Year),
        _ => None,
    }
}

/// A date as a bounded temporal interval: anchor (start) in Unix seconds (UTC) and grain.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct GranularDate {
    /// Start of the interval in Unix seconds (UTC). Fractional allowed for sub-second grains if needed.
    anchor_epoch_sec: i64,
    grain: Grain,
}

impl GranularDate {
    pub fn new(anchor_epoch_sec: i64, grain: Grain) -> Self {
        Self {
            anchor_epoch_sec,
            grain,
        }
    }

    pub fn grain(&self) -> Grain {
        self.grain
    }

    /// Start of the interval in seconds since Unix epoch (UTC).
    pub fn min_epoch_sec(&self) -> f64 {
        self.anchor_epoch_sec as f64
    }

    /// End of the interval: last instant still inside the interval (exclusive end = max + 1 for discrete).
    /// For Second grain we treat the interval as [anchor, anchor+1) seconds; for Minute [anchor, anchor+60), etc.
    pub fn max_epoch_sec(&self) -> f64 {
        let anchor = self.anchor_epoch_sec;
        let dt = NaiveDateTime::from_timestamp_opt(anchor, 0).unwrap_or(NaiveDateTime::MIN);
        let end = match self.grain {
            Grain::Year => {
                let next = NaiveDate::from_ymd_opt(dt.year() + 1, 1, 1).and_then(|d| d.and_hms_opt(0, 0, 0));
                next.map(|t| t.timestamp()).unwrap_or(i64::MAX) - 1
            }
            Grain::Month => {
                let (y, m) = if dt.month() == 12 {
                    (dt.year() + 1, 1)
                } else {
                    (dt.year(), dt.month() + 1)
                };
                NaiveDate::from_ymd_opt(y, m, 1)
                    .and_then(|d| d.and_hms_opt(0, 0, 0))
                    .map(|t| t.timestamp() - 1)
                    .unwrap_or(i64::MAX)
            }
            Grain::Day => {
                let d = NaiveDate::from_ymd_opt(dt.year(), dt.month(), dt.day()).unwrap_or_default();
                (d.succ_opt().and_then(|d| d.and_hms_opt(0, 0, 0)).map(|t| t.timestamp()).unwrap_or(i64::MAX)) - 1
            }
            Grain::Hour => anchor + 3600 - 1,
            Grain::Minute => anchor + 60 - 1,
            Grain::Second => anchor,
        };
        end as f64
    }

    /// Anchor in seconds (for arithmetic: Date ± Time).
    pub fn anchor_epoch_sec(&self) -> i64 {
        self.anchor_epoch_sec
    }

    /// New date with the same grain but shifted anchor (for Date + Time).
    pub fn with_anchor_epoch_sec(self, anchor_epoch_sec: i64) -> Self {
        Self {
            anchor_epoch_sec,
            grain: self.grain,
        }
    }
}

/// Parse an ISO 8601 temporal string (as emitted by the lexer after `@`) into a GranularDate.
/// Valid forms: YYYY, YYYY-MM, YYYY-MM-DD, YYYY-MM-DDTHH, YYYY-MM-DDTHH:MM, YYYY-MM-DDTHH:MM:SS.
pub fn parse_temporal_literal(s: &str) -> Result<GranularDate, String> {
    let s = s.trim();
    if s.is_empty() {
        return Err("empty temporal literal".to_string());
    }
    let parts: Vec<&str> = s.splitn(2, 'T').collect();
    let date_part = parts[0];
    let time_part = parts.get(1).copied().unwrap_or("");
    let date_components: Vec<&str> = date_part.split('-').collect();
    let year: i32 = date_components
        .first()
        .and_then(|y| y.parse().ok())
        .ok_or_else(|| format!("invalid year: {date_part}"))?;
    if !(1..=9999).contains(&year) {
        return Err(format!("year out of range: {year}"));
    }
    let (month, day) = match date_components.len() {
        1 => (1u32, 1u32),
        2 => {
            let m: u32 = date_components[1].parse().map_err(|_| format!("invalid month: {}", date_components[1]))?;
            if !(1..=12).contains(&m) {
                return Err(format!("month out of range: {m}"));
            }
            (m, 1)
        }
        3 => {
            let m: u32 = date_components[1].parse().map_err(|_| format!("invalid month: {}", date_components[1]))?;
            let d: u32 = date_components[2].parse().map_err(|_| format!("invalid day: {}", date_components[2]))?;
            if !(1..=12).contains(&m) {
                return Err(format!("month out of range: {m}"));
            }
            (m, d)
        }
        _ => return Err(format!("invalid date part: {date_part}")),
    };
    let (hour, minute, second) = if time_part.is_empty() {
        (0u32, 0u32, 0u32)
    } else {
        let time_components: Vec<&str> = time_part.split(':').collect();
        match time_components.len() {
            1 => {
                let h: u32 = time_components[0].parse().map_err(|_| format!("invalid hour: {}", time_components[0]))?;
                if h > 23 {
                    return Err(format!("hour out of range: {h}"));
                }
                (h, 0u32, 0u32)
            }
            2 => {
                let h: u32 = time_components[0].parse().map_err(|_| format!("invalid hour: {}", time_components[0]))?;
                let m: u32 = time_components[1].parse().map_err(|_| format!("invalid minute: {}", time_components[1]))?;
                if h > 23 || m > 59 {
                    return Err("hour or minute out of range".to_string());
                }
                (h, m, 0u32)
            }
            3 => {
                let h: u32 = time_components[0].parse().map_err(|_| format!("invalid hour: {}", time_components[0]))?;
                let m: u32 = time_components[1].parse().map_err(|_| format!("invalid minute: {}", time_components[1]))?;
                let s: u32 = time_components[2].parse().map_err(|_| format!("invalid second: {}", time_components[2]))?;
                if h > 23 || m > 59 || s > 59 {
                    return Err("hour, minute or second out of range".to_string());
                }
                (h, m, s)
            }
            _ => return Err(format!("invalid time part: {time_part}")),
        }
    };
    let grain = match (date_components.len(), time_part.is_empty(), time_part.split(':').count()) {
        (1, true, _) => Grain::Year,
        (2, true, _) => Grain::Month,
        (3, true, _) => Grain::Day,
        (3, false, 1) => Grain::Hour,
        (3, false, 2) => Grain::Minute,
        (3, false, 3) => Grain::Second,
        _ => return Err(format!("invalid temporal pattern: {s}")),
    };
    let naive = NaiveDate::from_ymd_opt(year, month, day)
        .and_then(|d| d.and_hms_opt(hour, minute, second))
        .ok_or_else(|| format!("invalid date: {year}-{month}-{day} {hour}:{minute}:{second}"))?;
    let anchor_epoch_sec = naive.timestamp();
    Ok(GranularDate::new(anchor_epoch_sec, grain))
}

impl fmt::Display for GranularDate {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let dt = NaiveDateTime::from_timestamp_opt(self.anchor_epoch_sec, 0).unwrap_or(NaiveDateTime::MIN);
        match self.grain {
            Grain::Year => write!(f, "@{}", dt.year()),
            Grain::Month => write!(f, "@{:04}-{:02}", dt.year(), dt.month()),
            Grain::Day => write!(f, "@{:04}-{:02}-{:02}", dt.year(), dt.month(), dt.day()),
            Grain::Hour => write!(
                f,
                "@{:04}-{:02}-{:02}T{:02}",
                dt.year(),
                dt.month(),
                dt.day(),
                dt.hour()
            ),
            Grain::Minute => write!(
                f,
                "@{:04}-{:02}-{:02}T{:02}:{:02}",
                dt.year(),
                dt.month(),
                dt.day(),
                dt.hour(),
                dt.minute()
            ),
            Grain::Second => write!(
                f,
                "@{:04}-{:02}-{:02}T{:02}:{:02}:{:02}",
                dt.year(),
                dt.month(),
                dt.day(),
                dt.hour(),
                dt.minute(),
                dt.second()
            ),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn grain_ordering() {
        assert!(Grain::Year < Grain::Second);
        assert!(Grain::Day.at_least_as_fine_as(Grain::Month));
        assert!(!Grain::Month.at_least_as_fine_as(Grain::Day));
    }
}
