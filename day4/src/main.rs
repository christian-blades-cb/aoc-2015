extern crate md5;

use std::fs::File;
use std::io::prelude::*;

fn main() -> Result<(), std::io::Error> {
    let mut file = File::open("input-day4")?;
    let mut key = String::new();
    file.read_to_string(&mut key)?;

    println!("day4.1 {:?}", five_zeros(&key));
    println!("day4.2 {:?}", six_zeros(&key));

    Ok(())
}

fn five_zeros(key: &str) -> Option<usize> {
    for i in 0..std::usize::MAX {
        let val = format!("{}{}", key, i);
        let digest = md5::compute(val.as_bytes());
        let hex = format!("{:x}", digest);
        if hex.starts_with("00000") {
            return Some(i);
        }
    }
    None
}

fn six_zeros(key: &str) -> Option<usize> {
    for i in 0..std::usize::MAX {
        let val = format!("{}{}", key, i);
        let digest = md5::compute(val.as_bytes());
        let hex = format!("{:x}", digest);
        if hex.starts_with("000000") {
            return Some(i);
        }
    }
    None
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_part1() {
        assert_eq!(five_zeros("abcdef"), Some(609043));
        assert_eq!(five_zeros("pqrstuv"), Some(1048970));
    }
}
