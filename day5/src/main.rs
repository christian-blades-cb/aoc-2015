use std::fs::File;
use std::io::prelude::*;
use std::io::BufReader;

fn main() -> Result<(), std::io::Error> {
    let file = File::open("input-day5")?;
    let buf = BufReader::new(file);

    let nice_count: usize = buf
        .lines()
        .filter_map(|ln| if is_nice(&ln.unwrap()) { Some(1) } else { None })
        .sum();
    println!("day5.1 {}", nice_count);

    Ok(())
}

fn is_nice(input: &str) -> bool {
    let did_i_stutter = stutters(&input);
    let vowels: usize = input
        .chars()
        .filter_map(|c| match c {
            'a' => Some(1),
            'e' => Some(1),
            'i' => Some(1),
            'o' => Some(1),
            'u' => Some(1),
            _ => None,
        })
        .sum();
    let bad_sets = vec!["ab", "cd", "pq", "xy"];
    let has_bad_set = bad_sets
        .iter()
        .filter(|&&s| input.contains(s))
        .next()
        .is_some();

    // println!("vowels: {}", vowels);
    // println!("stutters: {}", did_i_stutter);
    // println!("has_bad_set: {}", has_bad_set);

    !has_bad_set && vowels >= 3 && did_i_stutter
}

fn stutters(input: &str) -> bool {
    let mut stutters = input
        .chars()
        .scan(' ', |prev, c| {
            if *prev == c {
                Some(Stutter::Double(c))
            } else {
                *prev = c;
                Some(Stutter::None)
            }
        })
        .filter(|x| {
            if let Stutter::Double(_) = x {
                true
            } else {
                false
            }
        })
        .take(1);
    stutters.next().is_some()
}

#[derive(Debug)]
enum Stutter {
    Double(char),
    None,
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_is_nice() {
        assert!(is_nice("ugknbfddgicrmopn"));
        assert!(is_nice("aaa"));
        assert!(!is_nice("jchzalrnumimnmhp"));
        assert!(!is_nice("haegwjzuvuyypxyu"));
        assert!(!is_nice("dvszwmarrgswjxmb"));
    }

    #[test]
    fn test_stutters() {
        assert!(stutters("aa"));
    }
}
