use std::fs::File;
use std::io::prelude::*;

fn main() -> Result<(), std::io::Error> {
    let mut file = File::open("input-day5")?;
    let mut buf = String::new();
    file.read_to_string(&mut buf)?;

    let nice_count: usize = buf
        .lines()
        .filter_map(|ln| if is_nice(&ln) { Some(1) } else { None })
        .sum();
    println!("day5.1 {}", nice_count);
    let day2_nice: usize = buf
        .lines()
        .filter_map(|ln| if day2(&ln) { Some(1) } else { None })
        .sum();
    println!("day5.2 {}", day2_nice);
    Ok(())
}

fn is_nice(input: &str) -> bool {
    let did_i_stutter = stutters(&input); // aa bb cc dd ee
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

fn repeating_pair(input: &str) -> bool {
    let seed = input[0..1].to_string();
    let pairs: Vec<String> = input[1..]
        .chars()
        .scan(seed, |prev, c| {
            let this = format!("{}{}", prev, c).to_string();
            *prev = c.to_string();
            Some(this)
        })
        .collect();

    let count: usize = pairs
        .iter()
        .enumerate()
        .filter_map(|(i, x)| {
            let matches = match_index(x, &pairs);
            if matches.len() < 2 {
                return None;
            }

            matches
                .iter()
                .filter_map(|&match_i| {
                    if match_i == i || match_i == i + 1 || match_i == i.saturating_sub(1) {
                        None
                    } else {
                        Some(1)
                    }
                })
                .next()
        })
        .sum();

    count > 0
}

fn match_index(needle: &str, haystack: &[String]) -> Vec<usize> {
    haystack
        .iter()
        .enumerate()
        .filter_map(|(i, x)| if x == needle { Some(i) } else { None })
        .collect()
}

#[derive(Debug)]
enum Stutter {
    Double(char),
    None,
}

fn aba(input: &str) -> bool {
    let seed = input[0..2].to_string();
    let mut aba_iter = input[2..]
        .chars()
        .scan(seed, |prev, c| {
            let this = format!("{}{}", prev, c);
            *prev = this[1..3].to_string();
            let a = this.get(0..1);
            let x = this.get(2..3);
            if a == x {
                Some(Aba::Aba(c))
            } else {
                Some(Aba::None)
            }
        })
        .filter(|x| match x {
            Aba::Aba(_) => true,
            Aba::None => false,
        })
        .take(1);
    aba_iter.next().is_some()
}

#[derive(Debug)]
enum Aba {
    Aba(char),
    None,
}

fn day2(input: &str) -> bool {
    let sep_pattern = aba(input);
    let rep_pair = repeating_pair(input);
    sep_pattern && rep_pair
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

    #[test]
    fn test_aba() {
        assert!(aba("aba"));
        assert!(aba("aaa"));
        assert!(!aba("aab"));
        assert!(!aba("abba"));
    }

    #[test]
    fn test_day2() {
        assert!(day2("qjhvhtzxzqqjkmpb"));
        assert!(day2("xxyxx"));
        assert!(!day2("uurcxstgmygtbstg"));
        assert!(!day2("ieodomkazucvgmuy"));
    }

    #[test]
    fn test_repeating_pair() {
        assert!(repeating_pair("aaaa"));
        assert!(repeating_pair("aabcdefaa"));
        assert!(!repeating_pair("abc"));
        assert!(!repeating_pair("aaa"));
    }
}
