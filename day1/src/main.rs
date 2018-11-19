use std::fs::File;
use std::io::prelude::*;

fn main() -> Result<(), std::io::Error> {
    let mut file = File::open("input-day1")?;
    let mut buf = Vec::new();
    file.read_to_end(&mut buf)?;

    println!("day1.1 {}", part1(&buf));
    println!("day1.2 {:?}", part2(&buf)); // not 1770 too low
    Ok(())
}

fn part1(input: &[u8]) -> isize {
    input.iter().fold(0, |acc, c| match c {
        b'(' => acc + 1,
        b')' => acc - 1,
        _ => acc,
    })
}

fn part2(input: &[u8]) -> Option<usize> {
    let mut floor = 0;
    for (i, c) in input.iter().enumerate() {
        floor = match c {
            b'(' => floor + 1,
            b')' => floor - 1,
            _ => floor,
        };
        if floor == -1 {
            return Some(i + 1);
        }
    }
    None
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_part1() {
        assert_eq!(part1("(())".as_bytes()), 0);
        assert_eq!(part1("()()".as_bytes()), 0);
        assert_eq!(part1("(((".as_bytes()), 3);
        assert_eq!(part1("(()(()(".as_bytes()), 3);
        assert_eq!(part1("))(((((".as_bytes()), 3);
        assert_eq!(part1("())".as_bytes()), -1);
        assert_eq!(part1("))(".as_bytes()), -1);
        assert_eq!(part1(")))".as_bytes()), -3);
        assert_eq!(part1(")())())".as_bytes()), -3);
    }

    #[test]
    fn test_part2() {
        assert_eq!(part2(")".as_bytes()), Some(1));
        assert_eq!(part2("()())".as_bytes()), Some(5));
    }
}
