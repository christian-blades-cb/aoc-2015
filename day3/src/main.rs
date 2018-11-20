extern crate tap;

use std::collections::HashMap;
use std::fs::File;
use std::io::prelude::*;
use std::ops::Add;
use tap::TapOps;

fn main() -> Result<(), std::io::Error> {
    let mut file = File::open("input-day3")?;
    let mut buf = Vec::new();
    file.read_to_end(&mut buf)?;

    let houses = visits(&buf);
    let multi_visits = multivisits(&houses);
    println!("day3.1 {}", multi_visits);

    let split_visits = part2_visits(&buf);
    println!("day3.2 {}", split_visits);

    Ok(())
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
struct Coords(isize, isize);

impl Add for Coords {
    type Output = Coords;

    fn add(self, other: Self) -> Self::Output {
        Coords(self.0 + other.0, self.1 + other.1)
    }
}

fn parse_move(mv: &u8) -> Coords {
    match mv {
        b'^' => Coords(0, 1),
        b'v' => Coords(0, -1),
        b'<' => Coords(-1, 0),
        b'>' => Coords(1, 0),
        _ => Coords(0, 0),
    }
}

type SantaVisits = HashMap<Coords, usize>;

fn visits<'a>(moves: impl IntoIterator<Item = &'a u8>) -> SantaVisits {
    moves
        .into_iter()
        .map(|c| parse_move(c))
        .fold(
            (
                Coords(0, 0),
                HashMap::new().tap(|hm| hm.insert(Coords(0, 0), 1usize)),
            ),
            |(santa, mut houses), mv| {
                let visit = santa + mv;
                houses.entry(visit).and_modify(|e| *e += 1).or_insert(1);
                (visit, houses)
            },
        )
        .1
}

fn multivisits(visits: &SantaVisits) -> usize {
    visits.iter().map(|(_, &v)| if v > 0 { 1 } else { 0 }).sum()
}

fn part2_visits(input: &[u8]) -> usize {
    let mut santa_houses = visits(input.iter().step_by(2));
    let robo_houses = visits(input.iter().skip(1).step_by(2));
    santa_houses.extend(robo_houses);
    multivisits(&santa_houses)
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_part1() {
        assert_eq!(multivisits(&visits(">".as_bytes())), 2);
        assert_eq!(multivisits(&visits("^>v<".as_bytes())), 4);
        assert_eq!(multivisits(&visits("^v^v^v^v^v".as_bytes())), 2);
    }

    #[test]
    fn test_part2() {
        assert_eq!(part2_visits("^v".as_bytes()), 3);
        assert_eq!(part2_visits("^>v<".as_bytes()), 3);
        assert_eq!(part2_visits("^v^v^v^v^v".as_bytes()), 11);
    }
}
