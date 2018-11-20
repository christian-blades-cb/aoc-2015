use std::fs::File;
use std::io::prelude::*;
use std::io::BufReader;

fn main() -> Result<(), std::io::Error> {
    let file = File::open("input-day2")?;
    let buf = BufReader::new(file);
    let mut total_area = 0;
    let mut total_ribbon = 0;
    for ln in buf.lines() {
        let line = ln?;
        let dims = parse_dims(&line);
        let area = paper_area(&dims);
        let ribbon = ribbon_len(&dims);
        total_area += area;
        total_ribbon += ribbon;
    }
    println!("day2.1 {}", total_area);
    println!("day2.2 {}", total_ribbon);
    Ok(())
}

struct Dimensions(usize, usize, usize);

fn parse_dims(line: &str) -> Dimensions {
    let parts: Vec<&str> = line.split('x').take(3).collect();
    let l: usize = parts[0].parse().unwrap();
    let w: usize = parts[1].parse().unwrap();
    let h: usize = parts[2].parse().unwrap();
    Dimensions(l, w, h)
}

fn paper_area(dims: &Dimensions) -> usize {
    let Dimensions(l, w, h) = dims;
    let sides = vec![l * w, l * h, w * h];
    let min = sides.iter().min().unwrap_or(&0);
    sides.iter().fold(*min, |acc, s| acc + (s * 2))
}

fn ribbon_len(dims: &Dimensions) -> usize {
    let Dimensions(l, w, h) = dims;
    let faces = vec![(l, w), (l, h), (w, h)];
    let min_face = faces
        .iter()
        .min_by(|(&x1, &y1), (&x2, &y2)| (2 * x1 + 2 * y1).cmp(&(2 * x2 + 2 * y2)))
        .unwrap();
    let perimeter = min_face.0 * 2 + min_face.1 * 2;
    let volume = l * w * h;
    perimeter + volume
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_part1() {
        assert_eq!(paper_area(&parse_dims("2x3x4")), 58);
        assert_eq!(paper_area(&parse_dims("1x1x10")), 43);
    }

    #[test]
    fn test_part2() {
        assert_eq!(ribbon_len(&parse_dims("2x3x4")), 34);
        assert_eq!(ribbon_len(&parse_dims("1x1x10")), 14);
    }
}
