#[macro_use]
extern crate nom;

use std::fs::File;
use std::io::prelude::*;
use nom::{space, digit, line_ending};
use nom::types::CompleteStr;

fn main() -> Result<(), std::io::Error> {
    let mut file = File::open("input-day6")?;
    let mut buf = String::new();
    file.read_to_string(&mut buf)?;

    let mut lights = Grid::new(1000, 1000);
    let mut lights_part2 = Grid2::new(1000,1000);
    let instructions = buf.lines().filter_map(|ln| {
        let res = parse_instruction(CompleteStr(ln));
        if let Ok((_, i)) = res {
            Some(i)
        } else {
            println!("failed_parse? {:?}", res);
            None
        }
    });
    for instruction in instructions {
        match instruction {
            Instruction::TurnOn(tl, br) => lights.set_rect(tl, br, true),
            Instruction::TurnOff(tl, br) => lights.set_rect(tl, br, false),
            Instruction::Toggle(tl, br) => lights.flip_rect(tl, br),
        }

        match instruction {
            Instruction::TurnOn(tl, br) => lights_part2.adjust_rect(tl, br, 1),
            Instruction::TurnOff(tl, br) => lights_part2.adjust_rect(tl, br, -1),
            Instruction::Toggle(tl, br) => lights_part2.adjust_rect(tl, br, 2),
        }
    }

    println!("day6.1 {}", lights.lit_count()); // 542387 too low
    println!("day6.2 {}", lights_part2.sum_brightness()); 

    Ok(())
}

struct Grid {
    grid: Vec<bool>,
    width: usize,
}

#[derive(Debug, Eq, PartialEq, Clone, Copy)]
struct Coord(usize, usize);

#[derive(Debug, Eq, PartialEq)]
enum Instruction {
    TurnOn(Coord, Coord),
    TurnOff(Coord, Coord),
    Toggle(Coord, Coord),
}

named!(parse_command<CompleteStr, CompleteStr>,
       alt!(tag!("turn off") | tag!("turn on") | tag!("toggle")));

named!(parse_coord<CompleteStr, Coord>,
       do_parse!(
           coords: separated_pair!(call!(digit), char!(','), call!(digit)) >>
               (Coord(coords.0.parse().unwrap(), coords.1.parse().unwrap()))
       ));

named!(parse_instruction<CompleteStr, Instruction>,
       do_parse!(
           command: parse_command >>
           space >>
           top_left: parse_coord >>
           space >>
           tag!("through") >>
           space >>
           bot_right: parse_coord >>
           alt!(eof!() | line_ending) >>
           (match command.as_ref() {                   
               "turn on" => Instruction::TurnOn(top_left, bot_right),
               "turn off" => Instruction::TurnOff(top_left, bot_right),
               "toggle" => Instruction::Toggle(top_left, bot_right),
               _ => unreachable!(),
           })));

impl Grid {
    fn new(width: usize, height: usize) -> Self {
        Grid {
            grid: vec![false; width * height],
            width: width,
        }
    }

    fn flip_rect(&mut self, top_left: Coord, bot_right: Coord) {
        for x in top_left.0..=bot_right.0 {
            for y in top_left.1..=bot_right.1 {
                self.toggle_cell(x, y);
            }
        }
    }

    fn set_rect(&mut self, top_left: Coord, bot_right: Coord, on: bool) {
        for x in top_left.0..=bot_right.0 {
            for y in top_left.1..=bot_right.1 {
                self.set_cell(x, y, on);
            }
        }
    }

    fn lit_count(&self) -> usize {
        self.grid
            .iter()
            .map(|&state| if state { 1 } else { 0 })
            .sum()
    }

    fn toggle_cell(&mut self, x: usize, y: usize) {
        self.grid[x * self.width + y] ^= true;
    }

    fn set_cell(&mut self, x: usize, y: usize, on: bool) {
        self.grid[x * self.width + y] = on;
    }
}

struct Grid2 {
    grid: Vec<usize>,
    width: usize,
}

impl Grid2 {
    fn new(width: usize, height: usize) -> Grid2 {
        Grid2{
            grid: vec![0; width * height],
            width: width,
        }
    }
    
    fn adjust_rect(&mut self, top_left: Coord, bot_right: Coord, level: isize) {
        for x in top_left.0..=bot_right.0 {
            for y in top_left.1..=bot_right.1 {
                self.adjust_cell(x, y, level);
            }
        }
    }

    fn adjust_cell(&mut self, x: usize, y: usize, level: isize) {
        let idx = x * self.width + y;
        if level < 0 {
            self.grid[idx] = self.grid[idx].saturating_sub(-level as usize);
        } else {
            self.grid[idx] = self.grid[idx].saturating_add(level as usize);
        }
    }

    fn sum_brightness(&self) -> usize {
        self.grid.iter().sum()
    }
}

#[cfg(test)]
mod test {
    use super::*;
    
    #[test]
    fn test_parse_coords() {
        assert_eq!(parse_coord("128,129 ".into()), Ok((" ".into(), Coord(128,129))));
        assert_eq!(parse_coord("128,129".into()), Ok(("".into(), Coord(128,129))));
    }

    #[test]
    fn test_parse_instruction() {
        assert_eq!(parse_instruction("turn off 190,902 through 532,970".into()), Ok(("".into(), Instruction::TurnOff(Coord(190,902), Coord(532,970)))));
        assert_eq!(parse_instruction("toggle 936,774 through 937,775".into()), Ok(("".into(), Instruction::Toggle(Coord(936,774), Coord(937,775)))));
    }

    #[test]
    fn test_turnon() {
        let mut grid = Grid::new(15,15);
        grid.set_rect(Coord(0,0), Coord(9,9), true);
        assert_eq!(grid.lit_count(), 10*10);
    }

    #[test]
    fn test_grid2() {
        let mut grid = Grid2::new(10,10);
        grid.adjust_rect(Coord(0,0), Coord(0,0), 1);
        // grid.adjust_cell(0, 0, 1);
        assert_eq!(grid.sum_brightness(), 1);
        grid.adjust_rect(Coord(0,0), Coord(0,0), -1);
        assert_eq!(grid.sum_brightness(), 0);
        grid.adjust_rect(Coord(0,0), Coord(0,0), -1);
        assert_eq!(grid.sum_brightness(), 0);
        grid.adjust_rect(Coord(0,0), Coord(9,9), 2);
        assert_eq!(grid.sum_brightness(), 2 * 10 * 10);
    }
}
