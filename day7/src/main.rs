#[macro_use]
extern crate log;
extern crate env_logger;
#[macro_use]
extern crate nom;
extern crate dot;

use nom::types::CompleteStr;
use nom::{alpha, digit, space};
use std::borrow::Cow;
use std::collections::HashMap;
use std::fs::File;
use std::io::prelude::*;

fn main() -> Result<(), std::io::Error> {
    env_logger::init();

    let mut file = File::open("input-day7")?;
    let mut buf = String::new();
    file.read_to_string(&mut buf)?;

    let mut board = Board::new();
    part1(&buf, &mut board);

    {
        println!("outputting board.dot");
        let mut outfile = File::create("board.dot")?;
        board.render_to(&mut outfile);
    }

    println!("solving");
    let res_p1 = get_signal(&board, "a");
    println!("day7.1 {:?}", res_p1);

    Ok(())
}

fn part1(buf: &str, board: &mut Board) {
    let instructions = buf.lines().filter_map(|ln| {
        let inst = parse_wiring(ln.into());
        if let Ok((_, (name, wiring))) = inst {
            Some((name, wiring))
        } else {
            None
        }
    });
    for (name, wiring) in instructions {
        board.insert(name.as_ref().into(), Wire(wiring));
    }
}

struct Board(WireBoard);
type WireBoard = HashMap<Terminal, Wire>;
type Signal = u16;
type Terminal = String;

impl Board {
    fn new() -> Self {
        Board(HashMap::new())
    }

    fn get(&self, key: &str) -> Option<&Wire> {
        self.0.get(key)
    }

    // fn get(&self, key: &Terminal) -> Option<&Wire> {
    //     self.0.get(key)
    // }

    fn insert(&mut self, k: Terminal, v: Wire) -> Option<Wire> {
        self.0.insert(k, v)
    }

    fn iter(&self) -> std::collections::hash_map::Iter<Terminal, Wire> {
        self.0.iter()
    }

    fn len(&self) -> usize {
        self.0.len()
    }

    fn render_to<W: Write>(&self, output: &mut W) {
        dot::render(self, output).unwrap()
    }
}

type Nd = (Terminal, Wire);
type Ed = (Terminal, Terminal);

impl<'a> dot::Labeller<'a, Nd, Ed> for Board {
    fn graph_id(&'a self) -> dot::Id<'a> {
        dot::Id::new("Board").unwrap()
    }

    fn node_id(&'a self, n: &Nd) -> dot::Id<'a> {
        dot::Id::new(format!("N{}", n.0)).unwrap()
    }

    fn node_label<'b>(&'b self, n: &Nd) -> dot::LabelText<'b> {
        let (name, Wire(val)) = n;
        dot::LabelText::LabelStr(
            match val {
                Wiring::Wire(ref other) => format!("{:?} -> {}", other, name),
                Wiring::Not(ref other) => format!("{:?} -> {}", other, name),
                Wiring::And(ref lhs, ref rhs) => format!("{:?} AND {:?} -> {}", lhs, rhs, name),
                Wiring::Or(ref lhs, ref rhs) => format!("{:?} OR {:?} -> {}", lhs, rhs, name),
                Wiring::Lshift(ref other, shift_by) => {
                    format!("{:?} LSHIFT {} -> {}", other, shift_by, name)
                }
                Wiring::Rshift(ref other, shift_by) => {
                    format!("{:?} RSHIFT {} -> {}", other, shift_by, name)
                }
            }
            .into(),
        )
    }
}

impl<'a> dot::GraphWalk<'a, Nd, Ed> for Board {
    fn nodes(&self) -> dot::Nodes<'a, Nd> {
        let nodes: Vec<Nd> = self
            .iter()
            .map(|(k, v)| (k.to_string(), v.clone()))
            .collect();
        Cow::Owned(nodes)
    }

    fn edges(&'a self) -> dot::Edges<'a, Ed> {
        let edges: Vec<Ed> = self
            .iter()
            .filter_map(|(k, Wire(v))| match v {
                Wiring::Wire(SignalRef::Wire(ref w)) => Some(vec![(k.to_string(), w.to_string())]),
                Wiring::Wire(SignalRef::Signal(_)) => None,
                Wiring::Not(SignalRef::Wire(ref w)) => Some(vec![(k.to_string(), w.to_string())]),
                Wiring::Not(SignalRef::Signal(_)) => None,
                Wiring::And(SignalRef::Signal(_), SignalRef::Signal(_)) => None,
                Wiring::And(SignalRef::Signal(_), SignalRef::Wire(ref w)) => {
                    Some(vec![(k.to_string(), w.to_string())])
                }
                Wiring::And(SignalRef::Wire(ref w), SignalRef::Signal(_)) => {
                    Some(vec![(k.to_string(), w.to_string())])
                }
                Wiring::And(SignalRef::Wire(ref lhs), SignalRef::Wire(ref rhs)) => Some(vec![
                    (k.to_string(), lhs.to_string()),
                    (k.to_string(), rhs.to_string()),
                ]),
                Wiring::Or(SignalRef::Signal(_), SignalRef::Signal(_)) => None,
                Wiring::Or(SignalRef::Signal(_), SignalRef::Wire(ref w)) => {
                    Some(vec![(k.to_string(), w.to_string())])
                }
                Wiring::Or(SignalRef::Wire(ref w), SignalRef::Signal(_)) => {
                    Some(vec![(k.to_string(), w.to_string())])
                }
                Wiring::Or(SignalRef::Wire(ref lhs), SignalRef::Wire(ref rhs)) => Some(vec![
                    (k.to_string(), lhs.to_string()),
                    (k.to_string(), rhs.to_string()),
                ]),
                Wiring::Lshift(SignalRef::Signal(_), _) => None,
                Wiring::Lshift(SignalRef::Wire(ref w), _) => {
                    Some(vec![(k.to_string(), w.to_string())])
                }
                Wiring::Rshift(SignalRef::Signal(_), _) => None,
                Wiring::Rshift(SignalRef::Wire(ref w), _) => {
                    Some(vec![(k.to_string(), w.to_string())])
                }
            })
            .flatten()
            .collect();
        Cow::Owned(edges)
    }

    fn source(&self, e: &Ed) -> Nd {
        (e.0.to_string(), self.get(&e.0).unwrap().clone())
    }

    fn target(&self, e: &Ed) -> Nd {
        (e.1.to_string(), self.get(&e.1).unwrap().clone())
    }
}

#[derive(Debug, Eq, PartialEq, Clone)]
enum SignalRef {
    Wire(Terminal),
    Signal(Signal),
}

impl From<&str> for SignalRef {
    fn from(x: &str) -> SignalRef {
        SignalRef::Wire(x.into())
    }
}

impl From<Signal> for SignalRef {
    fn from(x: Signal) -> SignalRef {
        SignalRef::Signal(x)
    }
}

impl SignalRef {
    fn signal(&self, hm: &Board) -> Option<Signal> {
        debug!("getting signal {:?}", self);
        match self {
            SignalRef::Wire(ref other) => get_signal(hm, other),
            SignalRef::Signal(val) => Some(*val),
        }
    }
}

#[derive(Debug, Eq, PartialEq, Clone)]
enum Wiring {
    Wire(SignalRef),
    Not(SignalRef),
    And(SignalRef, SignalRef),
    Or(SignalRef, SignalRef),
    Lshift(SignalRef, Signal),
    Rshift(SignalRef, Signal),
}

#[derive(Clone)]
struct Wire(Wiring);

impl Wire {
    fn signal(&self, hm: &Board) -> Option<Signal> {
        debug!("wiredef: {:?}", self.0);
        match self.0 {
            Wiring::Wire(ref other) => other.signal(hm),
            Wiring::Not(ref other) => other.signal(hm).map(|val| !val),
            Wiring::Lshift(ref other, shift_by) => other.signal(hm).map(|x| x << shift_by),
            Wiring::Rshift(ref other, shift_by) => other.signal(hm).map(|x| x >> shift_by),
            Wiring::And(ref lhs, ref rhs) => {
                if let (Some(lval), Some(rval)) = (lhs.signal(hm), rhs.signal(hm)) {
                    Some(lval & rval)
                } else {
                    None
                }
            }
            Wiring::Or(ref lhs, ref rhs) => {
                if let (Some(lval), Some(rval)) = (lhs.signal(hm), rhs.signal(hm)) {
                    Some(lval | rval)
                } else {
                    None
                }
            }
        }
    }
}

fn get_signal(hm: &Board, key: &str) -> Option<Signal> {
    match hm.get(key).map(|sw| sw.signal(hm)) {
        Some(Some(x)) => Some(x),
        _ => None,
    }
}

named!(parse_not<CompleteStr, (CompleteStr, Wiring)>,
       do_parse!(
           tag!("NOT") >>
               space >>
               other: alpha >>
               space >>
               tag!("->") >>
               space >>
               name: alpha >>
               ((name, Wiring::Not(other.as_ref().into())))));

named!(parse_shift<CompleteStr, (CompleteStr, Wiring)>,
       do_parse!(
           lhs: alpha >>
               space >>
               oper: alt!(tag!("LSHIFT") | tag!("RSHIFT")) >>
               space >>
               shift_by: digit >>
               space >>
               tag!("->") >>
               space >>
               name: alpha >>
               ((name, match oper.as_ref() {
                   "LSHIFT" => Wiring::Lshift(lhs.as_ref().into(), shift_by.parse().unwrap()),
                   "RSHIFT" => Wiring::Rshift(lhs.as_ref().into(), shift_by.parse().unwrap()),
                   _ => unreachable!(),
               }))));

named!(parse_signalref_signal<CompleteStr, SignalRef>,
       do_parse!(
           signal: digit >>
               (signal.parse::<Signal>().unwrap().into())));

named!(parse_signalref_wire<CompleteStr, SignalRef>,
       do_parse!(
           wire: alpha >>
               (wire.as_ref().into())));

named!(parse_signalref<CompleteStr, SignalRef>,
       alt!(parse_signalref_signal|parse_signalref_wire));

named!(parse_bool<CompleteStr, (CompleteStr, Wiring)>,
       do_parse!(
           lhs: parse_signalref >>
               space >>
               oper: alt!(tag!("AND") | tag!("OR")) >>
               space >>
               rhs: parse_signalref >>
               space >>
               tag!("->") >>
               space >>
               name: alpha >>
               ((name, match oper.as_ref() {
                   "AND" => Wiring::And(lhs, rhs),
                   "OR" => Wiring::Or(lhs, rhs),
                   _ => unreachable!(),
               }))));

named!(parse_wire<CompleteStr, (CompleteStr, Wiring)>,
       do_parse!(
           wire: parse_signalref >>
               space >>
               tag!("->") >>
               space >>
               name: alpha >>
               ((name, Wiring::Wire(wire)))));

named!(parse_wiring<CompleteStr, (CompleteStr, Wiring)>,
       alt!(parse_not | parse_shift | parse_bool | parse_wire));

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_part1() {
        let buf = "123 -> x
456 -> y
x AND y -> d
x OR y -> e
x LSHIFT 2 -> f
y RSHIFT 2 -> g
NOT x -> h
NOT y -> i";
        let mut board = Board::new();
        part1(buf, &mut board);
        assert_eq!(get_signal(&board, "d"), Some(72));
        assert_eq!(get_signal(&board, "e"), Some(507));
        assert_eq!(get_signal(&board, "f"), Some(492));
        assert_eq!(get_signal(&board, "g"), Some(114));
        assert_eq!(get_signal(&board, "h"), Some(65412));
        assert_eq!(get_signal(&board, "i"), Some(65079));
        assert_eq!(get_signal(&board, "x"), Some(123));
        assert_eq!(get_signal(&board, "y"), Some(456));
    }

    #[test]
    fn test_parse_wiring() {
        assert_eq!(
            parse_wiring("x AND y -> d".into()),
            Ok(("".into(), ("d".into(), Wiring::And("x".into(), "y".into()))))
        );
        assert_eq!(
            parse_wiring("ly -> x".into()),
            Ok(("".into(), ("x".into(), Wiring::Wire("ly".into()))))
        );
        assert_eq!(
            parse_wiring("123 -> xy".into()),
            Ok(("".into(), ("xy".into(), Wiring::Wire(123.into()))))
        );
    }

    #[test]
    fn test_parse_bool() {
        assert_eq!(
            parse_bool("ib AND ic -> ie".into()),
            Ok((
                "".into(),
                ("ie".into(), Wiring::And("ib".into(), "ic".into()))
            ))
        );
        assert_eq!(
            parse_bool("fq OR fr -> fs".into()),
            Ok((
                "".into(),
                ("fs".into(), Wiring::Or("fq".into(), "fr".into()))
            ))
        );
        assert_eq!(
            parse_bool("1 AND lu -> lv".into()),
            Ok(("".into(), ("lv".into(), Wiring::And(1.into(), "lu".into()))))
        );
    }

    #[test]
    fn test_parse_shift() {
        assert_eq!(
            parse_shift("as RSHIFT 3 -> au".into()),
            Ok(("".into(), ("au".into(), Wiring::Rshift("as".into(), 3))))
        );
        assert_eq!(
            parse_shift("hb LSHIFT 1 -> hv".into()),
            Ok(("".into(), ("hv".into(), Wiring::Lshift("hb".into(), 1))))
        );
    }

    #[test]
    fn test_parse_not() {
        assert_eq!(
            parse_not("NOT l -> m".into()),
            Ok(("".into(), ("m".into(), Wiring::Not("l".into())))),
        );
    }

    #[test]
    fn test_signal() {
        let mut hm = Board::new();
        hm.insert("x".into(), Wire(Wiring::Wire(42.into())));
        let wire = hm.get("x").unwrap();
        assert_eq!(wire.signal(&hm), Some(42));
    }

    #[test]
    fn test_not() {
        let mut hm = Board::new();
        hm.insert("x".into(), Wire(Wiring::Not("y".into())));
        hm.insert("y".into(), Wire(Wiring::Wire(42.into())));
        let wire = hm.get("x").unwrap();
        assert_eq!(wire.signal(&hm), Some(!42u16));
    }

    #[test]
    fn test_lshift() {
        let mut hm = Board::new();
        hm.insert("x".into(), Wire(Wiring::Lshift("y".into(), 8)));
        hm.insert("y".into(), Wire(Wiring::Wire(42.into())));
        let wire = hm.get("x").unwrap();
        assert_eq!(wire.signal(&hm), Some(42u16 << 8));
    }

    #[test]
    fn test_rshift() {
        let mut hm = Board::new();
        hm.insert("x".into(), Wire(Wiring::Rshift("y".into(), 8)));
        hm.insert("y".into(), Wire(Wiring::Wire((42 << 8).into())));
        let wire = hm.get("x").unwrap();
        assert_eq!(wire.signal(&hm), Some(42u16));
    }

    #[test]
    fn test_and() {
        let mut hm = Board::new();
        hm.insert("x".into(), Wire(Wiring::And("y".into(), "z".into())));
        hm.insert("y".into(), Wire(Wiring::Wire(42.into())));
        hm.insert("z".into(), Wire(Wiring::Wire(45.into())));
        let wire = hm.get("x").unwrap();
        assert_eq!(wire.signal(&hm), Some(42 & 45));
    }

    #[test]
    fn test_or() {
        let mut hm = Board::new();
        hm.insert("x".into(), Wire(Wiring::Or("y".into(), "z".into())));
        hm.insert("y".into(), Wire(Wiring::Wire(42.into())));
        hm.insert("z".into(), Wire(Wiring::Wire(45.into())));
        let wire = hm.get("x").unwrap();
        assert_eq!(wire.signal(&hm), Some(42 | 45));
    }

    #[test]
    fn test_wire() {
        let mut hm = Board::new();
        hm.insert("x".into(), Wire(Wiring::Wire("y".into())));
        hm.insert("y".into(), Wire(Wiring::Wire(42.into())));
        let wire = hm.get("x").unwrap();
        assert_eq!(wire.signal(&hm), Some(42));
    }
}
