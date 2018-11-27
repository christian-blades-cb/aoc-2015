extern crate tap;
#[macro_use]
extern crate log;
extern crate env_logger;
#[macro_use]
extern crate nom;
extern crate dot;
extern crate topological_sort;

use nom::types::CompleteStr;
use nom::{alpha, digit, space};
use std::borrow::Cow;
use std::collections::HashMap;
use std::fs::File;
use std::io::prelude::*;
use tap::TapOps;
use topological_sort::TopologicalSort;

fn main() -> Result<(), std::io::Error> {
    env_logger::init();

    let mut file = File::open("input-day7")?;
    let mut buf = String::new();
    file.read_to_string(&mut buf)?;

    let mut board = Board::new();
    board.populate(&buf);

    // change to true to generate a dot file for graphviz
    if false {
        println!("outputting board.dot");
        let mut outfile = File::create("board.dot")?;
        board.render_to(&mut outfile);
    }

    let mut cached = Cache::new(&board);
    let res_p1 = cached.solve("a");
    println!("day7.1 {:?}", res_p1);

    board
        .0
        .entry("b".into())
        .and_modify(|e| *e = Wire(Wiring::Wire(SignalRef::Signal(res_p1.unwrap()))));
    let mut cached = Cache::new(&board);
    let res_p2 = cached.solve("a");
    println!("day7.2 {:?}", res_p2);

    Ok(())
}

struct Cache<'a> {
    inner: &'a Board,
    cache: HashMap<Terminal, Signal>,
}

impl<'a> Cache<'a> {
    fn new(board: &'a Board) -> Cache<'a> {
        Cache {
            inner: board,
            cache: HashMap::new(),
        }
    }

    fn solve(&mut self, key: &str) -> Option<Signal> {
        let res = self.cache.get(key).map(|&v| v);
        if let Some(s) = res {
            return Some(s);
        }

        // build topology
        let mut topology: TopologicalSort<&str> =
            self.inner
                .iter()
                .fold(
                    TopologicalSort::new(),
                    |mut acc, (this, Wire(wiring))| match wiring {
                        Wiring::Wire(SignalRef::Signal(_)) => acc,
                        Wiring::Wire(SignalRef::Wire(w)) => {
                            acc.tap(|a| a.add_dependency(w.as_ref(), this.as_ref()))
                        }
                        Wiring::Not(SignalRef::Signal(_)) => acc,
                        Wiring::Not(SignalRef::Wire(w)) => {
                            acc.tap(|a| a.add_dependency(w.as_ref(), this.as_ref()))
                        }
                        Wiring::Lshift(SignalRef::Wire(w), _) => {
                            acc.tap(|a| a.add_dependency(w.as_ref(), this.as_ref()))
                        }
                        Wiring::Lshift(SignalRef::Signal(_), _) => acc,
                        Wiring::Rshift(SignalRef::Wire(w), _) => {
                            acc.tap(|a| a.add_dependency(w.as_ref(), this.as_ref()))
                        }
                        Wiring::Rshift(SignalRef::Signal(_), _) => acc,
                        Wiring::And(lhs, rhs) => {
                            if let SignalRef::Wire(w) = lhs {
                                acc.add_dependency(w.as_ref(), this.as_ref());
                            }
                            if let SignalRef::Wire(w) = rhs {
                                acc.add_dependency(w.as_ref(), this.as_ref());
                            }
                            acc
                        }
                        Wiring::Or(lhs, rhs) => {
                            if let SignalRef::Wire(w) = lhs {
                                acc.add_dependency(w.as_ref(), this.as_ref());
                            }
                            if let SignalRef::Wire(w) = rhs {
                                acc.add_dependency(w.as_ref(), this.as_ref());
                            }
                            acc
                        }
                    },
                );

        // * pop each set of nodes with no dependencies
        // * solve nodes out of cache
        // * cache node
        // * repeat until we've exhausted all of the nodes
        loop {
            let to_solve = topology.pop_all();
            if to_solve.len() == 0 {
                break;
            }
            for wire in to_solve {
                info!("solving for {}", wire);
                let Wire(wiring) = self.inner.get(wire).unwrap();
                match wiring {
                    Wiring::Wire(SignalRef::Signal(v)) => {
                        self.cache.insert(wire.into(), *v);
                    }
                    Wiring::Wire(SignalRef::Wire(w)) => {
                        let v = self.cache.get(w).unwrap();
                        self.cache.insert(wire.into(), *v);
                    }
                    Wiring::Not(SignalRef::Signal(v)) => {
                        self.cache.insert(wire.into(), !v);
                    }
                    Wiring::Not(SignalRef::Wire(w)) => {
                        let v = self.cache.get(w).unwrap();
                        self.cache.insert(wire.into(), !v);
                    }
                    Wiring::Lshift(SignalRef::Signal(v), shift_by) => {
                        self.cache.insert(wire.into(), v << shift_by);
                    }
                    Wiring::Lshift(SignalRef::Wire(w), shift_by) => {
                        let v = self.cache.get(w).unwrap();
                        self.cache.insert(wire.into(), v << shift_by);
                    }
                    Wiring::Rshift(SignalRef::Signal(v), shift_by) => {
                        self.cache.insert(wire.into(), v >> shift_by);
                    }
                    Wiring::Rshift(SignalRef::Wire(w), shift_by) => {
                        let v = self.cache.get(w).unwrap();
                        self.cache.insert(wire.into(), v >> shift_by);
                    }
                    Wiring::And(lhs, rhs) => {
                        let l_v = match lhs {
                            SignalRef::Wire(w) => self.cache.get(w).unwrap(),
                            SignalRef::Signal(v) => v,
                        };
                        let r_v = match rhs {
                            SignalRef::Wire(w) => self.cache.get(w).unwrap(),
                            SignalRef::Signal(v) => v,
                        };
                        self.cache.insert(wire.into(), l_v & r_v);
                    }
                    Wiring::Or(lhs, rhs) => {
                        let l_v = match lhs {
                            SignalRef::Wire(w) => self.cache.get(w).unwrap(),
                            SignalRef::Signal(v) => v,
                        };
                        let r_v = match rhs {
                            SignalRef::Wire(w) => self.cache.get(w).unwrap(),
                            SignalRef::Signal(v) => v,
                        };
                        self.cache.insert(wire.into(), l_v | r_v);
                    }
                }
            }
        }

        self.cache.get(key).map(|&k| k)
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

    fn populate(&mut self, buf: &str) {
        let instructions = buf.lines().filter_map(|ln| {
            let inst = parse_wiring(ln.into());
            if let Ok((_, (name, wiring))) = inst {
                Some((name, wiring))
            } else {
                None
            }
        });
        for (name, wiring) in instructions {
            self.0.insert(name.as_ref().into(), Wire(wiring));
        }
    }

    fn get(&self, key: &str) -> Option<&Wire> {
        self.0.get(key)
    }

    fn iter(&self) -> std::collections::hash_map::Iter<Terminal, Wire> {
        self.0.iter()
    }

    // writes a graphviz dot file of the wiring-board
    fn render_to<W: Write>(&self, output: &mut W) {
        dot::render(self, output).unwrap()
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

////////////////////////
// parser-combinators //
////////////////////////

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
    fn test_p1_realistic() {
        let buf = "o AND q -> r
p -> q
b OR n -> o
b AND n -> p
k AND m -> n
l -> m
d OR j -> k
d AND j -> l
b RSHIFT 2 -> d
g AND i -> j
h -> i
e AND f -> h
e OR f -> g
b RSHIFT 3 -> e
b RSHIFT 5 -> f
19138 -> b
";
        let mut board = Board::new();
        board.populate(buf);
        let mut cached = Cache::new(&board);
        let b = 19138;
        assert_eq!(cached.solve("b"), Some(b));
        let f = b >> 5;
        assert_eq!(cached.solve("f"), Some(f));
        let e = b >> 3;
        assert_eq!(cached.solve("e"), Some(e));
        let g = e | f;
        assert_eq!(cached.solve("g"), Some(g));
        let h = e & f;
        assert_eq!(cached.solve("h"), Some(h));
        let i = h;
        assert_eq!(cached.solve("i"), Some(i));
        let j = g & i;
        assert_eq!(cached.solve("j"), Some(j));
        let d = b >> 2;
        assert_eq!(cached.solve("d"), Some(d));
        let l = d & j;
        assert_eq!(cached.solve("l"), Some(l));
        let k = d | j;
        assert_eq!(cached.solve("k"), Some(k));
        let m = l;
        assert_eq!(cached.solve("m"), Some(m));
        let n = k & m;
        assert_eq!(cached.solve("n"), Some(n));
        let p = b & n;
        assert_eq!(cached.solve("p"), Some(p));
        let o = b | n;
        assert_eq!(cached.solve("o"), Some(o));
        let q = p;
        assert_eq!(cached.solve("q"), Some(q));
    }

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
        board.populate(buf);
        let mut cached = Cache::new(&board);
        assert_eq!(cached.solve("d"), Some(72));
        assert_eq!(cached.solve("e"), Some(507));
        assert_eq!(cached.solve("f"), Some(492));
        assert_eq!(cached.solve("g"), Some(114));
        assert_eq!(cached.solve("h"), Some(65412));
        assert_eq!(cached.solve("i"), Some(65079));
        assert_eq!(cached.solve("x"), Some(123));
        assert_eq!(cached.solve("y"), Some(456));
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
}

/////////////////////////////////////////////////////////////////////////
// All this nonsense is for generating a graphviz .dot file for visual //
// debugging                                                           //
/////////////////////////////////////////////////////////////////////////

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
