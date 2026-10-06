// MonoTree's three traversals for the tree sweep (gibbon_benchmark.py
// --tree-sweep), ported from BintreeBench (ECOOP 2017) and aligned with
// tree_sweep/programs/*/MonoTree*.hs: 64-bit leaves, mkTree d 0 gives every
// one of the 2^d leaves d(d+1)/2, and every subtree is built separately.
//
//   treebench <build|add1|sum> --size-param DEPTH --iterate N
//
// prints each iteration's time in Gibbon's format, then the sum of the
// result (of the last tree built, of add1's output, or the sum itself).
use std::env;
use std::hint::black_box;
use std::time::Instant;

enum Tree {
    Leaf(i64),
    Node(Box<Tree>, Box<Tree>),
}

fn mk_tree(d: i64, acc: i64) -> Box<Tree> {
    if d == 0 {
        Box::new(Tree::Leaf(acc))
    } else {
        Box::new(Tree::Node(mk_tree(d - 1, d + acc), mk_tree(d - 1, d + acc)))
    }
}

fn add1_tree(t: &Tree) -> Box<Tree> {
    match t {
        Tree::Leaf(x) => Box::new(Tree::Leaf(x + 1)),
        Tree::Node(l, r) => Box::new(Tree::Node(add1_tree(l), add1_tree(r))),
    }
}

fn sum_tree(t: &Tree) -> i64 {
    match t {
        Tree::Leaf(x) => *x,
        Tree::Node(l, r) => sum_tree(l) + sum_tree(r),
    }
}

fn arg(args: &[String], flag: &str) -> i64 {
    let i = args.iter().position(|a| a == flag).expect(flag);
    args[i + 1].parse().expect(flag)
}

fn main() {
    let args: Vec<String> = env::args().collect();
    let pass = args[1].as_str();
    let depth = arg(&args, "--size-param");
    let iters = arg(&args, "--iterate").max(1);
    let mut times = Vec::with_capacity(iters as usize);
    let answer;
    match pass {
        "build" => {
            println!("Running pass buildTree (build): ");
            let mut last = None;
            for _ in 0..iters {
                drop(last.take()); // freed outside the timed region
                let t0 = Instant::now();
                let t = mk_tree(black_box(depth), 0);
                times.push(t0.elapsed().as_secs_f64());
                last = Some(black_box(t));
            }
            answer = sum_tree(last.as_ref().unwrap());
        }
        "add1" => {
            let tree = mk_tree(depth, 0);
            println!("Running pass add1Tree (map): ");
            let mut last = None;
            for _ in 0..iters {
                drop(last.take());
                let t0 = Instant::now();
                let t = add1_tree(black_box(&tree));
                times.push(t0.elapsed().as_secs_f64());
                last = Some(black_box(t));
            }
            answer = sum_tree(last.as_ref().unwrap());
        }
        "sum" => {
            let tree = mk_tree(depth, 0);
            println!("Running pass sumTree (fold): ");
            let mut s = 0;
            for _ in 0..iters {
                let t0 = Instant::now();
                s = black_box(sum_tree(black_box(&tree)));
                times.push(t0.elapsed().as_secs_f64());
            }
            answer = s;
        }
        _ => panic!("pass must be build, add1 or sum"),
    }
    let shown: Vec<String> = times.iter().map(|t| format!("{:.9}", t)).collect();
    println!("ITER TIMES: [{}]", shown.join(", "));
    println!("End");
    println!("{}", answer);
}
