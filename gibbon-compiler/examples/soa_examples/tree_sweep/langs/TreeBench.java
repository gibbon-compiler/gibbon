// MonoTree's three traversals for the tree sweep (gibbon_benchmark.py
// --tree-sweep), ported from BintreeBench (ECOOP 2017, treebench.java) and
// aligned with tree_sweep/programs/*/MonoTree*.hs: 64-bit leaves, mkTree d 0
// gives every one of the 2^d leaves d(d+1)/2, and every subtree is built
// separately.
//
//   java TreeBench <build|add1|sum> --size-param DEPTH --iterate N
//
// prints each iteration's time in Gibbon's format, then the sum of the result.
import java.util.ArrayList;
import java.util.List;

public final class TreeBench {
    abstract static class Tree {
        abstract Tree add1();
        abstract long sum();
    }

    static final class Leaf extends Tree {
        final long v;
        Leaf(long v) { this.v = v; }
        Tree add1() { return new Leaf(v + 1); }
        long sum() { return v; }
    }

    static final class Node extends Tree {
        final Tree l, r;
        Node(Tree l, Tree r) { this.l = l; this.r = r; }
        Tree add1() { return new Node(l.add1(), r.add1()); }
        long sum() { return l.sum() + r.sum(); }
    }

    static Tree mkTree(long d, long acc) {
        if (d == 0) return new Leaf(acc);
        return new Node(mkTree(d - 1, d + acc), mkTree(d - 1, d + acc));
    }

    static long arg(String[] args, String flag) {
        for (int i = 0; i + 1 < args.length; i++)
            if (args[i].equals(flag)) return Long.parseLong(args[i + 1]);
        throw new IllegalArgumentException("missing " + flag);
    }

    // Read once per iteration, so the JIT cannot treat the input as constant.
    static volatile long depthBox;
    static volatile Tree treeBox;

    public static void main(String[] args) {
        String pass = args[0];
        long depth = arg(args, "--size-param");
        int iters = (int) Math.max(1, arg(args, "--iterate"));
        List<Double> times = new ArrayList<>();
        long answer;
        depthBox = depth;
        switch (pass) {
            case "build": {
                System.out.println("Running pass buildTree (build): ");
                Tree last = null;
                for (int i = 0; i < iters; i++) {
                    long t0 = System.nanoTime();
                    last = mkTree(depthBox, 0);
                    times.add((System.nanoTime() - t0) / 1e9);
                    treeBox = last;
                }
                answer = last.sum();
                break;
            }
            case "add1": {
                treeBox = mkTree(depth, 0);
                System.out.println("Running pass add1Tree (map): ");
                Tree last = null;
                for (int i = 0; i < iters; i++) {
                    Tree in = treeBox;
                    long t0 = System.nanoTime();
                    last = in.add1();
                    times.add((System.nanoTime() - t0) / 1e9);
                }
                answer = last.sum();
                break;
            }
            case "sum": {
                treeBox = mkTree(depth, 0);
                System.out.println("Running pass sumTree (fold): ");
                long s = 0;
                for (int i = 0; i < iters; i++) {
                    Tree in = treeBox;
                    long t0 = System.nanoTime();
                    s = in.sum();
                    times.add((System.nanoTime() - t0) / 1e9);
                }
                answer = s;
                break;
            }
            default:
                throw new IllegalArgumentException("pass must be build, add1 or sum");
        }
        StringBuilder b = new StringBuilder("ITER TIMES: [");
        for (int i = 0; i < times.size(); i++)
            b.append(i > 0 ? ", " : "").append(String.format("%.9f", times.get(i)));
        System.out.println(b.append("]"));
        System.out.println("End");
        System.out.println(answer);
    }
}
