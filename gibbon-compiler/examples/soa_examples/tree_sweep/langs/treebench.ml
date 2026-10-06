(* MonoTree's three traversals for the tree sweep (gibbon_benchmark.py
   --tree-sweep), ported from BintreeBench (ECOOP 2017) and aligned with
   tree_sweep/programs/*/MonoTree*.hs: OCaml's 63-bit ints hold every value
   these depths produce, mkTree d 0 gives every one of the 2^d leaves
   d(d+1)/2, and every subtree is built separately.

     treebench <build|add1|sum> --size-param DEPTH --iterate N

   prints each iteration's time in Gibbon's format, then the sum of the
   result. *)

type tree = Leaf of int | Node of tree * tree

external now_ns : unit -> int = "tb_now_ns_ml" [@@noalloc]

let rec mk_tree d acc =
  if d = 0 then Leaf acc
  else Node (mk_tree (d - 1) (d + acc), mk_tree (d - 1) (d + acc))

let rec add1_tree = function
  | Leaf x -> Leaf (x + 1)
  | Node (l, r) -> Node (add1_tree l, add1_tree r)

let rec sum_tree = function
  | Leaf x -> x
  | Node (l, r) -> sum_tree l + sum_tree r

let arg flag =
  let a = Sys.argv in
  let rec go i = if a.(i) = flag then int_of_string a.(i + 1) else go (i + 1) in
  go 1

let () =
  let pass = Sys.argv.(1) in
  let depth = arg "--size-param" in
  let iters = max 1 (arg "--iterate") in
  let times = Array.make iters 0.0 in
  let timed i f =
    let t0 = now_ns () in
    let r = f () in
    times.(i) <- float_of_int (now_ns () - t0) /. 1e9;
    r
  in
  let answer =
    match pass with
    | "build" ->
        print_string "Running pass buildTree (build): \n";
        let last = ref (Leaf 0) in
        for i = 0 to iters - 1 do
          last := timed i (fun () -> mk_tree (Sys.opaque_identity depth) 0)
        done;
        sum_tree !last
    | "add1" ->
        let tree = mk_tree depth 0 in
        print_string "Running pass add1Tree (map): \n";
        let last = ref tree in
        for i = 0 to iters - 1 do
          last := timed i (fun () -> add1_tree (Sys.opaque_identity tree))
        done;
        sum_tree !last
    | "sum" ->
        let tree = mk_tree depth 0 in
        print_string "Running pass sumTree (fold): \n";
        let s = ref 0 in
        for i = 0 to iters - 1 do
          s := timed i (fun () -> sum_tree (Sys.opaque_identity tree))
        done;
        !s
    | _ -> failwith "pass must be build, add1 or sum"
  in
  print_string "ITER TIMES: [";
  Array.iteri (fun i t -> Printf.printf "%s%.9f" (if i > 0 then ", " else "") t) times;
  print_string "]\nEnd\n";
  Printf.printf "%d\n" answer
