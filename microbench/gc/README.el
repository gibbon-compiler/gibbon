(defun overhead (a b)
  (* (/ (- b a) a) 100))

Tree insert:
----------------------------------------

./examples/bench_tree_insert.exe 25 2000000

| gibbon's pointer code         | 4.526952e+00 |
| built-in malloc'd linked-list | N/A          |
| no-gc                         | 1.525001e+00 |
| gc                            | 5.700926e+00 |
| gc with insets                | 9.746816e+00 |


Reverse List:
----------------------------------------

./examples/bench_ll.exe --inf-buffer-size 32 1000000 1

| gibbon's pointer code         | 2.563863e-02 |
| built-in malloc'd linked-list | 6.527711e-02 |
| no-gc                         | 1.032399e-01 |
| gc                            | 6.202352e-01 |
| gc with insets                | 1.000417e+00 |
