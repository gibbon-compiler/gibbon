#lang racket
  
(require "traversal.gib")
(require "../../gibbon/main.rkt")

;;(write (Leaf 1.1 1.1 2))


(define pointList (vector ( cons 0.242578 0.0134696) ( cons 0.383139 0.414653) ( cons 0.067769 0.993127) ( cons 0.484308 0.765338) ( cons 0.0318338 0.0309355) ( cons 0.93264 0.88788) ( cons 0.59133 0.478779) ( cons 0.833354 0.186335) ( cons 0.735653 0.115053) ( cons 0.698659 0.355604) ( cons 0.6383 0.908211) ( cons 0.294 0.264972) ( cons 0.377494 0.54162) ( cons 0.00928182 0.999465) ( cons 0.0129019 0.842497) ( cons 0.85247 0.467011) ( cons 0.0536072 0.976748) ( cons 0.196755 0.856973) ( cons 0.144214 0.800662) ( cons 0.729398 0.985791) ( cons 0.183406 0.49976) ( cons 0.469862 0.970991) ( cons 0.45077 0.0957919) ( cons 0.974082 0.390235) ( cons 0.68067 0.0266693) ( cons 0.231241 0.468739) ( cons 0.0979601 0.41541) ( cons 0.796294 0.316403) ( cons 0.778534 0.828493) ( cons 0.48714 0.369049) ( cons 0.602845 0.0242644) ( cons 0.811112 0.355793) ( cons 0.806109 0.274877) ( cons 0.859817 0.951019) ( cons 0.777276 0.680837) ( cons 0.835185 0.96113) ( cons 0.705425 0.0737512) ( cons 0.536857 0.957186) ( cons 0.418065 0.418777) ( cons 0.381617 0.836927) ( cons 0.240062 0.726211) ( cons 0.431613 0.116691) ( cons 0.223913 0.309588) ( cons 0.244801 0.377034) ( cons 0.807539 0.314736) ( cons 0.77523 0.283334) ( cons 0.996349 0.632867) ( cons 0.600911 0.50948) ( cons 0.834129 0.199443) ( cons 0.0359808 0.730005) ( cons 0.197911 0.293198) ( cons 0.770347 0.21475) ( cons 0.30922 0.0606627) ( cons 0.55759 0.416917) ( cons 0.115945 0.685545) ( cons 0.959951 0.893088) ( cons 0.136134 0.9978) ( cons 0.0279733 0.148065) ( cons 0.522975 0.641339) ( cons 0.989146 0.578133) ( cons 0.68053 0.674978) ( cons 0.362046 0.91471) ( cons 0.530369 0.917611) ( cons 0.283109 0.208989) ( cons 0.471816 0.806578) ( cons 0.161689 0.514298) ( cons 0.813117 0.0641685) ( cons 0.479624 0.0433095) ( cons 0.902915 0.294501) ( cons 0.68573 0.0660333) ( cons 0.82122 0.242774) ( cons 0.310257 0.492554) ( cons 0.356179 0.307991) ( cons 0.396982 0.0709161) ( cons 0.886517 0.684032) ( cons 0.528226 0.902819) ( cons 0.686503 0.063316) ( cons 0.15214 0.023765) ( cons 0.418943 0.174793) ( cons 0.752751 0.490316) ( cons 0.747744 0.329275) ( cons 0.117577 0.118128) ( cons 0.374985 0.37697) ( cons 0.728745 0.014481) ( cons 0.382013 0.4905) ( cons 0.827577 0.0796647) ( cons 0.923967 0.118042) ( cons 0.938252 0.195973) ( cons 0.726118 0.857863) ( cons 0.103638 0.83891) ( cons 0.56511 0.810401) ( cons 0.406969 0.934977) ( cons 0.160874 0.816055) ( cons 0.43174 0.248101) ( cons 0.830523 0.596219) ( cons 0.645779 0.608169) ( cons 0.495466 0.304382) ( cons 0.755627 0.82861) ( cons 0.455551 0.438145) ( cons 0.897431 0.118944))
)


(define (lesX a b) ( < (car a) (car b) ) )
(define (lesY a b) ( < (cdr a) (cdr b) )  )

(define (buildTree strtIndex endIndex  depth pLst)
  (let ( [size ( + ( - endIndex  strtIndex) 1) ] [mid  (quotient  (+ endIndex strtIndex ) 2 ) ] )

    ;;do always sort mutable vector
   (if (even? depth) (vector-sort! pLst lesX strtIndex (+ endIndex 1) ) (vector-sort! pLst lesY strtIndex  (+ endIndex 1)) )


    (if (= size 1 )
        ;;then
        ( Leaf (car (vector-ref pLst mid))  (cdr  (vector-ref pLst mid)) 0 )
        ;;else
        ( let   ([splitAccess   (if (even? depth) 1 0 )  ]
                 [splitLocation (if (even? depth) (car (vector-ref pLst mid)) (cdr (vector-ref pLst mid) ))]
                 [rightChild (buildTree (+ mid 1 ) endIndex  (+ depth 1) pLst)  ]
                 [leftChild  (buildTree strtIndex mid  (+ depth 1 ) pLst)       ]
                 )
                (let ( [ minxRight (match rightChild [(Leaf x y c) x]  [(Node _ _ minX _ _ _ _ _ ) minX])]
                       [ maxxRight (match rightChild [(Leaf x y c) x]  [(Node _ _ _ maxX _ _ _ _ ) maxX])]
                       [ minyRight (match rightChild [(Leaf x y c) y]  [(Node _ _ _ _ minY _ _ _ ) minY])]
                       [ maxyRight (match rightChild [(Leaf x y c) y]  [(Node _ _ _ _ _ maxY _ _ ) maxY])]
                       [ minxLeft (match leftChild [(Leaf x y c) x]  [(Node _ _ minX _ _ _ _ _ ) minX])]
                       [ maxxLeft (match leftChild [(Leaf x y c) x]  [(Node _ _ _ maxX _ _ _ _ ) maxX])]
                       [ minyLeft (match leftChild [(Leaf x y c) y]  [(Node _ _ _ _ minY _ _ _ ) minY])]
                       [ maxyLeft (match leftChild [(Leaf x y c) y]  [(Node _ _ _ _ _ maxY _ _ ) maxY])]
                      )
                  
                  (  Node  splitAccess splitLocation ( min minxRight minxLeft) ( max maxxRight maxxLeft) ( min minyRight minyLeft) ( max maxyRight maxyLeft) rightChild leftChild )  
        )
        )
    )
  )
  )

   

;;(  Leaf (car (vector-ref lst 0))  (cdr  (vector-ref lst 0)) 0)   )

( define inputTree  (buildTree 0 (- (vector-length pointList) 1) 0 pointList) )
(newline)
(write inputTree)

;;(newline)
;;(write (pointCorrelation  inputTree 0.0 0.0 20.0 ))
;;(newline)

(for/fold ([sum 0]) ( [p pointList] )  (values  (+ sum (pointCorrelation_v2  inputTree (car p) (cdr p) 0.7 )) ))

(for ( [p pointList] )  (write   (pointCorrelation_v2  inputTree (car p) (cdr p) 0.7 ) ) ( newline))



 #|

;; build-tree can use the full Racket language.
;; In fact, this code is not type checked.
(define (build-tree sz)
  (Bar (Foo 3) (Foo 1)))

(define (bench sz iters)
  (define tr (build-tree sz))
  ;; Use the traversal written in treelang
  (time
   (for ((_ (in-range iters)))
     (traverse tr))))

(bench 20 10)
(display "Done benchmarking\n")


(define (build-tree [pList : PointList ]) : Tree
  (if (eq? n 0)
      (Leaf 100)
      (let ([min1  : Int (- n 1)])
      (let ([l : Tree (build-tree min1)]
            [r : Tree (build-tree min1)])
        (Node l r)))))

(define (add1-tree [tr : Tree]) : Tree
  (case tr
    [(Leaf n) (let ([nplus : Int (+ 1 n)])
                (Leaf nplus))]
    [(Node x y)
     (let ([x2 : Tree (add1-tree x)]
           [y2 : Tree (add1-tree y)])
       (Node x2 y2))]))

(let ([tr0 : Tree (build-tree 2)])
    (time (add1-tree tr0)))|#
