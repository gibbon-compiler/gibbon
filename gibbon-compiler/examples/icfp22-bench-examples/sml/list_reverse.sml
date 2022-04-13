datatype List = Nil | Cons of (int * List)

fun reverse xs acc = (
    case xs of
	Nil => acc
      | Cons (z, zs) => reverse zs (Cons (z, acc)))

fun createVec n = if (n = 0) then Nil else Cons (n, createVec (n - 1))

						
