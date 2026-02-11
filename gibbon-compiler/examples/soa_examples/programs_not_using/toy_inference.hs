-- Packed 2D vector
data Vec2 = Vec2 Float Float
  deriving (Show)

-- Packed layer: 2x2 weights and 2 biases
data Layer = Layer Float Float Float Float Float Float
  deriving (Show)

-- Packed binary tree of layers
data NetTree = Leaf Layer | Node NetTree NetTree
  deriving (Show)

-- ReLU activation
relu :: Float -> Float
relu x = if x > 0.0 then x else 0.0

-- Sigmoid activation
sigmoid :: Float -> Float
sigmoid x = 1.0 / (1.0 + exp (-x))

-- Tanh activation
tanhAct :: Float -> Float
tanhAct x = (exp x - exp (-x)) / (exp x + exp (-x))

-- Softmax over Vec2
softmax :: Vec2 -> Vec2
softmax (Vec2 x y) =
  let ex = exp x
      ey = exp y
      sum = ex + ey
  in Vec2 (ex / sum) (ey / sum)

-- Add two Vec2s
addVec :: Vec2 -> Vec2 -> Vec2
addVec (Vec2 x1 y1) (Vec2 x2 y2) = Vec2 (x1 + x2) (y1 + y2)

-- Matrix-vector multiplication for 2x2 layer
matVecMul :: Layer -> Vec2 -> Vec2
matVecMul (Layer w11 w12 w21 w22 b1 b2) (Vec2 x1 x2) =
  let y1 = w11 * x1 + w12 * x2 + b1
      y2 = w21 * x1 + w22 * x2 + b2
  in Vec2 y1 y2

-- Apply activation to Vec2
applyActivation :: String -> Vec2 -> Vec2
applyActivation act (Vec2 x y) =
  case act of
    "relu"    -> Vec2 (relu x) (relu y)
    "sigmoid" -> Vec2 (sigmoid x) (sigmoid y)
    "tanh"    -> Vec2 (tanhAct x) (tanhAct y)
    "softmax" -> softmax (Vec2 x y)
    _         -> Vec2 x y  -- no activation

-- Forward pass through a layer with activation
forward :: Layer -> Vec2 -> String -> Vec2
forward layer input act =
  let raw = matVecMul layer input
  in applyActivation act raw

-- Recursive inference over packed tree
evalNet :: NetTree -> Vec2 -> String -> Vec2
evalNet nt input act =
  case nt of
    Leaf l     -> forward l input act
    Node l r   ->
      let leftOut  = evalNet l input act
          rightOut = evalNet r input act
      in addVec leftOut rightOut

-- Example network with 3 layers
net :: NetTree
net = Node
        (Node
          (Leaf (Layer 0.5 0.3 0.2 0.8 0.1 (-0.2)))
          (Leaf (Layer 0.4 0.6 0.7 0.1 0.0 0.3)))
        (Leaf (Layer 0.9 0.1 0.3 0.4 0.2 (-0.1)))

-- Example input
input :: Vec2
input = Vec2 1.0 2.0

-- Run inference
main :: IO ()
main = do
  let resultReLU    = evalNet net input "relu"
  let resultSigmoid = evalNet net input "sigmoid"
  let resultTanh    = evalNet net input "tanh"
  let resultSoftmax = evalNet net input "softmax"
  putStrLn "ReLU output:"
  print resultReLU
  putStrLn "Sigmoid output:"
  print resultSigmoid
  putStrLn "Tanh output:"
  print resultTanh
  putStrLn "Softmax output:"
  print resultSoftmax
