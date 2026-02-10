------------------------------
-- 1. DOM Tree Benchmark (style + layout)
------------------------------

-- DOMNode:
-- Each node has 10 fields:
--   field1: tag id (Int)
--   field2-10: numeric style/layout attributes (Float)
--   children: 4 fixed-arity DOMNode fields
-- Purpose:
--   Simulates a DOM tree where a rendering/layout pass may only use style-related fields,
--   skipping other fields like tag or ID. Useful for measuring how skipping unused fields
--   affects traversal performance (e.g., benefit from Struct-of-Arrays layouts).

data DOMNode = DOMNode
  Int Float Float Float Float Float Float Float Float Float
  DOMNode DOMNode DOMNode DOMNode
  | DOMLeaf

-- mkDOM n:
-- Creates a synthetic DOM tree of depth n with 4 children per node.
-- Fields are filled with numeric values for computation.
mkDOM :: Int -> DOMNode
mkDOM 0 = DOMLeaf
mkDOM n =
  let f = fromIntegral n * 0.1
  in DOMNode n f (f+1) (f+2) (f+3) (f+4) (f+5) (f+6) (f+7) (f+8)
             (mkDOM (n-1))
             (mkDOM (n-1))
             (mkDOM (n-1))
             (mkDOM (n-1))

-- foldDOM_Style:
-- Traverses the DOM tree and sums only style-related fields (5,6,7,10),
-- performing a small per-node computation.
-- Realistic: corresponds to layout or style calculation passes that ignore unused fields.
foldDOM_Style :: DOMNode -> Float
foldDOM_Style DOMLeaf = 0.0
foldDOM_Style (DOMNode _ _ _ _ e f g h _ _ c1 c2 c3 c4) =
  let local = e*f - g + h -- small per-node computation
  in local
     + foldDOM_Style c1 + foldDOM_Style c2 + foldDOM_Style c3 + foldDOM_Style c4

-- foldDOM_Tag:
-- Traverses the DOM tree and sums only the tag field (field 1).
-- Realistic: simulates operations that only care about node identity, ignoring layout/style.
foldDOM_Tag :: DOMNode -> Int
foldDOM_Tag DOMLeaf = 0
foldDOM_Tag (DOMNode a _ _ _ _ _ _ _ _ _ c1 c2 c3 c4) =
  a + foldDOM_Tag c1 + foldDOM_Tag c2 + foldDOM_Tag c3 + foldDOM_Tag c4

------------------------------
-- 2. Scene Graph Benchmark (transform + material)
------------------------------

-- SceneNode:
-- Each node has 10 fields representing transformation, material, and other properties.
-- Children: 4 fixed SceneNode fields.
-- Purpose: models a scene graph traversal in graphics engines.
-- Folds may only need transform-related fields for certain computations, skipping others.
data SceneNode = SceneNode
  Float Float Float Float Float Float Float Float Float Float
  SceneNode SceneNode SceneNode SceneNode
  | SceneLeaf

-- mkScene n:
-- Builds a synthetic scene graph of depth n.
mkScene :: Int -> SceneNode
mkScene 0 = SceneLeaf
mkScene n =
  let f = fromIntegral n * 0.5
  in SceneNode f (f+0.1) (f+0.2) (f+0.3) (f+0.4) (f+0.5) (f+0.6) (f+0.7) (f+0.8) (f+0.9)
                 (mkScene (n-1))
                 (mkScene (n-1))
                 (mkScene (n-1))
                 (mkScene (n-1))

-- foldScene_Transform:
-- Traverses the scene graph, computing only transform-related fields (1-4),
-- with small per-node computations (a*b + c - d).
-- Realistic: mimics a render pass or physics pass that only uses part of the node data.
foldScene_Transform :: SceneNode -> Float
foldScene_Transform SceneLeaf = 0.0
foldScene_Transform (SceneNode a b c d _ _ _ _ _ _ c1 c2 c3 c4) =
  let local = a*b + c - d
  in local
     + foldScene_Transform c1 + foldScene_Transform c2
     + foldScene_Transform c3 + foldScene_Transform c4

------------------------------
-- 3. AST Tree Benchmark (opcode + type info)
------------------------------

-- ASTNode:
-- Each node has 10 fields: opcode, type info, metadata, numeric attributes.
-- Children: 4 fixed ASTNode fields.
-- Purpose: models an abstract syntax tree traversal.
-- Some passes (e.g., optimization, type checking) only touch a subset of fields.
data ASTNode = ASTNode
  Int Int Float Int Float Float Int Float Int Float
  ASTNode ASTNode ASTNode ASTNode
  | ASTLeaf

-- mkAST n:
-- Builds a synthetic AST of depth n.
mkAST :: Int -> ASTNode
mkAST 0 = ASTLeaf
mkAST n =
  let f = fromIntegral n * 0.25
  in ASTNode n (n+1) f (n+2) (f+1) (f+2) (n+3) (f+3) (n+4) (f+4)
             (mkAST (n-1))
             (mkAST (n-1))
             (mkAST (n-1))
             (mkAST (n-1))

-- foldAST_Opcode:
-- Traverses the AST and only sums opcode/type fields (1,2,4),
-- mimicking compiler analyses that skip metadata or numeric attributes.
foldAST_Opcode :: ASTNode -> Float
foldAST_Opcode ASTLeaf = 0.0
foldAST_Opcode (ASTNode a b _ d _ _ _ _ _ _ c1 c2 c3 c4) =
  let local = fromIntegral (a + b + d)
  in local + foldAST_Opcode c1 + foldAST_Opcode c2 + foldAST_Opcode c3 + foldAST_Opcode c4

------------------------------
-- 4. Physics Tree Benchmark (position + velocity + force)
------------------------------

-- PhysicsNode:
-- Each node has 10 fields representing position, velocity, mass, force, collision info.
-- Children: 4 fixed PhysicsNode fields.
-- Purpose: models a physics or simulation tree.
-- Some passes only compute over position/velocity, ignoring other fields.
data PhysicsNode = PhysicsNode
  Float Float Float Float Float Float Float Float Float Float
  PhysicsNode PhysicsNode PhysicsNode PhysicsNode
  | PhysicsLeaf

-- mkPhysics n:
-- Builds a synthetic physics tree of depth n.
mkPhysics :: Int -> PhysicsNode
mkPhysics 0 = PhysicsLeaf
mkPhysics n =
  let f = fromIntegral n * 0.1
  in PhysicsNode f (f+0.1) (f+0.2) (f+0.3) (f+0.4) (f+0.5) (f+0.6) (f+0.7) (f+0.8) (f+0.9)
                  (mkPhysics (n-1))
                  (mkPhysics (n-1))
                  (mkPhysics (n-1))
                  (mkPhysics (n-1))

-- foldPhysics_PosVel:
-- Traverses the physics tree and computes only position/velocity fields (1-4),
-- with small per-node computations (x*x + y*z - w).
-- Realistic: mimics force integration or motion updates, skipping mass or collision info.
foldPhysics_PosVel :: PhysicsNode -> Float
foldPhysics_PosVel PhysicsLeaf = 0.0
foldPhysics_PosVel (PhysicsNode x y z w _ _ _ _ _ _ c1 c2 c3 c4) =
  let local = x*x + y*z - w
  in local + foldPhysics_PosVel c1 + foldPhysics_PosVel c2 + foldPhysics_PosVel c3 + foldPhysics_PosVel c4
