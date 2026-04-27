/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anton Kovsharov, Antoine du Fresne von Hohenesche, Sorrachai Yingchareonthawornchai
-/

module

public import GraphAlgorithms.DataStructures.SplayTrees.BinaryTree
public import Mathlib.Data.Real.Basic

@[expose] public section

variable {α : Type} [LinearOrder α]

-- =========================================================================
-- §1  Definitions
-- =========================================================================
-- Rotation primitives, direction / frame types, descend, splayUp, splayBU.


def rotateRight : BinaryTree α → BinaryTree α
  | .node (.node a x b) y c => .node a x (.node b y c)
  | t => t

def rotateLeft : BinaryTree α → BinaryTree α
  | .node a x (.node b y c) => .node (.node a x b) y c
  | t => t


inductive Dir
  | L -- target descended into the left subtree from this parent
  | R -- target descended into the right subtree from this parent
  deriving DecidableEq, Repr

/-- Single primitive rotation that brings the `d`-child of the root up one
level. `L` ↦ `rotateRight`, `R` ↦ `rotateLeft`. -/
def Dir.bringUp : Dir → BinaryTree α → BinaryTree α
  | .L => rotateRight
  | .R => rotateLeft

/-- Apply `op` to the `d`-child of the root, leaving everything else fixed. -/
def applyChild (d : Dir) (op : BinaryTree α → BinaryTree α) : BinaryTree α → BinaryTree α
  | .node l k r =>
    match d with
    | .L => .node (op l) k r
    | .R => .node l k (op r)
  | .empty => .empty

/-- One frame of the search path: the direction we took from this ancestor,
its key, and the subtree we did *not* descend into. -/
structure Frame (α : Type) where
  dir : Dir
  key : α
  sibling : BinaryTree α

/-- Re-attach a subtree `c` below the ancestor described by `f`. -/
def Frame.attach (c : BinaryTree α) (f : Frame α) : BinaryTree α :=
  match f.dir with
  | .L => .node c f.key f.sibling
  | .R => .node f.sibling f.key c

/-- Descend from `t` toward `q`, returning the subtree reached (either the
matching node or `.empty` if `q` is absent) and the path above it. The head
of the returned list is the deepest frame (parent of the returned subtree). -/
def descend (t : BinaryTree α) (q : α) : BinaryTree α × List (Frame α) :=
  go t []
where
  go : BinaryTree α → List (Frame α) → BinaryTree α × List (Frame α)
  | .empty, acc => (.empty, acc)
  | .node l k r, acc =>
    if q = k then (.node l k r, acc)
    else if q < k then go l ({ dir := .L, key := k, sibling := r } :: acc)
    else go r ({ dir := .R, key := k, sibling := l } :: acc)

/-- Splay the subtree `c` upward along `path`, pairing frames from the bottom
up. Each double step (parent `f1`, grandparent `f2`) is:
* **same-direction** (`zig-zig` / `zag-zag`): two outer rotations in direction
  `f2.dir`;
* **opposite-direction** (`zig-zag` / `zag-zig`): one inner rotation at the
  `f2.dir`-child (in direction `f1.dir`), then one outer rotation (in
  direction `f2.dir`).
A leftover single frame is a plain zig/zag. -/
def splayUp : BinaryTree α → List (Frame α) → BinaryTree α
  | c, [] => c
  | c, [f] => f.dir.bringUp (f.attach c)
  | c, f1 :: f2 :: rest =>
    let s := f2.attach (f1.attach c)
    let s' :=
      if f1.dir = f2.dir then
        f2.dir.bringUp (f2.dir.bringUp s)
      else
        f2.dir.bringUp (applyChild f2.dir f1.dir.bringUp s)
    splayUp s' rest

/-- Bottom-up splay: the "textbook" splay analysed by Tarjan, Sundar, and
Elmasry. If `q` is absent the last visited ancestor is splayed to the root. -/
def splayBU (t : BinaryTree α) (q : α) : BinaryTree α :=
  match descend t q with
  | (.empty, []) => .empty
  | (.empty, f :: rest) => splayUp (f.attach .empty) rest
  | (x@(.node _ _ _), path) => splayUp x path

/-- Cost of a bottom-up splay: one unit per rotation, i.e. the length of the
search path. -/
def splayBU.cost (t : BinaryTree α) (q : α) : ℝ :=
  (descend t q).2.length
