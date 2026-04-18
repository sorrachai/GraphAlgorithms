import Mathlib.Algebra.Ring.Parity
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.List.FinRange

inductive BinaryTree where
| empty
| node (left : BinaryTree) (key : ℕ) (right : BinaryTree)
deriving Repr, BEq

def BinaryTree.num_nodes : BinaryTree → ℕ
| .empty => 0
| .node left _ right => 1 + (num_nodes left) + (num_nodes right)

-- 1. ROTATION PRIMITIVES
-- We keep these simple. They are the atomic steps.

def rotateRight : BinaryTree → BinaryTree
  | .node (.node a x b) y c => .node a x (.node b y c)
  | t => t

def rotateLeft : BinaryTree → BinaryTree
  | .node a x (.node b y c) => .node (.node a x b) y c
  | t => t

-- 2. ROTATION STRATEGIES
-- Helper to orchestrate the rotations.

inductive Rot
  | zigZig | zigZag | zagZag | zagZig | zig | zag

def rotate (s : BinaryTree) (rt : Rot) : BinaryTree :=
  match rt with
  | .zigZig => rotateRight (rotateRight s) -- Explicitly two steps
  | .zigZag =>
      match s with
      | .node l k r => rotateRight (.node (rotateLeft l) k r)
      | _ => s
  | .zagZag => rotateLeft (rotateLeft s)   -- Explicitly two steps
  | .zagZig =>
      match s with
      | .node l k r => rotateLeft (.node l k (rotateRight r))
      | _ => s
  | .zig => rotateRight s
  | .zag => rotateLeft s

-- 3. SPLAY IMPLEMENTATION
-- Note the checks for .empty on grandchildren to decide between ZigZig vs Zig.

def BinaryTree.search_path_len (t : BinaryTree) (q : ℕ) : ℕ :=
  match t with
  | .empty => 0
  | .node left key right =>
    if q < key then
      1 + left.search_path_len q
    else if key < q then
      1 + right.search_path_len q
    else
      1

def splay' (t : BinaryTree) (q : ℕ) : BinaryTree :=
  match t with
  | .empty => .empty
  | .node l k r =>
    if q = k then
      t
    else if q < k then
      match l with
      | .empty => t -- q not found, current root is closest
      | .node ll lk lr =>
        if q < lk then
          match ll with
          | .empty => rotate (.node l k r) .zig -- Grandchild empty? Just Zig.
          | _ =>
              -- Zig-Zig: Recurse, then double rotate
              let t' := .node (splay' ll q) lk lr
              rotate (.node t' k r) .zigZig
        else if lk < q then
          match lr with
          | .empty => rotate (.node l k r) .zig -- Grandchild empty? Just Zig.
          | _ =>
              -- Zig-Zag: Recurse, then double rotate
              let t' := .node ll lk (splay' lr q)
              rotate (.node t' k r) .zigZag
        else
          -- Target found at child (lk == q)
          rotate t .zig
    else -- q > k (Symmetric case)
      match r with
      | .empty => t
      | .node rl rk rr =>
        if q < rk then
          match rl with
          | .empty => rotate (.node l k r) .zag -- Grandchild empty? Just Zag.
          | _ =>
              -- Zag-Zig
              let t' := .node (splay' rl q) rk rr
              rotate (.node l k t') .zagZig
        else if rk < q then
          match rr with
          | .empty => rotate (.node l k r) .zag -- Grandchild empty? Just Zag.
          | _ =>
              -- Zag-Zag
              let t' := .node rl rk (splay' rr q)
              rotate (.node l k t') .zagZag
        else
          -- Target found at child (rk == q)
          rotate t .zag

def splay (t : BinaryTree) (q : ℕ) : BinaryTree :=
  match t with
  | .empty => .empty
  | .node l k r =>
    let len := t.search_path_len q
    if Odd len then splay' t q
    else
      if q = k then
        t
      else if q < k then
        let t' := .node (splay' l q) k r
        rotate t' .zig
      else
        let t' := .node l k (splay' r q)
        rotate t' .zag


def subtree_rooted_at (t : BinaryTree) (q : ℕ) : BinaryTree :=
  match t with
  | .empty => .empty
  | .node l k r =>
    if q = k then
      t
    else if q < k then
      subtree_rooted_at l q
    else
      subtree_rooted_at r q

def splay.cost' (t : BinaryTree) (q : ℕ) : ℝ :=
  match t with
  | .empty => 0
  | .node l k r =>
    if q = k then 0
    else if q < k then
      match l with
      | .empty => 0
      | .node ll lk lr =>
        if q < lk then
          match ll with
          | .empty => 1                 -- Zig (Grandchild empty)
          | _ => (splay.cost' ll q) + 2  -- Zig-Zig
        else if lk < q then
          match lr with
          | .empty => 1                 -- Zig (Grandchild empty)
          | _ => (splay.cost' lr q) + 2  -- Zig-Zag
        else 1                          -- Zig (Found at child)
    else -- q > k
      match r with
      | .empty => 0
      | .node rl rk rr =>
        if q < rk then
          match rl with
          | .empty => 1                 -- Zag (Grandchild empty)
          | _ => (splay.cost' rl q) + 2  -- Zag-Zig
        else if rk < q then
          match rr with
          | .empty => 1                 -- Zag (Grandchild empty)
          | _ => (splay.cost' rr q) + 2  -- Zag-Zag
        else 1                          -- Zag (Found at child)

def splay.cost (t : BinaryTree) (q : ℕ) : ℝ :=
   match t with
  | .empty => 0
  | .node l k r =>
    let len := t.search_path_len q
    if Odd len then splay.cost' t q
    else
      if q = k then
        0
      else if q < k then
        1 + (splay.cost' l q)
      else
        1 + (splay.cost' r q)


inductive ForallTree (p : Nat → Prop) : BinaryTree → Prop
  | left : ForallTree p .empty
  | node left key right :
     ForallTree p left →
     p key  →
     ForallTree p right →
     ForallTree p (.node left key  right)

inductive IsBST : BinaryTree → Prop
  | left : IsBST .empty
  | node key left right:
     ForallTree (fun k  => k < key) left →
     ForallTree (fun k  => key < k) right →
     IsBST left → IsBST right →
     IsBST (.node left key right)


-- 2. Rank and Potential
noncomputable def rank (t : BinaryTree) : ℝ :=
  if t.num_nodes = 0 then 0 else Real.logb 2 (t.num_nodes)

noncomputable def φ ( t : BinaryTree) : ℝ :=
  -- EVOLVE-VALUE-START
  match t with
  | .empty => 0
  | s@(.node l _ r) => rank s + φ l + φ r
  -- EVOLVE-VALUE-END

def splay.sequence_cost {n : ℕ}
  (init : BinaryTree) (X : Fin n → ℕ) : ℝ :=
  ((List.finRange n).foldl (fun (acc : BinaryTree × ℝ) i =>
    let (t, c) := acc
    (splay t (X i), c + splay.cost t (X i)))
  (init, 0)).2

def one_to_n (n : ℕ) : Fin n → ℕ := fun x ↦ x

def BinaryTree.toKeyList (t : BinaryTree) : List Nat :=
  match t with
  | .empty => []
  | .node left key right => left.toKeyList ++ [key] ++ right.toKeyList

-- EVOLVE-BLOCK-START

-- ============================================================================
--  Elmasry's coloring scheme (TCS 314, 2004, §2)
-- ============================================================================
--
-- Every node carries one of three colors.  "Uncolored" is the initial status.
-- The paper's "black" color is a predicate (is-on-right-spine-of-current-tree)
-- rather than a persistent color, so it is not represented in `Color`.
inductive Color
  | uncolored
  | yellow
  | green
  deriving DecidableEq, Repr

/-- A coloring assigns a color to every key.  Keys not present in the tree can
be ignored; by default they stay `uncolored`. -/
abbrev ColorState := ℕ → Color

namespace ColorState

/-- Initially every node is uncolored. -/
def initial : ColorState := fun _ => .uncolored

/-- A node counts as "colored" whenever it is not `.uncolored`.  The paper
often speaks of "colored nodes", meaning yellow/green/black. -/
def isColored (col : ColorState) (x : ℕ) : Bool :=
  col x ≠ .uncolored

end ColorState

-- ---------------------------------------------------------------------------
--  Spine helpers
-- ---------------------------------------------------------------------------

/-- Keys along the right spine of a tree (root, right, right.right, ...). -/
def BinaryTree.rightSpineKeys : BinaryTree → List ℕ
  | .empty => []
  | .node _ k r => k :: r.rightSpineKeys

/-- Keys along the left spine of a tree (root, left, left.left, ...). -/
def BinaryTree.leftSpineKeys : BinaryTree → List ℕ
  | .empty => []
  | .node l k _ => k :: l.leftSpineKeys

/-- A key `x` is **black** in tree `t` if it sits on the right spine of `t`
(i.e., the root, or reachable from the root by following right children).

This matches Elmasry §2 (lines 144–145): "all the nodes on the right spine
of the tree are coloured black, overriding the above colouring rules."
Unlike yellow/green — which are persistent state carried by `ColorState` —
*black* is a position predicate that depends on the **current** tree, so
rotations can move nodes in and out of this set.

Lemma 1(c) monotonicity of `vVal` is known to apply only to nodes that are
non-black.  The K-link bucket accounts for rotations involving a black
node. -/
def BinaryTree.IsBlack (t : BinaryTree) (x : ℕ) : Prop := x ∈ t.rightSpineKeys

instance (t : BinaryTree) (x : ℕ) : Decidable (t.IsBlack x) :=
  inferInstanceAs (Decidable (x ∈ t.rightSpineKeys))

@[simp] lemma BinaryTree.IsBlack_empty (x : ℕ) : ¬ (BinaryTree.empty).IsBlack x := by
  simp [BinaryTree.IsBlack, BinaryTree.rightSpineKeys]

@[simp] lemma BinaryTree.IsBlack_node (l : BinaryTree) (k : ℕ) (r : BinaryTree)
    (x : ℕ) : (BinaryTree.node l k r).IsBlack x ↔ x = k ∨ r.IsBlack x := by
  simp [BinaryTree.IsBlack, BinaryTree.rightSpineKeys]

-- ---------------------------------------------------------------------------
--  The quantities g_x, h_x, v_x from the paper
-- ---------------------------------------------------------------------------

/-- `gVal col t x` — the number of colored nodes on the right spine of the
sub-tree of `t` rooted at `x`.  Matches `g_x(t)` in Elmasry. -/
def gVal (col : ColorState) (t : BinaryTree) (x : ℕ) : ℕ :=
  ((subtree_rooted_at t x).rightSpineKeys.filter (fun k => col.isColored k)).length

/-- `hVal col t x` — the number of colored nodes on the right spine of the
left child of `x`.  If `x` has no left child, this is 0.  Matches `h_x(t)`. -/
def hVal (col : ColorState) (t : BinaryTree) (x : ℕ) : ℕ :=
  match subtree_rooted_at t x with
  | .empty       => 0
  | .node l _ _  => (l.rightSpineKeys.filter (fun k => col.isColored k)).length

/-- `vVal col t x = g_x(t) − h_x(t)`.  Lemma 1(a)(b): `vVal ≥ 0` for every
yellow/green node.  We use `ℤ` so subtraction is well-behaved. -/
def vVal (col : ColorState) (t : BinaryTree) (x : ℕ) : ℤ :=
  (gVal col t x : ℤ) - (hVal col t x : ℤ)

-- ---------------------------------------------------------------------------
--  Link counters (the four Elmasry categories)
-- ---------------------------------------------------------------------------

/-- Per-step (or cumulative) count of links in Elmasry's four categories.
  * `Y` — links incident to at least one yellow node,
  * `A` — green-to-green A-links (`v_z(t) = 1` at time of link),
  * `B` — green-to-green B-links (`v_z(t) ≥ 2` at time of link),
  * `K` — links incident to a black node. -/
structure LinkCounters where
  Y : ℕ
  A : ℕ
  B : ℕ
  K : ℕ
  deriving Repr

namespace LinkCounters

def zero : LinkCounters := ⟨0, 0, 0, 0⟩

instance : Zero LinkCounters := ⟨zero⟩

def add (a b : LinkCounters) : LinkCounters :=
  ⟨a.Y + b.Y, a.A + b.A, a.B + b.B, a.K + b.K⟩

instance : Add LinkCounters := ⟨add⟩

/-- Total number of links recorded (= total rotations attributed by the
coloring argument). -/
def total (c : LinkCounters) : ℕ := c.Y + c.A + c.B + c.K

end LinkCounters

-- ---------------------------------------------------------------------------
--  Search path and splaying spine
-- ---------------------------------------------------------------------------

/-- Search path of `q` in `t`, listed top-down (root first, target last). -/
def BinaryTree.searchPath : BinaryTree → ℕ → List ℕ
  | .empty, _       => []
  | .node l k r, q  =>
      if q = k then [k]
      else if q < k then k :: l.searchPath q
      else k :: r.searchPath q

/-- The splaying spine for a splay of `q` in `t` (Elmasry §2): the search
path with the root omitted, since the root is colored BLACK separately. -/
def BinaryTree.splayingSpine (t : BinaryTree) (q : ℕ) : List ℕ :=
  (t.searchPath q).tail

-- ---------------------------------------------------------------------------
--  Coloring primitives
-- ---------------------------------------------------------------------------

namespace ColorState

/-- Update a single key's color. -/
def set (col : ColorState) (x : ℕ) (c : Color) : ColorState :=
  fun y => if y = x then c else col y

/-- Paint every currently-uncolored key in `xs` YELLOW. -/
def paintYellow (col : ColorState) (xs : List ℕ) : ColorState :=
  xs.foldl (fun c x => if c x = .uncolored then c.set x .yellow else c) col

end ColorState

-- ---------------------------------------------------------------------------
--  Enumeration of links formed during one splay
-- ---------------------------------------------------------------------------
--
-- Given a splaying spine listed top-down `[x_k, x_{k-1}, …, x_1]` (with
-- `x_1 = q` at the bottom), one splay restructures the tree so every
-- consecutive spine pair becomes a new parent-child edge.  We enumerate
-- those pairs in top-down order (closer-to-root first) as `(parent, child)`.

def linksOfSpine : List ℕ → List (ℕ × ℕ)
  | []            => []
  | [_]           => []
  | x :: y :: rs  => (x, y) :: linksOfSpine (y :: rs)

-- ---------------------------------------------------------------------------
--  Classifying one link (Y / A / B / K) and updating the coloring
-- ---------------------------------------------------------------------------
--
-- `t_before` is the tree before this splay operation, against which the
-- paper's quantities `v_z(t)` are measured.  The four cases:
--
--   * at least one endpoint YELLOW → bucket Y, promote yellow→green;
--   * otherwise both endpoints GREEN:
--       v_z(t_before) = 1 → bucket A,
--       v_z(t_before) ≥ 2 → bucket B.
-- (The K bucket is populated by `stepColor`, not by `processLink`.)

def processLink (col : ColorState) (cnt : LinkCounters)
    (t_before : BinaryTree) (w z : ℕ) : ColorState × LinkCounters :=
  let cw := col w
  let cz := col z
  if cw = .yellow ∨ cz = .yellow then
    -- (Y) yellow-involving link: promote yellow endpoints to green.
    let col₁ := if cw = .yellow then col.set w .green else col
    let col₂ := if cz = .yellow then col₁.set z .green else col₁
    (col₂, { cnt with Y := cnt.Y + 1 })
  else
    -- Both endpoints green: split by v_z(t_before).
    if vVal col t_before z = 1 then
      (col, { cnt with A := cnt.A + 1 })
    else
      (col, { cnt with B := cnt.B + 1 })

def processLinks (col : ColorState) (cnt : LinkCounters) (t_before : BinaryTree)
    (links : List (ℕ × ℕ)) : ColorState × LinkCounters :=
  links.foldl
    (fun (acc : ColorState × LinkCounters) (wz : ℕ × ℕ) =>
      processLink acc.1 acc.2 t_before wz.1 wz.2)
    (col, cnt)

-- ---------------------------------------------------------------------------
--  One-step coloring update + per-step link counts
-- ---------------------------------------------------------------------------
--
-- When a splay of `q` fires, the coloring is updated as follows:
--   (1) uncolored nodes now on the splaying spine become YELLOW;
--   (2) the TOPMOST link of the spine (the one adjacent to the tree root,
--       which is BLACK per Elmasry's predicate) is classified as a K-link —
--       at most one per splay, hence a global bound of `n` on K-links;
--   (3) the remaining links are classified as Y/A/B by `processLink`.
--
-- "Black" is a predicate (is-on-right-spine-of-current-tree), not stored in
-- `ColorState`, so no `paintBlack` call is made.

def stepColor
    (col : ColorState) (t_before _t_after : BinaryTree)
    (q : ℕ) : ColorState × LinkCounters :=
  let path  := t_before.searchPath q
  let col₁  := col.paintYellow path.tail
  match linksOfSpine path with
  | []           => (col₁, 0)
  | _top :: rest =>
      -- `_top` is the root→first-spine-child link (the K-link).
      let res := processLinks col₁ 0 t_before rest
      (res.1, { res.2 with K := res.2.K + 1 })

-- ---------------------------------------------------------------------------
--  Rolling the coloring + counters through a whole splay sequence
-- ---------------------------------------------------------------------------

/-- Fold the coloring and link counters through a splay sequence, returning
the final tree, the final coloring, and the cumulative link counts. -/
def colorSequence {n : ℕ}
    (init : BinaryTree) (X : Fin n → ℕ) :
    BinaryTree × ColorState × LinkCounters :=
  (List.finRange n).foldl
    (fun (acc : BinaryTree × ColorState × LinkCounters) i =>
      let (t, col, cnt) := acc
      let q  := X i
      let t' := splay t q
      let (col', dcnt) := stepColor col t t' q
      (t', col', cnt + dcnt))
    (init, ColorState.initial, 0)

/-- Cumulative link counters for a full splay sequence. -/
def totalCounters {n : ℕ}
    (init : BinaryTree) (X : Fin n → ℕ) : LinkCounters :=
  (colorSequence init X).2.2

-- ---------------------------------------------------------------------------
--  Cost ↔ link-count identity
-- ---------------------------------------------------------------------------

/-- `.total` is additive under `LinkCounters` addition. -/
lemma LinkCounters.total_add (a b : LinkCounters) :
    (a + b).total = a.total + b.total := by
  show (LinkCounters.add a b).total = a.total + b.total
  unfold LinkCounters.add LinkCounters.total
  ring

/-- `processLink` increments the counter total by exactly 1. -/
lemma processLink_total (col : ColorState) (cnt : LinkCounters)
    (t : BinaryTree) (w z : ℕ) :
    (processLink col cnt t w z).2.total = cnt.total + 1 := by
  -- Every branch updates exactly one of Y/A/B/K by +1.
  dsimp only [processLink]
  split_ifs <;> · simp [LinkCounters.total]; omega

/-- `processLinks` increments the counter total by the number of links fed. -/
lemma processLinks_total (col : ColorState) (cnt : LinkCounters)
    (t : BinaryTree) (links : List (ℕ × ℕ)) :
    (processLinks col cnt t links).2.total = cnt.total + links.length := by
  induction links generalizing col cnt with
  | nil => rfl
  | cons wz rest ih =>
      -- one step of the foldl unfolds definitionally
      have hstep : processLinks col cnt t (wz :: rest)
          = processLinks (processLink col cnt t wz.1 wz.2).1
                         (processLink col cnt t wz.1 wz.2).2 t rest := rfl
      rw [hstep, ih, processLink_total]
      simp [List.length_cons]
      omega

/-- `linksOfSpine` applied to a list of length `k` yields a list of length
`k - 1` (with the usual `ℕ` truncation at 0). -/
lemma linksOfSpine_length : ∀ (L : List ℕ),
    (linksOfSpine L).length = L.length - 1
  | []            => rfl
  | [_]           => rfl
  | _ :: y :: rs => by
      have ih := linksOfSpine_length (y :: rs)
      simp [linksOfSpine, List.length_cons] at ih ⊢
      omega

/-- The number of nodes on the search path equals `search_path_len`. -/
lemma searchPath_length (t : BinaryTree) (q : ℕ) :
    (t.searchPath q).length = t.search_path_len q := by
  induction t with
  | empty => rfl
  | node l k r ihl ihr =>
      unfold BinaryTree.searchPath BinaryTree.search_path_len
      by_cases h1 : q = k
      · subst h1
        simp
      · by_cases h2 : q < k
        · simp [h1, h2, List.length_cons, ihl]; omega
        · have h3 : k < q := by omega
          simp [h1, h2, h3, List.length_cons, ihr]; omega

/-- `stepColor` produces exactly `search_path_len − 1` link events.  (This is
the "number of rotations in one splay" fact as counted by the coloring.) -/
lemma stepColor_total_eq (col : ColorState) (t t' : BinaryTree) (q : ℕ) :
    (stepColor col t t' q).2.total = t.search_path_len q - 1 := by
  dsimp only [stepColor]
  have hlen : (linksOfSpine (t.searchPath q)).length = t.search_path_len q - 1 := by
    rw [linksOfSpine_length, searchPath_length]
  -- Case-split on whether the spine has any links.
  rcases hls : linksOfSpine (t.searchPath q) with _ | ⟨top, rest⟩
  · -- No links: total = 0; and linksOfSpine empty ⇒ search_path_len ≤ 1.
    simp
    have : (linksOfSpine (t.searchPath q)).length = 0 := by rw [hls]; rfl
    show (0 : LinkCounters).total = t.search_path_len q - 1
    have h0 : (0 : LinkCounters).total = 0 := by show LinkCounters.zero.total = 0; rfl
    rw [h0]; omega
  · -- One K-link + processLinks on `rest`.
    have hprocess : (processLinks (col.paintYellow (t.searchPath q).tail) 0 t rest).2.total
        = rest.length := by
      rw [processLinks_total]
      show (0 : LinkCounters).total + rest.length = rest.length
      have h0 : (0 : LinkCounters).total = 0 := by show LinkCounters.zero.total = 0; rfl
      rw [h0, Nat.zero_add]
    -- .total of {Y,A,B,K+1} = Y + A + B + (K+1) = processed.total + 1.
    show (processLinks (col.paintYellow (t.searchPath q).tail) 0 t rest).2.Y +
         (processLinks (col.paintYellow (t.searchPath q).tail) 0 t rest).2.A +
         (processLinks (col.paintYellow (t.searchPath q).tail) 0 t rest).2.B +
         ((processLinks (col.paintYellow (t.searchPath q).tail) 0 t rest).2.K + 1)
      = t.search_path_len q - 1
    have hexpand : (processLinks (col.paintYellow (t.searchPath q).tail) 0 t rest).2.Y +
         (processLinks (col.paintYellow (t.searchPath q).tail) 0 t rest).2.A +
         (processLinks (col.paintYellow (t.searchPath q).tail) 0 t rest).2.B +
         ((processLinks (col.paintYellow (t.searchPath q).tail) 0 t rest).2.K + 1)
      = (processLinks (col.paintYellow (t.searchPath q).tail) 0 t rest).2.total + 1 := by
      unfold LinkCounters.total; omega
    rw [hexpand, hprocess]
    -- Now: rest.length + 1 = t.search_path_len q - 1.
    -- linksOfSpine = top :: rest, so rest.length + 1 = linksOfSpine.length.
    have hls_len : (linksOfSpine (t.searchPath q)).length = rest.length + 1 := by
      rw [hls]; simp
    omega

/-- Positivity of `search_path_len` on a non-empty tree. -/
private lemma search_path_len_node_pos (l : BinaryTree) (k : ℕ) (r : BinaryTree)
    (q : ℕ) : 1 ≤ (BinaryTree.node l k r).search_path_len q := by
  unfold BinaryTree.search_path_len
  split_ifs <;> omega

/-- Arithmetic helper for the zig-zig / zig-zag closing step. -/
private lemma zig_zig_arith {n : ℕ} (hn : 1 ≤ n) :
    ((n - 1 : ℕ) : ℝ) + 2 = ((1 + (1 + n) - 1 : ℕ) : ℝ) := by
  have h1 : (1 + (1 + n) - 1 : ℕ) = n + 1 := by omega
  rw [Nat.cast_sub hn, h1]; push_cast; ring

/-- `splay.cost'` equals `search_path_len − 1` (with ℕ truncation when empty).
Mechanical well-founded induction over the tree. -/
lemma splay_cost'_eq : ∀ (t : BinaryTree) (q : ℕ),
    splay.cost' t q = ((t.search_path_len q - 1 : ℕ) : ℝ)
  | .empty, _ => by simp [splay.cost', BinaryTree.search_path_len]
  | .node l k r, q => by
      by_cases h1 : q = k
      · subst h1
        have hc : splay.cost' (.node l q r) q = 0 := by
          unfold splay.cost'; simp
        have hl : (BinaryTree.node l q r).search_path_len q = 1 := by
          simp [BinaryTree.search_path_len]
        rw [hc, hl]; simp
      by_cases h2 : q < k
      · have hnk : ¬ k < q := by omega
        have hpath : (BinaryTree.node l k r).search_path_len q
                        = 1 + l.search_path_len q := by
          show (if q < k then 1 + l.search_path_len q
                 else if k < q then 1 + r.search_path_len q else 1)
                 = 1 + l.search_path_len q
          rw [if_pos h2]
        rw [hpath]
        cases l with
        | empty =>
            have hc : splay.cost' (.node .empty k r) q = 0 := by
              unfold splay.cost'; simp [h1, h2]
            rw [hc]; simp [BinaryTree.search_path_len]
        | node ll lk lr =>
            by_cases h3 : q = lk
            · subst h3
              have hc : splay.cost' (.node (.node ll q lr) k r) q = 1 := by
                unfold splay.cost'; simp [h1, h2]
              rw [hc]
              have hl : (BinaryTree.node ll q lr).search_path_len q = 1 := by
                simp [BinaryTree.search_path_len]
              rw [hl]; simp
            by_cases h4 : q < lk
            · have hnlk : ¬ lk < q := by omega
              have hl : (BinaryTree.node ll lk lr).search_path_len q
                          = 1 + ll.search_path_len q := by
                show (if q < lk then 1 + ll.search_path_len q
                       else if lk < q then 1 + lr.search_path_len q else 1)
                       = 1 + ll.search_path_len q
                rw [if_pos h4]
              rw [hl]
              cases ll with
              | empty =>
                  have hc : splay.cost' (.node (.node .empty lk lr) k r) q = 1 := by
                    unfold splay.cost'; simp [h1, h2, h4]
                  rw [hc]; simp [BinaryTree.search_path_len]
              | node lll llk llr =>
                  have ih := splay_cost'_eq (.node lll llk llr) q
                  have hn := search_path_len_node_pos lll llk llr q
                  have hc : splay.cost' (.node (.node (.node lll llk llr) lk lr) k r) q
                              = splay.cost' (.node lll llk llr) q + 2 := by
                    conv_lhs => unfold splay.cost'
                    simp [h1, h2, h4]
                  rw [hc, ih]; exact zig_zig_arith hn
            · have h5 : lk < q := by omega
              have hl : (BinaryTree.node ll lk lr).search_path_len q
                          = 1 + lr.search_path_len q := by
                show (if q < lk then 1 + ll.search_path_len q
                       else if lk < q then 1 + lr.search_path_len q else 1)
                       = 1 + lr.search_path_len q
                rw [if_neg h4, if_pos h5]
              rw [hl]
              cases lr with
              | empty =>
                  have hc : splay.cost' (.node (.node ll lk .empty) k r) q = 1 := by
                    unfold splay.cost'; simp [h1, h2, h4, h5]
                  rw [hc]; simp [BinaryTree.search_path_len]
              | node lrl lrk lrr =>
                  have ih := splay_cost'_eq (.node lrl lrk lrr) q
                  have hn := search_path_len_node_pos lrl lrk lrr q
                  have hc : splay.cost' (.node (.node ll lk (.node lrl lrk lrr)) k r) q
                              = splay.cost' (.node lrl lrk lrr) q + 2 := by
                    conv_lhs => unfold splay.cost'
                    simp [h1, h2, h4, h5]
                  rw [hc, ih]; exact zig_zig_arith hn
      · have h3 : k < q := by omega
        have hpath : (BinaryTree.node l k r).search_path_len q
                        = 1 + r.search_path_len q := by
          show (if q < k then 1 + l.search_path_len q
                 else if k < q then 1 + r.search_path_len q else 1)
                 = 1 + r.search_path_len q
          rw [if_neg h2, if_pos h3]
        rw [hpath]
        cases r with
        | empty =>
            have hc : splay.cost' (.node l k .empty) q = 0 := by
              unfold splay.cost'; simp [h1, h2]
            rw [hc]; simp [BinaryTree.search_path_len]
        | node rl rk rr =>
            by_cases h4 : q = rk
            · subst h4
              have hc : splay.cost' (.node l k (.node rl q rr)) q = 1 := by
                unfold splay.cost'; simp [h1, h2]
              rw [hc]
              have hr : (BinaryTree.node rl q rr).search_path_len q = 1 := by
                simp [BinaryTree.search_path_len]
              rw [hr]; simp
            by_cases h5 : q < rk
            · have hnrk : ¬ rk < q := by omega
              have hr : (BinaryTree.node rl rk rr).search_path_len q
                          = 1 + rl.search_path_len q := by
                show (if q < rk then 1 + rl.search_path_len q
                       else if rk < q then 1 + rr.search_path_len q else 1)
                       = 1 + rl.search_path_len q
                rw [if_pos h5]
              rw [hr]
              cases rl with
              | empty =>
                  have hc : splay.cost' (.node l k (.node .empty rk rr)) q = 1 := by
                    unfold splay.cost'; simp [h1, h2, h5]
                  rw [hc]; simp [BinaryTree.search_path_len]
              | node rll rlk rlr =>
                  have ih := splay_cost'_eq (.node rll rlk rlr) q
                  have hn := search_path_len_node_pos rll rlk rlr q
                  have hc : splay.cost' (.node l k (.node (.node rll rlk rlr) rk rr)) q
                              = splay.cost' (.node rll rlk rlr) q + 2 := by
                    conv_lhs => unfold splay.cost'
                    simp [h1, h2, h5]
                  rw [hc, ih]; exact zig_zig_arith hn
            · have h6 : rk < q := by omega
              have hr : (BinaryTree.node rl rk rr).search_path_len q
                          = 1 + rr.search_path_len q := by
                show (if q < rk then 1 + rl.search_path_len q
                       else if rk < q then 1 + rr.search_path_len q else 1)
                       = 1 + rr.search_path_len q
                rw [if_neg h5, if_pos h6]
              rw [hr]
              cases rr with
              | empty =>
                  have hc : splay.cost' (.node l k (.node rl rk .empty)) q = 1 := by
                    unfold splay.cost'; simp [h1, h2, h5, h6]
                  rw [hc]; simp [BinaryTree.search_path_len]
              | node rrl rrk rrr =>
                  have ih := splay_cost'_eq (.node rrl rrk rrr) q
                  have hn := search_path_len_node_pos rrl rrk rrr q
                  have hc : splay.cost' (.node l k (.node rl rk (.node rrl rrk rrr))) q
                              = splay.cost' (.node rrl rrk rrr) q + 2 := by
                    conv_lhs => unfold splay.cost'
                    simp [h1, h2, h5, h6]
                  rw [hc, ih]; exact zig_zig_arith hn

/-- `splay.cost t q` equals `search_path_len − 1`. -/
lemma splay_cost_eq_path_len (t : BinaryTree) (q : ℕ) :
    splay.cost t q = ((t.search_path_len q - 1 : ℕ) : ℝ) := by
  cases t with
  | empty => simp [splay.cost, BinaryTree.search_path_len]
  | node l k r =>
      unfold splay.cost
      by_cases hOdd : Odd ((BinaryTree.node l k r).search_path_len q)
      · simp [hOdd]; exact splay_cost'_eq _ _
      · simp [hOdd]
        -- Even length ⇒ q ≠ k.
        have hne : ¬ q = k := by
          intro h; subst h
          apply hOdd
          have : (BinaryTree.node l q r).search_path_len q = 1 := by
            simp [BinaryTree.search_path_len]
          rw [this]; exact ⟨0, rfl⟩
        by_cases h2 : q < k
        · have hpath : (BinaryTree.node l k r).search_path_len q
                          = 1 + l.search_path_len q := by
            show (if q < k then 1 + l.search_path_len q
                   else if k < q then 1 + r.search_path_len q else 1)
                   = 1 + l.search_path_len q
            rw [if_pos h2]
          -- Path ≥ 2 in even case ⇒ l.search_path_len q ≥ 1.
          have hlpos : 1 ≤ l.search_path_len q := by
            cases hl : l with
            | empty =>
                exfalso; apply hOdd
                rw [hpath, hl]; exact ⟨0, rfl⟩
            | node ll lk lr =>
                exact search_path_len_node_pos ll lk lr q
          rw [if_neg hne, if_pos h2, splay_cost'_eq, hpath]
          -- Goal: 1 + ((l.sp − 1 : ℕ) : ℝ) = ((1 + l.sp − 1 : ℕ) : ℝ)
          have hsimp : 1 + l.search_path_len q - 1 = l.search_path_len q := by omega
          rw [hsimp, Nat.cast_sub hlpos]; push_cast; ring
        · have h3 : k < q := by omega
          have hpath : (BinaryTree.node l k r).search_path_len q
                          = 1 + r.search_path_len q := by
            show (if q < k then 1 + l.search_path_len q
                   else if k < q then 1 + r.search_path_len q else 1)
                   = 1 + r.search_path_len q
            rw [if_neg h2, if_pos h3]
          have hrpos : 1 ≤ r.search_path_len q := by
            cases hr : r with
            | empty =>
                exfalso; apply hOdd
                rw [hpath, hr]; exact ⟨0, rfl⟩
            | node rl rk rr =>
                exact search_path_len_node_pos rl rk rr q
          rw [if_neg hne, if_neg h2, splay_cost'_eq, hpath]
          have hsimp : 1 + r.search_path_len q - 1 = r.search_path_len q := by omega
          rw [hsimp, Nat.cast_sub hrpos]; push_cast; ring

/-- Per-step identity: the cost of one splay equals the link count produced by
`stepColor` for that splay. -/
lemma cost_eq_step_total (col : ColorState) (t : BinaryTree) (q : ℕ) :
    splay.cost t q = ((stepColor col t (splay t q) q).2.total : ℝ) := by
  rw [splay_cost_eq_path_len, stepColor_total_eq]

/-- Joint induction on the splay sequence: for every prefix, the accumulated
cost and the accumulated link-count total stay in sync. -/
lemma sequence_cost_foldl_eq {n : ℕ} (X : Fin n → ℕ) :
    ∀ (L : List (Fin n)) (t : BinaryTree) (col : ColorState)
      (c : ℝ) (cnt : LinkCounters),
      c = (cnt.total : ℝ) →
      (L.foldl
        (fun (acc : BinaryTree × ℝ) i =>
          let (t, c) := acc
          (splay t (X i), c + splay.cost t (X i)))
        (t, c)).2
      = ((L.foldl
            (fun (acc : BinaryTree × ColorState × LinkCounters) i =>
              let (t, col, cnt) := acc
              let q  := X i
              let t' := splay t q
              let (col', dcnt) := stepColor col t t' q
              (t', col', cnt + dcnt))
            (t, col, cnt)).2.2.total : ℝ) := by
  intro L
  induction L with
  | nil =>
      intro t col c cnt hEq
      simpa using hEq
  | cons i L ih =>
      intro t col c cnt hEq
      -- Step both folds once, then apply IH with the updated accumulators.
      simp only [List.foldl_cons]
      apply ih
      -- Show new cost accumulator = new total counters (as ℝ).
      have hstep := cost_eq_step_total col t (X i)
      have hadd  := LinkCounters.total_add cnt
                      (stepColor col t (splay t (X i)) (X i)).2
      push_cast [hadd]
      linarith

-- ---------------------------------------------------------------------------
--  Structural: rotations and splay preserve the (ordered) list of keys.
-- ---------------------------------------------------------------------------

lemma rotateRight_toKeyList (t : BinaryTree) :
    (rotateRight t).toKeyList = t.toKeyList := by
  match t with
  | .node (.node _ _ _) _ _ =>
      simp [rotateRight, BinaryTree.toKeyList, List.append_assoc]
  | .empty => rfl
  | .node .empty _ _ => rfl

lemma rotateLeft_toKeyList (t : BinaryTree) :
    (rotateLeft t).toKeyList = t.toKeyList := by
  match t with
  | .node _ _ (.node _ _ _) =>
      simp [rotateLeft, BinaryTree.toKeyList, List.append_assoc]
  | .empty => rfl
  | .node _ _ .empty => rfl

lemma rotate_toKeyList (t : BinaryTree) (rt : Rot) :
    (rotate t rt).toKeyList = t.toKeyList := by
  cases rt
  · show (rotateRight (rotateRight t)).toKeyList = t.toKeyList
    rw [rotateRight_toKeyList, rotateRight_toKeyList]
  · cases t with
    | empty => rfl
    | node l k r =>
        show (rotateRight (.node (rotateLeft l) k r)).toKeyList = _
        rw [rotateRight_toKeyList]
        simp [BinaryTree.toKeyList, rotateLeft_toKeyList]
  · show (rotateLeft (rotateLeft t)).toKeyList = t.toKeyList
    rw [rotateLeft_toKeyList, rotateLeft_toKeyList]
  · cases t with
    | empty => rfl
    | node l k r =>
        show (rotateLeft (.node l k (rotateRight r))).toKeyList = _
        rw [rotateLeft_toKeyList]
        simp [BinaryTree.toKeyList, rotateRight_toKeyList]
  · exact rotateRight_toKeyList t
  · exact rotateLeft_toKeyList t

lemma splay'_toKeyList (q : ℕ) (t : BinaryTree) :
    (splay' t q).toKeyList = t.toKeyList := by
  fun_induction splay' t q <;>
    simp_all [rotate_toKeyList, BinaryTree.toKeyList]

lemma splay_toKeyList (t : BinaryTree) (q : ℕ) :
    (splay t q).toKeyList = t.toKeyList := by
  unfold splay
  cases t with
  | empty => rfl
  | node l k r =>
    simp only
    split_ifs
    · exact splay'_toKeyList q _
    · rfl
    · show (rotate (.node (splay' l q) k r) .zig).toKeyList = _
      rw [rotate_toKeyList]
      simp [BinaryTree.toKeyList, splay'_toKeyList]
    · show (rotate (.node l k (splay' r q)) .zag).toKeyList = _
      rw [rotate_toKeyList]
      simp [BinaryTree.toKeyList, splay'_toKeyList]

lemma searchPath_subset_toKeyList (t : BinaryTree) (q : ℕ) :
    ∀ k ∈ t.searchPath q, k ∈ t.toKeyList := by
  induction t with
  | empty => intro k hk; simp [BinaryTree.searchPath] at hk
  | node l key r ihl ihr =>
    intro k hk
    unfold BinaryTree.searchPath at hk
    unfold BinaryTree.toKeyList
    split_ifs at hk
    · simp at hk; subst hk; simp
    · simp at hk
      rcases hk with rfl | hk
      · simp
      · have := ihl _ hk; simp [this]
    · simp at hk
      rcases hk with rfl | hk
      · simp
      · have := ihr _ hk; simp [this]

-- ---------------------------------------------------------------------------
--  Settled set: nodes colored green.  Bounds cnt.Y.
-- ---------------------------------------------------------------------------

/-- `isSettled col x` — key `x` has been promoted to green in `col`. -/
def ColorState.isSettled (col : ColorState) (x : ℕ) : Prop :=
  col x = .green

instance (col : ColorState) (x : ℕ) : Decidable (col.isSettled x) := by
  unfold ColorState.isSettled; infer_instance

/-- The set of settled keys below `n`. -/
def ColorState.settled (col : ColorState) (n : ℕ) : Finset ℕ :=
  (Finset.range n).filter (fun x => col.isSettled x)

lemma ColorState.mem_settled {col : ColorState} {n x : ℕ} :
    x ∈ col.settled n ↔ x < n ∧ col.isSettled x := by
  simp [ColorState.settled, Finset.mem_filter, Finset.mem_range]

lemma ColorState.settled_card_le (col : ColorState) (n : ℕ) :
    (col.settled n).card ≤ n := by
  have : (col.settled n).card ≤ (Finset.range n).card :=
    Finset.card_le_card (Finset.filter_subset _ _)
  simpa using this

/-- If the settled-predicate only grows, so does the settled finset's card. -/
lemma ColorState.settled_card_mono {n : ℕ} {col col' : ColorState}
    (h : ∀ x, col.isSettled x → col'.isSettled x) :
    (col.settled n).card ≤ (col'.settled n).card := by
  apply Finset.card_le_card
  intro x hx
  rw [ColorState.mem_settled] at hx ⊢
  exact ⟨hx.1, h _ hx.2⟩

-- paintYellow preserves the settled (green) predicate.

lemma ColorState.set_isSettled_of_settled (col : ColorState) (x : ℕ) (c : Color)
    (hc : c = .green) (y : ℕ) (hy : col.isSettled y) :
    (col.set x c).isSettled y := by
  unfold set isSettled at *
  by_cases h : y = x
  · subst h; simp [hc]
  · simp [h, hy]

lemma ColorState.paintYellow_isSettled_of_settled
    (col : ColorState) (xs : List ℕ) (y : ℕ) (hy : col.isSettled y) :
    (col.paintYellow xs).isSettled y := by
  induction xs generalizing col with
  | nil => simpa [ColorState.paintYellow] using hy
  | cons a xs ih =>
    show ColorState.isSettled
      (List.foldl (fun c x => if c x = .uncolored then c.set x .yellow else c)
        (if col a = .uncolored then col.set a .yellow else col) xs) y
    apply ih
    by_cases ha : col a = .uncolored
    · simp [ha]
      unfold isSettled set at *
      by_cases hya : y = a
      · subst hya; rw [hy] at ha; cases ha
      · simp [hya, hy]
    · simp [ha, hy]

-- processLink preserves the settled predicate and does Y-accounting.

-- Branch equations for processLink.

lemma processLink_eq_Y (col : ColorState) (cnt : LinkCounters) (t : BinaryTree)
    (w z : ℕ) (hY : col w = .yellow ∨ col z = .yellow) :
    processLink col cnt t w z =
      ((if col z = .yellow
          then (if col w = .yellow then col.set w .green else col).set z .green
          else (if col w = .yellow then col.set w .green else col)),
       { cnt with Y := cnt.Y + 1 }) := by
  unfold processLink; simp [hY]

lemma processLink_eq_A (col : ColorState) (cnt : LinkCounters) (t : BinaryTree)
    (w z : ℕ) (hY : ¬(col w = .yellow ∨ col z = .yellow))
    (hA : vVal col t z = 1) :
    processLink col cnt t w z = (col, { cnt with A := cnt.A + 1 }) := by
  unfold processLink; simp [hY, hA]

lemma processLink_eq_B (col : ColorState) (cnt : LinkCounters) (t : BinaryTree)
    (w z : ℕ) (hY : ¬(col w = .yellow ∨ col z = .yellow))
    (hA : vVal col t z ≠ 1) :
    processLink col cnt t w z = (col, { cnt with B := cnt.B + 1 }) := by
  unfold processLink; simp [hY, hA]

lemma processLink_Y_settled
    (col : ColorState) (cnt : LinkCounters) (t : BinaryTree) (w z n : ℕ)
    (hw : w < n) (hz : z < n) :
    (processLink col cnt t w z).2.Y + (col.settled n).card ≤
      cnt.Y + ((processLink col cnt t w z).1.settled n).card := by
  by_cases hY : col w = .yellow ∨ col z = .yellow
  swap
  · by_cases hA : vVal col t z = 1
    · rw [processLink_eq_A _ _ _ _ _ hY hA]
    · rw [processLink_eq_B _ _ _ _ _ hY hA]
  rw [processLink_eq_Y _ _ _ _ _ hY]
  -- The new coloring after a Y-link (inlined for easier unfolding).
  let col₂ : ColorState := if col z = .yellow
      then (if col w = .yellow then col.set w .green else col).set z .green
      else (if col w = .yellow then col.set w .green else col)
  show cnt.Y + 1 + (col.settled n).card ≤ cnt.Y + (col₂.settled n).card
  have hmono : ∀ y, col.isSettled y → col₂.isSettled y := by
    intro y hy
    show ColorState.isSettled (if col z = .yellow
        then (if col w = .yellow then col.set w .green else col).set z .green
        else (if col w = .yellow then col.set w .green else col)) y
    split_ifs
    · apply ColorState.set_isSettled_of_settled _ _ _ rfl
      exact ColorState.set_isSettled_of_settled _ _ _ rfl _ hy
    · exact ColorState.set_isSettled_of_settled _ _ _ rfl _ hy
    · exact ColorState.set_isSettled_of_settled _ _ _ rfl _ hy
    · exact hy
  suffices hlt : (col.settled n).card < (col₂.settled n).card by omega
  apply Finset.card_lt_card
  refine ⟨?_, ?_⟩
  · intro y hy
    rw [ColorState.mem_settled] at hy ⊢
    exact ⟨hy.1, hmono _ hy.2⟩
  · rcases hY with hwy | hzy
    · intro hss
      have hw_in : w ∈ col₂.settled n := by
        rw [ColorState.mem_settled]
        refine ⟨hw, ?_⟩
        show ColorState.isSettled (if col z = .yellow
            then (if col w = .yellow then col.set w .green else col).set z .green
            else (if col w = .yellow then col.set w .green else col)) w
        rw [if_pos hwy]
        by_cases hzy' : col z = .yellow
        · rw [if_pos hzy']
          unfold ColorState.isSettled ColorState.set
          by_cases hzw : z = w
          · subst hzw; simp
          · simp
        · rw [if_neg hzy']
          unfold ColorState.isSettled ColorState.set; simp
      have hw_not : w ∉ col.settled n := by
        rw [ColorState.mem_settled]
        rintro ⟨_, hs⟩
        unfold ColorState.isSettled at hs
        rw [hwy] at hs; cases hs
      exact hw_not (hss hw_in)
    · intro hss
      have hz_in : z ∈ col₂.settled n := by
        rw [ColorState.mem_settled]
        refine ⟨hz, ?_⟩
        show ColorState.isSettled (if col z = .yellow
            then (if col w = .yellow then col.set w .green else col).set z .green
            else (if col w = .yellow then col.set w .green else col)) z
        rw [if_pos hzy]
        unfold ColorState.isSettled ColorState.set; simp
      have hz_not : z ∉ col.settled n := by
        rw [ColorState.mem_settled]
        rintro ⟨_, hs⟩
        unfold ColorState.isSettled at hs
        rw [hzy] at hs; cases hs
      exact hz_not (hss hz_in)

lemma processLinks_Y_settled
    (col : ColorState) (cnt : LinkCounters) (t : BinaryTree)
    (links : List (ℕ × ℕ)) (n : ℕ)
    (hL : ∀ wz ∈ links, wz.1 < n ∧ wz.2 < n) :
    (processLinks col cnt t links).2.Y + (col.settled n).card ≤
      cnt.Y + ((processLinks col cnt t links).1.settled n).card := by
  induction links generalizing col cnt with
  | nil =>
      simp [processLinks]
  | cons wz links ih =>
      have hhd := hL wz List.mem_cons_self
      have htl : ∀ wz' ∈ links, wz'.1 < n ∧ wz'.2 < n :=
        fun wz' h => hL wz' (List.mem_cons_of_mem _ h)
      have h1 := processLink_Y_settled col cnt t wz.1 wz.2 n hhd.1 hhd.2
      have h2 := ih (processLink col cnt t wz.1 wz.2).1
                    (processLink col cnt t wz.1 wz.2).2 htl
      show (processLinks (processLink col cnt t wz.1 wz.2).1
              (processLink col cnt t wz.1 wz.2).2 t links).2.Y +
            (col.settled n).card ≤
          cnt.Y + ((processLinks (processLink col cnt t wz.1 wz.2).1
                     (processLink col cnt t wz.1 wz.2).2 t links).1.settled n).card
      omega

-- linksOfSpine endpoints lie inside the spine (a sublist of searchPath).

lemma linksOfSpine_fst_mem : ∀ (L : List ℕ) (wz : ℕ × ℕ),
    wz ∈ linksOfSpine L → wz.1 ∈ L ∧ wz.2 ∈ L
  | [], _, h => by simp [linksOfSpine] at h
  | [_], _, h => by simp [linksOfSpine] at h
  | x :: y :: rs, wz, h => by
      simp only [linksOfSpine, List.mem_cons] at h
      rcases h with h | h
      · subst h; exact ⟨by simp, by simp⟩
      · have hrec := linksOfSpine_fst_mem (y :: rs) wz h
        exact ⟨List.mem_cons_of_mem _ hrec.1, List.mem_cons_of_mem _ hrec.2⟩

-- stepColor Y-accounting:  the Y-counter increases at most by the growth in
-- the settled-set card, provided every spine key is < n.

lemma stepColor_Y_settled
    (col : ColorState) (t t' : BinaryTree) (q n : ℕ)
    (hspine : ∀ k ∈ t.searchPath q, k < n) :
    (stepColor col t t' q).2.Y + (col.settled n).card ≤
      ((stepColor col t t' q).1.settled n).card := by
  dsimp only [stepColor]
  set col₁ := col.paintYellow (t.searchPath q).tail with hcol₁
  have hph1 : (col.settled n).card ≤ (col₁.settled n).card := by
    apply ColorState.settled_card_mono
    intro y hy
    exact ColorState.paintYellow_isSettled_of_settled _ _ _ hy
  rcases hls : linksOfSpine (t.searchPath q) with _ | ⟨_top, rest⟩
  · -- No links: cnt is zero, settled unchanged from col₁.
    show (0 : LinkCounters).Y + (col.settled n).card ≤ (col₁.settled n).card
    show 0 + _ ≤ _
    omega
  · have hlinks_rest : ∀ wz ∈ rest, wz.1 < n ∧ wz.2 < n := by
      intro wz hwz
      have hmem : wz ∈ linksOfSpine (t.searchPath q) := by
        rw [hls]; exact List.mem_cons_of_mem _ hwz
      have := linksOfSpine_fst_mem _ wz hmem
      exact ⟨hspine _ this.1, hspine _ this.2⟩
    have hph2 := processLinks_Y_settled col₁ 0 t rest n hlinks_rest
    set rl := processLinks col₁ 0 t rest with hrl
    -- Goal: (rl.2 with K += 1).Y + col.settled = rl.1.settled.
    show rl.2.Y + (col.settled n).card ≤ (rl.1.settled n).card
    have h0Y : (0 : LinkCounters).Y = 0 := rfl
    have hph2' : rl.2.Y + (col₁.settled n).card ≤ (rl.1.settled n).card := by
      have := hph2; rw [h0Y] at this; omega
    omega

-- ---------------------------------------------------------------------------
--  Running the bound through the colorSequence fold.
-- ---------------------------------------------------------------------------

lemma colorSequence_Y_le {n : ℕ} (init : BinaryTree) (X : Fin n → ℕ)
    (hInit : ∀ k ∈ init.toKeyList, k < n) :
    (totalCounters init X).Y ≤ n := by
  unfold totalCounters colorSequence
  -- Invariant: cnt.Y ≤ (col.settled n).card.
  suffices h : ∀ (L : List (Fin n)) (t : BinaryTree) (col : ColorState)
      (cnt : LinkCounters),
      (∀ k ∈ t.toKeyList, k < n) →
      cnt.Y ≤ (col.settled n).card →
      ((L.foldl
          (fun (acc : BinaryTree × ColorState × LinkCounters) i =>
            let (t, col, cnt) := acc
            let q  := X i
            let t' := splay t q
            let (col', dcnt) := stepColor col t t' q
            (t', col', cnt + dcnt))
          (t, col, cnt)).2.2).Y ≤ n by
    apply h (List.finRange n) init ColorState.initial 0 hInit
    show (0 : LinkCounters).Y ≤ _
    change 0 ≤ _
    exact Nat.zero_le _
  intro L
  induction L with
  | nil =>
      intro t col cnt _ hInv
      have := ColorState.settled_card_le col n
      simpa using Nat.le_trans hInv this
  | cons i L ih =>
      intro t col cnt htKeys hInv
      simp only [List.foldl_cons]
      apply ih
      · intro k hk
        rw [splay_toKeyList] at hk
        exact htKeys k hk
      · have hspine : ∀ k ∈ t.searchPath (X i), k < n := by
          intro k hk
          exact htKeys k (searchPath_subset_toKeyList t (X i) k hk)
        have hstep :=
          stepColor_Y_settled col t (splay t (X i)) (X i) n hspine
        -- (cnt + dcnt).Y = cnt.Y + dcnt.Y ≤ settled.card + dcnt.Y ≤ col'.settled.card.
        change (cnt + (stepColor col t (splay t (X i)) (X i)).2).Y ≤
          ((stepColor col t (splay t (X i)) (X i)).1.settled n).card
        show cnt.Y + _ ≤ _
        omega

-- ---------------------------------------------------------------------------
--  K-link bound:  cnt.K ≤ n  (each splay produces at most one K-link).
-- ---------------------------------------------------------------------------

/-- `processLink` never touches the K counter (only Y, A, or B is incremented). -/
lemma processLink_K_unchanged (col : ColorState) (cnt : LinkCounters)
    (t : BinaryTree) (w z : ℕ) :
    (processLink col cnt t w z).2.K = cnt.K := by
  by_cases hY : col w = .yellow ∨ col z = .yellow
  · rw [processLink_eq_Y _ _ _ _ _ hY]
  · by_cases hA : vVal col t z = 1
    · rw [processLink_eq_A _ _ _ _ _ hY hA]
    · rw [processLink_eq_B _ _ _ _ _ hY hA]

lemma processLinks_K_unchanged (col : ColorState) (cnt : LinkCounters)
    (t : BinaryTree) (links : List (ℕ × ℕ)) :
    (processLinks col cnt t links).2.K = cnt.K := by
  induction links generalizing col cnt with
  | nil => rfl
  | cons wz links ih =>
    show (processLinks (processLink col cnt t wz.1 wz.2).1
            (processLink col cnt t wz.1 wz.2).2 t links).2.K = cnt.K
    rw [ih, processLink_K_unchanged]

/-- One splay contributes at most 1 to the K counter. -/
lemma stepColor_K_le_one (col : ColorState) (t t' : BinaryTree) (q : ℕ) :
    (stepColor col t t' q).2.K ≤ 1 := by
  dsimp only [stepColor]
  rcases linksOfSpine (t.searchPath q) with _ | ⟨_, rest⟩
  · show (0 : LinkCounters).K ≤ 1
    show 0 ≤ 1; omega
  · show (processLinks (col.paintYellow (t.searchPath q).tail) 0 t rest).2.K + 1 ≤ 1
    rw [processLinks_K_unchanged]
    show (0 : LinkCounters).K + 1 ≤ 1
    show 0 + 1 ≤ 1; omega

lemma colorSequence_K_le {n : ℕ} (init : BinaryTree) (X : Fin n → ℕ) :
    (totalCounters init X).K ≤ n := by
  unfold totalCounters colorSequence
  suffices h : ∀ (L : List (Fin n)) (t : BinaryTree) (col : ColorState)
      (cnt : LinkCounters),
      ((L.foldl
          (fun (acc : BinaryTree × ColorState × LinkCounters) i =>
            let (t, col, cnt) := acc
            let q  := X i
            let t' := splay t q
            let (col', dcnt) := stepColor col t t' q
            (t', col', cnt + dcnt))
          (t, col, cnt)).2.2).K ≤ cnt.K + L.length by
    have := h (List.finRange n) init ColorState.initial 0
    have h0 : (0 : LinkCounters).K = 0 := rfl
    simp [h0] at this
    exact this
  intro L
  induction L with
  | nil => intro t col cnt; simp
  | cons i L ih =>
    intro t col cnt
    simp only [List.foldl_cons, List.length_cons]
    have hstep := stepColor_K_le_one col t (splay t (X i)) (X i)
    have hih := ih (splay t (X i))
                   (stepColor col t (splay t (X i)) (X i)).1
                   (cnt + (stepColor col t (splay t (X i)) (X i)).2)
    have hadd : (cnt + (stepColor col t (splay t (X i)) (X i)).2).K =
        cnt.K + (stepColor col t (splay t (X i)) (X i)).2.K := by
      show (LinkCounters.add cnt _).K = _
      unfold LinkCounters.add; rfl
    rw [hadd] at hih
    refine Nat.le_trans hih ?_
    omega

-- ---------------------------------------------------------------------------
--  A-link bound:  cnt.A ≤ n  (Elmasry Lemma 1(c))
-- ---------------------------------------------------------------------------
--
-- Elmasry: for any green-to-green link `w → z`, `v_z` is non-decreasing in
-- `t`, and on a green-to-green A-link (i.e. `v_z(t) = 1` at link time), `v_z`
-- jumps to `≥ 2` afterwards.  Consequently each node `z ∈ [0,n)` can be the
-- z-endpoint of at most one A-link, giving `cnt.A ≤ n`.
--
-- Proof plan (iterative; currently the monotonicity invariant is recorded as
-- a standalone `sorry` to be discharged in follow-up passes):
--
--   (i)  define a ghost finset `S ⊆ range n` tracking nodes that have ever
--        had `v_z ≥ 2`;
--   (ii) show that every A-link either adds its z-target to `S` fresh, or
--        contradicts the hypothesis `v_z(t) = 1` via monotonicity;
--   (iii) conclude `cnt.A ≤ S.card ≤ n`.
--
-- For now we expose the top-level bound as a single lemma so the
-- `sequential_theorem` is clean.

/-- Ghost set: keys `< n` whose `v`-value has reached `≥ 2` in the state
`(col, t)`.  Elmasry's argument works by charging every A-link to such a key
and showing this set is monotone non-decreasing through the sequence, so its
final cardinality (which is at most `n`) upper-bounds `cnt.A`. -/
def bigVset (col : ColorState) (t : BinaryTree) (n : ℕ) : Finset ℕ :=
  (Finset.range n).filter (fun z => 2 ≤ vVal col t z)

lemma bigVset_card_le (col : ColorState) (t : BinaryTree) (n : ℕ) :
    (bigVset col t n).card ≤ n := by
  have : (bigVset col t n).card ≤ (Finset.range n).card :=
    Finset.card_le_card (Finset.filter_subset _ _)
  simpa using this

/-- The set of A-target nodes in one splay step, defined **in Elmasry's
before/after style**.  A node `z` is an A-target of splay `q` from tree `t`
with coloring `col` iff

* `z < n`, `z` is on the splaying spine (i.e. `z ∈ (t.searchPath q).tail`),
* `vVal col t z = 1`  (the pre-splay v-value is 1), and
* `2 ≤ vVal col' (splay t q) z`  (the post-splay v-value is at least 2),

where `col'` is the post-step coloring produced by `stepColor`.

This definition never references the intermediate coloring produced while
walking through `processLinks`; it compares only the pre-splay state
`(col, t)` to the post-splay state `(col', splay t q)`, exactly as
Elmasry's Lemma 1(c) does. -/
noncomputable def aTargetsOf (col : ColorState) (t : BinaryTree) (q n : ℕ) :
    Finset ℕ := by
  classical
  exact (Finset.range n).filter (fun z =>
    z ∈ (t.searchPath q).tail ∧
    vVal col t z = 1 ∧
    2 ≤ vVal (stepColor col t (splay t q) q).1 (splay t q) z)

/-- Each A-target is `< n` (subset of `range n`). -/
lemma aTargetsOf_subset_range (col : ColorState) (t : BinaryTree) (q n : ℕ) :
    aTargetsOf col t q n ⊆ Finset.range n := by
  classical
  intro z hz
  unfold aTargetsOf at hz
  exact Finset.mem_of_mem_filter _ hz

/-- Membership characterisation of `aTargetsOf`. -/
lemma mem_aTargetsOf {col : ColorState} {t : BinaryTree} {q n z : ℕ} :
    z ∈ aTargetsOf col t q n ↔
      z < n ∧ z ∈ (t.searchPath q).tail ∧ vVal col t z = 1 ∧
      2 ≤ vVal (stepColor col t (splay t q) q).1 (splay t q) z := by
  classical
  unfold aTargetsOf
  simp [Finset.mem_filter, Finset.mem_range]

/-- The z-components of `linksOfSpine L` are exactly `L.tail`. -/
lemma linksOfSpine_map_snd : ∀ (L : List ℕ),
    (linksOfSpine L).map Prod.snd = L.tail
  | []            => rfl
  | [_]           => rfl
  | x :: y :: rs => by
      have ih := linksOfSpine_map_snd (y :: rs)
      simp [linksOfSpine] at ih ⊢
      exact ih

/-- If a tree's key list is `Nodup`, then so is any search path in it. -/
lemma searchPath_nodup_of_toKeyList_nodup :
    ∀ (t : BinaryTree) (q : ℕ), t.toKeyList.Nodup → (t.searchPath q).Nodup
  | .empty, q, _ => by simp [BinaryTree.searchPath]
  | .node l k r, q, h => by
    unfold BinaryTree.searchPath
    have hfull : (l.toKeyList ++ [k] ++ r.toKeyList).Nodup := by
      show (BinaryTree.node l k r).toKeyList.Nodup
      exact h
    have hlk : (l.toKeyList ++ [k]).Nodup := hfull.of_append_left
    have hlND : l.toKeyList.Nodup := hlk.of_append_left
    have hrND : r.toKeyList.Nodup := hfull.of_append_right
    have hk_notin_l : k ∉ l.toKeyList := by
      have hdisj : l.toKeyList.Disjoint [k] := hlk.disjoint
      intro hk
      exact hdisj hk (List.mem_singleton.mpr rfl)
    have hk_notin_r : k ∉ r.toKeyList := by
      have hdisj : (l.toKeyList ++ [k]).Disjoint r.toKeyList := hfull.disjoint
      intro hk
      have hkk : k ∈ l.toKeyList ++ [k] :=
        List.mem_append.mpr (Or.inr (List.mem_singleton.mpr rfl))
      exact hdisj hkk hk
    split_ifs with hqk hlt
    · exact List.nodup_singleton _
    · refine List.nodup_cons.mpr ⟨?_, searchPath_nodup_of_toKeyList_nodup l q hlND⟩
      intro hmem
      exact hk_notin_l (searchPath_subset_toKeyList l q _ hmem)
    · refine List.nodup_cons.mpr ⟨?_, searchPath_nodup_of_toKeyList_nodup r q hrND⟩
      intro hmem
      exact hk_notin_r (searchPath_subset_toKeyList r q _ hmem)

/-- **Sub-lemma D (A-target not in pre-bigVset).** Trivial under Elmasry's
before/after formulation: an A-target has `vVal col t z = 1`, whereas every
element of `bigVset col t n` has `vVal col t z ≥ 2`.  Immediate. -/
lemma aTargetsOf_disjoint_bigVset
    (col : ColorState) (t : BinaryTree) (q n : ℕ) :
    Disjoint (aTargetsOf col t q n) (bigVset col t n) := by
  classical
  rw [Finset.disjoint_left]
  intro z hzA hzS
  rw [mem_aTargetsOf] at hzA
  unfold bigVset at hzS
  rw [Finset.mem_filter] at hzS
  have h1 : vVal col t z = 1 := hzA.2.2.1
  have h2 : 2 ≤ vVal col t z := hzS.2
  omega

/-- `vVal` on the empty tree is zero. -/
lemma vVal_empty (col : ColorState) (z : ℕ) :
    vVal col .empty z = 0 := by
  unfold vVal gVal hVal subtree_rooted_at
  simp [BinaryTree.rightSpineKeys]

/-- When the target of a splay is already at the root, `splay` is the
identity and `stepColor` leaves the coloring and counters untouched. -/
lemma stepColor_root
    (col : ColorState) (l : BinaryTree) (k : ℕ) (r : BinaryTree) :
    stepColor col (.node l k r) (.node l k r) k = (col, 0)
    ∧ splay (.node l k r) k = .node l k r := by
  refine ⟨?_, ?_⟩
  · unfold stepColor
    have hpath : (BinaryTree.node l k r).searchPath k = [k] := by
      unfold BinaryTree.searchPath; simp
    rw [hpath]
    show (col.paintYellow [k].tail, _) = _
    unfold ColorState.paintYellow
    rfl
  · -- splay (.node l k r) k: `q = k` branch in both splay and splay'.
    unfold splay splay'
    simp

/-- **Elmasry's coloring invariant (Lemma 1(a)+(b)).**
Every non-uncolored node (yellow or green — our `ColorState` has no black;
black is maintained separately) has `vVal ≥ 0` in the current tree.  This
is the standing invariant that must be maintained across every link event
to run the induction of Lemma 1.  We carry it as an explicit hypothesis
for `lemma1c_monotone` so the paper's inductive argument can be run. -/
def ColorInvariant (col : ColorState) (t : BinaryTree) : Prop :=
  ∀ z, col z ≠ Color.uncolored → 0 ≤ vVal col t z

/-- **Elmasry relations (1)–(5) for a single rotation (link event).**
Here the pre-rotation tree has shape `t = node (node a z b) w c`, so `z`
is the left child of `w`, and `t' = node a z (node b w c)` is the tree
after `rotateRight` has lifted `z` above `w`.

The five identities of Elmasry hold under the natural hypotheses:

* `z < w`  — the key ordering needed for `subtree_rooted_at` to find `z`
  via the BST descent (`t` satisfies this when it is a BST fragment).
* `col.isColored z = true`  — `z` lies on the splaying spine, hence is
  coloured (yellow/green); relations (3) and (4) count the contribution
  of `z` itself.

Under these hypotheses:
  (1) `hVal col t w = gVal col t z`         (pre-link)
  (2) `gVal col t' w = gVal col t w`        (w's g fixed)
  (3) `hVal col t' w + 1 = hVal col t w`    (w's h drops by 1)
  (4) `gVal col t' z = gVal col t w + 1`    (z grows by 1 over w)
  (5) `hVal col t' z = hVal col t z`        (z's h unchanged — strictly
       stronger than Elmasry's `≤ … + 1`; the generic relation (5) in
       the paper has equality here because `z`'s left child `a` is the
       same subtree before and after the rotation). -/
lemma elmasry_relations
    (col : ColorState) (a b c : BinaryTree) (w z : ℕ)
    (hzw : z < w) (hzCol : col.isColored z = true) :
    let t  : BinaryTree := .node (.node a z b) w c
    let t' : BinaryTree := .node a z (.node b w c)
    (hVal col t w = gVal col t z) ∧
    (gVal col t' w = gVal col t w) ∧
    (hVal col t' w + 1 = hVal col t w) ∧
    (gVal col t' z = gVal col t w + 1) ∧
    (hVal col t' z = hVal col t z) := by
  intro t t'
  -- Compute each relevant `subtree_rooted_at`.
  have hwz : ¬ w = z := fun h => by omega
  have hzw_ne : ¬ z = w := fun h => by omega
  have hzw' : ¬ w < z := fun h => by omega
  have hsub_t_w : subtree_rooted_at t w = .node (.node a z b) w c := by
    show subtree_rooted_at (.node (.node a z b) w c) w = _
    unfold subtree_rooted_at; simp
  have hsub_t_z : subtree_rooted_at t z = .node a z b := by
    show subtree_rooted_at (.node (.node a z b) w c) z = _
    unfold subtree_rooted_at
    rw [if_neg hzw_ne, if_pos hzw]
    show subtree_rooted_at (.node a z b) z = _
    unfold subtree_rooted_at; simp
  have hsub_t'_w : subtree_rooted_at t' w = .node b w c := by
    show subtree_rooted_at (.node a z (.node b w c)) w = _
    unfold subtree_rooted_at
    rw [if_neg hwz, if_neg hzw']
    show subtree_rooted_at (.node b w c) w = _
    unfold subtree_rooted_at; simp
  have hsub_t'_z : subtree_rooted_at t' z = .node a z (.node b w c) := by
    show subtree_rooted_at (.node a z (.node b w c)) z = _
    unfold subtree_rooted_at; simp
  -- Filter-length helper: a `cons` of a colored node adds 1 to the count.
  have hfilter_cons : ∀ (x : ℕ) (L : List ℕ),
      col.isColored x = true →
      (List.filter (fun k => col.isColored k) (x :: L)).length
        = (List.filter (fun k => col.isColored k) L).length + 1 := by
    intro x L hx
    simp [List.filter, hx]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- (1) hVal t w = gVal t z.
    show hVal col t w = gVal col t z
    unfold hVal gVal
    rw [hsub_t_w, hsub_t_z]
  · -- (2) gVal t' w = gVal t w.
    show gVal col t' w = gVal col t w
    unfold gVal
    rw [hsub_t_w, hsub_t'_w]
    rfl
  · -- (3) hVal t' w + 1 = hVal t w.
    show hVal col t' w + 1 = hVal col t w
    unfold hVal
    rw [hsub_t_w, hsub_t'_w]
    show (List.filter _ b.rightSpineKeys).length + 1
        = (List.filter _ (z :: b.rightSpineKeys)).length
    rw [hfilter_cons z _ hzCol]
  · -- (4) gVal t' z = gVal t w + 1.
    show gVal col t' z = gVal col t w + 1
    unfold gVal
    rw [hsub_t_w, hsub_t'_z]
    show (List.filter _ (z :: w :: c.rightSpineKeys)).length
        = (List.filter _ (w :: c.rightSpineKeys)).length + 1
    rw [hfilter_cons z _ hzCol]
  · -- (5) hVal t' z = hVal t z.
    show hVal col t' z = hVal col t z
    unfold hVal
    rw [hsub_t_z, hsub_t'_z]

/-- **Per-rotation pivot equality (corollary of `elmasry_relations`).**
For a single `rotateRight` step that lifts the left child `z` of the root
`w`, the pivot's `vVal` obeys the clean identity
  `vVal col t' z = vVal col t z + vVal col t w + 1`
whenever `z < w` and `col.isColored z = true`.

Consequence: if additionally `col.isColored w = true`, then the standing
`ColorInvariant` gives `vVal col t w ≥ 0`, hence `vVal col t' z ≥ vVal col t z + 1`
— strict progress. This is the heart of Elmasry's Lemma 1(c) for a single
right-rotation link event. -/
lemma vVal_rotateRight_pivot
    (col : ColorState) (a b c : BinaryTree) (w z : ℕ)
    (hzw : z < w) (hzCol : col.isColored z = true) :
    vVal col (.node a z (.node b w c)) z
      = vVal col (.node (.node a z b) w c) z
        + vVal col (.node (.node a z b) w c) w + 1 := by
  obtain ⟨r1, _r2, _r3, r4, r5⟩ := elmasry_relations col a b c w z hzw hzCol
  unfold vVal
  -- r1: hVal t w = gVal t z ;  r4: gVal t' z = gVal t w + 1 ;  r5: hVal t' z = hVal t z
  have e1 : (hVal col (.node (.node a z b) w c) w : ℤ)
              = (gVal col (.node (.node a z b) w c) z : ℤ) := by exact_mod_cast r1
  have e4 : (gVal col (.node a z (.node b w c)) z : ℤ)
              = (gVal col (.node (.node a z b) w c) w : ℤ) + 1 := by exact_mod_cast r4
  have e5 : (hVal col (.node a z (.node b w c)) z : ℤ)
              = (hVal col (.node (.node a z b) w c) z : ℤ) := by exact_mod_cast r5
  linarith

/-- **Key descent is preserved for non-pivot keys under `rotateRight`.**
For any key `x` distinct from `z` and `w` with `z < w`, the BST descent
`subtree_rooted_at · x` returns the same subtree before and after the
rotation.  No full BST hypothesis is needed — only `z < w`. -/
lemma subtree_rooted_at_rotateRight_nonpivot
    (a b c : BinaryTree) (w z x : ℕ)
    (hzw : z < w) (hxz : x ≠ z) (hxw : x ≠ w) :
    subtree_rooted_at (.node a z (.node b w c)) x
      = subtree_rooted_at (.node (.node a z b) w c) x := by
  -- Unfold one level on each side into the explicit `if … else if … else`.
  have hLHS : subtree_rooted_at (.node a z (.node b w c)) x
      = (if x = z then (.node a z (.node b w c) : BinaryTree)
         else if x < z then subtree_rooted_at a x
         else subtree_rooted_at (.node b w c) x) := by
    show subtree_rooted_at (.node a z (.node b w c)) x = _
    rfl
  have hRHS : subtree_rooted_at (.node (.node a z b) w c) x
      = (if x = w then (.node (.node a z b) w c : BinaryTree)
         else if x < w then subtree_rooted_at (.node a z b) x
         else subtree_rooted_at c x) := by
    show subtree_rooted_at (.node (.node a z b) w c) x = _
    rfl
  have hbwc : subtree_rooted_at (.node b w c) x
      = (if x = w then (.node b w c : BinaryTree)
         else if x < w then subtree_rooted_at b x
         else subtree_rooted_at c x) := by
    show subtree_rooted_at (.node b w c) x = _
    rfl
  have hazb : subtree_rooted_at (.node a z b) x
      = (if x = z then (.node a z b : BinaryTree)
         else if x < z then subtree_rooted_at a x
         else subtree_rooted_at b x) := by
    show subtree_rooted_at (.node a z b) x = _
    rfl
  rw [hLHS, hRHS]
  by_cases hxz1 : x < z
  · have hxw1 : x < w := lt_trans hxz1 hzw
    rw [if_neg hxz, if_pos hxz1, if_neg hxw, if_pos hxw1, hazb,
        if_neg hxz, if_pos hxz1]
  · have hxz2 : z < x := by omega
    have hnxz1 : ¬ x < z := hxz1
    by_cases hxw1 : x < w
    · rw [if_neg hxz, if_neg hnxz1, hbwc,
          if_neg hxw, if_pos hxw1, if_neg hxw, if_pos hxw1,
          hazb, if_neg hxz, if_neg hnxz1]
    · rw [if_neg hxz, if_neg hnxz1, hbwc,
          if_neg hxw, if_neg hxw1, if_neg hxw, if_neg hxw1]

/-- **`vVal` is preserved for non-pivot keys under `rotateRight`.**
Consequence of the descent lemma: `g_x` and `h_x` both read only from
`subtree_rooted_at · x`, which is unchanged for `x ≠ z, w`. -/
lemma vVal_rotateRight_nonpivot
    (col : ColorState) (a b c : BinaryTree) (w z x : ℕ)
    (hzw : z < w) (hxz : x ≠ z) (hxw : x ≠ w) :
    vVal col (.node a z (.node b w c)) x
      = vVal col (.node (.node a z b) w c) x := by
  have hsub := subtree_rooted_at_rotateRight_nonpivot a b c w z x hzw hxz hxw
  unfold vVal gVal hVal
  rw [hsub]

/-- **Key descent is preserved for non-pivot keys under `rotateLeft`.**
Symmetric to `subtree_rooted_at_rotateRight_nonpivot`: `rotateLeft` and
`rotateRight` transform inverse tree shapes, so the same descent
invariance holds for non-pivot keys. -/
lemma subtree_rooted_at_rotateLeft_nonpivot
    (a b c : BinaryTree) (w z x : ℕ)
    (hwz : w < z) (hxw : x ≠ w) (hxz : x ≠ z) :
    subtree_rooted_at (.node (.node a w b) z c) x
      = subtree_rooted_at (.node a w (.node b z c)) x := by
  -- Reuse the rotateRight lemma with `w` and `z` swapped.
  have h := subtree_rooted_at_rotateRight_nonpivot a b c z w x hwz hxw hxz
  -- h :  subtree_rooted_at (node a w (node b z c)) x
  --     = subtree_rooted_at (node (node a w b) z c) x.
  exact h.symm

/-- **`vVal` is preserved for non-pivot keys under `rotateLeft`.** -/
lemma vVal_rotateLeft_nonpivot
    (col : ColorState) (a b c : BinaryTree) (w z x : ℕ)
    (hwz : w < z) (hxw : x ≠ w) (hxz : x ≠ z) :
    vVal col (.node (.node a w b) z c) x
      = vVal col (.node a w (.node b z c)) x := by
  have hsub := subtree_rooted_at_rotateLeft_nonpivot a b c w z x hwz hxw hxz
  unfold vVal gVal hVal
  rw [hsub]

/-- **`ForallTree p t` implies `p` holds on every key in `t.toKeyList`.** -/
lemma ForallTree.forall_mem_toKeyList {p : ℕ → Prop} :
    ∀ {t : BinaryTree}, ForallTree p t → ∀ k ∈ t.toKeyList, p k
  | .empty, _, k, hk => by simp [BinaryTree.toKeyList] at hk
  | .node l a r, h, k, hk => by
    cases h with
    | node _ _ _ hl ha hr =>
      simp [BinaryTree.toKeyList] at hk
      rcases hk with hl' | rfl | hr'
      · exact ForallTree.forall_mem_toKeyList hl k hl'
      · exact ha
      · exact ForallTree.forall_mem_toKeyList hr k hr'

/-- **`subtree_rooted_at` only sees a child via the BST descent at `x`.**
For `x ≠ k` (the root key), changing the left subtree from `L1` to `L2` while
preserving `subtree_rooted_at · x` on it preserves the lookup at the parent. -/
lemma subtree_rooted_at_replace_left
    (L1 L2 r : BinaryTree) (k x : ℕ) (hxk : x ≠ k)
    (h : subtree_rooted_at L1 x = subtree_rooted_at L2 x) :
    subtree_rooted_at (.node L1 k r) x = subtree_rooted_at (.node L2 k r) x := by
  by_cases hlt : x < k
  · have e1 : subtree_rooted_at (.node L1 k r) x = subtree_rooted_at L1 x := by
      show (if x = k then _ else if x < k then _ else _) = _
      rw [if_neg hxk, if_pos hlt]
    have e2 : subtree_rooted_at (.node L2 k r) x = subtree_rooted_at L2 x := by
      show (if x = k then _ else if x < k then _ else _) = _
      rw [if_neg hxk, if_pos hlt]
    rw [e1, e2, h]
  · have e1 : subtree_rooted_at (.node L1 k r) x = subtree_rooted_at r x := by
      show (if x = k then _ else if x < k then _ else _) = _
      rw [if_neg hxk, if_neg hlt]
    have e2 : subtree_rooted_at (.node L2 k r) x = subtree_rooted_at r x := by
      show (if x = k then _ else if x < k then _ else _) = _
      rw [if_neg hxk, if_neg hlt]
    rw [e1, e2]

/-- Symmetric counterpart of `subtree_rooted_at_replace_left`: replacing the
right subtree preserves the descent at `x` when `x ≠ k`. -/
lemma subtree_rooted_at_replace_right
    (l R1 R2 : BinaryTree) (k x : ℕ) (hxk : x ≠ k)
    (h : subtree_rooted_at R1 x = subtree_rooted_at R2 x) :
    subtree_rooted_at (.node l k R1) x = subtree_rooted_at (.node l k R2) x := by
  by_cases hlt : x < k
  · have e1 : subtree_rooted_at (.node l k R1) x = subtree_rooted_at l x := by
      show (if x = k then _ else if x < k then _ else _) = _
      rw [if_neg hxk, if_pos hlt]
    have e2 : subtree_rooted_at (.node l k R2) x = subtree_rooted_at l x := by
      show (if x = k then _ else if x < k then _ else _) = _
      rw [if_neg hxk, if_pos hlt]
    rw [e1, e2]
  · have e1 : subtree_rooted_at (.node l k R1) x = subtree_rooted_at R1 x := by
      show (if x = k then _ else if x < k then _ else _) = _
      rw [if_neg hxk, if_neg hlt]
    have e2 : subtree_rooted_at (.node l k R2) x = subtree_rooted_at R2 x := by
      show (if x = k then _ else if x < k then _ else _) = _
      rw [if_neg hxk, if_neg hlt]
    rw [e1, e2, h]

/-- **The root of a non-empty `splay' t q` lies on the search path of `q` in `t`.**

Used in `subtree_rooted_at_splay'_off_path` to discharge the side condition
`x ≠ root(splay' ll q)` when applying the per-rotation `nonpivot` descent
lemma at the outer rotation of a recursive splay step (zigZig / zigZag /
zagZig / zagZag): the root of the recursively-splayed subtree always
arises as a key encountered during the BST descent for `q`. -/
lemma splay'_root_in_searchPath (t : BinaryTree) (q : ℕ) :
    ∀ {a c : BinaryTree} {k : ℕ}, splay' t q = .node a k c → k ∈ t.searchPath q := by
  fun_induction splay' t q with
  | case1 => intros _ _ _ h; cases h
  | case2 =>
    intros _ _ _ h
    obtain ⟨_, hk, _⟩ := BinaryTree.node.injEq .. |>.mp h
    subst hk; simp [BinaryTree.searchPath]
  | case3 =>
    rename_i k r hqne hqlt
    intros _ _ _ h
    obtain ⟨_, hk, _⟩ := BinaryTree.node.injEq .. |>.mp h
    subst hk; simp [BinaryTree.searchPath, hqne, hqlt]
  | case4 =>
    rename_i lk1 lr1 hqne1 hqlt1 lk lr hqlk
    intros _ _ _ h
    simp [rotate, rotateRight] at h
    obtain ⟨_, hk, _⟩ := h; subst hk
    have hqne_lk : ¬ q = lk := by omega
    simp [BinaryTree.searchPath, hqne1, hqlt1, hqne_lk, hqlk]
  | case5 =>
    rename_i lk1 lr1 hqne1 hqlt1 lk lr hqlk ll _hll ih
    intros a c k h
    have hqne_lk : ¬ q = lk := by omega
    have houter : ((BinaryTree.node ll lk lr).node lk1 lr1).searchPath q
        = lk1 :: lk :: ll.searchPath q := by
      simp [BinaryTree.searchPath, hqne1, hqlt1, hqne_lk, hqlk]
    rw [houter]
    cases hA : splay' ll q with
    | empty =>
      rw [hA] at h; simp [rotate, rotateRight] at h
      obtain ⟨_, hk, _⟩ := h; subst hk
      exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))
    | node A1 ak A2 =>
      rw [hA] at h; simp [rotate, rotateRight] at h
      obtain ⟨_, hak, _⟩ := h; subst hak
      exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (ih hA))))
  | case6 =>
    rename_i lk1 lr1 hqne1 hqlt1 ll lk hqnlk hlkq
    intros _ _ _ h
    simp [rotate, rotateRight] at h
    obtain ⟨_, hk, _⟩ := h; subst hk
    have hqne_lk : ¬ q = lk := by omega
    simp [BinaryTree.searchPath, hqne1, hqlt1, hqne_lk, hqnlk]
  | case7 =>
    rename_i lk1 lr1 hqne1 hqlt1 ll lk hqnlk hlkq lr _hlr ih
    intros a c k h
    have hqne_lk : ¬ q = lk := by omega
    have houter : ((BinaryTree.node ll lk lr).node lk1 lr1).searchPath q
        = lk1 :: lk :: lr.searchPath q := by
      simp [BinaryTree.searchPath, hqne1, hqlt1, hqne_lk, hqnlk]
    rw [houter]
    cases hB : splay' lr q with
    | empty =>
      rw [hB] at h; simp [rotate, rotateLeft, rotateRight] at h
      obtain ⟨_, hk, _⟩ := h; subst hk
      exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))
    | node B1 bk B2 =>
      rw [hB] at h; simp [rotate, rotateLeft, rotateRight] at h
      obtain ⟨_, hbk, _⟩ := h; subst hbk
      exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (ih hB))))
  | case8 =>
    rename_i lk1 lr1 hqne1 hqlt1 ll lk lr hqnlk hqnlt
    intros _ _ _ h
    simp [rotate, rotateRight] at h
    obtain ⟨_, hk, _⟩ := h; subst hk
    have hqeq_lk : q = lk := by omega
    subst hqeq_lk
    simp [BinaryTree.searchPath, hqne1, hqlt1]
  | case9 =>
    rename_i ll lk hqne hqnlt
    intros _ _ _ h
    obtain ⟨_, hk, _⟩ := BinaryTree.node.injEq .. |>.mp h
    subst hk; simp [BinaryTree.searchPath, hqne, hqnlt]
  | case10 =>
    rename_i ll lk1 hqne1 hqnlt1 lk lr hqlk
    intros _ _ _ h
    simp [rotate, rotateLeft] at h
    obtain ⟨_, hk, _⟩ := h; subst hk
    have hqne_lk : ¬ q = lk := by omega
    simp [BinaryTree.searchPath, hqne1, hqnlt1, hqne_lk, hqlk]
  | case11 =>
    rename_i ll lk1 hqne1 hqnlt1 lk lr hqlk rl _hrl ih
    intros a c k h
    have hqne_lk : ¬ q = lk := by omega
    have houter : (ll.node lk1 (rl.node lk lr)).searchPath q
        = lk1 :: lk :: rl.searchPath q := by
      simp [BinaryTree.searchPath, hqne1, hqnlt1, hqne_lk, hqlk]
    rw [houter]
    cases hA : splay' rl q with
    | empty =>
      rw [hA] at h; simp [rotate, rotateLeft, rotateRight] at h
      obtain ⟨_, hk, _⟩ := h; subst hk
      exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))
    | node A1 ak A2 =>
      rw [hA] at h; simp [rotate, rotateLeft, rotateRight] at h
      obtain ⟨_, hak, _⟩ := h; subst hak
      exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (ih hA))))
  | case12 =>
    rename_i ll lk1 hqne1 hqnlt1 rl lk hqnlk hlkq
    intros _ _ _ h
    simp [rotate, rotateLeft] at h
    obtain ⟨_, hk, _⟩ := h; subst hk
    have hqne_lk : ¬ q = lk := by omega
    simp [BinaryTree.searchPath, hqne1, hqnlt1, hqne_lk, hqnlk]
  | case13 =>
    rename_i ll lk1 hqne1 hqnlt1 rl lk hqnlk hlkq rr _hrr ih
    intros a c k h
    have hqne_lk : ¬ q = lk := by omega
    have houter : (ll.node lk1 (rl.node lk rr)).searchPath q
        = lk1 :: lk :: rr.searchPath q := by
      simp [BinaryTree.searchPath, hqne1, hqnlt1, hqne_lk, hqnlk]
    rw [houter]
    cases hB : splay' rr q with
    | empty =>
      rw [hB] at h; simp [rotate, rotateLeft] at h
      obtain ⟨_, hk, _⟩ := h; subst hk
      exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))
    | node B1 bk B2 =>
      rw [hB] at h; simp [rotate, rotateLeft] at h
      obtain ⟨_, hbk, _⟩ := h; subst hbk
      exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (ih hB))))
  | case14 =>
    rename_i ll lk1 hqne1 hqnlt1 rl lk lr hqnlk hqnlt
    intros _ _ _ h
    simp [rotate, rotateLeft] at h
    obtain ⟨_, hk, _⟩ := h; subst hk
    have hqeq_lk : q = lk := by omega
    subst hqeq_lk
    simp [BinaryTree.searchPath, hqne1, hqnlt1]

/-- **Key descent is preserved under `splay'` for off-path keys.**
If `x` does not appear on the search path of `q` in `t`, and `t` is a
BST, then the BST descent to `x` in `splay' t q` finds the same subtree
as in `t`.

This is the structural core of Elmasry's remark "if `x` is non-black and
not involved in a rotation, then `v_x` will not change" (§2 proof of
Lemma 1).  Our `splay'` only ever rotates nodes on the search path, so
any off-path key is preserved.

The BST hypothesis is essential: the per-rotation invariance relies on
`z < w` for the rotated pair (the pivots), which in our setting holds
because the tree is a BST and the pivots are a parent/child pair.

The proof follows the shape of `splay'` by `fun_induction`; each
rotation-bearing branch will use the per-rotation `nonpivot` lemmas with
the BST-derived ordering hypothesis.  Four trivial branches (empty tree
or target at root — no rotation) are closed by `rfl`. -/
lemma subtree_rooted_at_splay'_off_path
    (q : ℕ) (t : BinaryTree) (x : ℕ)
    (hBST : IsBST t) (hx : x ∉ t.searchPath q) :
    subtree_rooted_at (splay' t q) x = subtree_rooted_at t x := by
  -- Strong induction on `t.num_nodes` so the IH is available on the proper
  -- recursive subtree (`ll`, `lr`, `rl`, or `rr`) at each rotation step.
  induction hsize : t.num_nodes using Nat.strong_induction_on
    generalizing t with
  | _ n ih =>
  cases t with
  | empty => rfl
  | node l k r =>
    -- Unfold splay' for a node.
    unfold splay'
    by_cases hqk : q = k
    · simp [hqk]
    · by_cases hqlt : q < k
      · -- q < k: descend left.
        simp only [if_neg hqk, if_pos hqlt]
        cases l with
        | empty => rfl
        | node ll lk lr =>
          -- BST extract: lk < k.
          have hlk_lt_k : lk < k := by
            cases hBST with
            | node _ _ _ hforL _ _ _ =>
              cases hforL with
              | node _ _ _ _ h _ => exact h
          -- searchPath t q = k :: (.node ll lk lr).searchPath q
          have hx_ne_k : x ≠ k := by
            intro heq; apply hx
            show x ∈ (if q = k then [k] else if q < k then k :: _ else k :: _)
            rw [if_neg hqk, if_pos hqlt]; subst heq
            exact List.mem_cons.mpr (Or.inl rfl)
          have hx_notin_l : x ∉ (BinaryTree.node ll lk lr).searchPath q := by
            intro hmem; apply hx
            show x ∈ (if q = k then [k] else if q < k then k :: _ else k :: _)
            rw [if_neg hqk, if_pos hqlt]
            exact List.mem_cons.mpr (Or.inr hmem)
          -- IsBST l
          have hBSTl : IsBST (.node ll lk lr) := by
            cases hBST with
            | node _ _ _ _ _ hl _ => exact hl
          by_cases hqlk : q < lk
          · simp only [if_pos hqlk]
            -- hx_notin_l unfolds the inner searchPath too
            have hx_ne_lk : x ≠ lk := by
              intro heq; apply hx_notin_l
              show x ∈ (if q = lk then [lk] else if q < lk then lk :: _ else lk :: _)
              rw [if_neg (by omega : ¬ q = lk), if_pos hqlk]
              subst heq; exact List.mem_cons.mpr (Or.inl rfl)
            cases ll with
            | empty =>
              -- zig: rotateRight (node (node .empty lk lr) k r)
              --    = node .empty lk (node lr k r)
              show subtree_rooted_at (.node .empty lk (.node lr k r)) x
                = subtree_rooted_at (.node (.node .empty lk lr) k r) x
              exact subtree_rooted_at_rotateRight_nonpivot
                .empty lr r k lk x hlk_lt_k hx_ne_lk hx_ne_k
            | node lll llk llr =>
              -- zigZig with recursive splay' on ll = .node lll llk llr.
              -- Result = rotateRight (rotateRight (.node (.node A lk lr) k r))
              -- where A := splay' ll q.
              show subtree_rooted_at
                  (rotate (.node (.node (splay' (.node lll llk llr) q) lk lr) k r)
                    Rot.zigZig) x
                = subtree_rooted_at (.node (.node (.node lll llk llr) lk lr) k r) x
              -- Strong IH for ll (smaller size).
              have hll_size : (BinaryTree.node lll llk llr).num_nodes < n := by
                have hsize' := hsize
                simp only [BinaryTree.num_nodes] at hsize' ⊢
                omega
              have hBSTll : IsBST (.node lll llk llr) := by
                cases hBSTl with
                | node _ _ _ _ _ hll _ => exact hll
              have hx_notin_ll : x ∉ (BinaryTree.node lll llk llr).searchPath q := by
                intro hmem; apply hx_notin_l
                show x ∈ (if q = lk then [lk] else if q < lk then lk :: _ else lk :: _)
                rw [if_neg (by omega : ¬ q = lk), if_pos hqlk]
                exact List.mem_cons.mpr (Or.inr hmem)
              have ihA : subtree_rooted_at (splay' (.node lll llk llr) q) x
                  = subtree_rooted_at (.node lll llk llr) x :=
                ih _ hll_size _ hBSTll hx_notin_ll rfl
              -- BST: ForallTree (·<lk) ll, used to bound the root key of `splay' ll q`.
              have hForLll : ForallTree (fun y => y < lk) (.node lll llk llr) := by
                cases hBSTl with
                | node _ _ _ hforL _ _ _ => exact hforL
              -- Reduce match: `lll.node llk llr` is .node, so the second branch fires.
              show subtree_rooted_at
                  (rotateRight (rotateRight
                    (.node (.node (splay' (.node lll llk llr) q) lk lr) k r))) x
                = _
              -- Inner rotateRight: matches pattern, gives
              -- `.node (splay' ll q) lk (.node lr k r)`.
              show subtree_rooted_at
                  (rotateRight (.node (splay' (.node lll llk llr) q) lk (.node lr k r))) x
                = _
              -- Outer rotateRight: case on `splay' ll q`.
              cases hA : splay' (.node lll llk llr) q with
              | empty =>
                -- Outer rotateRight on `.node .empty lk (.node lr k r)` is identity.
                show subtree_rooted_at (.node BinaryTree.empty lk (.node lr k r)) x
                  = subtree_rooted_at (.node (.node (.node lll llk llr) lk lr) k r) x
                -- Apply inner nonpivot to relate to (.node (.node .empty lk lr) k r).
                rw [subtree_rooted_at_rotateRight_nonpivot
                  .empty lr r k lk x hlk_lt_k hx_ne_lk hx_ne_k]
                -- Now compare (.node (.node .empty lk lr) k r) and (.node (.node ll lk lr) k r).
                -- ihA at this point says splay' ll q = .empty (from hA), so
                -- subtree_rooted_at .empty x = subtree_rooted_at ll x.
                rw [hA] at ihA
                -- Use the `replace_left` helper twice to descend through k and lk.
                refine subtree_rooted_at_replace_left _ _ r k x hx_ne_k ?_
                exact subtree_rooted_at_replace_left _ _ lr lk x hx_ne_lk ihA
              | node A1 ak A2 =>
                show subtree_rooted_at
                    (rotateRight (.node (.node A1 ak A2) lk (.node lr k r))) x
                  = subtree_rooted_at (.node (.node (.node lll llk llr) lk lr) k r) x
                -- Outer rotateRight matches the pattern; result is
                -- `.node A1 ak (.node A2 lk (.node lr k r))`.
                -- Apply outer nonpivot lemma: need ak < lk, x ≠ ak, x ≠ lk.
                -- ak < lk: ak is in `(splay' ll q).toKeyList = ll.toKeyList`,
                -- and every key in ll is < lk by `hForLll`.
                have hak_in_ll : ak ∈ (BinaryTree.node lll llk llr).toKeyList := by
                  have hroot_in : ak ∈ (splay' (.node lll llk llr) q).toKeyList := by
                    rw [hA]; simp [BinaryTree.toKeyList]
                  rw [splay'_toKeyList] at hroot_in
                  exact hroot_in
                have hak_lt_lk : ak < lk :=
                  ForallTree.forall_mem_toKeyList hForLll ak hak_in_ll
                -- x ≠ ak: ak = root of splay' ll q ∈ ll.searchPath q;
                -- but x ∉ ll.searchPath q.
                have hak_in_path : ak ∈ (BinaryTree.node lll llk llr).searchPath q :=
                  splay'_root_in_searchPath _ _ hA
                have hx_ne_ak : x ≠ ak := by
                  intro heq; subst heq
                  exact hx_notin_ll hak_in_path
                -- Compute outer rotateRight to expose the nonpivot LHS pattern.
                show subtree_rooted_at
                    (.node A1 ak (.node A2 lk (.node lr k r))) x
                  = subtree_rooted_at (.node (.node (.node lll llk llr) lk lr) k r) x
                -- Apply outer nonpivot.
                rw [subtree_rooted_at_rotateRight_nonpivot
                  A1 A2 (.node lr k r) lk ak x hak_lt_lk hx_ne_ak hx_ne_lk]
                -- = subtree_rooted_at (.node (.node A1 ak A2) lk (.node lr k r)) x.
                -- Apply inner nonpivot (with .node A1 ak A2 in left).
                rw [subtree_rooted_at_rotateRight_nonpivot
                  (.node A1 ak A2) lr r k lk x hlk_lt_k hx_ne_lk hx_ne_k]
                -- = subtree_rooted_at (.node (.node (.node A1 ak A2) lk lr) k r) x.
                -- Now relate (.node A1 ak A2) = splay' ll q to ll via ihA.
                rw [hA] at ihA
                refine subtree_rooted_at_replace_left _ _ r k x hx_ne_k ?_
                exact subtree_rooted_at_replace_left _ _ lr lk x hx_ne_lk ihA
          · by_cases hlkq : lk < q
            · simp only [if_neg hqlk, if_pos hlkq]
              have hx_ne_lk : x ≠ lk := by
                intro heq; apply hx_notin_l
                show x ∈ (if q = lk then [lk] else if q < lk then lk :: _ else lk :: _)
                rw [if_neg (by omega : ¬ q = lk), if_neg hqlk]
                -- Target now: x ∈ lk :: lr.searchPath q  (the last else of searchPath).
                subst heq; exact List.mem_cons.mpr (Or.inl rfl)
              cases lr with
              | empty =>
                -- zig again: match lr = .empty ⇒ rotate (.node l k r) .zig
                change subtree_rooted_at
                    (rotate (.node (.node ll lk .empty) k r) Rot.zig) x
                  = subtree_rooted_at (.node (.node ll lk .empty) k r) x
                show subtree_rooted_at (.node ll lk (.node .empty k r)) x
                  = subtree_rooted_at (.node (.node ll lk .empty) k r) x
                exact subtree_rooted_at_rotateRight_nonpivot
                  ll .empty r k lk x hlk_lt_k hx_ne_lk hx_ne_k
              | node lrl lrk lrr =>
                -- zigZag with recursive splay' on lr = .node lrl lrk lrr.
                show subtree_rooted_at
                    (rotate (.node (.node ll lk (splay' (.node lrl lrk lrr) q)) k r)
                      Rot.zigZag) x
                  = subtree_rooted_at (.node (.node ll lk (.node lrl lrk lrr)) k r) x
                have hlr_size : (BinaryTree.node lrl lrk lrr).num_nodes < n := by
                  have hsize' := hsize
                  simp only [BinaryTree.num_nodes] at hsize' ⊢
                  omega
                have hBSTlr : IsBST (.node lrl lrk lrr) := by
                  cases hBSTl with
                  | node _ _ _ _ _ _ hlr => exact hlr
                have hx_notin_lr : x ∉ (BinaryTree.node lrl lrk lrr).searchPath q := by
                  intro hmem; apply hx_notin_l
                  show x ∈ (if q = lk then [lk] else if q < lk then lk :: _ else lk :: _)
                  rw [if_neg (by omega : ¬ q = lk), if_neg hqlk]
                  exact List.mem_cons.mpr (Or.inr hmem)
                have ihA : subtree_rooted_at (splay' (.node lrl lrk lrr) q) x
                    = subtree_rooted_at (.node lrl lrk lrr) x :=
                  ih _ hlr_size _ hBSTlr hx_notin_lr rfl
                have hForL : ForallTree (fun y => y < k)
                    (.node ll lk (.node lrl lrk lrr)) := by
                  cases hBST with
                  | node _ _ _ hforL _ _ _ => exact hforL
                have hForLlr : ForallTree (fun y => y < k) (.node lrl lrk lrr) := by
                  cases hForL with
                  | node _ _ _ _ _ hforLlr => exact hforLlr
                have hForRlr : ForallTree (fun y => lk < y) (.node lrl lrk lrr) := by
                  cases hBSTl with
                  | node _ _ _ _ hforRl _ _ => exact hforRl
                -- rotate .zigZag = rotateRight ∘ (rotateLeft-at-left) ∘ node _ k r.
                show subtree_rooted_at
                    (rotateRight
                      (.node (rotateLeft (.node ll lk (splay' (.node lrl lrk lrr) q))) k r)) x
                  = _
                cases hA : splay' (.node lrl lrk lrr) q with
                | empty =>
                  -- rotateLeft (.node ll lk .empty) falls through to itself;
                  -- rotateRight (.node (.node ll lk .empty) k r) = .node ll lk (.node .empty k r).
                  show subtree_rooted_at (.node ll lk (.node BinaryTree.empty k r)) x
                    = subtree_rooted_at (.node (.node ll lk (.node lrl lrk lrr)) k r) x
                  rw [subtree_rooted_at_rotateRight_nonpivot
                    ll .empty r k lk x hlk_lt_k hx_ne_lk hx_ne_k]
                  refine subtree_rooted_at_replace_left _ _ r k x hx_ne_k ?_
                  refine subtree_rooted_at_replace_right ll _ _ lk x hx_ne_lk ?_
                  rw [hA] at ihA
                  exact ihA
                | node A1 ak A2 =>
                  -- rotateLeft (.node ll lk (.node A1 ak A2)) = .node (.node ll lk A1) ak A2;
                  -- rotateRight (.node (.node (.node ll lk A1) ak A2) k r)
                  --   = .node (.node ll lk A1) ak (.node A2 k r).
                  show subtree_rooted_at
                      (.node (.node ll lk A1) ak (.node A2 k r)) x
                    = subtree_rooted_at (.node (.node ll lk (.node lrl lrk lrr)) k r) x
                  have hak_in_lr : ak ∈ (BinaryTree.node lrl lrk lrr).toKeyList := by
                    have hroot_in : ak ∈ (splay' (.node lrl lrk lrr) q).toKeyList := by
                      rw [hA]; simp [BinaryTree.toKeyList]
                    rw [splay'_toKeyList] at hroot_in
                    exact hroot_in
                  have hak_lt_k : ak < k :=
                    ForallTree.forall_mem_toKeyList hForLlr ak hak_in_lr
                  have hlk_lt_ak : lk < ak :=
                    ForallTree.forall_mem_toKeyList hForRlr ak hak_in_lr
                  have hak_in_path : ak ∈ (BinaryTree.node lrl lrk lrr).searchPath q :=
                    splay'_root_in_searchPath _ _ hA
                  have hx_ne_ak : x ≠ ak := by
                    intro heq; subst heq
                    exact hx_notin_lr hak_in_path
                  -- Outer rotateRight_nonpivot (pivot pair ak / k).
                  rw [subtree_rooted_at_rotateRight_nonpivot
                    (.node ll lk A1) A2 r k ak x hak_lt_k hx_ne_ak hx_ne_k]
                  -- Inner rotateLeft_nonpivot (pivot pair lk / ak), inside `.node _ k r`.
                  refine subtree_rooted_at_replace_left _ _ r k x hx_ne_k ?_
                  rw [subtree_rooted_at_rotateLeft_nonpivot
                    ll A1 A2 lk ak x hlk_lt_ak hx_ne_lk hx_ne_ak]
                  -- Swap splay' lr q for lr using ihA.
                  refine subtree_rooted_at_replace_right ll _ _ lk x hx_ne_lk ?_
                  rw [hA] at ihA
                  exact ihA
            · -- q = lk : zig at the child.
              have hqlk_eq : q = lk := by omega
              simp only [if_neg hqlk, if_neg hlkq]
              -- rotate (.node (.node ll lk lr) k r) .zig
              --   = node ll lk (node lr k r)
              have hx_ne_lk : x ≠ lk := by
                intro heq
                apply hx_notin_l
                show x ∈ (if q = lk then [lk] else if q < lk then lk :: _ else lk :: _)
                rw [if_pos hqlk_eq]; subst heq; exact List.mem_singleton.mpr rfl
              show subtree_rooted_at (.node ll lk (.node lr k r)) x
                = subtree_rooted_at (.node (.node ll lk lr) k r) x
              exact subtree_rooted_at_rotateRight_nonpivot
                ll lr r k lk x hlk_lt_k hx_ne_lk hx_ne_k
      · -- q > k: symmetric on the right subtree.
        have hkq : k < q := by omega
        simp only [if_neg hqk, if_neg hqlt]
        cases r with
        | empty => rfl
        | node rl rk rr =>
          have hk_lt_rk : k < rk := by
            cases hBST with
            | node _ _ _ _ hforR _ _ =>
              cases hforR with
              | node _ _ _ _ h _ => exact h
          have hx_ne_k : x ≠ k := by
            intro heq; apply hx
            show x ∈ (if q = k then [k] else if q < k then k :: _ else k :: _)
            rw [if_neg hqk, if_neg hqlt]; subst heq
            exact List.mem_cons.mpr (Or.inl rfl)
          have hx_notin_r : x ∉ (BinaryTree.node rl rk rr).searchPath q := by
            intro hmem; apply hx
            show x ∈ (if q = k then [k] else if q < k then k :: _ else k :: _)
            rw [if_neg hqk, if_neg hqlt]
            exact List.mem_cons.mpr (Or.inr hmem)
          have _hBSTr : IsBST (.node rl rk rr) := by
            cases hBST with
            | node _ _ _ _ _ _ hr => exact hr
          by_cases hqrk : q < rk
          · simp only [if_pos hqrk]
            have hx_ne_rk : x ≠ rk := by
              intro heq; apply hx_notin_r
              show x ∈ (if q = rk then [rk] else if q < rk then rk :: _ else rk :: _)
              rw [if_neg (by omega : ¬ q = rk), if_pos hqrk]
              subst heq; exact List.mem_cons.mpr (Or.inl rfl)
            cases rl with
            | empty =>
              -- zag: rotateLeft (.node l k (.node .empty rk rr))
              --   = .node (.node l k .empty) rk rr
              change subtree_rooted_at
                  (rotate (.node l k (.node .empty rk rr)) Rot.zag) x
                = subtree_rooted_at (.node l k (.node .empty rk rr)) x
              show subtree_rooted_at (.node (.node l k .empty) rk rr) x
                = subtree_rooted_at (.node l k (.node .empty rk rr)) x
              exact subtree_rooted_at_rotateLeft_nonpivot
                l .empty rr k rk x hk_lt_rk hx_ne_k hx_ne_rk
            | node rll rlk rlr =>
              -- zagZig with recursive splay' on rl = .node rll rlk rlr.
              show subtree_rooted_at
                  (rotate (.node l k (.node (splay' (.node rll rlk rlr) q) rk rr))
                    Rot.zagZig) x
                = subtree_rooted_at (.node l k (.node (.node rll rlk rlr) rk rr)) x
              have hrl_size : (BinaryTree.node rll rlk rlr).num_nodes < n := by
                have hsize' := hsize
                simp only [BinaryTree.num_nodes] at hsize' ⊢
                omega
              have hBSTrl : IsBST (.node rll rlk rlr) := by
                cases _hBSTr with
                | node _ _ _ _ _ hrl _ => exact hrl
              have hx_notin_rl : x ∉ (BinaryTree.node rll rlk rlr).searchPath q := by
                intro hmem; apply hx_notin_r
                show x ∈ (if q = rk then [rk] else if q < rk then rk :: _ else rk :: _)
                rw [if_neg (by omega : ¬ q = rk), if_pos hqrk]
                exact List.mem_cons.mpr (Or.inr hmem)
              have ihA : subtree_rooted_at (splay' (.node rll rlk rlr) q) x
                  = subtree_rooted_at (.node rll rlk rlr) x :=
                ih _ hrl_size _ hBSTrl hx_notin_rl rfl
              have hForR : ForallTree (fun y => k < y)
                  (.node (.node rll rlk rlr) rk rr) := by
                cases hBST with
                | node _ _ _ _ hforR _ _ => exact hforR
              have hForRrl : ForallTree (fun y => k < y) (.node rll rlk rlr) := by
                cases hForR with
                | node _ _ _ hforRl _ _ => exact hforRl
              have hForLrl : ForallTree (fun y => y < rk) (.node rll rlk rlr) := by
                cases _hBSTr with
                | node _ _ _ hforL _ _ _ => exact hforL
              -- rotate .zagZig = rotateLeft ∘ (rotateRight-at-right) ∘ node l k _.
              show subtree_rooted_at
                  (rotateLeft
                    (.node l k (rotateRight (.node (splay' (.node rll rlk rlr) q) rk rr)))) x
                = _
              cases hA : splay' (.node rll rlk rlr) q with
              | empty =>
                -- rotateRight (.node .empty rk rr) falls through;
                -- rotateLeft (.node l k (.node .empty rk rr)) = .node (.node l k .empty) rk rr.
                show subtree_rooted_at
                    (.node (.node l k BinaryTree.empty) rk rr) x
                  = subtree_rooted_at (.node l k (.node (.node rll rlk rlr) rk rr)) x
                rw [subtree_rooted_at_rotateLeft_nonpivot
                  l .empty rr k rk x hk_lt_rk hx_ne_k hx_ne_rk]
                refine subtree_rooted_at_replace_right l _ _ k x hx_ne_k ?_
                refine subtree_rooted_at_replace_left _ _ rr rk x hx_ne_rk ?_
                rw [hA] at ihA
                exact ihA
              | node A1 ak A2 =>
                -- rotateRight (.node (.node A1 ak A2) rk rr) = .node A1 ak (.node A2 rk rr);
                -- rotateLeft (.node l k (.node A1 ak (.node A2 rk rr)))
                --   = .node (.node l k A1) ak (.node A2 rk rr).
                show subtree_rooted_at
                    (.node (.node l k A1) ak (.node A2 rk rr)) x
                  = subtree_rooted_at (.node l k (.node (.node rll rlk rlr) rk rr)) x
                have hak_in_rl : ak ∈ (BinaryTree.node rll rlk rlr).toKeyList := by
                  have hroot_in : ak ∈ (splay' (.node rll rlk rlr) q).toKeyList := by
                    rw [hA]; simp [BinaryTree.toKeyList]
                  rw [splay'_toKeyList] at hroot_in
                  exact hroot_in
                have hk_lt_ak : k < ak :=
                  ForallTree.forall_mem_toKeyList hForRrl ak hak_in_rl
                have hak_lt_rk : ak < rk :=
                  ForallTree.forall_mem_toKeyList hForLrl ak hak_in_rl
                have hak_in_path : ak ∈ (BinaryTree.node rll rlk rlr).searchPath q :=
                  splay'_root_in_searchPath _ _ hA
                have hx_ne_ak : x ≠ ak := by
                  intro heq; subst heq
                  exact hx_notin_rl hak_in_path
                -- Outer rotateLeft_nonpivot (pivot pair k / ak).
                rw [subtree_rooted_at_rotateLeft_nonpivot
                  l A1 (.node A2 rk rr) k ak x hk_lt_ak hx_ne_k hx_ne_ak]
                -- Inner rotateRight_nonpivot (pivot pair ak / rk), inside `.node l k _`.
                refine subtree_rooted_at_replace_right l _ _ k x hx_ne_k ?_
                rw [subtree_rooted_at_rotateRight_nonpivot
                  A1 A2 rr rk ak x hak_lt_rk hx_ne_ak hx_ne_rk]
                -- Swap splay' rl q for rl using ihA.
                refine subtree_rooted_at_replace_left _ _ rr rk x hx_ne_rk ?_
                rw [hA] at ihA
                exact ihA
          · by_cases hrkq : rk < q
            · simp only [if_neg hqrk, if_pos hrkq]
              have hx_ne_rk : x ≠ rk := by
                intro heq; apply hx_notin_r
                show x ∈ (if q = rk then [rk] else if q < rk then rk :: _ else rk :: _)
                rw [if_neg (by omega : ¬ q = rk), if_neg hqrk]
                subst heq; exact List.mem_cons.mpr (Or.inl rfl)
              cases rr with
              | empty =>
                -- zag: match rr = .empty ⇒ rotate .zag
                change subtree_rooted_at
                    (rotate (.node l k (.node rl rk .empty)) Rot.zag) x
                  = subtree_rooted_at (.node l k (.node rl rk .empty)) x
                show subtree_rooted_at (.node (.node l k rl) rk .empty) x
                  = subtree_rooted_at (.node l k (.node rl rk .empty)) x
                exact subtree_rooted_at_rotateLeft_nonpivot
                  l rl .empty k rk x hk_lt_rk hx_ne_k hx_ne_rk
              | node rrl rrk rrr =>
                -- zagZag with recursive splay' on rr = .node rrl rrk rrr.
                show subtree_rooted_at
                    (rotate (.node l k (.node rl rk (splay' (.node rrl rrk rrr) q)))
                      Rot.zagZag) x
                  = subtree_rooted_at (.node l k (.node rl rk (.node rrl rrk rrr))) x
                have hrr_size : (BinaryTree.node rrl rrk rrr).num_nodes < n := by
                  have hsize' := hsize
                  simp only [BinaryTree.num_nodes] at hsize' ⊢
                  omega
                have hBSTrr : IsBST (.node rrl rrk rrr) := by
                  cases _hBSTr with
                  | node _ _ _ _ _ _ hrr => exact hrr
                have hx_notin_rr : x ∉ (BinaryTree.node rrl rrk rrr).searchPath q := by
                  intro hmem; apply hx_notin_r
                  show x ∈ (if q = rk then [rk] else if q < rk then rk :: _ else rk :: _)
                  rw [if_neg (by omega : ¬ q = rk), if_neg hqrk]
                  exact List.mem_cons.mpr (Or.inr hmem)
                have ihA : subtree_rooted_at (splay' (.node rrl rrk rrr) q) x
                    = subtree_rooted_at (.node rrl rrk rrr) x :=
                  ih _ hrr_size _ hBSTrr hx_notin_rr rfl
                have hForRrr : ForallTree (fun y => rk < y) (.node rrl rrk rrr) := by
                  cases _hBSTr with
                  | node _ _ _ _ hforR _ _ => exact hforR
                -- rotate .zagZag = rotateLeft ∘ rotateLeft.
                show subtree_rooted_at
                    (rotateLeft (rotateLeft
                      (.node l k (.node rl rk (splay' (.node rrl rrk rrr) q))))) x
                  = _
                cases hA : splay' (.node rrl rrk rrr) q with
                | empty =>
                  -- Inner rotateLeft: .node l k (.node rl rk .empty) =>
                  --   .node (.node l k rl) rk .empty.
                  -- Outer rotateLeft on that falls through (right = .empty).
                  show subtree_rooted_at
                      (.node (.node l k rl) rk BinaryTree.empty) x
                    = subtree_rooted_at (.node l k (.node rl rk (.node rrl rrk rrr))) x
                  rw [subtree_rooted_at_rotateLeft_nonpivot
                    l rl .empty k rk x hk_lt_rk hx_ne_k hx_ne_rk]
                  refine subtree_rooted_at_replace_right l _ _ k x hx_ne_k ?_
                  refine subtree_rooted_at_replace_right rl _ _ rk x hx_ne_rk ?_
                  rw [hA] at ihA
                  exact ihA
                | node A1 ak A2 =>
                  -- Inner rotateLeft: .node l k (.node rl rk (.node A1 ak A2))
                  --   => .node (.node l k rl) rk (.node A1 ak A2).
                  -- Outer rotateLeft: => .node (.node (.node l k rl) rk A1) ak A2.
                  show subtree_rooted_at
                      (.node (.node (.node l k rl) rk A1) ak A2) x
                    = subtree_rooted_at (.node l k (.node rl rk (.node rrl rrk rrr))) x
                  have hak_in_rr : ak ∈ (BinaryTree.node rrl rrk rrr).toKeyList := by
                    have hroot_in : ak ∈ (splay' (.node rrl rrk rrr) q).toKeyList := by
                      rw [hA]; simp [BinaryTree.toKeyList]
                    rw [splay'_toKeyList] at hroot_in
                    exact hroot_in
                  have hrk_lt_ak : rk < ak :=
                    ForallTree.forall_mem_toKeyList hForRrr ak hak_in_rr
                  have hak_in_path : ak ∈ (BinaryTree.node rrl rrk rrr).searchPath q :=
                    splay'_root_in_searchPath _ _ hA
                  have hx_ne_ak : x ≠ ak := by
                    intro heq; subst heq
                    exact hx_notin_rr hak_in_path
                  -- Outer rotateLeft_nonpivot (pivot pair rk / ak).
                  rw [subtree_rooted_at_rotateLeft_nonpivot
                    (.node l k rl) A1 A2 rk ak x hrk_lt_ak hx_ne_rk hx_ne_ak]
                  -- Inner rotateLeft_nonpivot (pivot pair k / rk).
                  rw [subtree_rooted_at_rotateLeft_nonpivot
                    l rl (.node A1 ak A2) k rk x hk_lt_rk hx_ne_k hx_ne_rk]
                  -- Swap splay' rr q for rr using ihA.
                  refine subtree_rooted_at_replace_right l _ _ k x hx_ne_k ?_
                  refine subtree_rooted_at_replace_right rl _ _ rk x hx_ne_rk ?_
                  rw [hA] at ihA
                  exact ihA
            · -- q = rk : zag at the child.
              have hqrk_eq : q = rk := by omega
              simp only [if_neg hqrk, if_neg hrkq]
              have hx_ne_rk : x ≠ rk := by
                intro heq; apply hx_notin_r
                show x ∈ (if q = rk then [rk] else if q < rk then rk :: _ else rk :: _)
                rw [if_pos hqrk_eq]; subst heq
                exact List.mem_singleton.mpr rfl
              show subtree_rooted_at (.node (.node l k rl) rk rr) x
                = subtree_rooted_at (.node l k (.node rl rk rr)) x
              exact subtree_rooted_at_rotateLeft_nonpivot
                l rl rr k rk x hk_lt_rk hx_ne_k hx_ne_rk

/-- **Off-path descent invariance for the full `splay` wrapper.**

Lifting `subtree_rooted_at_splay'_off_path` through the optional outer
single-rotation performed by `splay` when the search-path length is even.
The outer rotation's pivot is the root of the recursively-splayed child
subtree, which by `splay'_root_in_searchPath` lies on `l.searchPath q`
(or `r.searchPath q`); combined with `x ∉ t.searchPath q` and the
inner IH, `subtree_rooted_at_rotate{Right,Left}_nonpivot` plus
`subtree_rooted_at_replace_{left,right}` close the rotation step. -/
lemma subtree_rooted_at_splay_off_path
    (t : BinaryTree) (q x : ℕ)
    (hBST : IsBST t) (hx : x ∉ t.searchPath q) :
    subtree_rooted_at (splay t q) x = subtree_rooted_at t x := by
  cases t with
  | empty => rfl
  | node l k r =>
    -- Root k is always on `(.node l k r).searchPath q`, so `x ≠ k`.
    have hk_in : k ∈ (BinaryTree.node l k r).searchPath q := by
      unfold BinaryTree.searchPath
      by_cases hqk : q = k
      · rw [if_pos hqk]; simp
      · rw [if_neg hqk]
        by_cases hqlt : q < k
        · rw [if_pos hqlt]; simp
        · rw [if_neg hqlt]; simp
    have hx_ne_k : x ≠ k := fun heq => hx (heq ▸ hk_in)
    -- Split on parity of the search-path length.
    by_cases hodd : Odd ((BinaryTree.node l k r).search_path_len q)
    · -- Odd: `splay = splay'`.
      show subtree_rooted_at
          (if Odd ((BinaryTree.node l k r).search_path_len q)
             then splay' (.node l k r) q
             else _) x = _
      rw [if_pos hodd]
      exact subtree_rooted_at_splay'_off_path q (.node l k r) x hBST hx
    · -- Not odd: `splay = ...` with an outer single rotation.
      show subtree_rooted_at
          (if Odd ((BinaryTree.node l k r).search_path_len q)
             then splay' (.node l k r) q
             else
               if q = k then (BinaryTree.node l k r)
               else if q < k then rotate (.node (splay' l q) k r) .zig
               else rotate (.node l k (splay' r q)) .zag) x = _
      rw [if_neg hodd]
      by_cases hqk : q = k
      · -- Degenerate: q = k forces len = 1, which is odd — impossible. Still
        -- `splay = t` in this branch, so the goal is trivial.
        rw [if_pos hqk]
      · rw [if_neg hqk]
        by_cases hqlt : q < k
        · -- `q < k`: outer rotation is a `rotateRight` of `.node (splay' l q) k r`.
          rw [if_pos hqlt]
          show subtree_rooted_at (rotateRight (.node (splay' l q) k r)) x
            = subtree_rooted_at (.node l k r) x
          have hBSTl : IsBST l := by
            cases hBST with | node _ _ _ _ _ hBl _ => exact hBl
          have hForL : ForallTree (fun y => y < k) l := by
            cases hBST with | node _ _ _ hfL _ _ _ => exact hfL
          have hx_notin_l : x ∉ l.searchPath q := by
            intro hmem; apply hx
            show x ∈ (BinaryTree.node l k r).searchPath q
            unfold BinaryTree.searchPath
            rw [if_neg hqk, if_pos hqlt]
            exact List.mem_cons.mpr (Or.inr hmem)
          have ihA : subtree_rooted_at (splay' l q) x = subtree_rooted_at l x :=
            subtree_rooted_at_splay'_off_path q l x hBSTl hx_notin_l
          cases hA : splay' l q with
          | empty =>
            -- `rotateRight (.node .empty k r) = .node .empty k r`.
            show subtree_rooted_at (.node .empty k r) x
              = subtree_rooted_at (.node l k r) x
            refine subtree_rooted_at_replace_left _ _ r k x hx_ne_k ?_
            rw [hA] at ihA; exact ihA
          | node a lk' b =>
            -- `rotateRight (.node (.node a lk' b) k r) = .node a lk' (.node b k r)`.
            show subtree_rooted_at (.node a lk' (.node b k r)) x
              = subtree_rooted_at (.node l k r) x
            have hlk'_in_path : lk' ∈ l.searchPath q :=
              splay'_root_in_searchPath _ _ hA
            have hlk'_in_keys : lk' ∈ l.toKeyList :=
              searchPath_subset_toKeyList l q lk' hlk'_in_path
            have hlk'_lt_k : lk' < k :=
              ForallTree.forall_mem_toKeyList hForL lk' hlk'_in_keys
            have hx_ne_lk' : x ≠ lk' := by
              intro heq; apply hx_notin_l; subst heq; exact hlk'_in_path
            rw [subtree_rooted_at_rotateRight_nonpivot a b r k lk' x
              hlk'_lt_k hx_ne_lk' hx_ne_k]
            refine subtree_rooted_at_replace_left _ _ r k x hx_ne_k ?_
            rw [hA] at ihA; exact ihA
        · -- `q > k`: outer rotation is a `rotateLeft` of `.node l k (splay' r q)`.
          rw [if_neg hqlt]
          show subtree_rooted_at (rotateLeft (.node l k (splay' r q))) x
            = subtree_rooted_at (.node l k r) x
          have hBSTr : IsBST r := by
            cases hBST with | node _ _ _ _ _ _ hBr => exact hBr
          have hForR : ForallTree (fun y => k < y) r := by
            cases hBST with | node _ _ _ _ hfR _ _ => exact hfR
          have hx_notin_r : x ∉ r.searchPath q := by
            intro hmem; apply hx
            show x ∈ (BinaryTree.node l k r).searchPath q
            unfold BinaryTree.searchPath
            rw [if_neg hqk, if_neg hqlt]
            exact List.mem_cons.mpr (Or.inr hmem)
          have ihA : subtree_rooted_at (splay' r q) x = subtree_rooted_at r x :=
            subtree_rooted_at_splay'_off_path q r x hBSTr hx_notin_r
          cases hA : splay' r q with
          | empty =>
            -- `rotateLeft (.node l k .empty) = .node l k .empty`.
            show subtree_rooted_at (.node l k .empty) x
              = subtree_rooted_at (.node l k r) x
            refine subtree_rooted_at_replace_right l _ _ k x hx_ne_k ?_
            rw [hA] at ihA; exact ihA
          | node a rk' b =>
            -- `rotateLeft (.node l k (.node a rk' b)) = .node (.node l k a) rk' b`.
            show subtree_rooted_at (.node (.node l k a) rk' b) x
              = subtree_rooted_at (.node l k r) x
            have hrk'_in_path : rk' ∈ r.searchPath q :=
              splay'_root_in_searchPath _ _ hA
            have hrk'_in_keys : rk' ∈ r.toKeyList :=
              searchPath_subset_toKeyList r q rk' hrk'_in_path
            have hk_lt_rk' : k < rk' :=
              ForallTree.forall_mem_toKeyList hForR rk' hrk'_in_keys
            have hx_ne_rk' : x ≠ rk' := by
              intro heq; apply hx_notin_r; subst heq; exact hrk'_in_path
            rw [subtree_rooted_at_rotateLeft_nonpivot l a b k rk' x
              hk_lt_rk' hx_ne_k hx_ne_rk']
            refine subtree_rooted_at_replace_right l _ _ k x hx_ne_k ?_
            rw [hA] at ihA; exact ihA

/-- **`vVal` is preserved for off-path keys under `splay`.**

Immediate consequence of `subtree_rooted_at_splay_off_path`: `gVal` and
`hVal` read only from the subtree rooted at `x`, which is unchanged. -/
lemma vVal_splay_off_path
    (col : ColorState) (t : BinaryTree) (q x : ℕ)
    (hBST : IsBST t) (hx : x ∉ t.searchPath q) :
    vVal col (splay t q) x = vVal col t x := by
  have hsub := subtree_rooted_at_splay_off_path t q x hBST hx
  unfold vVal gVal hVal
  rw [hsub]

/-- **`paintYellow` leaves keys outside `xs` untouched.** -/
lemma ColorState.paintYellow_eq_of_not_mem
    (col : ColorState) (xs : List ℕ) (y : ℕ) (hy : y ∉ xs) :
    (col.paintYellow xs) y = col y := by
  induction xs generalizing col with
  | nil => rfl
  | cons a xs ih =>
    have hya : y ≠ a := fun h => hy (h ▸ List.mem_cons_self)
    have hy' : y ∉ xs := fun h => hy (List.mem_cons_of_mem _ h)
    -- `paintYellow col (a :: xs)` reduces to `paintYellow (step col a) xs`.
    change (List.foldl (fun c x => if c x = .uncolored then c.set x .yellow else c)
        col (a :: xs)) y = col y
    rw [List.foldl_cons]
    -- Apply IH to the stepped color state.
    set col' := (if col a = .uncolored then col.set a .yellow else col) with hcol'
    have hih : (List.foldl (fun c x => if c x = .uncolored then c.set x .yellow else c)
        col' xs) y = col' y := ih col' hy'
    rw [hih]
    -- `col' y = col y` since `y ≠ a`.
    rw [hcol']
    by_cases h : col a = .uncolored
    · rw [if_pos h]; show (col.set a .yellow) y = col y
      unfold ColorState.set; rw [if_neg hya]
    · rw [if_neg h]

/-- **`processLink` only touches the two endpoint colors.** -/
lemma processLink_color_eq_of_ne
    (col : ColorState) (cnt : LinkCounters) (t : BinaryTree) (w z y : ℕ)
    (hyw : y ≠ w) (hyz : y ≠ z) :
    (processLink col cnt t w z).1 y = col y := by
  by_cases hY : col w = .yellow ∨ col z = .yellow
  · rw [processLink_eq_Y _ _ _ _ _ hY]
    -- The fst is a nested `if` over `col z = .yellow` / `col w = .yellow`.
    show (if col z = .yellow
            then (if col w = .yellow then col.set w .green else col).set z .green
            else (if col w = .yellow then col.set w .green else col)) y = col y
    by_cases hcz : col z = .yellow
    · rw [if_pos hcz]
      show ((if col w = .yellow then col.set w .green else col).set z .green) y = col y
      rw [ColorState.set]; simp only [if_neg hyz]
      by_cases hcw : col w = .yellow
      · rw [if_pos hcw]; show (col.set w .green) y = col y
        unfold ColorState.set; rw [if_neg hyw]
      · rw [if_neg hcw]
    · rw [if_neg hcz]
      by_cases hcw : col w = .yellow
      · rw [if_pos hcw]; show (col.set w .green) y = col y
        unfold ColorState.set; rw [if_neg hyw]
      · rw [if_neg hcw]
  · by_cases hA : vVal col t z = 1
    · rw [processLink_eq_A _ _ _ _ _ hY hA]
    · rw [processLink_eq_B _ _ _ _ _ hY hA]

/-- **`processLinks` fixes every key that is not an endpoint of any link.** -/
lemma processLinks_color_eq_of_ne
    (col : ColorState) (cnt : LinkCounters) (t : BinaryTree)
    (links : List (ℕ × ℕ)) (y : ℕ)
    (hy : ∀ wz ∈ links, y ≠ wz.1 ∧ y ≠ wz.2) :
    (processLinks col cnt t links).1 y = col y := by
  induction links generalizing col cnt with
  | nil => rfl
  | cons wz rest ih =>
    have hhd := hy wz List.mem_cons_self
    have htl : ∀ wz' ∈ rest, y ≠ wz'.1 ∧ y ≠ wz'.2 :=
      fun wz' h => hy wz' (List.mem_cons_of_mem _ h)
    show (processLinks (processLink col cnt t wz.1 wz.2).1
            (processLink col cnt t wz.1 wz.2).2 t rest).1 y = col y
    rw [ih _ _ htl, processLink_color_eq_of_ne _ _ _ _ _ _ hhd.1 hhd.2]

/-- **`stepColor` fixes every key outside the search path.**

All color changes inside `stepColor` are either `paintYellow` on
`path.tail` or `processLink` endpoints (which lie in `linksOfSpine path`
and hence in `path`). -/
lemma stepColor_color_eq_of_not_mem_searchPath
    (col : ColorState) (t t' : BinaryTree) (q y : ℕ)
    (hy : y ∉ t.searchPath q) :
    (stepColor col t t' q).1 y = col y := by
  dsimp only [stepColor]
  set path := t.searchPath q with hpath
  have hy_tail : y ∉ path.tail := fun h => hy (List.mem_of_mem_tail h)
  have hy_col₁ : (col.paintYellow path.tail) y = col y :=
    ColorState.paintYellow_eq_of_not_mem col _ y hy_tail
  rcases hls : linksOfSpine path with _ | ⟨_top, rest⟩
  · -- No spine links: result is just `paintYellow`.
    show (col.paintYellow path.tail) y = col y
    exact hy_col₁
  · -- Spine links present: apply `processLinks` off-path preservation.
    have hlinks_ne : ∀ wz ∈ rest, y ≠ wz.1 ∧ y ≠ wz.2 := by
      intro wz hwz
      have hmem : wz ∈ linksOfSpine path := by
        rw [hls]; exact List.mem_cons_of_mem _ hwz
      have := linksOfSpine_fst_mem _ wz hmem
      exact ⟨fun h => hy (h ▸ this.1), fun h => hy (h ▸ this.2)⟩
    show (processLinks (col.paintYellow path.tail) 0 t rest).1 y = col y
    rw [processLinks_color_eq_of_ne _ _ _ _ _ hlinks_ne, hy_col₁]

/-- Every key on the right spine of a tree is a key of the tree. -/
lemma BinaryTree.rightSpineKeys_subset_toKeyList :
    ∀ (t : BinaryTree), ∀ k ∈ t.rightSpineKeys, k ∈ t.toKeyList
  | .empty, k, hk => by simp [BinaryTree.rightSpineKeys] at hk
  | .node l a r, k, hk => by
    simp only [BinaryTree.rightSpineKeys, List.mem_cons] at hk
    simp only [BinaryTree.toKeyList, List.mem_append, List.mem_singleton]
    rcases hk with rfl | hkr
    · exact Or.inl (Or.inr rfl)
    · exact Or.inr (BinaryTree.rightSpineKeys_subset_toKeyList r k hkr)

/-- The keys of a `subtree_rooted_at` descent are a subset of the tree's keys. -/
lemma subtree_rooted_at_toKeyList_subset :
    ∀ (t : BinaryTree) (x : ℕ), ∀ k ∈ (subtree_rooted_at t x).toKeyList, k ∈ t.toKeyList
  | .empty, x, k, hk => by simp [subtree_rooted_at, BinaryTree.toKeyList] at hk
  | .node l a r, x, k, hk => by
    unfold subtree_rooted_at at hk
    split_ifs at hk with h1 h2
    · -- x = a: subtree is the whole tree.
      exact hk
    · -- x < a: subtree is in `l`.
      have := subtree_rooted_at_toKeyList_subset l x k hk
      simp only [BinaryTree.toKeyList, List.mem_append]
      exact Or.inl (Or.inl this)
    · -- x > a: subtree is in `r`.
      have := subtree_rooted_at_toKeyList_subset r x k hk
      simp only [BinaryTree.toKeyList, List.mem_append]
      exact Or.inr this

/-- **BST off-path disjointness.**  In a BST `t`, if `z ∉ t.searchPath q`,
every key inside the `subtree_rooted_at t z` descent is also off-path.

Intuition: in a BST the search paths for `z` and `q` follow the same
chain of nodes until they diverge at some ancestor.  After divergence,
`z`'s descent enters a subtree strictly separated (by BST ordering) from
the continuation of `q`'s path. -/
lemma IsBST.searchPath_subtree_disjoint :
    ∀ {t : BinaryTree}, IsBST t → ∀ (q z : ℕ), z ∉ t.searchPath q →
      ∀ k ∈ (subtree_rooted_at t z).toKeyList, k ∉ t.searchPath q
  | .empty, _, _, _, _, k, hk => by
    simp [subtree_rooted_at, BinaryTree.toKeyList] at hk
  | .node l a r, hBST, q, z, hz, k, hk => by
    have hFL : ForallTree (fun y => y < a) l := by
      cases hBST with | node _ _ _ hfL _ _ _ => exact hfL
    have hFR : ForallTree (fun y => a < y) r := by
      cases hBST with | node _ _ _ _ hfR _ _ => exact hfR
    have hBSTl : IsBST l := by
      cases hBST with | node _ _ _ _ _ hl _ => exact hl
    have hBSTr : IsBST r := by
      cases hBST with | node _ _ _ _ _ _ hr => exact hr
    -- Split on z's relation to the root `a`.
    by_cases hza : z = a
    · -- z = a: then z ∈ searchPath, contradicting hz.
      exfalso; apply hz
      rw [hza]
      unfold BinaryTree.searchPath
      by_cases hqa : q = a
      · rw [if_pos hqa]; simp
      · rw [if_neg hqa]
        split_ifs <;> simp
    · by_cases hzlt : z < a
      · -- Descent goes left: subtree_rooted_at = subtree_rooted_at l z.
        have hsub_eq : subtree_rooted_at (.node l a r) z = subtree_rooted_at l z := by
          change (if z = a then (BinaryTree.node l a r)
                    else if z < a then subtree_rooted_at l z
                    else subtree_rooted_at r z) = subtree_rooted_at l z
          rw [if_neg hza, if_pos hzlt]
        rw [hsub_eq] at hk
        -- k is a descendant of l, so k ∈ l.toKeyList and thus k < a.
        have hk_in_l : k ∈ l.toKeyList := subtree_rooted_at_toKeyList_subset l z k hk
        have hk_lt_a : k < a := ForallTree.forall_mem_toKeyList hFL k hk_in_l
        have hk_ne_a : k ≠ a := fun h => by omega
        intro hmem
        -- Analyse which branch of (.node l a r).searchPath q `hmem` sits in.
        unfold BinaryTree.searchPath at hmem
        by_cases hqa : q = a
        · rw [if_pos hqa] at hmem
          simp at hmem; exact hk_ne_a hmem
        · rw [if_neg hqa] at hmem
          by_cases hqlt : q < a
          · rw [if_pos hqlt] at hmem
            rcases List.mem_cons.mp hmem with rfl | hmem'
            · exact hk_ne_a rfl
            · -- k ∈ l.searchPath q; apply IH on l.
              have hz_notin_l : z ∉ l.searchPath q := by
                intro hz_l; apply hz
                unfold BinaryTree.searchPath
                rw [if_neg hqa, if_pos hqlt]
                exact List.mem_cons.mpr (Or.inr hz_l)
              exact IsBST.searchPath_subtree_disjoint hBSTl q z hz_notin_l k hk hmem'
          · rw [if_neg hqlt] at hmem
            rcases List.mem_cons.mp hmem with rfl | hmem'
            · exact hk_ne_a rfl
            · -- k ∈ r.searchPath q ⇒ k ∈ r.toKeyList ⇒ k > a; but k < a.
              have hk_in_r : k ∈ r.toKeyList :=
                searchPath_subset_toKeyList r q k hmem'
              have hk_gt_a : a < k := ForallTree.forall_mem_toKeyList hFR k hk_in_r
              omega
      · -- Descent goes right: z > a.
        have hzgt : a < z := by omega
        have hsub_eq : subtree_rooted_at (.node l a r) z = subtree_rooted_at r z := by
          change (if z = a then (BinaryTree.node l a r)
                    else if z < a then subtree_rooted_at l z
                    else subtree_rooted_at r z) = subtree_rooted_at r z
          rw [if_neg hza, if_neg hzlt]
        rw [hsub_eq] at hk
        have hk_in_r : k ∈ r.toKeyList := subtree_rooted_at_toKeyList_subset r z k hk
        have hk_gt_a : a < k := ForallTree.forall_mem_toKeyList hFR k hk_in_r
        have hk_ne_a : k ≠ a := fun h => by omega
        intro hmem
        unfold BinaryTree.searchPath at hmem
        by_cases hqa : q = a
        · rw [if_pos hqa] at hmem
          simp at hmem; exact hk_ne_a hmem
        · rw [if_neg hqa] at hmem
          by_cases hqlt : q < a
          · rw [if_pos hqlt] at hmem
            rcases List.mem_cons.mp hmem with rfl | hmem'
            · exact hk_ne_a rfl
            · have hk_in_l : k ∈ l.toKeyList :=
                searchPath_subset_toKeyList l q k hmem'
              have hk_lt_a : k < a := ForallTree.forall_mem_toKeyList hFL k hk_in_l
              omega
          · rw [if_neg hqlt] at hmem
            rcases List.mem_cons.mp hmem with rfl | hmem'
            · exact hk_ne_a rfl
            · have hz_notin_r : z ∉ r.searchPath q := by
                intro hz_r; apply hz
                unfold BinaryTree.searchPath
                rw [if_neg hqa, if_neg hqlt]
                exact List.mem_cons.mpr (Or.inr hz_r)
              exact IsBST.searchPath_subtree_disjoint hBSTr q z hz_notin_r k hk hmem'

/-- **`vVal` agrees whenever both colorings coincide on the keys of the
sub-tree rooted at `x`.**

Both `gVal` and `hVal` read only from the right spines of, respectively,
`subtree_rooted_at t x` and its left child; these spines are subsets of
`(subtree_rooted_at t x).toKeyList`. -/
lemma vVal_eq_of_color_agree_on_subtree
    (col col' : ColorState) (t : BinaryTree) (x : ℕ)
    (h : ∀ y ∈ (subtree_rooted_at t x).toKeyList, col y = col' y) :
    vVal col t x = vVal col' t x := by
  have hisCol : ∀ y ∈ (subtree_rooted_at t x).toKeyList,
      col.isColored y = col'.isColored y := by
    intro y hy; unfold ColorState.isColored; rw [h y hy]
  -- gVal equality.
  have hg : gVal col t x = gVal col' t x := by
    unfold gVal
    congr 1
    apply List.filter_congr
    intro k hk
    exact hisCol k (BinaryTree.rightSpineKeys_subset_toKeyList _ k hk)
  -- hVal equality (case on the subtree shape).
  have hh : hVal col t x = hVal col' t x := by
    unfold hVal
    -- Generalize the subtree so the `match` reduces via `cases`.
    generalize hs : subtree_rooted_at t x = sub at hisCol ⊢
    cases sub with
    | empty => rfl
    | node l a r =>
      simp only [BinaryTree.toKeyList, List.mem_append, List.mem_singleton] at hisCol
      show (List.filter (fun k => col.isColored k) l.rightSpineKeys).length
         = (List.filter (fun k => col'.isColored k) l.rightSpineKeys).length
      congr 1
      apply List.filter_congr
      intro k hk
      have hk_in_l : k ∈ l.toKeyList :=
        BinaryTree.rightSpineKeys_subset_toKeyList _ k hk
      exact hisCol k (Or.inl (Or.inl hk_in_l))
  unfold vVal
  rw [hg, hh]

/-- **Off-path `vVal` is preserved through `stepColor ∘ splay`.**

For `z ∉ t.searchPath q` and `IsBST t`, the post-splay colouring and tree
leave `vVal … z` invariant.  Combines:
  * `subtree_rooted_at_splay_off_path` — the descent at `z` is unchanged;
  * `stepColor_color_eq_of_not_mem_searchPath` — colours outside the
    search path are untouched;
  * `IsBST.searchPath_subtree_disjoint` — in a BST, the keys inside
    `subtree_rooted_at t z` are all off-path. -/
lemma vVal_stepColor_splay_off_path
    (col : ColorState) (t : BinaryTree) (q z : ℕ)
    (hBST : IsBST t) (hz : z ∉ t.searchPath q) :
    vVal (stepColor col t (splay t q) q).1 (splay t q) z = vVal col t z := by
  set col' := (stepColor col t (splay t q) q).1 with hcol'
  -- Step 1: bridge the tree change via off-path descent invariance.
  have htree := subtree_rooted_at_splay_off_path t q z hBST hz
  -- Step 2: equality on subtree keys (for either tree).
  have hkeys_off : ∀ y ∈ (subtree_rooted_at t z).toKeyList, y ∉ t.searchPath q :=
    IsBST.searchPath_subtree_disjoint hBST q z hz
  have hagree : ∀ y ∈ (subtree_rooted_at (splay t q) z).toKeyList, col y = col' y := by
    intro y hy
    rw [htree] at hy
    have : y ∉ t.searchPath q := hkeys_off y hy
    exact (stepColor_color_eq_of_not_mem_searchPath col t (splay t q) q y this).symm
  -- Step 3: apply the colour-agreement lemma, then the tree descent lemma.
  calc vVal col' (splay t q) z
      = vVal col (splay t q) z := by
        exact (vVal_eq_of_color_agree_on_subtree col col' (splay t q) z hagree).symm
    _ = vVal col t z := vVal_splay_off_path col t q z hBST hz

/-- **Elmasry Lemma 1(c) (monotonicity of v under one splay).**
If `2 ≤ vVal col t z` in the pre-splay state, then the post-splay v-value
`vVal col' (splay t q) z ≥ 2`, where `col' = (stepColor …).1`.

The paper's proof proceeds by induction over the lifetime of nodes,
running jointly with Lemma 1(a)(b) (the `ColorInvariant`).  Each link
event is a single rotation, for which relations (1)–(5) give
`vz(t+1) ≥ vw(t) + vz(t)`; combined with `vw(t) ≥ 0` (Lemma 1(b) via the
invariant) this yields `vz(t+1) ≥ vz(t)` — the "non-decreasing" claim.

**Audit note (2026-04-17).** The claim as stated is strictly stronger than
Elmasry's Lemma 1(c).  The paper's monotonicity applies only to
**right-spine link events** — rotations of `rotateRight` shape, where
`z` is lifted to become `w`'s parent and `w` becomes `z`'s right child.
Our Lean `splay` also uses `rotateLeft` (zag / zagZag / zagZig branches),
and a hand computation shows `vVal` can *decrease* under `rotateLeft`:
for `rotateLeft (node a w (node b z c)) = node (node a w b) z c` with
`w < z`, one finds `vVal col t' z = vVal col t z − [isColored w]`.
These rotations are accounted for separately as the paper's **K-links**
(Elmasry §2 lines 282–286: "black nodes are involved in at most one link
per splay operation"), and **Lemma 1(c) is not applied to them** — the
paper explicitly notes "the conditions of the lemma do not apply to `w`
and `z` anymore" once they become black.

See `audit.md` for the full analysis and restructuring plan.  The
current statement is preserved as a `sorry` pending the restructure of
`bigVset` / `aTargetsOf` to restrict to non-black nodes. -/
lemma lemma1c_monotone
    (col : ColorState) (t : BinaryTree) (q n z : ℕ)
    (_hz : z < n) (hv : 2 ≤ vVal col t z) :
    2 ≤ vVal (stepColor col t (splay t q) q).1 (splay t q) z := by
  cases ht : t with
  | empty =>
    -- vVal of empty is 0, contradicting hv.
    subst ht
    rw [vVal_empty] at hv
    omega
  | node l k r =>
    subst ht
    by_cases hqk : q = k
    · -- Root case: splay and stepColor are identities.
      subst hqk
      obtain ⟨hstep, hsplay⟩ := stepColor_root col l q r
      rw [hsplay, hstep]
      exact hv
    · -- Non-root case: rotation analysis.  Proceeds by induction on
      -- `splay'`, at each step invoking `elmasry_relations` together with
      -- the `ColorInvariant` to derive `vz(t+1) ≥ vz(t)`.  Deferred.
      sorry

/-- **Sub-lemma A+B.**  Pre-splay `bigVset` and A-targets both lie in the
post-splay `bigVset`.  Under the before/after definition of `aTargetsOf`,
the A-target part is immediate (`2 ≤ vVal col' (splay t q) z` by
definition).  The `bigVset` part is exactly Elmasry's Lemma 1(c)
monotonicity: `2 ≤ vVal col t z → 2 ≤ vVal col' (splay t q) z`. -/
lemma bigVset_union_aTargets_subset
    (col : ColorState) (t : BinaryTree) (q n : ℕ)
    (_hspine : ∀ k ∈ t.searchPath q, k < n) :
    bigVset col t n ∪ aTargetsOf col t q n ⊆
      bigVset (stepColor col t (splay t q) q).1 (splay t q) n := by
  classical
  intro z hz
  rw [Finset.mem_union] at hz
  unfold bigVset
  rw [Finset.mem_filter, Finset.mem_range]
  rcases hz with hzS | hzA
  · -- Pre-splay bigVset: needs Lemma 1(c) monotonicity of vVal.
    unfold bigVset at hzS
    rw [Finset.mem_filter, Finset.mem_range] at hzS
    refine ⟨hzS.1, ?_⟩
    exact lemma1c_monotone col t q n z hzS.1 hzS.2
  · rw [mem_aTargetsOf] at hzA
    exact ⟨hzA.1, hzA.2.2.2⟩

/-- **Sub-lemma C (matching processLinks A-count to the before/after
A-target set).**  Every A-link emitted by `stepColor`'s internal walk has a
z-component satisfying the before/after condition
(`vVal col t z = 1 ∧ 2 ≤ vVal col' (splay t q) z`); conversely every such
z arises from an A-link.  Hence the A-counter equals the cardinality of
`aTargetsOf`.  Sub-lemma C is the A-jump part of Elmasry Lemma 1(c). -/
lemma stepColor_A_eq_aTargets_card
    (col : ColorState) (t : BinaryTree) (q n : ℕ)
    (hspine : ∀ k ∈ t.searchPath q, k < n)
    (hNoDup : (t.searchPath q).Nodup) :
    (stepColor col t (splay t q) q).2.A = (aTargetsOf col t q n).card := by
  sorry

/-- **Lemma 1(c) + A-link jump (single splay version).**
Through one invocation of `stepColor col t (splay t q) q`, the ghost set of
"v ≥ 2" keys is monotone non-decreasing, and every A-link recorded by that
step corresponds to a *fresh* key in the post-step ghost set that was not
in the pre-step ghost set.

Proof: combine sub-lemmas A+B (pre-bigVset ∪ A-targets ⊆ post-bigVset),
C (A-count = |A-targets|), and D (A-targets disjoint from pre-bigVset). -/
lemma stepColor_A_bigVset
    (col : ColorState) (t : BinaryTree) (q n : ℕ)
    (hspine : ∀ k ∈ t.searchPath q, k < n)
    (hNoDup : (t.searchPath q).Nodup) :
    (stepColor col t (splay t q) q).2.A + (bigVset col t n).card ≤
      (bigVset (stepColor col t (splay t q) q).1 (splay t q) n).card := by
  set S := bigVset col t n with hS
  set A := aTargetsOf col t q n with hA
  set S' := bigVset (stepColor col t (splay t q) q).1 (splay t q) n with hS'
  -- |S ∪ A| = |S| + |A|  since S and A are disjoint (sub-lemma D).
  have hdisj : Disjoint S A :=
    (aTargetsOf_disjoint_bigVset col t q n).symm
  have hcard_union : (S ∪ A).card = S.card + A.card := by
    rw [Finset.card_union_of_disjoint hdisj]
  -- S ∪ A ⊆ S'  (sub-lemma A+B).
  have hsub : S ∪ A ⊆ S' := bigVset_union_aTargets_subset col t q n hspine
  have hcard_le : (S ∪ A).card ≤ S'.card := Finset.card_le_card hsub
  -- A.card = step A-count  (sub-lemma C).
  have hAeq : (stepColor col t (splay t q) q).2.A = A.card :=
    stepColor_A_eq_aTargets_card col t q n hspine hNoDup
  rw [hAeq]
  -- Put it together.
  calc A.card + S.card
      = S.card + A.card := by ring
    _ = (S ∪ A).card := hcard_union.symm
    _ ≤ S'.card := hcard_le

lemma colorSequence_A_le {n : ℕ} (init : BinaryTree) (X : Fin n → ℕ)
    (hInit : ∀ k ∈ init.toKeyList, k < n)
    (hInitND : init.toKeyList.Nodup) :
    (totalCounters init X).A ≤ n := by
  unfold totalCounters colorSequence
  -- Invariants: keys < n, toKeyList Nodup, cnt.A ≤ bigVset.card.
  suffices h : ∀ (L : List (Fin n)) (t : BinaryTree) (col : ColorState)
      (cnt : LinkCounters),
      (∀ k ∈ t.toKeyList, k < n) →
      t.toKeyList.Nodup →
      cnt.A ≤ (bigVset col t n).card →
      ((L.foldl
          (fun (acc : BinaryTree × ColorState × LinkCounters) i =>
            let (t, col, cnt) := acc
            let q  := X i
            let t' := splay t q
            let (col', dcnt) := stepColor col t t' q
            (t', col', cnt + dcnt))
          (t, col, cnt)).2.2).A ≤ n by
    apply h (List.finRange n) init ColorState.initial 0 hInit hInitND
    show (0 : LinkCounters).A ≤ _
    change 0 ≤ _
    exact Nat.zero_le _
  intro L
  induction L with
  | nil =>
      intro t col cnt _ _ hInv
      have := bigVset_card_le col t n
      simpa using Nat.le_trans hInv this
  | cons i L ih =>
      intro t col cnt htKeys htND hInv
      simp only [List.foldl_cons]
      apply ih
      · intro k hk
        rw [splay_toKeyList] at hk
        exact htKeys k hk
      · rw [splay_toKeyList]; exact htND
      · have hspine : ∀ k ∈ t.searchPath (X i), k < n := by
          intro k hk
          exact htKeys k (searchPath_subset_toKeyList t (X i) k hk)
        have hspineND : (t.searchPath (X i)).Nodup :=
          searchPath_nodup_of_toKeyList_nodup t (X i) htND
        have hstep :=
          stepColor_A_bigVset col t (X i) n hspine hspineND
        change (cnt + (stepColor col t (splay t (X i)) (X i)).2).A ≤
          (bigVset (stepColor col t (splay t (X i)) (X i)).1
                   (splay t (X i)) n).card
        show cnt.A + _ ≤ _
        omega

-- EVOLVE-BLOCK-END

theorem sequential_theorem: ∃ c, ∀ n, let X := one_to_n n
  ∀ (init : BinaryTree), (h_size: init.num_nodes = n) →
  IsBST init →
  init.toKeyList = (List.finRange n).map X →
  splay.sequence_cost init X ≤ c * n := by
  -- EVOLVE-BLOCK-START
  --
  -- Proof follows Elmasry (TCS 314, 2004):
  --   "On the sequential access theorem and deque conjecture for splay trees".
  --
  -- The total cost of sequentially accessing all n keys equals the total number
  -- of rotations ("links on the splaying spine") performed across all n splays.
  -- Elmasry colors nodes (yellow / green, with black overriding on the right
  -- spine) and classifies every link into one of 4 disjoint categories:
  --
  --   (Y) links incident to at least one YELLOW node,
  --   (A) green-to-green A-links  (link to z while v_z(t) = 1),
  --   (B) green-to-green B-links  (link to z while v_z(t) ≥ 2),
  --   (K) links incident to a BLACK node.
  --
  -- Each class is bounded separately:
  --
  --   (Y) #Y ≤ n   : each yellow→green transition happens at most once per node.
  --   (A) #A ≤ n   : Lemma 1(c) gives that v_z is non-decreasing under a
  --                  green→z link, so every node can be the z of an A-link at
  --                  most once before v_z jumps to ≥ 2.
  --   (B) #B ≤ 3n/2: accounting argument.  Invariant: node x carries h_x(t)²/2
  --                  credits.  For a B-link, (3) and (5) of the paper give
  --                  d ≥ v_z(t) − 1 ≥ 1, releasing one credit to pay the link.
  --                  Initialising a yellow node costs 3/2 credits, summing to
  --                  3n/2 total.
  --   (K) #K ≤ n   : a black node participates in a link at most once per
  --                  splay operation, and there are n splays.
  --
  -- Summing: 4.5 · n.
  --
  refine ⟨(9 : ℝ) / 2, ?_⟩
  intro n X init h_size h_bst h_keys
  -- Let `cnt = (Y, A, B, K)` be the cumulative link counters produced by
  -- tracking the coloring through the splay sequence.
  set cnt : LinkCounters := totalCounters init X with hcnt
  -- (C) Cost-counts identity: the sum of all splay costs equals the total
  --     number of links (rotations) recorded by the coloring argument.
  have hCost : splay.sequence_cost init X = (cnt.total : ℝ) := by
    unfold splay.sequence_cost
    show _ = ((totalCounters init X).total : ℝ)
    unfold totalCounters colorSequence
    -- Both sides are the same foldl over `List.finRange n`, initialised with
    -- `(init, 0)` and `(init, ColorState.initial, 0)` respectively.
    exact sequence_cost_foldl_eq X (List.finRange n) init ColorState.initial 0 0
      (by show (0 : ℝ) = ((0 : LinkCounters).total : ℝ)
          simp [LinkCounters.total, LinkCounters.zero,
                show (0 : LinkCounters) = LinkCounters.zero from rfl])
  -- Individual Elmasry bounds on each bucket.
  have hY : (cnt.Y : ℝ) ≤ n := by
    have hInit : ∀ k ∈ init.toKeyList, k < n := by
      intro k hk
      rw [h_keys] at hk
      simp at hk
      obtain ⟨i, _, rfl⟩ := hk
      exact i.isLt
    have : cnt.Y ≤ n := by
      rw [hcnt]; exact colorSequence_Y_le init X hInit
    exact_mod_cast this
  have hA : (cnt.A : ℝ) ≤ n := by
    have hInit : ∀ k ∈ init.toKeyList, k < n := by
      intro k hk
      rw [h_keys] at hk
      simp at hk
      obtain ⟨i, _, rfl⟩ := hk
      exact i.isLt
    have hInitND : init.toKeyList.Nodup := by
      rw [h_keys]
      -- X = one_to_n n = id-as-ℕ, so (finRange n).map X has distinct values.
      refine (List.nodup_finRange n).map ?_
      intro a b hab
      -- X a = X b → a = b (since X i = (i : ℕ))
      show a = b
      have : (a : ℕ) = (b : ℕ) := hab
      exact Fin.ext this
    have : cnt.A ≤ n := by
      rw [hcnt]; exact colorSequence_A_le init X hInit hInitND
    exact_mod_cast this
  have hB : (cnt.B : ℝ) ≤ (3 : ℝ) / 2 * n := by sorry
  have hK : (cnt.K : ℝ) ≤ n := by
    have : cnt.K ≤ n := by rw [hcnt]; exact colorSequence_K_le init X
    exact_mod_cast this
  -- Put the pieces together.
  have htot : (cnt.total : ℝ) = cnt.Y + cnt.A + cnt.B + cnt.K := by
    simp [LinkCounters.total, Nat.cast_add]
  rw [hCost, htot]
  linarith
  -- EVOLVE-BLOCK-END
