import Mathlib.Analysis.SpecialFunctions.Log.Base
import GraphAlgorithms.DataStructures.SplayTrees.BinaryTree

set_option autoImplicit false

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

def splay (t : BinaryTree) (q : ℕ) : BinaryTree :=
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
              let t' := .node (splay ll q) lk lr
              rotate (.node t' k r) .zigZig
        else if lk < q then
          match lr with
          | .empty => rotate (.node l k r) .zig -- Grandchild empty? Just Zig.
          | _ =>
              -- Zig-Zag: Recurse, then double rotate
              let t' := .node ll lk (splay lr q)
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
              let t' := .node (splay rl q) rk rr
              rotate (.node l k t') .zagZig
        else if rk < q then
          match rr with
          | .empty => rotate (.node l k r) .zag -- Grandchild empty? Just Zag.
          | _ =>
              -- Zag-Zag
              let t' := .node rl rk (splay rr q)
              rotate (.node l k t') .zagZag
        else
          -- Target found at child (rk == q)
          rotate t .zag


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



-- 4. COST FUNCTION
-- Exactly matches the logic above.
-- 1 for Zig/Zag, 2 for any double rotation.

def splay.cost (t : BinaryTree) (q : ℕ) : ℝ :=
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
          | _ => (splay.cost ll q) + 2  -- Zig-Zig
        else if lk < q then
          match lr with
          | .empty => 1                 -- Zig (Grandchild empty)
          | _ => (splay.cost lr q) + 2  -- Zig-Zag
        else 1                          -- Zig (Found at child)
    else -- q > k
      match r with
      | .empty => 0
      | .node rl rk rr =>
        if q < rk then
          match rl with
          | .empty => 1                 -- Zag (Grandchild empty)
          | _ => (splay.cost rl q) + 2  -- Zag-Zig
        else if rk < q then
          match rr with
          | .empty => 1                 -- Zag (Grandchild empty)
          | _ => (splay.cost rr q) + 2  -- Zag-Zag
        else 1                          -- Zag (Found at child)




theorem splay_cost_pos (q : ℕ) (t : BinaryTree) : 0 ≤ splay.cost t q := by
  fun_induction splay.cost <;> grind

@[simp, grind =]
theorem num_nodes_rotateRight (t : BinaryTree) :
  (rotateRight t).num_nodes = t.num_nodes := by
  unfold rotateRight
  cases t with
  | empty => rfl -- .empty case is trivial
  | node l k r =>
    cases l with
    | empty => rfl -- No rotation, trivial
    | node ll lk lr =>
      simp [BinaryTree.num_nodes, add_assoc]
      grind

@[simp, grind =]
theorem num_nodes_rotateLeft (t : BinaryTree) :
  (rotateLeft t).num_nodes = t.num_nodes := by
  -- Symmetric proof to rotateRight
  unfold rotateLeft
  cases t with
  | empty => rfl
  | node l k r =>
    cases r with
    | empty => rfl
    | node rl rk rr =>
      simp [BinaryTree.num_nodes, add_assoc]
      grind

@[simp] theorem num_nodes_splay (t : BinaryTree) (q : ℕ) :
  (splay t q).num_nodes = t.num_nodes := by
  fun_induction splay <;> try grind
  all_goals simp [rotate]
  all_goals
    unfold BinaryTree.num_nodes
    simp
    unfold BinaryTree.num_nodes
    grind

-- 2. Rank and Potential Definitions
noncomputable def rank (t : BinaryTree) : ℝ :=
  if t.num_nodes = 0 then 0 else Real.logb 2 (t.num_nodes)

noncomputable def φ : BinaryTree → ℝ
  | .empty => 0
  | s@(.node l _ r) => rank s + φ l + φ r


-- 4. Helper to find the rank of the node *being splayed* (x)
--    This fixes the inequality by comparing against the specific node x, not the root.
noncomputable def target_rank (s : BinaryTree) (rt : Rot) : ℝ :=
  match rt, s with
  -- ZigZig: x is left.left
  | .zigZig, .node (.node ll _ _) _ _ => rank ll
  -- ZigZag: x is left.right
  | .zigZag, .node (.node _ _ lr) _ _ => rank lr
  -- ZagZag: x is right.right
  | .zagZag, .node _ _ (.node _ _ rr) => rank rr
  -- ZagZig: x is right.left
  | .zagZig, .node _ _ (.node rl _ _) => rank rl
  -- Zig: x is left
  | .zig,    .node l _ _              => rank l
  -- Zag: x is right
  | .zag,    .node _ _ r              => rank r
  | _, _ => rank s -- Fallback

theorem log_sum_le {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hsum : a + b ≤ c) :
    Real.logb 2 a + Real.logb 2 b ≤ 2 * Real.logb 2 c - 2 :=  by
  have h1 : Real.logb 2 a = Real.log a / Real.log (2 : ℝ) := rfl
  have h2 : Real.logb 2 b = Real.log b / Real.log (2 : ℝ) := rfl
  have h3 : Real.logb 2 c = Real.log c / Real.log (2 : ℝ) := rfl
  rw [h1, h2, h3]
  have h4 : 0 < (2 : ℝ) := by norm_num
  have h5 : Real.log (2 : ℝ) > 0 := by
    apply Real.log_pos
    all_goals linarith
  have h6 : Real.log a + Real.log b ≤ 2 * Real.log c - 2 * Real.log (2 : ℝ) := by
    have h7 : a + b ≤ c := hsum
    have h8 : a * b ≤ (c ^ 2) / 4 := by
      nlinarith [sq_nonneg (a - b), sq_nonneg (a + b - c), mul_pos ha hb,
      sq_nonneg (c - (a + b)),
      mul_nonneg (show 0 ≤ c - (a + b) by nlinarith) (show 0 ≤ (a + b) by nlinarith)]
    have h9 : Real.log a + Real.log b = Real.log (a * b) := by
      rw [Real.log_mul (by positivity) (by positivity)]
    have h10 : 2 * Real.log c - 2 * Real.log (2 : ℝ) = Real.log (c ^ 2 / 4) := by
      have hc_pos : c > 0 := by
        nlinarith
      have hc2_pos : c ^ 2 > 0 := by
        have hc_pos' : c > 0 := hc_pos
        positivity
      have h11 : Real.log (c ^ 2 / 4) = Real.log (c ^ 2) - Real.log (4 : ℝ) := by
        have h4_pos : (4 : ℝ) > 0 := by norm_num
        rw [Real.log_div (by linarith) (by linarith)]
      have h12 : Real.log (c ^ 2) = 2 * Real.log c := by
        simp [Real.log_pow]
      have h13 : Real.log (4 : ℝ) = 2 * Real.log (2 : ℝ) := by
        calc
          Real.log (4 : ℝ) = Real.log ((2 : ℝ) ^ 2) := by norm_num
          _ = 2 * Real.log (2 : ℝ) := by simp [Real.log_pow]
      rw [h11, h12, h13]
    have h14 : Real.log (a * b) ≤ Real.log (c ^ 2 / 4) := by
      apply Real.log_le_log
      · -- Show that a * b > 0
        positivity
      · -- Show that a * b ≤ c^2 / 4
        linarith [h8]
    nlinarith [h9, h10, h14]
  have h8 : Real.log a / Real.log (2 : ℝ) + Real.log b / Real.log (2 : ℝ)
    ≤ 2 * (Real.log c / Real.log (2 : ℝ)) - 2 := by
    have h9 : Real.log (2 : ℝ) > 0 := h5
    have h10 : Real.log a + Real.log b ≤ 2 * Real.log c - 2 * Real.log (2 : ℝ) := h6
    have h11 : Real.log a / Real.log (2 : ℝ) +
      Real.log b / Real.log (2 : ℝ) = (Real.log a + Real.log b) / Real.log (2 : ℝ) := by
      ring_nf
    have h12 : 2 * (Real.log c / Real.log (2 : ℝ)) - 2 =
       (2 * Real.log c - 2 * Real.log (2 : ℝ)) / Real.log (2 : ℝ) := by grind
    rw [h11, h12]
    exact (div_le_div_iff_of_pos_right h5).mpr h6
  linarith

def valid_rot (s : BinaryTree) (rt : Rot) : Prop :=
  match rt, s with
  -- Double rotations require a grandchild
  | .zigZig, .node (.node (.node _ _ _) _ _) _ _ => True
  | .zigZag, .node (.node _ _ (.node _ _ _)) _ _ => True
  | .zagZag, .node _ _ (.node _ _ (.node _ _ _)) => True
  | .zagZig, .node _ _ (.node (.node _ _ _) _ _) => True
  -- Single rotations only require a child
  | .zig,    .node (.node _ _ _) _ _             => True
  | .zag,    .node _ _ (.node _ _ _)             => True
  -- Everything else is invalid
  | _, _ => False

lemma valid_rot_imp (s : BinaryTree) (rt : Rot) : valid_rot s rt →
  match rt with
  | .zigZig => ∃ A x B p C g D, s = .node (.node (.node A x B) p C) g D
    ∧ ((rotate s .zigZig) = .node A x (.node B p (.node C g D)))
  | .zigZag => ∃ A p B x C g D, s = .node (.node A p (.node B x C)) g D
    ∧ ((rotate s .zigZag) = .node (.node A p B) x (.node C g D))
  | .zagZag => ∃ A g B p C x D, s = .node A g (.node B p (.node C x D))
    ∧ ((rotate s .zagZag) = .node (.node (.node A g B) p C) x D)
  | .zagZig => ∃ A g B x C p D, s = .node A g (.node (.node B x C) p D)
    ∧ ((rotate s .zagZig) = .node (.node A g B) x (.node C p D))
  | .zig => ∃ A x B p C, s = .node (.node A x B) p C
    ∧ (rotate s .zig) = .node A x (.node B p C)
  | .zag => ∃ A p B x C, s = .node A p (.node B x C)
    ∧ (rotate s .zag) = .node (.node A p B) x C := by
  intro h
  split
  all_goals
  simp [valid_rot] at h
  split at h <;> simp_all [rotate,rotateRight,rotateLeft]

/-
Zig-Zig (Left-Left): rotate right twice
      g              x
     / \            / \
    p   D    =>    A   p
   / \                / \
  x   C              B   g
 / \                    / \
A   B                  C   D
-/

/-
Zag-Zag (Right-Right): rotate left twice
  x                  z
 / \                / \
A   y      =>      y   D
   / \            / \
  B   z          x   C
     / \        / \
    C   D      A   B
-/

/-
Zag-Zig (Right-Left): rotate right on right child, then rotate left
  g                x
 / \              / \
A   p      =>    g   p
   / \          / \ / \
  x   D        A  B C  D
 / \
B   C
-/

theorem pot_change_rotation (s : BinaryTree) (rt : Rot)
   : valid_rot s rt ->
  let result := rotate s rt
  let x_rank := target_rank s rt
  φ result - φ s ≤
    match rt with
    | .zigZig | .zigZag | .zagZag | .zagZig =>  3 * (rank result - x_rank) - 2
    | .zig | .zag => 3 * (rank result - x_rank)
  := by
  intro h result x_rank
  split <;> expose_names
  · -- Zigzig
    apply valid_rot_imp at h;simp at h; obtain ⟨A,x,B,p,C,g,D,⟨hs,hs'⟩⟩ := h
    subst result
    rw [hs']
    subst hs
    dsimp [φ]
    have: rank (A.node x (B.node p (C.node g D))) = rank (((A.node x B).node p C).node g D) := by
      suffices (A.node x (B.node p (C.node g D))).num_nodes =
              (((A.node x B).node p C).node g D).num_nodes by grind [rank]
      simp [BinaryTree.num_nodes]
      ring

    suffices (rank (B.node p (C.node g D)) + rank (C.node g D)) -
      ((rank ((A.node x B).node p C) + rank (A.node x B))) ≤
    3 * (rank (A.node x (B.node p (C.node g D))) - rank (A.node x B)) - 2 by grind [target_rank]

    let r'p := rank (B.node p (C.node g D))
    let r'g := rank (C.node g D)
    let rp := rank ((A.node x B).node p C)
    let rx := rank (A.node x B)
    let r'x:= rank (A.node x (B.node p (C.node g D)))

    change r'p + r'g - (rp + rx) ≤ 3*(r'x-rx)-2

    have rxr'g: rx + r'g ≤ 2*r'x - 2 := by
      simp [rx,r'g,r'x,rank,BinaryTree.num_nodes]
      apply log_sum_le <;> linarith

    have r'prp:  r'p - rp ≤ r'x - rx := by
      have : r'p ≤ r'x := by
        simp [r'p,r'x,rank,BinaryTree.num_nodes]
        apply Real.logb_le_logb_of_le
        all_goals linarith
      have : rx ≤ rp := by
        simp [rx,rp,rank,BinaryTree.num_nodes]
        apply Real.logb_le_logb_of_le
        all_goals linarith
      linarith

    calc
      r'p + r'g - (rp + rx) = r'p + (rx + r'g) - (rp + 2*rx) := by linarith
      _ ≤ r'p - rp + 2*r'x - 2*rx - 2 := by linarith
      _ ≤ 3 * (r'x - rx) - 2 := by linarith
  · -- zigZag
/-
Zag-Zig (Right-Left): rotate right on right child, then rotate left
  g                x
 / \              / \
A   p      =>    g   p
   / \          / \ / \
  x   D        A  B C  D
 / \
B   C
-/
    apply valid_rot_imp at h;simp at h; obtain ⟨A,p,B,x,C,g,D,⟨hs,hs'⟩⟩ := h
    subst result
    rw [hs']
    subst hs
    dsimp [φ]
    have: rank ((A.node p B).node x (C.node g D)) = rank ((A.node p (B.node x C)).node g D)  := by
      suffices ((A.node p B).node x (C.node g D)).num_nodes =
             ((A.node p (B.node x C)).node g D).num_nodes by grind [rank]
      simp [BinaryTree.num_nodes]
      ring

    suffices (rank (A.node p B)) + (rank (C.node g D)) -
    ((rank (A.node p (B.node x C))  + (rank (B.node x C)))) ≤
  3 * (rank ((A.node p B).node x (C.node g D)) - x_rank) - 2 by grind
    dsimp [x_rank,target_rank]

    let r'p := rank (A.node p B)
    let r'g := rank (C.node g D)
    let rp := rank (A.node p (B.node x C))
    let rx := rank (B.node x C)
    let r'x:= rank ((A.node p B).node x (C.node g D))

    change r'p + r'g - (rp + rx) ≤ 3*(r'x-rx)-2

    have gain: r'p + r'g ≤ 2*r'x - 2 := by
      simp [r'p,r'g,r'x,rank,BinaryTree.num_nodes]
      apply log_sum_le <;> linarith
    have : rx ≤ rp := by
        simp [rx,rp,rank,BinaryTree.num_nodes]
        apply Real.logb_le_logb_of_le
        all_goals linarith

    grw [gain]
    grw [← this]
    suffices  2 *(r'x - rx) ≤ 3 * (r'x - rx)   by grind
    suffices (rx ≤ r'x ) by grind
    simp [rx,r'x,rank,BinaryTree.num_nodes]
    apply Real.logb_le_logb_of_le
    all_goals linarith

  · -- zagZag
    apply valid_rot_imp at h;simp at h; obtain ⟨A,g,B,p,C,x,D,⟨hs,hs'⟩⟩ := h
    subst result
    rw [hs']
    subst hs
    dsimp [φ]
    have: rank (((A.node g B).node p C).node x D) = rank (A.node g (B.node p (C.node x D))) := by
      suffices (((A.node g B).node p C).node x D).num_nodes =
               (A.node g (B.node p (C.node x D))).num_nodes by grind [rank]
      simp [BinaryTree.num_nodes]
      ring

    suffices  (rank ((A.node g B).node p C) + (rank (A.node g B) ) ) -
    ( (rank (B.node p (C.node x D)) + (rank (C.node x D)))) ≤
    3 * (rank (((A.node g B).node p C).node x D) - x_rank) - 2 by grind

    let r'p := rank ((A.node g B).node p C)
    let r'g := rank (A.node g B)
    let rp := rank (B.node p (C.node x D))
    let rx := rank (C.node x D)
    let r'x:= rank (((A.node g B).node p C).node x D)

    change r'p + r'g - (rp + rx) ≤ 3*(r'x-rx)-2

    have rxr'g: rx + r'g ≤ 2*r'x - 2 := by
      simp [rx,r'g,r'x,rank,BinaryTree.num_nodes]
      apply log_sum_le <;> linarith

    have r'prp:  r'p - rp ≤ r'x - rx := by
      have : r'p ≤ r'x := by
        simp [r'p,r'x,rank,BinaryTree.num_nodes]
        apply Real.logb_le_logb_of_le
        all_goals linarith
      have : rx ≤ rp := by
        simp [rx,rp,rank,BinaryTree.num_nodes]
        apply Real.logb_le_logb_of_le
        all_goals linarith
      linarith

    calc
      r'p + r'g - (rp + rx) = r'p + (rx + r'g) - (rp + 2*rx) := by linarith
      _ ≤ r'p - rp + 2*r'x - 2*rx - 2 := by linarith
      _ ≤ 3 * (r'x - rx) - 2 := by linarith

  · --zagZig
    apply valid_rot_imp at h;simp at h; obtain ⟨A,g,B,x ,C ,p ,D,⟨hs,hs'⟩⟩ := h
    subst result
    rw [hs']
    subst hs
    dsimp [φ]
    have: rank ((A.node g B).node x (C.node p D)) = rank (A.node g ((B.node x C).node p D)) := by
      suffices ((A.node g B).node x (C.node p D)).num_nodes =
             (A.node g ((B.node x C).node p D)).num_nodes by grind [rank]
      simp [BinaryTree.num_nodes]
      ring

    suffices  (rank (A.node g B)) + (rank (C.node p D) ) -
    ( (rank ((B.node x C).node p D) + (rank (B.node x C) ) )) ≤
  3 * (rank ((A.node g B).node x (C.node p D)) - x_rank) - 2 by grind

    dsimp [x_rank,target_rank]

    let r'p := rank (A.node g B)
    let r'g := rank (C.node p D)
    let rp := rank ((B.node x C).node p D)
    let rx := rank (B.node x C)
    let r'x:= rank ((A.node g B).node x (C.node p D))

    change r'p + r'g - (rp + rx) ≤ 3*(r'x-rx)-2

    have gain: r'p + r'g ≤ 2*r'x - 2 := by
      simp [r'p,r'g,r'x,rank,BinaryTree.num_nodes]
      apply log_sum_le <;> linarith
    have : rx ≤ rp := by
        simp [rx,rp,rank,BinaryTree.num_nodes]
        apply Real.logb_le_logb_of_le
        all_goals linarith

    grw [gain]
    grw [← this]
    suffices  2 *(r'x - rx) ≤ 3 * (r'x - rx)   by grind
    suffices (rx ≤ r'x ) by grind
    simp [rx,r'x,rank,BinaryTree.num_nodes]
    apply Real.logb_le_logb_of_le
    all_goals linarith
  · -- zig
    apply valid_rot_imp at h;simp at h; obtain ⟨A ,x ,B ,p ,C,⟨hs,hs'⟩⟩ := h
    subst result
    rw [hs']
    subst hs
    dsimp [φ]
    have: rank (A.node x (B.node p C)) = rank ((A.node x B).node p C) := by
      suffices (A.node x (B.node p C)).num_nodes =
             ((A.node x B).node p C).num_nodes by grind [rank]
      simp [BinaryTree.num_nodes]
      ring
    suffices  (rank (B.node p C) ) - ((rank (A.node x B) ) ) ≤
      3 * (rank (A.node x (B.node p C)) - x_rank) by grind
    dsimp [x_rank,target_rank]
    have: rank (B.node p C) ≤ rank (A.node x (B.node p C)) := by
      simp [rank,BinaryTree.num_nodes]
      apply Real.logb_le_logb_of_le
      all_goals linarith
    have: rank (A.node x B) ≤ rank (A.node x (B.node p C)) := by
      simp [rank,BinaryTree.num_nodes]
      apply Real.logb_le_logb_of_le
      all_goals linarith
    grind
  · -- zag
    apply valid_rot_imp at h;simp at h; obtain ⟨A ,p ,B ,x ,C,⟨hs,hs'⟩⟩ := h
    subst result
    rw [hs']
    subst hs
    dsimp [φ]
    have: rank (A.node p (B.node x C)) = rank ((A.node p B).node x C) := by
      suffices (A.node p (B.node x C)).num_nodes =
             ((A.node p B).node x C).num_nodes by grind [rank]
      simp [BinaryTree.num_nodes]
      ring
    suffices  (rank (A.node p B) ) - ((rank (B.node x C) ) ) ≤
      3 * (rank (A.node p (B.node x C)) - x_rank) by grind
    dsimp [x_rank,target_rank]
    have: rank (A.node p B) ≤ rank (A.node p (B.node x C)) := by
      simp [rank,BinaryTree.num_nodes]
      apply Real.logb_le_logb_of_le
      all_goals linarith
    have: rank (B.node x C) ≤ rank (A.node p (B.node x C)) := by
      simp [rank,BinaryTree.num_nodes]
      apply Real.logb_le_logb_of_le
      all_goals linarith
    grind

-- How potential changes when only one subtree changes
lemma sum_of_logs_subtree_change (l l' : BinaryTree) (k : ℕ) (r : BinaryTree) :
  φ (.node l' k r) - φ (.node l k r) =
  φ l' - φ l + (rank (.node l' k r) - rank (.node l k r)) := by
  simp [φ]
  ring

lemma sum_of_logs_subtree_change_right (r r' : BinaryTree) (k : ℕ) (l : BinaryTree) :
  φ (.node l k r') - φ (.node l k r) =
  φ r' - φ r + (rank (.node l k r') - rank (.node l k r)) := by
  simp [φ]
  ring


/-- Helper lemma: splaying preserves the number of nodes, hence preserves rank -/
@[simp] lemma rank_splay_eq (t : BinaryTree) (q : ℕ) : rank (splay t q) = rank t := by
  simp [rank, num_nodes_splay]

/-- Helper lemma: splaying preserves the number of nodes, hence preserves rank -/
@[simp] lemma rank_empty : rank BinaryTree.empty = 0 := by simp [rank,BinaryTree.num_nodes];


theorem splay_nonempty_of_nonempty (q : ℕ) (s : BinaryTree) (ne : s ≠ BinaryTree.empty) :
  splay s q ≠ BinaryTree.empty := by
  fun_induction splay <;> simp_all [rotate,rotateRight,rotateLeft]
  all_goals grind

lemma BinaryTree.rank_pos (t : BinaryTree) : 0 ≤ rank t := by
  simp [rank]
  split_ifs
  · rfl
  · refine Real.logb_nonneg ?_ ?_
    · exact one_lt_two
    · expose_names
      norm_cast
      exact Nat.one_le_iff_ne_zero.mpr h

@[simp]
theorem splay_cost_empty_eq (q : ℕ) : splay.cost BinaryTree.empty q = 0 := by rfl


macro "splay_cost_case" : tactic => `(tactic| (
  conv => left; unfold splay.cost
  split_ifs <;> split
  · grw [← splay_cost_pos]; simp
  · expose_names
    rename_i heq
    injection heq
    expose_names
    subst_vars
    split_ifs <;> split
    · simp only [splay_cost_empty_eq, add_zero, Nat.one_le_ofNat]
    · ring_nf; rfl
))

theorem splay_cost_zigZig (q k : ℕ) (r ll : BinaryTree) (lk : ℕ) (lr : BinaryTree)
   (c1 : ¬q = k) (c2 : q < k) (c3 : q < lk) :
  splay.cost ((ll.node lk lr).node k r) q ≤ 2 + splay.cost ll q := by splay_cost_case

theorem splay_cost_zigZag (q k : ℕ) (r ll : BinaryTree) (lk : ℕ)
  (lr : BinaryTree) (c1 : ¬q = k) (c2 : q < k) (c3 : ¬q < lk) (c4 : lk < q) :
  splay.cost ((ll.node lk lr).node k r) q ≤ 2 + splay.cost lr q := by splay_cost_case

theorem splay_cost_zagZig (q : ℕ) (ll : BinaryTree) (lk : ℕ) (h : ¬q = lk) (h_1 : ¬q < lk)
  (ll_1 : BinaryTree) (lk_1 : ℕ) (lr : BinaryTree) (h_2 : q < lk_1) :
  let t := ll_1.node lk_1 lr;
  let original := ll.node lk t;
  let cost := splay.cost original q;
  cost ≤ 2 + splay.cost ll_1 q := by simp;splay_cost_case

theorem splay_cost_zagZag (q : ℕ) (ll : BinaryTree) (lk : ℕ) (h : ¬q = lk) (h_1 : ¬q < lk)
  (ll_1 : BinaryTree) (lk_1 : ℕ) (lr : BinaryTree) (h_2 : ¬q < lk_1) (h_3 : lk_1 < q) :
  let t := ll_1.node lk_1 lr;
  let original := ll.node lk t;
  let cost := splay.cost original q;
  cost ≤ 2 + splay.cost lr q := by simp;splay_cost_case

set_option maxHeartbeats 2000000

theorem splay_potential_change (t : BinaryTree) (q : ℕ) :
  φ (splay t q) - φ t + splay.cost t q ≤
  3 * rank (splay t q) - 3 * rank (subtree_rooted_at t q) + 1 := by
  fun_induction splay
  · simp [subtree_rooted_at,splay.cost]
  · simp [subtree_rooted_at]
    norm_cast
    unfold splay.cost
    grind
  · simp_all [subtree_rooted_at, rank_empty]
    norm_cast
    unfold splay.cost
    simp_all
    expose_names
    grind [BinaryTree.rank_pos]
  · -- Zig but not Zig
    expose_names
    let t := (BinaryTree.node .empty lk_1 lr_1).node lk lr
    let t' := rotate (t) Rot.zig
    let cost := (splay.cost t q)
    change φ t' - φ t + cost ≤ 3 * rank (t') - 3 * rank (subtree_rooted_at t q) + 1
    have h_valid: valid_rot t Rot.zig := by simp [valid_rot,t]
    have pot_res_inter := pot_change_rotation t .zig h_valid
    simp at pot_res_inter
    grw [pot_res_inter]
    have: rank t' = rank t := by simp [t',rotate,rank]
    rw [this]
    simp
    norm_cast
    simp [cost]
    unfold splay.cost
    simp
    split_ifs
    simp [target_rank,t]

    suffices subtree_rooted_at t q  = .empty by
      rw [this]
      simp
      apply BinaryTree.rank_pos

    simp [subtree_rooted_at,h,h_1,subtree_rooted_at,t]
    split_ifs <;> simp_all
  · -- Zig-zig case.
    rename_i k r c1 c2 ll lk lr c3 h_ll_ne ih
    let t' := (splay ll q).node lk lr
    let inter := t'.node k r
    let result := rotate inter .zigZig
    let t := ll.node lk lr
    let original := t.node k r
    let cost := splay.cost original q
    dsimp

    have: rank t' = rank t := by
        simp only [rank, BinaryTree.num_nodes, num_nodes_splay, t', t]
    have rank_inter_orig: rank inter = rank original := by
        simp only [rank, BinaryTree.num_nodes, num_nodes_splay, inter, original, t', t]

    -- Step 1: restate the goal
    change φ result - φ original + cost ≤
      3 * rank (result) - 3 * rank (subtree_rooted_at original q) + 1

    -- Step 2: decompose the potentials into intermediate tree
    have h_decomp_inter : φ result - φ original
      = (φ result - φ inter) + (φ inter - φ original) := by ring

    -- Potential change of (φ inter - φ original) is due to the change in the sub-tree
    have pot_inter_orig :  φ inter - φ original = (φ (splay ll q) - φ ll) :=
      by calc
        φ inter - φ original = (φ t' - φ t) + (rank inter - rank original) :=
          by simp [sum_of_logs_subtree_change, inter, original, t]
        _ = (φ t' - φ t) := by grind
        _ = (φ (splay ll q) - φ ll) + (rank t' - rank t) :=
          by simp [sum_of_logs_subtree_change, t', t]
        _ = φ (splay ll q) - φ ll := by grind
    --

    have h_valid_rot : valid_rot inter .zigZig := by
      unfold valid_rot
      simp [inter,t']
      split <;> all_goals simp_all
      expose_names
      absurd h
      simp
      apply non_empty_exist
      apply splay_nonempty_of_nonempty
      assumption

    -- Potential change of result from inter is due to rotation
    have pot_res_inter : φ result - φ inter ≤ 3 * (rank result - target_rank inter Rot.zigZig) - 2
      := pot_change_rotation inter .zigZig h_valid_rot

    dsimp [target_rank,inter,t'] at pot_res_inter
    replace pos_res_inter : φ result - φ (inter) ≤
      3 * (rank result - rank (splay ll q)) - 2 := by grind

    -- Step 3: rewrite ih
    replace ih:  φ (splay ll q) - φ ll ≤
      3 * rank (splay ll q) - 3 * rank (subtree_rooted_at ll q) + 1 - (splay.cost ll q) := by grind

    rw [h_decomp_inter,pot_inter_orig]
    grw [pot_res_inter,ih]
    have: (subtree_rooted_at original q) = (subtree_rooted_at ll q) := by
      observe: q ≠ lk
      conv =>
        left
        unfold subtree_rooted_at
        simp [c1,c2]
        unfold subtree_rooted_at
        simp [this,c3]

    suffices  cost ≤  2 +  (splay.cost ll q) by grind
    apply splay_cost_zigZig
    all_goals grind
  · expose_names
    -- Zig but not Zag
    let t := (ll.node lk_1 .empty).node lk lr
    let t' := rotate (t) Rot.zig
    let cost := (splay.cost t q)
    change φ t' - φ t + cost ≤ 3 * rank (t') - 3 * rank (subtree_rooted_at t q) + 1
    have h_valid: valid_rot t Rot.zig := by simp [valid_rot,t]
    have pot_res_inter := pot_change_rotation t .zig h_valid
    simp at pot_res_inter
    grw [pot_res_inter]
    have: rank t' = rank t := by simp [t',rotate,rank]
    rw [this]
    simp
    norm_cast
    simp [cost]
    unfold splay.cost
    simp
    split_ifs
    simp [target_rank,t]

    suffices subtree_rooted_at t q  = .empty by
      rw [this]
      simp
      apply BinaryTree.rank_pos

    simp [t,subtree_rooted_at,h,h_1,subtree_rooted_at]
    split_ifs <;> simp_all

  · -- Zig-Zag
    rename_i k r c1 c2 ll lk lr c3 c4 h_lr_ne ih
    let t' := ll.node lk (splay lr q)

    let inter := t'.node k r
    let result := rotate inter .zigZag
    let t := ll.node lk lr
    let original := t.node k r
    let cost := splay.cost original q

    have: rank t' = rank t := by
        simp only [rank, BinaryTree.num_nodes, num_nodes_splay, t', t]
    have rank_inter_orig: rank inter = rank original := by
        simp only [rank, BinaryTree.num_nodes, num_nodes_splay, inter,
        original, t', t]
    dsimp

   /-
    Zig-Zag (Left-Right): rotate left on left child, then rotate right
       k              y
      / \            / \
    (lk)   D  =>    x   z
    /  \           / \ / \
  [ll] [lr]       A  B C  D
      / \
     B   C
    -/

    -- Step 1: restate the goal
    change φ result - φ original + cost ≤
      3 * rank (result) - 3 * rank (subtree_rooted_at original q)+ 1
    -- Step 2: decompose the potentials into intermediate tree

    have h_decomp_inter : φ result - φ original
      = (φ result - φ inter) + (φ inter - φ original) := by ring

    -- Potential change of (φ inter - φ original) is due to the change in the sub-tree
    have pot_inter_orig :  φ inter - φ original = (φ (splay lr q) - φ lr) :=
      by calc
        φ inter - φ original = (φ t' - φ t) + (rank inter - rank original) :=
          by simp [sum_of_logs_subtree_change, inter, original, t]
        _ = (φ t' - φ t) := by grind
        _ = (φ (splay lr q) - φ lr) + (rank t' - rank t) :=
          by simp [sum_of_logs_subtree_change_right, t', t]
        _ = φ (splay lr q) - φ lr := by grind

    have h_valid_rot : valid_rot inter .zigZag := by
      unfold valid_rot
      simp [inter,t']
      split <;> all_goals simp_all
      expose_names
      absurd h
      simp
      apply non_empty_exist
      apply splay_nonempty_of_nonempty
      assumption

    -- Potential change of result from inter is due to rotation
    have pot_res_inter : φ result - φ inter ≤ 3 * (rank result - target_rank inter Rot.zigZag) - 2
      := pot_change_rotation inter .zigZag h_valid_rot

    dsimp [target_rank,inter,t'] at pot_res_inter
    replace pos_res_inter : φ result - φ (inter) ≤
      3 * (rank result - rank (splay lr q)) - 2 := by grind

    -- Step 3: rewrite ih
    replace ih:  φ (splay lr q) - φ lr ≤
      3 * rank (splay lr q) - 3 * rank (subtree_rooted_at lr q) + 1 - (splay.cost lr q) := by grind

    rw [h_decomp_inter,pot_inter_orig]
    grw [pot_res_inter,ih]
    have: (subtree_rooted_at original q) = (subtree_rooted_at lr q) := by
      observe: q ≠ lk
      conv =>
        left
        unfold subtree_rooted_at
        simp [c1,c2]
        unfold subtree_rooted_at
        simp [this,c3]

    suffices cost ≤ 2+(splay.cost lr q) by grind
    apply splay_cost_zigZag
    all_goals grind

  · -- Zig
    expose_names
    have : lk_1 = q := by grind
    subst this
    let t := (ll.node lk_1 lr_1).node lk lr
    let t' := rotate (t) Rot.zig
    let cost := (splay.cost ((ll.node lk_1 lr_1).node lk lr) lk_1)
    change φ t' - φ t + cost ≤ 3 * rank (t') - 3 * rank (subtree_rooted_at t lk_1) + 1
    have h_valid: valid_rot t Rot.zig := by simp [valid_rot,t]
    have pot_res_inter := pot_change_rotation t .zig h_valid
    simp at pot_res_inter
    grw [pot_res_inter]
    have: rank t' = rank t := by simp [t',rotate,rank]
    rw [this]
    simp
    norm_cast
    simp [cost]
    unfold splay.cost
    simp
    split_ifs
    simp [target_rank,t]
    suffices subtree_rooted_at ((ll.node lk_1 lr_1).node lk lr) lk_1  = (ll.node lk_1 lr_1) by grind
    simp [subtree_rooted_at,h,h_1,subtree_rooted_at]

  · -- base case
    expose_names
    simp_all [subtree_rooted_at]
    split
    · grind
    · norm_cast
      unfold splay.cost
      split <;>
      all_goals simp_all
      grind [BinaryTree.rank_pos]
  · -- Zag not Zig
    expose_names
    let t := ll.node lk (BinaryTree.empty.node lk_1 lr)
    let t' := rotate (t) Rot.zag
    let cost := (splay.cost t q)
    change φ t' - φ t + cost ≤ 3 * rank (t') - 3 * rank (subtree_rooted_at t q) + 1
    have h_valid: valid_rot t Rot.zag := by simp [valid_rot,t]
    have pot_res_inter := pot_change_rotation t .zag h_valid
    simp at pot_res_inter
    grw [pot_res_inter]
    have: rank t' = rank t := by simp [t',rotate,rank]
    rw [this]
    simp
    norm_cast
    simp [cost]
    unfold splay.cost
    simp
    split_ifs
    simp [target_rank,t]

    suffices subtree_rooted_at t q  = .empty by
      rw [this]
      simp
      apply BinaryTree.rank_pos

    simp [t,subtree_rooted_at,h,h_1,subtree_rooted_at]
    split_ifs <;> simp_all
  · -- ZagZig
    expose_names
    let t' := (splay ll_1 q).node lk_1 lr
    let inter := ll.node lk t'
    let result := rotate inter .zagZig
    let t := (ll_1).node lk_1 lr
    let original := ll.node lk t
    let cost := splay.cost original q
    dsimp

    have: rank t' = rank t := by
        simp only [rank, BinaryTree.num_nodes, num_nodes_splay, t', t]
    have rank_inter_orig: rank inter = rank original := by
        simp only [rank, BinaryTree.num_nodes, num_nodes_splay, inter, original, t', t]

    -- Step 1: restate the goal
    change φ result - φ original + cost ≤
      3 * rank (result) - 3 * rank (subtree_rooted_at original q)+ 1
    -- Step 2: decompose the potentials into intermediate tree

    have h_decomp_inter : φ result - φ original
      = (φ result - φ inter) + (φ inter - φ original) := by ring

    -- Potential change of (φ inter - φ original) is due to the change in the sub-tree
    have pot_inter_orig :  φ inter - φ original = (φ (splay ll_1 q) - φ ll_1) :=
      by calc
        φ inter - φ original = (φ t' - φ t) + (rank inter - rank original) :=
          by simp [φ, inter, original, t]; ring
        _ = (φ t' - φ t) := by grind
        _ = (φ (splay ll_1 q) - φ ll_1) + (rank t' - rank t) :=
          by simp [φ, t', t]; ring
        _ = φ (splay ll_1 q) - φ ll_1 := by grind

    have h_valid_rot : valid_rot inter .zagZig := by
      unfold valid_rot
      simp [inter,t']
      split <;> all_goals simp_all
      expose_names
      absurd h_4
      simp
      apply non_empty_exist
      apply splay_nonempty_of_nonempty
      assumption

    -- Potential change of result from inter is due to rotation
    have pot_res_inter : φ result - φ inter ≤ 3 * (rank result - target_rank inter Rot.zagZig) - 2
      := pot_change_rotation inter .zagZig h_valid_rot

    dsimp [target_rank,inter,t'] at pot_res_inter
    replace pos_res_inter : φ result - φ (inter) ≤
      3 * (rank result - rank (splay ll_1 q)) - 2 := by grind

    -- Step 3: rewrite ih
    replace ih:  φ (splay ll_1 q) - φ ll_1 ≤ 3 * rank (splay ll_1 q)
     - 3 * rank (subtree_rooted_at ll_1 q) + 1 - (splay.cost ll_1 q) := by grind

    rw [h_decomp_inter,pot_inter_orig]
    grw [pot_res_inter,ih]
    have: (subtree_rooted_at original q) = (subtree_rooted_at ll_1 q) := by
      observe: q ≠ lk_1
      conv =>
        left
        unfold subtree_rooted_at
        simp [h,h_1]
        unfold subtree_rooted_at
        simp [this,h_2]

    suffices cost ≤ 2+(splay.cost ll_1 q) by grind
    exact splay_cost_zagZig q ll lk h h_1 ll_1 lk_1 lr h_2
  · -- Zag not Zag
    expose_names
    let t := ll.node lk (ll_1.node lk_1 BinaryTree.empty)
    let t' := rotate (t) Rot.zag
    let cost := (splay.cost t q)
    change φ t' - φ t + cost ≤ 3 * rank (t') - 3 * rank (subtree_rooted_at t q) + 1
    have h_valid: valid_rot t Rot.zag := by simp [valid_rot,t]
    have pot_res_inter := pot_change_rotation t .zag h_valid
    simp at pot_res_inter
    grw [pot_res_inter]
    have: rank t' = rank t := by simp [t',rotate,rank]
    rw [this]
    simp
    norm_cast
    simp [cost]
    unfold splay.cost
    simp
    split_ifs
    simp [target_rank,t]

    suffices subtree_rooted_at t q  = .empty by
      rw [this]
      simp
      apply BinaryTree.rank_pos

    simp [subtree_rooted_at,h,h_1,subtree_rooted_at,t]
    split_ifs <;> simp_all
  · -- ZagZag
    expose_names
    --rename_i k r c1 c2 ll lk lr c3 c4 h_lr_ne ih
    let t' := ll_1.node lk_1 (splay lr q)

    let inter := ll.node lk t'
    let result := rotate inter .zagZag
    let t := ll_1.node lk_1 lr
    let original := ll.node lk t
    let cost := splay.cost original q

    have: rank t' = rank t := by
        simp only [rank, BinaryTree.num_nodes, num_nodes_splay, t', t]
    have rank_inter_orig: rank inter = rank original := by
        simp only [rank, BinaryTree.num_nodes, num_nodes_splay, inter,
        original, t', t]
    dsimp

   /-
    Zig-Zag (Left-Right): rotate left on left child, then rotate right
       k              y
      / \            / \
    (lk)   D  =>    x   z
    /  \           / \ / \
  [ll] [lr]       A  B C  D
      / \
     B   C
    -/

    -- Step 1: restate the goal
    change φ result - φ original + cost ≤
      3 * rank (result) - 3 * rank (subtree_rooted_at original q)+ 1
    -- Step 2: decompose the potentials into intermediate tree

    have h_decomp_inter : φ result - φ original
      = (φ result - φ inter) + (φ inter - φ original) := by ring

    -- Potential change of (φ inter - φ original) is due to the change in the sub-tree
    have pot_inter_orig :  φ inter - φ original = (φ (splay lr q) - φ lr) :=
      by calc
        φ inter - φ original = (φ t' - φ t) + (rank inter - rank original) :=
          by simp [φ, inter, original, t];ring
        _ = (φ t' - φ t) := by grind
        _ = (φ (splay lr q) - φ lr) + (rank t' - rank t) :=
          by simp [sum_of_logs_subtree_change_right, t', t]
        _ = φ (splay lr q) - φ lr := by grind

    have h_valid_rot : valid_rot inter .zagZag := by
      unfold valid_rot
      simp [inter,t']
      split <;> all_goals simp_all
      expose_names
      absurd h_5
      simp
      apply non_empty_exist
      apply splay_nonempty_of_nonempty
      assumption

    -- Potential change of result from inter is due to rotation
    have pot_res_inter : φ result - φ inter ≤ 3 * (rank result - target_rank inter Rot.zagZag) - 2
      := pot_change_rotation inter .zagZag h_valid_rot

    dsimp [target_rank,inter,t'] at pot_res_inter
    replace pos_res_inter : φ result - φ (inter) ≤
      3 * (rank result - rank (splay lr q)) - 2 := by grind

    -- Step 3: rewrite ih
    replace ih:  φ (splay lr q) - φ lr ≤
      3 * rank (splay lr q) - 3 * rank (subtree_rooted_at lr q) + 1 - (splay.cost lr q) := by grind

    rw [h_decomp_inter,pot_inter_orig]
    grw [pot_res_inter,ih]
    have: (subtree_rooted_at original q) = (subtree_rooted_at lr q) := by
      observe: q ≠ lk_1
      conv =>
        left
        unfold subtree_rooted_at
        simp [h,h_1]
        unfold subtree_rooted_at
        simp [this,h_2,h_3]

    suffices cost ≤ 2+(splay.cost lr q) by grind
    exact splay_cost_zagZag q ll lk h h_1 ll_1 lk_1 lr h_2 h_3

  · -- Zag
    expose_names
    have : lk_1 = q := by grind
    subst this
    let t := ll.node lk (ll_1.node lk_1 lr)
    let t' := rotate (t) Rot.zag
    let cost := (splay.cost (t) lk_1)
    change φ t' - φ t + cost ≤ 3 * rank (t') - 3 * rank (subtree_rooted_at t lk_1) + 1
    have h_valid: valid_rot t Rot.zag := by simp [valid_rot,t]
    have pot_res_inter := pot_change_rotation t .zag h_valid
    simp at pot_res_inter
    grw [pot_res_inter]
    have: rank t' = rank t := by simp [t',rotate,rank]
    rw [this]
    simp
    norm_cast
    simp [cost]
    unfold splay.cost
    simp
    split_ifs
    simp [target_rank,t]
    suffices subtree_rooted_at t lk_1  = (ll_1.node lk_1 lr) by grind
    unfold subtree_rooted_at
    simp [subtree_rooted_at,h,h_1,subtree_rooted_at]

-- Amortized cost of Splay trees
theorem splay_amortized_bound (t : BinaryTree) (q : ℕ) :
  φ (splay t q) - φ t + splay.cost t q ≤ 3 * Real.logb 2 (t.num_nodes) + 1 := by
  have: rank (splay t q) = rank t := rank_splay_eq t q
  calc
    φ (splay t q) - φ t + splay.cost t q ≤
      3 * rank (splay t q) - 3 * rank (subtree_rooted_at t q) + 1 := splay_potential_change t q
    _ ≤ 3 * rank (splay t q) + 1 := by
      have: 0 ≤ rank (subtree_rooted_at t q) := by apply BinaryTree.rank_pos
      grind
    _ ≤ 3 * rank t + 1 := by grind
    _ ≤ 3 * Real.logb 2 (t.num_nodes) + 1 := by
      simp [rank]
      split_ifs with h
      · rw [h]
        simp only [CharP.cast_eq_zero, Real.logb_zero, mul_zero, le_refl]
      · simp
