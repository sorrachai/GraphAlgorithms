import Mathlib.Data.Sym.Sym2
-- Authors: Sorrachai Yingchareonthawornchai and Weixuan Yuan

set_option tactic.hygienic false
variable {α : Type*}

/- A nonempty sequence of vertices, built by appending vertices on the tail side. -/
@[grind] inductive VertexSeq (α : Type*)
  | singleton (v : α) : VertexSeq α
  | cons (w : VertexSeq α) (v : α) : VertexSeq α

namespace VertexSeq

/-! ### Basic accessors -/

/-- The vertices of a `VertexSeq` as a list, in traversal order. -/
@[grind] def toList : VertexSeq α → List α
  | .singleton v => [v]
  | .cons p v => p.toList.cons v

/-- The first node does not count in the sequence. -/
@[grind] def length : VertexSeq α → ℕ
  | .singleton _ => 0
  | .cons w _ => 1 + w.length

/-- The first vertex of a nonempty vertex sequence. -/
@[grind] def head : VertexSeq α → α
  | .singleton v => v
  | .cons w _ => head w

/-- The last vertex of a nonempty vertex sequence. -/
@[grind] def tail : VertexSeq α → α
  | .singleton v => v
  | .cons _ v => v

/-- The head of a singleton sequence is its unique vertex. -/
@[simp, grind =] lemma singleton_head_eq (u : α) :
  (VertexSeq.singleton u).head = u := by simp [head]
/-- The tail of a singleton sequence is its unique vertex. -/
@[simp, grind =] lemma singleton_tail_eq (u : α) :
  (VertexSeq.singleton u).tail = u := by simp [tail]

/-- Appending a vertex at the tail does not change the head. -/
@[simp, grind =] lemma cons_head_eq (w : VertexSeq α) (u : α) :
    (w.cons u).head = w.head := rfl

/-- Appending a vertex at the tail makes that vertex the tail. -/
@[simp, grind =] lemma cons_tail_eq (w : VertexSeq α) (u : α) :
    (w.cons u).tail = u := rfl

/-- The head vertex appears in the underlying list. -/
@[simp, grind ←] lemma head_mem_toList (w : VertexSeq α) : w.head ∈ w.toList := by
  induction w <;> grind

/-! ### dropHead, dropTail, append, reverse -/

/-- Drop the head vertex, leaving singletons unchanged. -/
@[grind] def dropHead : VertexSeq α → VertexSeq α
  | .singleton v => .singleton v
  | .cons (.singleton _) v => .singleton v
  | .cons w v => .cons (dropHead w) v

/-- Drop the tail vertex, leaving singletons unchanged. -/
@[grind] def dropTail : VertexSeq α → VertexSeq α
  | .singleton v => .singleton v
  | .cons w _ => w

/-- Append two nonempty vertex sequences, keeping both endpoints. -/
@[grind] def append : VertexSeq α → VertexSeq α → VertexSeq α
  | w, .singleton v => .cons w v
  | w, .cons w2 v => .cons (append w w2) v

/-- Reverse a vertex sequence. -/
@[grind] def reverse : VertexSeq α → VertexSeq α
  | .singleton v => .singleton v
  | .cons w v => append (.singleton v) (reverse w)

/-- The length of an append is the sum of lengths plus the connecting vertex. -/
@[simp, grind =] lemma length_append (p q : VertexSeq α) :
  (p.append q).length = p.length + q.length + 1 := by
  fun_induction append p q <;> grind

/-- Reversing a singleton leaves it unchanged. -/
@[simp, grind =] lemma singleton_reverse_eq (v : α) :
  (VertexSeq.singleton v).reverse = .singleton v := rfl

/-- The tail of an append is the tail of the second sequence. -/
@[simp, grind =] lemma append_tail (p q : VertexSeq α) : (p.append q).tail = q.tail := by
  fun_induction append <;> simp_all [tail]

/-- The head of an append is the head of the first sequence. -/
@[simp, grind =] lemma append_head (p q : VertexSeq α) : (p.append q).head = p.head := by
  fun_induction append <;> simp_all

/-- Appending a singleton puts its vertex at the tail. -/
@[simp, grind =] lemma append_singleton_tail (p : VertexSeq α) (x : α) :
    (p.append (.singleton x)).tail = x := by
  unfold append
  unfold tail
  split <;> aesop

/-- A singleton prepended to a sequence supplies the head. -/
@[simp, grind =] lemma singleton_append_head (p : VertexSeq α) (x : α) :
  ((VertexSeq.singleton x).append p).head = x := by
  unfold append
  unfold head
  split <;> aesop

/-- Append is associative. -/
@[simp, grind =] lemma append_assoc (p q r : VertexSeq α) :
    (p.append q).append r = p.append (q.append r) := by
  fun_induction append q r <;> simp_all [append]

/-- Reversing an append swaps the reversed factors. -/
@[simp, grind =] lemma reverse_append (p q : VertexSeq α) :
    (p.append q).reverse = q.reverse.append p.reverse := by
  fun_induction append <;> simp_all [reverse]

/-- Reversing twice gives the original sequence. -/
@[simp, grind =] lemma reverse_reverse (p : VertexSeq α) : (p.reverse).reverse = p := by
  fun_induction reverse p <;> aesop

/-- The head of a reversed sequence is the original tail. -/
@[simp, grind =] lemma head_reverse (p : VertexSeq α) : (p.reverse).head = p.tail := by
  fun_induction reverse p <;> aesop

/-- The tail of a reversed sequence is the original head. -/
@[simp, grind =] lemma tail_reverse (p : VertexSeq α) : (p.reverse).tail = p.head := by
  fun_induction reverse p <;> aesop

/-- Dropping the tail preserves the head. -/
@[simp, grind =] lemma dropTail_head (p : VertexSeq α) : p.dropTail.head = p.head := by
  fun_induction reverse p <;> aesop

/-- The tail vertex appears in the underlying list. -/
@[simp, grind ←] lemma tail_mem_toList (w : VertexSeq α) : w.tail ∈ w.toList := by
  induction w <;> grind [VertexSeq.toList, VertexSeq.tail]

/-- The list of an append is the second list followed by the first list. -/
@[simp, grind =] lemma toList_append (p q : VertexSeq α) :
    (p.append q).toList = q.toList ++ p.toList := by
  induction q generalizing p <;> grind

/-! ### takeUntil, dropUntil -/

/-- Take vertices until the first occurrence of `v` (including `v`). -/
@[simp, grind] def takeUntil [DecidableEq α] (w : VertexSeq α) (v : α)
  (h : v ∈ w.toList) : VertexSeq α :=
  match w with
  | .singleton x => .singleton x
  | .cons w2 x =>
    if h2 : v ∈ w2.toList then takeUntil w2 v h2
    else .cons w2 x

/-- Drop vertices until the last occurrence of `v` (not including `v`). -/
@[simp, grind] def dropUntil [DecidableEq α] (w : VertexSeq α) (v : α)
  (h : v ∈ w.toList) : VertexSeq α :=
  match w with
  | .singleton x => .singleton x
  | .cons w2 x =>
    if h2 : v ∈ w2.toList then .cons (dropUntil w2 v h2) x
    else .singleton x

/-- Taking until a vertex never increases length. -/
@[simp] lemma takeUntil_length_le [DecidableEq α] (w : VertexSeq α) (v : α)
    (h : v ∈ w.toList) : (w.takeUntil v h).length ≤ w.length := by
  fun_induction takeUntil w v h <;> grind

/-- Dropping until a vertex never increases length. -/
@[simp] lemma dropUntil_length_le [DecidableEq α] (w : VertexSeq α) (v : α)
    (h : v ∈ w.toList) : (w.dropUntil v h).length ≤ w.length := by
  fun_induction dropUntil w v h <;> grind

/-- `takeUntil` preserves the original head. -/
@[simp, grind =] lemma head_takeUntil [DecidableEq α] (w : VertexSeq α) (v : α)
    (h : v ∈ w.toList) :
    (takeUntil w v h).head = w.head := by
  induction w <;> grind

/-- `takeUntil` ends at the requested vertex. -/
@[simp, grind =] lemma tail_takeUntil [DecidableEq α] (w : VertexSeq α) (v : α)
    (h : v ∈ w.toList) :
    (takeUntil w v h).tail = v := by
  induction w <;> grind

/-- Every vertex in `takeUntil` already occurred in the original sequence. -/
@[simp, grind →] lemma mem_takeUntil [DecidableEq α] (w : VertexSeq α)
  (v x : α) (h : v ∈ w.toList) : x ∈ (takeUntil w v h).toList → x ∈ w.toList := by
  induction w generalizing v <;> grind

/-- `dropUntil` starts at the requested vertex. -/
@[simp, grind =] lemma head_dropUntil [DecidableEq α] (w : VertexSeq α) (v : α)
    (h : v ∈ w.toList) :
    (w.dropUntil v h).head = v := by
  induction w <;> grind

/-- `dropUntil` preserves the original tail. -/
@[simp, grind =] lemma tail_dropUntil [DecidableEq α] (w : VertexSeq α) (v : α)
    (h : v ∈ w.toList) :
    (w.dropUntil v h).tail = w.tail := by
  fun_induction VertexSeq.dropUntil w v h <;> simp [VertexSeq.tail]

/-- Every vertex in `dropUntil` already occurred in the original sequence. -/
@[simp, grind →] lemma mem_dropUntil [DecidableEq α] (w : VertexSeq α) (v x : α)
    (h : v ∈ w.toList) : x ∈ (w.dropUntil v h).toList → x ∈ w.toList := by
  induction w generalizing v <;> grind

/-- Taking until the head returns the singleton head sequence. -/
@[simp, grind .] lemma takeUntil_head_eq_singleton [DecidableEq α] (w : VertexSeq α)
    (h : w.head ∈ w.toList) :
    w.takeUntil w.head h = VertexSeq.singleton w.head := by
  induction w <;> grind

/-- Dropping until the head returns the original sequence. -/
@[simp, grind .] lemma dropUntil_head_eq_self [DecidableEq α] (w : VertexSeq α)
    (h : w.head ∈ w.toList) :
    w.dropUntil w.head h = w := by
  induction w <;> grind

/-! ### Loop erasure -/

/-- Erase loops by repeatedly cutting back to an earlier occurrence of the tail. -/
@[grind] def loopErase [DecidableEq α] : VertexSeq α → VertexSeq α
  | .singleton v => .singleton v
  | .cons w v =>
      if h : v ∈ w.toList then
        loopErase (takeUntil w v h)
      else
        .cons (loopErase w) v
  termination_by p => p.length
  decreasing_by
  · simp [length]; grind [takeUntil_length_le]
  · simp [length]

/-- Every vertex in `loopErase` already occurred in the original sequence. -/
@[grind →] lemma mem_loopErase [DecidableEq α] (w : VertexSeq α) :
    ∀ {x : α}, x ∈ w.loopErase.toList → x ∈ w.toList := by
  fun_induction loopErase w <;> grind [toList, mem_takeUntil]

/-- Loop erasure produces a duplicate-free vertex list. -/
@[grind ←] theorem loopErase_nodup [DecidableEq α] (w : VertexSeq α) : w.loopErase.toList.Nodup
  := by fun_induction VertexSeq.loopErase w <;> grind [toList, mem_loopErase]

/-- Loop erasure preserves the head. -/
@[simp, grind =] lemma head_loopErase [DecidableEq α] (w : VertexSeq α) : w.loopErase.head = w.head
  := by fun_induction loopErase w <;> simp_all

/-- Loop erasure preserves the tail. -/
@[simp, grind =] lemma tail_loopErase [DecidableEq α] (w : VertexSeq α) : w.loopErase.tail = w.tail
  := by fun_induction loopErase w <;> simp_all

/-- A duplicate-free sequence whose endpoints agree has length zero. -/
lemma length_zero_of_nodup_head_eq_tail
    (w : VertexSeq α) (hnd : w.toList.Nodup) (hht : w.head = w.tail) :
    w.length = 0 := by grind

/-! ### Splitting -/

/-- Split a sequence at an interior vertex into a prefix and suffix. -/
@[simp, grind →] lemma split [DecidableEq α]
    (w : VertexSeq α) (v : α) (h : v ∈ w.toList) (hne : v ≠ w.head) :
  (w.takeUntil v h).dropTail.append (w.dropUntil v h) = w := by
  induction w generalizing v <;> grind

end VertexSeq
