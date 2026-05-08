import GraphAlgorithms.Core.VertexSeq
-- Authors: Sorrachai Yingchareonthawornchai and Weixuan Yuan
-- This definition of walk is well-defined for both directed and undirected simple graphs.

set_option tactic.hygienic false
variable {α : Type*}

/-! ### Walk validity -/

/-- Graph-independent walk validity: adjacent vertices in the sequence are distinct. -/
@[grind] inductive IsWalk : VertexSeq α → Prop
  | singleton (v : α) : IsWalk (.singleton v)
  | cons (w : VertexSeq α) (u : α)
      (hw : IsWalk w)
      (hneq : w.tail ≠ u)
    : IsWalk (.cons w u)

grind_pattern IsWalk.singleton => IsWalk (.singleton v)
grind_pattern IsWalk.cons => IsWalk (.cons w u)

/-- A walk is a vertex sequence bundled with graph-independent walk validity. -/
structure Walk (α : Type*) where
  seq : VertexSeq α
  valid : IsWalk seq

namespace Walk
open VertexSeq

/-- Two walks are equal when their underlying vertex sequences are equal. -/
@[ext] lemma ext {w1 w2 : Walk α} (hseq : w1.seq = w2.seq) : w1 = w2 := by
  cases w1
  cases w2
  cases hseq
  rfl

/-- A nontrivial valid sequence has a valid prefix. -/
@[simp, grind =>] lemma valid_prefix (w2 : VertexSeq α) (v : α)
    (valid : IsWalk (w2.cons v)) : IsWalk w2 := by
  cases valid
  grind

/-- The final step of a valid sequence has distinct endpoints. -/
@[simp, grind <=] lemma tail_ne_of_valid_cons (w2 : VertexSeq α) (v : α)
    (valid : IsWalk (w2.cons v)) : w2.tail ≠ v := by
  cases valid
  grind

/-- Appending two valid sequences with distinct connecting endpoints is valid. -/
@[grind ←]
lemma validSeq_append (w1 w2 : VertexSeq α)
  (h1 : IsWalk w1) (h2 : IsWalk w2) (hneq : w1.tail ≠ w2.head) :
    IsWalk (w1.append w2) := by
  fun_induction w1.append w2 <;> grind

/-- Prepending a distinct vertex to the head of a valid sequence is valid. -/
@[grind ←]
theorem valid_singleton_append (p : VertexSeq α) (v : α) (h : IsWalk p) (h2 : p.head ≠ v) :
  IsWalk ((VertexSeq.singleton v).append p) := by grind

/-- Reversing a valid sequence preserves validity. -/
@[grind →, grind ←]
lemma valid_reverse (w : VertexSeq α) : IsWalk w → IsWalk w.reverse := by
  intro h
  induction h <;> grind

/-- Validity of an appended sequence decomposes into validity and a distinct connector. -/
@[grind →]
theorem valid_append_parts (p q : VertexSeq α) (h : IsWalk (p.append q))
  : IsWalk p ∧ IsWalk q ∧ p.tail ≠ q.head := by fun_induction append <;> grind

/-- Validity of a reversed sequence implies validity of the original sequence. -/
@[grind →]
lemma valid_of_reverse (w : VertexSeq α) : IsWalk w.reverse → IsWalk w := by
  fun_induction reverse <;> grind

/-- Reversal preserves and reflects walk validity. -/
@[simp, grind =]
lemma valid_reverse_iff (w : VertexSeq α) : IsWalk w.reverse ↔ IsWalk w := by grind

/-- A duplicate-free vertex sequence is valid as a walk. -/
@[grind →]
lemma valid_of_nodup (w : VertexSeq α) (h : w.toList.Nodup) : IsWalk w := by
  induction w <;> grind

/-- `takeUntil` preserves walk validity. -/
@[grind →]
lemma valid_takeUntil [DecidableEq α] (w : VertexSeq α) (v : α) (h : v ∈ w.toList)
  (hw : IsWalk w) :
    IsWalk (w.takeUntil v h) := by
  induction hw generalizing v <;> grind

/-- `dropUntil` preserves walk validity. -/
@[grind →]
lemma valid_dropUntil [DecidableEq α] (w : VertexSeq α) (v : α)
    (h : v ∈ w.toList) (hw : IsWalk w) :
    IsWalk (w.dropUntil v h) := by
  induction hw generalizing v <;> grind

/-- Loop erasure always yields a valid walk sequence. -/
lemma valid_loopErase [DecidableEq α] (w : VertexSeq α) : IsWalk w.loopErase := by
  grind [valid_of_nodup, loopErase_nodup]

/-! ### Basic walk wrappers -/

/-- The list of vertices visited by the walk, in order. -/
@[simp, grind] def support (w : Walk α) : List α := w.seq.toList

/-- The first vertex of a walk. -/
abbrev head (w : Walk α) : α := w.seq.head
/-- The last vertex of a walk. -/
abbrev tail (w : Walk α) : α := w.seq.tail
/-- The number of edges represented by a walk. -/
abbrev length (w : Walk α) : ℕ := w.seq.length

/-- Drop the final vertex of a walk, leaving singleton walks unchanged. -/
abbrev dropTail (w : Walk α) : Walk α :=
  { seq := w.seq.dropTail
    valid := by grind [Walk]}

/-- Append one new final vertex to a walk. -/
def append_single (w : Walk α) (u : α) (h : u ≠ w.tail) : Walk α :=
  ⟨w.seq.cons u, .cons w.seq u w.valid (by aesop)⟩

/-- Dropping the tail preserves the head of a walk. -/
@[simp, grind =]
lemma dropTail_head (w : Walk α) : w.dropTail.head = w.head := by
  cases w; induction valid <;> grind

/-- If dropping the tail does not change the tail, the walk has length zero. -/
@[simp, grind .]
lemma zero_of_dropTail_tail (w : Walk α) (h : w.dropTail.tail = w.tail) :
    w.length = 0 := by
  cases w; induction valid <;> grind

/-- A length-zero walk has equal endpoints. -/
@[simp, grind ←]
lemma endpoints_eq_of_zero (w : Walk α) (h : w.length = 0)
  : w.head = w.tail := by
  cases w; induction valid <;> grind

/-- Positive-length walks lose one edge when their tail is dropped. -/
lemma dropTail_length_succ (w : Walk α) (h : w.length ≠ 0) :
    w.dropTail.length + 1 = w.length := by
  cases w; induction valid <;> grind

/-! ### append, reverse -/

/-- The raw append of two walks is valid when their endpoints are distinct. -/
@[grind ←]
lemma valid_appendSeq (w1 w2 : Walk α) (hneq : w1.tail ≠ w2.head) :
    IsWalk (w1.seq.append w2.seq) := by
  cases w1; cases w2; grind

/-- Concatenate two walks whose touching endpoints agree. -/
@[grind =]
def append (w1 w2 : Walk α) (h : w1.tail = w2.head) : Walk α :=
  if h1 : w1.length = 0 then w2
  else
    { seq := w1.dropTail.seq.append w2.seq
      valid := by grind [Walk]}

/-- Reverse a walk. -/
@[grind =]
def reverse (w : Walk α) : Walk α :=
  { seq := w.seq.reverse
    valid := by grind [Walk]}

/-- The head of a reversed walk is the original tail. -/
@[simp, grind =] lemma head_reverse (w : Walk α) : (w.reverse).head = w.tail := by grind
/-- The tail of a reversed walk is the original head. -/
@[simp, grind =] lemma tail_reverse (w : Walk α) : (w.reverse).tail = w.head := by grind
/-- Appending walks preserves the head of the first walk. -/
@[simp, grind =] lemma append_head (w1 w2 : Walk α) (h : w1.tail = w2.head) :
    (Walk.append w1 w2 h).head = w1.head := by
  cases w1; induction valid <;> grind
/-- Appending walks preserves the tail of the second walk. -/
@[simp, grind =] lemma append_tail (w1 w2 : Walk α) (h : w1.tail = w2.head) :
    (Walk.append w1 w2 h).tail = w2.tail := by grind

/-- The length of a walk append is the sum of lengths. -/
@[simp, grind =] lemma length_append (w1 w2 : Walk α) (h : w1.tail = w2.head) :
    (Walk.append w1 w2 h).length = w1.length + w2.length := by
  unfold Walk.append
  by_cases h1 : w1.length = 0
  · grind
  · have hdrop : w1.dropTail.length + 1 = w1.length := by
      cases w1; induction valid <;> grind
    grind

/-! ### Paths and cycles -/

/-- A path is a walk whose support has no duplicate vertices. -/
@[grind] def IsPath (w : Walk α) : Prop := w.support.Nodup

/-- Turn a walk into a path by erasing loops. -/
abbrev toPath [DecidableEq α] (w : Walk α) : Walk α :=
  { seq := w.seq.loopErase
    valid := valid_loopErase w.seq }

/-- Loop erasure turns every walk into a path. -/
theorem isPath_toPath [DecidableEq α] (w : Walk α) : IsPath (toPath w) := by grind

/-- Dropping the tail of a path leaves a path. -/
lemma isPath_dropTail (w : Walk α) (hPath : IsPath w) : IsPath w.dropTail := by
  cases w with
  | mk seq valid =>
      cases valid <;> grind [IsPath, support, VertexSeq.toList]

/-- Converting to a path preserves the tail. -/
@[grind =] lemma toPath_tail [DecidableEq α] (w : Walk α) : (toPath w).tail = w.tail := by
  grind

/-- Converting to a path preserves the head. -/
@[grind =] lemma toPath_head [DecidableEq α] (w : Walk α) : (toPath w).head = w.head := by
  grind

/-- A cycle is a length-at-least-three closed walk whose dropped-tail part is a path. -/
@[grind] def IsCycle (w : Walk α) : Prop :=
  3 ≤ w.length ∧ w.head = w.tail ∧ IsPath w.dropTail

/-! ### takeUntil, dropUntil -/

/-- The walk prefix ending at the first occurrence of a support vertex. -/
@[grind] def takeUntil [DecidableEq α] (w : Walk α) (u : α) (hu : u ∈ w.support) : Walk α :=
  ⟨w.seq.takeUntil u hu, valid_takeUntil w.seq u hu w.valid⟩

/-- The walk suffix starting at the last occurrence of a support vertex. -/
@[grind] def dropUntil [DecidableEq α] (w : Walk α) (u : α) (hu : u ∈ w.support) : Walk α :=
  ⟨w.seq.dropUntil u hu, valid_dropUntil w.seq u hu w.valid⟩

/-- Split a walk at a support vertex into `takeUntil` followed by `dropUntil`. -/
@[simp, grind →] lemma split [DecidableEq α]
  (w : Walk α) (u : α) (hu : u ∈ w.support) :
    w = Walk.append (w.takeUntil u hu) (w.dropUntil u hu) (by grind) := by
  by_cases h : u = w.head
  · ext; grind
  · ext; grind

/-! ### Rerooting cycles -/

/-- Re-root a cycle at any chosen vertex in its support. -/
@[simp, grind] def rerootCycle [DecidableEq α] (w : Walk α) (hcyc : IsCycle w)
    (u : α) (hu : u ∈ w.support) : Walk α :=
  Walk.append (w.dropUntil u hu) (w.takeUntil u hu)
    (by rcases hcyc with ⟨_, hht, _⟩; grind)

/-- Dropping the tail of an append can be pushed to the second walk. -/
@[grind =] lemma dropTail_append (w1 w2 : Walk α) (h : w1.tail = w2.head)
  (hlen : w2.head ≠ w2.tail) :
  (Walk.append w1 w2 h).dropTail = Walk.append w1 w2.dropTail (by grind) := by
  by_cases h1 : w1.length = 0
  · grind
  · ext; cases w2; induction valid <;> grind

/-- Rerooting a cycle at a support vertex preserves the cycle property. -/
@[grind →] lemma isCycle_reroot [DecidableEq α] (w : Walk α) (hcyc : IsCycle w)
  (u : α) (hu : u ∈ w.support) :
  IsCycle (rerootCycle w hcyc u hu):= by
  have h2 : w.length = (w.rerootCycle hcyc u hu).length := by grind
  rcases hcyc with ⟨hlen, hht, hpath⟩
  refine ⟨?_, ?_, ?_⟩
  · grind
  · grind
  · by_cases h : u = w.head
    · have hz : w.length ≠ 0 := by omega
      grind
    · grind

/-- Length-zero walks with the same head are equal. -/
@[grind →] lemma eq_of_zero {p q : Walk α}
    (hp0 : p.length = 0) (hq0 : q.length = 0) (hhead : p.head = q.head) :
    p = q := by cases p; cases q; grind

/-- Positive-length walks are equal when their dropped tails and tails agree. -/
@[grind →] lemma eq_of_parts {p q : Walk α}
    (hp : p.length ≠ 0) (hq : q.length ≠ 0)
    (hdrop : p.dropTail = q.dropTail) (htail : p.tail = q.tail) :
    p = q := by cases p; cases q; grind


end Walk
