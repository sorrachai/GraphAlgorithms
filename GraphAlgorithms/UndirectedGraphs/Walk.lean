import MyLean.GraphAlgorithms.Core.Walk
import MyLean.GraphAlgorithms.UndirectedGraphs.SimpleGraphs
import Lean.LibrarySuggestions.Default

-- Authors: Sorrachai Yingchareonthawornchai and Weixuan Yuan
variable {α : Type*}

namespace Walk

set_option tactic.hygienic false

def IsWalkIn_VertexSeq (G : SimpleGraph α) : VertexSeq α → Prop
  | .singleton v => v ∈ G.vertexSet
  | .cons w u    => IsWalkIn_VertexSeq G w ∧ s(w.tail, u) ∈ G.edgeSet

def IsWalkIn (G : SimpleGraph α) (w : Walk α) : Prop :=
  IsWalkIn_VertexSeq G w.seq

lemma prepend_iswalk_in (G : SimpleGraph α) (w : Walk α)
    (hw : IsWalkIn G w) (u : α)
    (hneq : u ≠ w.seq.head) (hedg : s(u, w.seq.head) ∈ G.edgeSet) :
    IsWalkIn G
      ⟨VertexSeq.append (VertexSeq.singleton u) w.seq,
        prepend_iswalk w.seq u w.valid hneq⟩ := by
  suffices ∀ (p : VertexSeq α), IsWalkIn_VertexSeq G p →
      u ≠ p.head → s(u, p.head) ∈ G.edgeSet →
      IsWalkIn_VertexSeq G ((VertexSeq.singleton u).append p) by
    simpa [IsWalkIn] using this w.seq hw hneq hedg
  intro p; induction p with
  | singleton v =>
      intro hp _ he
      simpa [IsWalkIn_VertexSeq, VertexSeq.append] using
        ⟨G.incidence _ he _ (by simp), he⟩
  | cons p v ih =>
      intro ⟨hp, hpv⟩ hne he
      exact ⟨ih hp (by simpa [VertexSeq.head] using hne)
               (by simpa [VertexSeq.head] using he),
             by simpa [VertexSeq.tail_on_tail]⟩

lemma reverse_iswalk_in (G : SimpleGraph α) (w : Walk α) (hw : IsWalkIn G w) :
    IsWalkIn G w.reverse := by
  cases w with | mk seq valid =>
  induction valid with
  | singleton v => simpa [Walk.reverse, IsWalkIn, IsWalkIn_VertexSeq] using hw
  | cons p u hp hneq ih =>
      obtain ⟨hp_in, hedg⟩ : IsWalkIn_VertexSeq G (VertexSeq.cons p u) := by
        simpa [IsWalkIn] using hw
      simpa [Walk.reverse, VertexSeq.reverse] using
        prepend_iswalk_in G (Walk.reverse ⟨p, hp⟩) (ih hp_in) u
          (by simpa [Walk.reverse, Walk.head, Walk.tail] using hneq.symm)
          (by simp [Walk.reverse]; grind)

lemma dropTail_iswalk_in (G : SimpleGraph α) (w : Walk α)
    (hw : IsWalkIn G w) : IsWalkIn G w.dropTail := by
  cases w with | mk seq valid =>
  cases valid with
  | singleton _ => simpa [IsWalkIn, IsWalkIn_VertexSeq, dropTail] using hw
  | cons p u hp _ => simpa [IsWalkIn, dropTail] using (hw : IsWalkIn_VertexSeq G (p.cons u)).1

lemma last_edge_mem (G : SimpleGraph α) (w : Walk α)
    (hw : IsWalkIn G w) (hlen : w.length ≠ 0) :
    s(w.dropTail.tail, w.tail) ∈ G.edgeSet := by
  cases w with | mk seq valid =>
  cases valid with
  | singleton _ => simp [length] at hlen
  | cons p u _ _ => simpa [dropTail, tail] using (hw : IsWalkIn_VertexSeq G (p.cons u)).2

lemma isWalkIn_VertexSeq_append (G : SimpleGraph α)
    (p q : VertexSeq α)
    (hp : IsWalkIn_VertexSeq G p)
    (hq : IsWalkIn_VertexSeq G q)
    (hconn : s(p.tail, q.head) ∈ G.edgeSet) :
    IsWalkIn_VertexSeq G (p.append q) := by
  induction q generalizing p hp with
  | singleton v => simpa [VertexSeq.append, IsWalkIn_VertexSeq] using ⟨hp, hconn⟩
  | cons q v ih =>
      exact ⟨ih p hp hq.1 hconn, by simpa [VertexSeq.append, VertexSeq.tail_on_tail] using hq.2⟩

lemma two_seqs_append_iswalk_in (G : SimpleGraph α)
    (w1 w2 : Walk α)
    (h1 : IsWalkIn G w1) (h2 : IsWalkIn G w2)
    (hneq : w1.tail ≠ w2.head)
    (hedg : s(w1.tail, w2.head) ∈ G.edgeSet) :
    IsWalkIn G ⟨w1.seq.append w2.seq, two_seqs_append_of w1 w2 hneq⟩ := by
  simpa [IsWalkIn] using isWalkIn_VertexSeq_append G w1.seq w2.seq h1 h2 hedg

lemma append_iswalk_in (G : SimpleGraph α)
    (w1 w2 : Walk α)
    (h1 : IsWalkIn G w1) (h2 : IsWalkIn G w2)
    (h : w1.tail = w2.head) :
    IsWalkIn G (append w1 w2 h) := by
  by_cases hlen0 : w1.length = 0
  · simpa [Walk.append, hlen0] using h2
  · have hneq' : w1.dropTail.tail ≠ w2.head := by
      intro hEq; exact hlen0 (len_zero_of_drop_tail_eq_tail w1 (by simpa [h] using hEq))
    simpa [Walk.append, hlen0] using
      two_seqs_append_iswalk_in G w1.dropTail w2
        (dropTail_iswalk_in G w1 h1) h2 hneq'
        (by simpa [h] using last_edge_mem G w1 h1 hlen0)

lemma takeUntil_iswalk_in [DecidableEq α] (G : SimpleGraph α)
    (w : Walk α) (v : α) (h : v ∈ w.support) (hw : IsWalkIn G w) :
    IsWalkIn G ⟨w.seq.takeUntil v h, takeUntil_iswalk w.seq v h w.valid⟩ := by
  cases w with | mk seq valid =>
  induction valid generalizing v with
  | singleton x => simpa [support, IsWalkIn, IsWalkIn_VertexSeq, VertexSeq.takeUntil] using hw
  | cons p u hp hneq ih =>
      obtain ⟨hp_in, hedg⟩ : IsWalkIn_VertexSeq G (VertexSeq.cons p u) := by
        simpa [IsWalkIn] using hw
      by_cases hmem : v ∈ p.toList
      · simpa [support, VertexSeq.takeUntil, hmem, IsWalkIn] using ih v hmem hp_in
      · have hvu : v = u := by
          have := show v ∈ p.toList ++ [u] by simpa [support, VertexSeq.toList] using h
          simp [List.mem_append, hmem] at this; aesop
        subst hvu
        simpa [support, VertexSeq.takeUntil, hmem, IsWalkIn, IsWalkIn_VertexSeq] using
          ⟨hp_in, hedg⟩

lemma iswalk_in_subgraph (H G : SimpleGraph α) (w : Walk α)
    (hw : IsWalkIn H w) (hsub : SimpleGraph.subgraphOf H G) : IsWalkIn G w := by
  cases w with | mk seq valid =>
  induction valid with
  | singleton v => simpa [IsWalkIn, IsWalkIn_VertexSeq] using hsub.1 hw
  | cons p u hp hneq ih =>
      obtain ⟨hp_in, hedg⟩ : IsWalkIn_VertexSeq H (VertexSeq.cons p u) := by
        simpa [IsWalkIn] using hw
      exact ⟨ih hp_in, hsub.2 hedg⟩

lemma toPath_iswalk_in [DecidableEq α] (G : SimpleGraph α) (w : Walk α)
    (hw : IsWalkIn G w) : IsWalkIn G w.toPath := by
  suffices h : ∀ n : ℕ, ∀ w : Walk α, w.length = n →
      IsWalkIn G w → IsWalkIn G w.toPath by exact h w.length w rfl hw
  intro n
  refine Nat.strong_induction_on n ?_
  intro n ih w hlen hw
  cases w with | mk seq valid =>
  cases valid with
  | singleton v => simpa [Walk.toPath, VertexSeq.loopErase, IsWalkIn, IsWalkIn_VertexSeq] using hw
  | cons w0 u hw0 hneq =>
      obtain ⟨hw0_in, hedg⟩ : IsWalkIn_VertexSeq G (VertexSeq.cons w0 u) := by
        simpa [IsWalkIn] using hw
      have hw0lt : (⟨w0, hw0⟩ : Walk α).length < n := by
        have : 1 + (⟨w0, hw0⟩ : Walk α).length = n := by
          simpa [Walk.length, VertexSeq.length] using hlen
        omega
      by_cases hmem : u ∈ w0.toList
      · let p : Walk α := ⟨w0.takeUntil u hmem, takeUntil_iswalk w0 u hmem hw0⟩
        have hplt : p.length < n := lt_of_le_of_lt
          (by simp [p, Walk.length, VertexSeq.takeUntil_length_le]) hw0lt
        simpa [Walk.toPath, VertexSeq.loopErase, hmem, p] using
          ih p.length hplt p rfl
            (takeUntil_iswalk_in G ⟨w0, hw0⟩ u (by simpa [support, VertexSeq.toList]) hw0_in)
      · have hw0P := ih _ hw0lt (⟨w0, hw0⟩ : Walk α) rfl hw0_in
        simpa [Walk.toPath, VertexSeq.loopErase, hmem, IsWalkIn, IsWalkIn_VertexSeq] using
          ⟨hw0P, by simpa [Walk.tail_toPath] using hedg⟩

end Walk

namespace SimpleGraphs

/-- `u` can reach `v` in `G` iff there exists a walk in `G` from `u` to `v`. -/
def Reachable (G : SimpleGraph α) (u v : α) : Prop :=
  ∃ w : Walk α, Walk.IsWalkIn G w ∧ w.head = u ∧ w.tail = v

/-- `G` is connected iff every two vertices in `vertexSet` are reachable. -/
def Connected (G : SimpleGraph α) : Prop :=
  ∀ u v : α, u ∈ G.vertexSet → v ∈ G.vertexSet → Reachable G u v

/-- `G` is acyclic iff it contains no simple cycle. -/
def Acyclic (G : SimpleGraph α) : Prop :=
  ¬ ∃ w : Walk α, Walk.IsWalkIn G w ∧ Walk.IsCycle w

theorem reachable_refl (G : SimpleGraph α) (v : α) (hv : v ∈ G.vertexSet) :
    Reachable G v v := by
  use ⟨VertexSeq.singleton v, IsWalk.singleton v⟩
  refine ⟨?_, rfl, rfl⟩
  simpa [Walk.IsWalkIn, Walk.IsWalkIn_VertexSeq] using hv

theorem reachable_symm (G : SimpleGraph α) (u v : α) (huv : Reachable G u v) :
    Reachable G v u := by
  obtain ⟨w, hw, hu, hv⟩ := huv
  use w.reverse
  simp_all [Walk.reverse_iswalk_in G w hw, Walk.head_reverse, Walk.tail_reverse]

theorem reachable_trans (G : SimpleGraph α) (u v w : α)
    (huv : Reachable G u v) (hvw : Reachable G v w) : Reachable G u w := by
  rcases huv with ⟨w1, h1, hu, hv⟩
  rcases hvw with ⟨w2, h2, hv', hw⟩
  have h : w1.tail = w2.head := by
    calc
      w1.tail = v := hv
      _ = w2.head := hv'.symm
  refine ⟨Walk.append w1 w2 h, Walk.append_iswalk_in G w1 w2 h1 h2 h, ?_, ?_⟩
  · grind [Walk.head_on_head]
  · grind [Walk.tail_on_tail]

end SimpleGraphs
