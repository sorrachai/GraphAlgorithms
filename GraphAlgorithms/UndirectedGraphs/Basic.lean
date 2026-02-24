import Mathlib.Tactic
import Mathlib.Order.WithBot
import Mathlib.Data.Sym.Sym2
import Mathlib.Data.Finset.Basic

-- Undirected Graphs
-- Authors: Sorrachai Yingchareonthawornchai

set_option tactic.hygienic false
variable {α : Type*} {β : Type*} [DecidableEq α] [DecidableEq β]


structure UndirectedEdge (α β : Type*) where
  id : β
  endpoints : Sym2 α
deriving DecidableEq

abbrev Edge := UndirectedEdge

structure UndirectedGraph (α β : Type*) where
  vertexSet : Finset α
  edgeSet : Finset (Edge α β)
  incidence : ∀ e ∈ edgeSet, ∀ v ∈ e.endpoints, v ∈ vertexSet


def UndirectedGraph.noParallel {α β} (G : UndirectedGraph α β) : Prop :=
  ∀ e ∈ G.edgeSet, ∀ e' ∈ G.edgeSet, e.endpoints = e'.endpoints → e = e'

def UndirectedGraph.LoopLess {α β} (G : UndirectedGraph α β) : Prop :=
  ∀ e ∈ G.edgeSet, ¬ e.endpoints.IsDiag

def UndirectedGraph.Simple {α β} (G : UndirectedGraph α β) : Prop := G.noParallel ∧ G.LoopLess

--  To disallow multi-edges, define β as Unit
abbrev NoParallelUndirectedGraph (α : Type*) := UndirectedGraph α Unit

def SimpleGraph (α : Type*) :=
  { G : NoParallelUndirectedGraph α // ∀ e ∈ G.edgeSet, ¬ e.endpoints.IsDiag }

namespace UndirectedGraph

open Finset

/-- `V(G)` denotes the `vertexSet` of a graph `G`. -/
scoped notation "V(" G ")" => UndirectedGraph.vertexSet G

/-- `E(G)` denotes the `edgeSet` of a graph `G`. -/
scoped notation "E(" G ")" => UndirectedGraph.edgeSet G

abbrev IncidentEdgeSet (G : UndirectedGraph α β) (s : α) :
  Finset (Edge α β) := {e ∈ E(G) | s ∈ e.endpoints}

/-- `δ(G,v)` denotes the `edge-incident-set` of a vertex `v` in `G`. -/

scoped notation "δ(" G "," v ")" => UndirectedGraph.IncidentEdgeSet G v

abbrev Neighbors (G : UndirectedGraph α β) (s : α) :
  Finset α := {u ∈ V(G) | ∃ e ∈ E(G), s ∈ e.endpoints ∧ u ∈ e.endpoints ∧ u ≠ s}

/-- `N(G,v)` denotes the `neighbors` of a graph `G`. -/
scoped notation "N(" G "," v ")" => UndirectedGraph.Neighbors G v

/-- `deg(G)` denotes the `degree` of a graph `G`. -/
scoped notation "deg(" G "," v ")" => #δ(G,v)

abbrev subgraphOf (H G : UndirectedGraph α β) : Prop :=
  V(H) ⊆ V(G) ∧ E(H) ⊆ E(G)

scoped infix:50 " ⊆ᴳ " => UndirectedGraph.subgraphOf

/-- A walk is an alternating sequence of vertices and incident edges.  For vertices `u v : V`,
the type `walk u v` consists of all walks starting at `u` and ending at `v`.
Note that this definition does not depend on the graph.
-/
inductive Walk (α β : Type*) : α → α → Type _ where
  | nil {u : α} : Walk α β u u
  | cons {u v w : α} (e : Edge α β) :
      u ∈ e.endpoints → w ∈ e.endpoints → Walk α β w v → Walk α β u v

scoped notation:50 "(" u "," v ")-Walk-("a "," b ")" => Walk a b u v

namespace Walk

@[trans]
def append {u v w : α} : (u,v)-Walk-(α,β) → (v,w)-Walk-(α,β) → (u,w)-Walk-(α,β)
  | nil, q => q
  | cons e ht hh p, q => cons e ht hh (p.append q)

def reverse {u v : α} : (u,v)-Walk-(α,β) → (v,u)-Walk-(α,β)
  | nil => nil
  | cons e h1 h2 p => p.reverse.append (cons e h2 h1 nil)

def InGraph {u v} (G : UndirectedGraph α β) :  (u,v)-Walk-(α,β) → Prop
  | nil => u ∈ V(G)  --
  | cons e _ _ rest => e ∈ E(G) ∧ rest.InGraph G

example {H G u v} (h : H ⊆ᴳ G) (p : (u,v)-Walk-(α,β)) (hp : p.InGraph H) : p.InGraph G := by
  induction p <;> aesop (add simp [subgraphOf, Walk.InGraph])

/-- The number of edges in the walk. -/
def length {u v : α} : (u,v)-Walk-(α,β) → ℕ
  | Walk.nil => 0
  | Walk.cons _ _ _ p => 1 + p.length

/-- The list of vertices visited by the walk, in order. -/
def support {u v : α} : (u,v)-Walk-(α,β)  → List α
  | nil => [u]
  -- We explicitly capture 'v' (the current start) and 'p' (the rest of the walk)
  | cons (u := u) _ _ _ p => u :: p.support

/-- The list of edges traversed by the walk, in order. -/
def edges {u v : α} : (u,v)-Walk-(α,β) → List (Edge α β)
  | nil => []
  | cons e _ _ p => e :: p.edges

lemma length_support {α β} {u v : α} (p : (u,v)-Walk-(α,β)) :
  p.support.length = p.length + 1 := by
  induction p with
  | nil => rfl
  | cons _ _ _ p_tail ih =>
    -- Simply unfold definitions and use the inductive hypothesis
    simp [support, length, ih]
    omega

lemma mem_support_start {α β} {u v : α} (p : (u,v)-Walk-(α,β)) :
  u ∈ p.support := by
  induction p with
  | nil => simp [support]
  | cons e hv hw p ih => simp [support]

lemma mem_support_end {α β} {u v : α} (p : (u,v)-Walk-(α,β)) :
  v ∈ p.support := by
  induction p with
  | nil => simp [support]
  | cons e hv hw p ih => simp_all [support]



def is_path {u v : α} (p : (u,v)-Walk-(α,β)) : Prop := p.support.Nodup


--We only consider cycles in simple graphs.
def is_cycle {u : α} (p : (u,u)-Walk-(α,β)) : Prop :=
  p.length ≥ 3 ∧ p.support.tail.Nodup

abbrev Path (α β : Type*) (u v : α) := { p : (u,v)-Walk-(α,β) // Walk.is_path p }
scoped notation:50 "(" u "," v ")-Path-("a "," b ")" => Path a b u v

instance {α β : Type*} {u v : α} :
    Coe (Path α β u v) (Walk α β u v) where
  coe p := p.1

@[simp] lemma coe_mk {α β : Type*} {u v : α}
  (p : Walk α β u v) (hp : Walk.is_path p) :
  ((⟨p, hp⟩ : Path α β u v) : Walk α β u v) = p := rfl

/-- Given a vertex in the support of a path, give the path from (and including) that vertex to
the end. In other words, drop vertices from the front of a path until (and not including)
that vertex. -/
def dropUntil {v u : α} :
    ∀ (p : (v,u)-Walk-(α,β)) (x : α), x ∈ p.support → (x,u)-Walk-(α,β)
  | nil, x, hx => by
      have hx' : x = v := by simpa [support] using hx
      subst hx'
      exact Walk.nil
  | cons e hv hw p, x, hx => by
      by_cases h : x = v
      · subst h
        exact Walk.cons e hv hw p
      · have hx_tail : x ∈ p.support := by
          have hx_cons := (List.mem_cons).1 hx
          cases hx_cons with
          | inl hx_eq =>
              exact (h hx_eq).elim
          | inr hx' =>
              exact hx'
        exact dropUntil p x hx_tail

-- dropUntil gives a path if the original walk is a path
lemma dropUntil_preserves_path {u v : α} {p : (u,v)-Walk-(α,β)} (hp : p.is_path)
  (x : α) (hx : x ∈ p.support) :
  (p.dropUntil x hx).is_path := by
  dsimp [Walk.is_path] at hp ⊢
  induction p generalizing x with
  | nil =>
      have hx' : x = u_1 := by
        simp_all [support]
      subst hx'
      simp [dropUntil, support]
  | cons e hv hw p_tail ih =>
      have hp_tail : p_tail.support.Nodup := (List.nodup_cons).1 (by simpa [support] using hp) |>.2
      by_cases h : x = u_1
      · subst h
        simp_all [dropUntil, support]
      · simp_all [dropUntil, support]

def bypass {u v : α} :  (u,v)-Walk-(α,β) → (u,v)-Walk-(α,β)
  | nil => nil
  | cons e h1 h2 p =>
    let p' := p.bypass
    if hs : u ∈ p'.support then p'.dropUntil u hs
    else cons e h1 h2 p'


lemma bypass_is_path {u v : α} (p : (u,v)-Walk-(α,β)) : p.bypass.is_path := by
  induction p with
  | nil => simp! [is_path]
  | cons e h1 h2 p =>
    simp only [bypass]
    split_ifs with hs
    · exact dropUntil_preserves_path a_ih u_1 hs
    · simp_all [is_path, support]

def to_path {u v : α} (p : (u,v)-Walk-(α,β)) : (u,v)-Path-(α,β) :=
  ⟨p.bypass, p.bypass_is_path⟩

def to_cycle? {u : α} : (u,u)-Walk-(α,β) → Option ((u,u)-Walk-(α,β))
  | nil => none
  | cons e hv hw p =>
      let p' := p.bypass
      let q : (u,u)-Walk-(α,β) := Walk.cons e hv hw p'
      if q.length ≥ 3 then some q else none

lemma to_cycle?_is_cycle
  {u : α} (p : (u,u)-Walk-(α,β)) (q : (u,u)-Walk-(α,β))
  (h : p.to_cycle? = some q) :
  q.is_cycle := by
  dsimp [to_cycle?] at h
  cases p with
  | nil => simp_all
  | cons e hu hw p =>
    simp at h; rcases h with ⟨h1, h2⟩; rw[h2] at h1
    simp_all [is_cycle]
    rw[<-h2]; simp [support]
    have := bypass_is_path p; simp_all [is_path]



end Walk




def Reachable (G : UndirectedGraph α β) (u v : α) : Prop := ∃ p : (u,v)-Walk-(α,β), p.InGraph G

def PreConnected (G : UndirectedGraph α β) : Prop :=
  ∀ u v : α, (u ∈ V(G) ∧ v ∈ V(G)) → Reachable G u v

def Acyclic (G : UndirectedGraph α β) : Prop :=
  ∀ u ∈ V(G), ¬ ∃ (p : (u,u)-Walk-(α,β)), p.InGraph G ∧ p.is_cycle



namespace Walk

theorem distinct_path_implies_cyclic {G : UndirectedGraph α β} {u v : α}
  (p q : Path α β u v) (hpq : p ≠ q) (huv : u ≠ v)
  (hp : p.1.InGraph G) (hq : q.1.InGraph G) (hG : Simple G) :
  ¬ G.Acyclic := by
  sorry

end Walk


def Cut (G : UndirectedGraph α β) (U : Finset α) :
  Finset (Edge α β) := {e ∈ E(G) | ∃ u ∈ U, u ∈ e.endpoints ∧ ∃ v ∈ V(G) \ U, v ∈ e.endpoints}

def is_tree (G : UndirectedGraph α β) : Prop := G.PreConnected ∧ G.Acyclic

def is_forest (G : UndirectedGraph α β) : Prop := G.Acyclic

abbrev Tree (α β : Type*) := { G : UndirectedGraph α β // is_tree G }
abbrev Forest (α β : Type*) := { G : UndirectedGraph α β // is_forest G }
-- cuts, contractions

namespace Tree

instance {α β : Type*} : Coe (Tree α β) (UndirectedGraph α β) where
  coe T := T.1

@[simp] lemma coe_mk {α β : Type*}
  (G : UndirectedGraph α β) (h : is_tree G) :
  ((⟨G, h⟩ : Tree α β) : UndirectedGraph α β) = G := rfl


end Tree

namespace Cut
open Finset BigOperators

variable {R} [AddCommMonoid R] [CompleteLattice R] [CanonicallyOrderedAdd R]

def weight (G : UndirectedGraph α β) (U : Finset α) (w : Edge α β → R) : R :=
  Finset.sum (Cut G U) w


-- def size (G : UndirectedGraph α β) (U : Finset α) : ℕ := (Cut G U).card


lemma cut_submodular_grind (G : UndirectedGraph α β) (U W : Finset α) (w : Edge α β → R) :
  weight G (U ∩ W) w + weight G (U ∪ W) w ≤ weight G U w + weight G W w := by
  have h1 : Cut G (U ∩ W) ⊆ Cut G U ∪ Cut G W := by grind [Cut]
  have h2 : Cut G (U ∪ W) ⊆ Cut G U ∪ Cut G W := by grind [Cut]
  have h3 : Cut G (U ∩ W) ∩ Cut G (U ∪ W) ⊆ Cut G U ∩ Cut G W := by grind [Cut]
  have h : (G.Cut (U ∩ W)) ∪ (G.Cut (U ∪ W)) ⊆ (G.Cut U) ∪ (G.Cut W) := by apply union_subset h1 h2
  clear h1 h2
  repeat unfold weight
  rw[<-Finset.sum_union_inter]
  nth_rw 2 [<-Finset.sum_union_inter]
  have h3 : Finset.sum (G.Cut (U ∩ W) ∩ G.Cut (U ∪ W)) w ≤ Finset.sum (G.Cut U ∩ G.Cut W) w := by
    apply Finset.sum_le_sum_of_subset h3
  have h : Finset.sum (G.Cut (U ∩ W) ∪ G.Cut (U ∪ W)) w ≤ Finset.sum (G.Cut U ∪ G.Cut W) w := by
    apply Finset.sum_le_sum_of_subset h
  apply add_le_add h h3

lemma cut_submodular (G : UndirectedGraph α β) (U W : Finset α) (w : Edge α β → R) :
  weight G (U ∩ W) w + weight G (U ∪ W) w ≤ weight G U w + weight G W w := by
  have h1 : Cut G (U ∩ W) ⊆ Cut G U ∪ Cut G W := by
    rintro e he
    unfold Cut at he
    simp at he
    rcases he with ⟨h1, ⟨u, h2⟩⟩
    rcases h2 with ⟨⟨huU, huW⟩, h2, v, ⟨h3, h4⟩, h5⟩
    simp
    by_cases hvU : v ∈ U
    · right; apply h4 at hvU; unfold Cut; simp_all; use u; simp_all; use v
    · left; unfold Cut; simp_all; use u; simp_all; use v
  have h2 : Cut G (U ∪ W) ⊆ Cut G U ∪ Cut G W := by
    rintro e he
    unfold Cut at he
    simp at he
    rcases he with ⟨h1, ⟨u, h2⟩⟩
    rcases h2 with ⟨hu, hu1, v, ⟨hv1, hv2, hv3⟩ , hv⟩
    rcases hu with hu|hu
    simp; left; unfold Cut; simp_all; use u; simp_all; use v
    simp; right; unfold Cut; simp_all; use u; simp_all; use v
  have h3 : Cut G (U ∩ W) ∩ Cut G (U ∪ W) ⊆ Cut G U ∩ Cut G W := by
    rintro e he
    simp at he
    rcases he with ⟨he1, he2⟩
    simp [Cut] at he1
    rcases he1 with ⟨he, u, ⟨hu1, hu2⟩, hu3, v, ⟨hv1, hv2⟩, hv3⟩
    have hne : u ≠ v := by by_contra!; subst this; simp_all
    have huv : e.endpoints = s(u,v) := by
      apply (Sym2.mem_and_mem_iff hne).1; simp_all
    have hv4 : v ∉ U ∪ W := by
      by_contra!
      simp [Cut] at he2
      rcases he2 with ⟨he', u', hu1', hu2', v', hv1', hv2'⟩
      rw [huv] at hv2'
      apply Sym2.mem_iff'.1 at hv2'
      rcases hv2' with h|h;
      simp_all; simp_all
    simp; constructor
    unfold Cut; simp_all; use u; simp_all; use v; simp_all
    unfold Cut; simp_all; use u; simp_all; use v; simp_all
  have h : (G.Cut (U ∩ W)) ∪ (G.Cut (U ∪ W)) ⊆ (G.Cut U) ∪ (G.Cut W) := by
    apply union_subset h1 h2
  clear h1 h2
  repeat unfold weight
  rw[<-Finset.sum_union_inter]
  nth_rw 2 [<-Finset.sum_union_inter]
  have h3 : Finset.sum (G.Cut (U ∩ W) ∩ G.Cut (U ∪ W)) w ≤ Finset.sum (G.Cut U ∩ G.Cut W) w := by
    apply Finset.sum_le_sum_of_subset h3
  have h : Finset.sum (G.Cut (U ∩ W) ∪ G.Cut (U ∪ W)) w ≤ Finset.sum (G.Cut U ∪ G.Cut W) w := by
    apply Finset.sum_le_sum_of_subset h
  apply add_le_add h h3

def is_st_cut (G : UndirectedGraph α β) (U : Finset α) (s t : α) : Prop :=
  s ∈ U ∧ t ∉ U ∧ U.Nonempty ∧ U ⊂ V(G)

def is_st_mincut (G : UndirectedGraph α β) (U : Finset α) (s t : α) (w : Edge α β → R) : Prop :=
  is_st_cut G U s t ∧ ∀ W : Finset α, is_st_cut G W s t → weight G U w ≤ weight G W w


def st_mincut_value (G : UndirectedGraph α β) (s t : α) (w : Edge α β → R) : R :=
  sInf { W : R | ∃ U : Finset α, is_st_cut G U s t ∧ weight G U w = W}

lemma st_min_cut {G : UndirectedGraph α β} {U : Finset α} {s t : α} {w : Edge α β → R} :
  is_st_mincut G U s t w ↔ is_st_cut G U s t ∧ weight G U w = st_mincut_value G s t w  := by
  constructor
  · intro h; simp_all [is_st_mincut, st_mincut_value]
    apply le_antisymm
    apply le_sInf
    · rintro b ⟨W, hb1, hb2⟩
      rcases h with ⟨hcut, hmin⟩
      have hW := hmin W hb1
      simp_all
    · apply sInf_le
      use U; simp_all
  · intro h
    unfold is_st_mincut
    simp_all; rintro W hW; unfold st_mincut_value
    apply sInf_le; use W


def is_gomory_hu
  (G : UndirectedGraph α β) (wG : Edge α β → R)
  (T : Tree α β) (wT : Edge α β → R) : Prop :=
  V(T.1) = V(G) ∧
  ∀ s t : α,
    s ∈ V(G) → t ∈ V(G) → s ≠ t →
    ∃ U : Finset α,
      is_st_mincut G U s t wG ∧
      is_st_mincut (T.1) U s t wT ∧
      weight G U wG = weight (T.1) U wT


end Cut









end UndirectedGraph
