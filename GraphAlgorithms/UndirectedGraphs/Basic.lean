/-
Copyright (c) 2024 Basil Rohner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Basil Rohner
-/

import Mathlib.Tactic
import Mathlib.Order.WithBot
import Mathlib.Data.Sym.Sym2
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Multiset.Basic
import Mathlib.Topology.ContinuousMap.Basic

set_option tactic.hygienic false
set_option linter.unusedSectionVars false

-- TEMPORARY until graph definition fixed
namespace Set.graphOn_nonempty

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

structure Edge (α β : Type*) where
  id : β
  endpoints : Sym2 α
  deriving DecidableEq

class Graph (α β : Type*) where
  vertices : Set α
  edges : Set (Edge α β)
  incidence : ∀ e ∈ edges, ∀ v ∈ e.endpoints, v ∈ vertices

scoped macro "V(" G:term ")" : term => `(($G).vertices)
scoped macro "E(" G:term ")" : term => `(($G).edges)

class FinGraph (α β : Type*) extends Graph α β where
  fin_vertices : Finite vertices
  fin_edges : Finite edges

class SimpleGraph (α β : Type*) extends FinGraph α β where
  loopless : ∀ e ∈ edges, ¬e.endpoints.IsDiag
  simple : ¬∃ e ∈ edges, ∃ e' ∈ edges, e.id ≠ e'.id ∧ e.endpoints = e'.endpoints

/-! ### Coercions between graph classes -/

@[reducible]
instance instCoeFinGraphGraph {α β : Type*} : Coe (FinGraph α β) (Graph α β) :=
  ⟨fun G => { vertices := G.vertices, edges := G.edges, incidence := G.incidence }⟩

@[reducible]
instance instCoeSimpleGraphFinGraph {α β : Type*} : Coe (SimpleGraph α β) (FinGraph α β) :=
  ⟨fun G => { vertices := G.vertices, edges := G.edges, incidence := G.incidence,
               fin_vertices := G.fin_vertices, fin_edges := G.fin_edges }⟩

@[reducible]
instance instCoeSimpleGraphGraph {α β : Type*} : Coe (SimpleGraph α β) (Graph α β) :=
  ⟨fun G => { vertices := G.vertices, edges := G.edges, incidence := G.incidence }⟩

/-! ### FinGraph helpers -/

/-- The vertex set of a `FinGraph` as a `Finset`. -/
noncomputable def FinGraph.vertexFinset {α β : Type*} (G : FinGraph α β) : Finset α :=
  (Set.finite_coe_iff.mp G.fin_vertices).toFinset

/-- The edge set of a `FinGraph` as a `Finset`. -/
noncomputable def FinGraph.edgeFinset {α β : Type*} (G : FinGraph α β) : Finset (Edge α β) :=
  (Set.finite_coe_iff.mp G.fin_edges).toFinset

@[simp] lemma FinGraph.mem_vertexFinset {α β : Type*} (G : FinGraph α β) (v : α) :
    v ∈ G.vertexFinset ↔ v ∈ G.vertices := by
  simp [FinGraph.vertexFinset, Set.Finite.mem_toFinset]

@[simp] lemma FinGraph.mem_edgeFinset {α β : Type*} (G : FinGraph α β) (e : Edge α β) :
    e ∈ G.edgeFinset ↔ e ∈ G.edges := by
  simp [FinGraph.edgeFinset, Set.Finite.mem_toFinset]

scoped notation "VF(" G ")" => FinGraph.vertexFinset G
scoped notation "EF(" G ")" => FinGraph.edgeFinset G

/-! ### Incidence and degree -/

/-- Edges incident to vertex `v` in `G`. -/
noncomputable abbrev incidentEdges {α β : Type*} [DecidableEq α] (G : FinGraph α β) (v : α) :
    Finset (Edge α β) :=
  EF(G).filter (fun e => v ∈ e.endpoints)

scoped notation "δ(" G "," v ")" => incidentEdges G v
set_option quotPrecheck false in
scoped notation "deg(" G "," v ")" => Finset.card (δ(G, v))

/-- Neighbors of `v` in `G`. -/
noncomputable abbrev neighbors {α β : Type*} [DecidableEq α] (G : FinGraph α β) (v : α) :
    Finset α :=
  VF(G).filter (fun u => ∃ e ∈ EF(G), v ∈ e.endpoints ∧ u ∈ e.endpoints ∧ u ≠ v)

scoped notation "N(" G "," v ")" => neighbors G v

/-- `H` is a subgraph of `G`. -/
abbrev subgraphOf {α β : Type*} (H G : Graph α β) : Prop :=
  V(H) ⊆ V(G) ∧ E(H) ⊆ E(G)

scoped infix:50 " ⊆ᴳ " => subgraphOf

/-! ### Adjacency -/

/-- Two vertices are **adjacent** in `G` if some edge of `G` has both as endpoints. -/
def adj {α β : Type*} (G : Graph α β) (u v : α) : Prop :=
  ∃ e ∈ E(G), u ∈ e.endpoints ∧ v ∈ e.endpoints

/-! ### Complement -/

/-- Two graphs on the same vertex set are **complements** if, for every pair of
    distinct vertices, exactly one of the two graphs contains an edge between them. -/
def IsComplement {α β : Type*} (G H : SimpleGraph α β) : Prop :=
  V(G) = V(H) ∧
  ∀ u ∈ V(G), ∀ v ∈ V(G), u ≠ v →
    (adj (G : Graph α β) u v ↔ ¬adj (H : Graph α β) u v)

/-! ### Graph homomorphism and isomorphism -/

/-- `G` is **homomorphic** to `H`: there exists a map `φ : α → γ` sending `V(G)` into
    `V(H)` that preserves adjacency. -/
def IsHomomorphic {α β γ δ : Type*} (G : SimpleGraph α β) (H : SimpleGraph γ δ) : Prop :=
  ∃ φ : α → γ,
    (∀ v ∈ V(G), φ v ∈ V(H)) ∧
    (∀ u ∈ V(G), ∀ v ∈ V(G), adj (G : Graph α β) u v →
      adj (H : Graph γ δ) (φ u) (φ v))

/-- `G` is **isomorphic** to `H`: there exists a bijection `φ` between `V(G)` and
    `V(H)` that preserves and reflects adjacency. -/
def IsIsomorphic {α β γ δ : Type*} (G : SimpleGraph α β) (H : SimpleGraph γ δ) : Prop :=
  ∃ (φ : α → γ) (ψ : γ → α),
    (∀ v ∈ V(G), φ v ∈ V(H)) ∧
    (∀ v ∈ V(H), ψ v ∈ V(G)) ∧
    (∀ v ∈ V(G), ψ (φ v) = v) ∧
    (∀ v ∈ V(H), φ (ψ v) = v) ∧
    (∀ u ∈ V(G), ∀ v ∈ V(G),
      adj (G : Graph α β) u v ↔ adj (H : Graph γ δ) (φ u) (φ v))

scoped notation:50 G " ≅ " H => IsIsomorphic G H

/-! ### Connectivity and induced subgraphs -/

/-
  **TODO**: Define paths first and then quantify over paths directly
  instead of reflexive transitive closure on adjacency relation.
-/

/-- `G` is **connected** if every pair of vertices is joined by the reflexive-transitive
    closure of the adjacency relation (i.e. by a walk in `G`). -/
def IsConnected {α β : Type*} (G : SimpleGraph α β) : Prop :=
  ∀ u ∈ V(G), ∀ v ∈ V(G),
    Relation.ReflTransGen
      (fun x y => ∃ e ∈ E(G), x ∈ e.endpoints ∧ y ∈ e.endpoints)
      u v

/-- The **induced subgraph** `G[S]`: keep only vertices in `V(G) ∩ S` and edges
    with both endpoints in `S`. -/
def induce {α β : Type*} (G : SimpleGraph α β) (S : Set α) : SimpleGraph α β where
  vertices   := V(G) ∩ S
  edges      := { e ∈ E(G) | ∀ v ∈ e.endpoints, v ∈ S }
  incidence  := by
    intro e ⟨heG, hS⟩ v hv
    exact ⟨G.incidence e heG v hv, hS v hv⟩
  fin_vertices := by
    haveI : Finite ↥V(G) := G.fin_vertices
    exact Finite.of_injective (Set.inclusion Set.inter_subset_left)
      (Set.inclusion_injective _)
  fin_edges := by
    haveI : Finite ↥E(G) := G.fin_edges
    exact Finite.of_injective (Set.inclusion (Set.sep_subset _ _))
      (Set.inclusion_injective _)
  loopless   := fun e ⟨heG, _⟩ => G.loopless e heG
  simple     := by
    rintro ⟨e, ⟨heG, _⟩, e', ⟨he'G, _⟩, hid, heq⟩
    exact G.simple ⟨e, heG, e', he'G, hid, heq⟩

scoped notation G "[" S "]" => induce G S

/-! ## Walks, Paths, and Cycles -/

/-- A **walk** from `u` to `v` is an alternating sequence of vertices and
    incident edges.  Walks are defined independently of any graph; the
    predicate `Walk.InGraph` restricts a walk to lie inside a given graph. -/
inductive Walk (α β : Type*) : α → α → Type _ where
  | nil  {u : α} : Walk α β u u
  | cons {u v w : α} (e : Edge α β) :
      u ∈ e.endpoints → w ∈ e.endpoints → Walk α β w v → Walk α β u v

scoped notation:50 "(" u "," v ")-Walk-(" a "," b ")" => Walk a b u v

namespace Walk

@[trans]
def append {u v w : α} : (u, v)-Walk-(α, β) → (v, w)-Walk-(α, β) → (u, w)-Walk-(α, β)
  | nil,            q => q
  | cons e h1 h2 p, q => cons e h1 h2 (p.append q)

def reverse {u v : α} : (u, v)-Walk-(α, β) → (v, u)-Walk-(α, β)
  | nil            => nil
  | cons e h1 h2 p => p.reverse.append (cons e h2 h1 nil)

/-- A walk lies **inside a graph** if every edge it traverses is in `E(G)`.
    For `nil`, we additionally require that the base vertex is in `V(G)`. -/
def InGraph {u v : α} (G : Graph α β) : (u, v)-Walk-(α, β) → Prop
  | nil          => u ∈ G.vertices
  | cons e _ _ p => e ∈ G.edges ∧ p.InGraph G

/-- Number of edges in the walk. -/
def length {u v : α} : (u, v)-Walk-(α, β) → ℕ
  | nil           => 0
  | cons _ _ _ p  => 1 + p.length

/-- Ordered list of vertices visited (starting with `u`). -/
def support {u v : α} : (u, v)-Walk-(α, β) → List α
  | nil                   => [u]
  | cons (u := u) _ _ _ p => u :: p.support

/-- Ordered list of edges traversed. -/
def edges {u v : α} : (u, v)-Walk-(α, β) → List (Edge α β)
  | nil           => []
  | cons e _ _ p  => e :: p.edges

lemma length_support {u v : α} (p : (u, v)-Walk-(α, β)) :
    p.support.length = p.length + 1 := by
  induction p with
  | nil => rfl
  | cons _ _ _ _ ih => simp [support, length, ih]; omega

lemma mem_support_start {u v : α} (p : (u, v)-Walk-(α, β)) : u ∈ p.support := by
  cases p <;> simp [support]

lemma mem_support_end {u v : α} (p : (u, v)-Walk-(α, β)) : v ∈ p.support := by
  induction p with
  | nil           => simp [support]
  | cons _ _ _ _ ih => simp [support, ih]

lemma InGraph_mono {H G : Graph α β} {u v : α}
    (hsub : H ⊆ᴳ G) (p : (u, v)-Walk-(α, β)) (hp : p.InGraph H) :
    p.InGraph G := by
  induction p with
  | nil => exact hsub.1 hp
  | cons e h1 h2 p' ih => exact ⟨hsub.2 hp.1, ih hp.2⟩

/-- A walk is a **path** if its vertex support has no repeated entries. -/
def isPath {u v : α} (p : (u, v)-Walk-(α, β)) : Prop := p.support.Nodup

/-- A closed walk is a **cycle** if it has at least three edges and no repeated
    vertex other than the start/end. -/
def isCycle {u : α} (p : (u, u)-Walk-(α, β)) : Prop :=
  p.length ≥ 3 ∧ p.support.tail.Nodup

abbrev Path (α β : Type*) (u v : α) := { p : (u, v)-Walk-(α, β) // p.isPath }
scoped notation:50 "(" u "," v ")-Path-(" a "," b ")" => Path a b u v

instance {u v : α} : Coe (Path α β u v) (Walk α β u v) := ⟨(·.1)⟩

@[simp] lemma coe_path_mk {u v : α} (p : Walk α β u v) (hp : p.isPath) :
    ((⟨p, hp⟩ : Path α β u v) : Walk α β u v) = p := rfl

/-- Drop the walk until (not including) vertex `x`. -/
def dropUntil {v u : α} :
    ∀ (p : (v, u)-Walk-(α, β)) (x : α), x ∈ p.support → (x, u)-Walk-(α, β)
  | nil,            x, hx => by simp [support] at hx; subst hx; exact nil
  | cons e hv hw p, x, hx => by
      by_cases h : x = v
      · subst h; exact cons e hv hw p
      · exact dropUntil p x
          (List.mem_cons.mp hx |>.resolve_left h)

lemma dropUntil_isPath {u v : α} {p : (u, v)-Walk-(α, β)} (hp : p.isPath)
    (x : α) (hx : x ∈ p.support) : (p.dropUntil x hx).isPath := by
  induction p with
  | nil =>
    simp [support] at hx; subst hx
    simp [dropUntil, support, isPath]
  | cons e hv hw p_tail ih =>
    have hp_tail : p_tail.support.Nodup :=
      (List.nodup_cons.mp (by simpa [isPath, support] using hp)).2
    by_cases h : x = u
    · subst h
      simp [dropUntil, isPath]
      aesop
    · simp only [dropUntil, h, ↓reduceDIte]
      aesop

/-- The **bypass** of a walk: recursively short-circuits back-edges to produce a path. -/
def bypass {u v : α} : (u, v)-Walk-(α, β) → (u, v)-Walk-(α, β)
  | nil           => nil
  | cons e h1 h2 p =>
    let p' := p.bypass
    if hs : u ∈ p'.support then p'.dropUntil u hs
    else cons e h1 h2 p'

lemma bypass_isPath {u v : α} (p : (u, v)-Walk-(α, β)) : p.bypass.isPath := by
  induction p with
  | nil => simp [isPath, bypass, support]
  | cons e h1 h2 p ih =>
    simp only [bypass]
    split_ifs with hs
    · exact dropUntil_isPath ih _ hs
    · simp only [isPath, support, List.nodup_cons]
      exact ⟨hs, ih⟩

/-- Extract a path from any walk by applying `bypass`. -/
def toPath {u v : α} (p : (u, v)-Walk-(α, β)) : (u, v)-Path-(α, β) :=
  ⟨p.bypass, p.bypass_isPath⟩

/-- Try to extract a cycle of length ≥ 3 from a closed walk;
    returns `none` if the walk is too short. -/
def toCycle? {u : α} : (u, u)-Walk-(α, β) → Option ((u, u)-Walk-(α, β))
  | nil           => none
  | cons e hv hw p =>
    let q := Walk.cons e hv hw p.bypass
    if q.length ≥ 3 then some q else none

lemma toCycle?_isCycle {u : α} (p q : (u, u)-Walk-(α, β))
    (h : p.toCycle? = some q) : q.isCycle := by
  simp only [toCycle?] at h
  cases p with
  | nil => simp at h
  | cons e hu hw p =>
    simp only at h
    split_ifs at h with hlen
    · simp only [Option.some.injEq] at h; subst h
      exact ⟨hlen, by simp [support]; exact bypass_isPath p⟩

end Walk

/-! ## Connectivity and acyclicity -/

/-- Two vertices are **reachable** in `G` if there is a walk between them in `G`. -/
def Reachable (G : Graph α β) (u v : α) : Prop :=
  ∃ p : (u, v)-Walk-(α, β), p.InGraph G

/-- `G` is **preconnected** if every pair of vertices in `V(G)` is reachable
    from one another. -/
def PreConnected (G : Graph α β) : Prop :=
  ∀ u ∈ V(G), ∀ v ∈ V(G), Reachable G u v

/-- `G` is **acyclic** if it contains no cycle. -/
def Acyclic (G : Graph α β) : Prop :=
  ∀ u ∈ V(G), ¬∃ (p : (u, u)-Walk-(α, β)), p.InGraph G ∧ p.isCycle

namespace Walk

/-- Two distinct paths between the same endpoints in a simple graph imply
    the existence of a cycle. -/
theorem distinct_paths_imply_cyclic {G : SimpleGraph α β} {u v : α}
    (p q : Path α β u v) (hpq : p ≠ q) (huv : u ≠ v)
    (hp : p.1.InGraph G) (hq : q.1.InGraph G) :
    ¬Acyclic (G : Graph α β) := by
  sorry

end Walk

/-! ## Trees and forests -/

def isTree (G : SimpleGraph α β) : Prop := PreConnected (G : Graph α β) ∧ Acyclic (G : Graph α β)
def isForest (G : SimpleGraph α β) : Prop := Acyclic (G : Graph α β)

abbrev Tree (α β : Type*) := { G : SimpleGraph α β // isTree G }
abbrev Forest (α β : Type*) := { G : SimpleGraph α β // isForest G }

namespace Tree

instance : Coe (Tree α β) (SimpleGraph α β) := ⟨(·.1)⟩

@[simp] lemma coe_mk (G : SimpleGraph α β) (h : isTree G) :
    ((⟨G, h⟩ : Tree α β) : SimpleGraph α β) = G := rfl

end Tree

/-! ### Equivalent characterisations of trees

A non-empty finite simple graph satisfies any two of the following three
properties if and only if it satisfies all three:
  (T1) connected,
  (T2) acyclic,
  (T3) `|E| = |V| - 1`.
Additionally, all three are equivalent to:
  (T4) every pair of vertices is connected by a unique path.
-/

/-- **(T1 ∧ T3) → T2**: connected with `|E| = |V| - 1` implies acyclic. -/
theorem acyclic_of_connected_card (G : SimpleGraph α β)
    (hconn : PreConnected (G : Graph α β))
    (hcard : EF((G : FinGraph α β)).card + 1 = VF((G : FinGraph α β)).card) :
    Acyclic (G : Graph α β) := by
  sorry

/-- **(T2 ∧ T3) → T1**: acyclic with `|E| = |V| - 1` implies connected. -/
theorem connected_of_acyclic_card (G : SimpleGraph α β)
    (hacyc : Acyclic (G : Graph α β))
    (hcard : EF((G : FinGraph α β)).card + 1 = VF((G : FinGraph α β)).card) :
    PreConnected (G : Graph α β) := by
  sorry

/-- **(T1 ∧ T2) → T3**: connected and acyclic implies `|E| = |V| - 1`. -/
theorem card_of_connected_acyclic (G : SimpleGraph α β)
    (hconn : PreConnected (G : Graph α β))
    (hacyc : Acyclic (G : Graph α β)) :
    EF((G : FinGraph α β)).card + 1 = VF((G : FinGraph α β)).card := by
  sorry

/-- A tree is equivalently: connected with `|E| = |V| - 1`. -/
theorem isTree_iff_connected_card (G : SimpleGraph α β) :
    isTree G ↔ PreConnected (G : Graph α β) ∧
      EF((G : FinGraph α β)).card + 1 = VF((G : FinGraph α β)).card :=
  ⟨fun ⟨hconn, hacyc⟩ => ⟨hconn, card_of_connected_acyclic G hconn hacyc⟩,
   fun ⟨hconn, hcard⟩ => ⟨hconn, acyclic_of_connected_card G hconn hcard⟩⟩

/-- A tree is equivalently: acyclic with `|E| = |V| - 1`. -/
theorem isTree_iff_acyclic_card (G : SimpleGraph α β) :
    isTree G ↔ Acyclic (G : Graph α β) ∧
      EF((G : FinGraph α β)).card + 1 = VF((G : FinGraph α β)).card :=
  ⟨fun ⟨hconn, hacyc⟩ => ⟨hacyc, card_of_connected_acyclic G hconn hacyc⟩,
   fun ⟨hacyc, hcard⟩ => ⟨connected_of_acyclic_card G hacyc hcard, hacyc⟩⟩

/-- **(T4)**: every pair of vertices in `V(G)` is connected by exactly one path. -/
def UniquePaths (G : SimpleGraph α β) : Prop :=
  ∀ u ∈ V(G), ∀ v ∈ V(G),
    ∃! p : (u, v)-Walk-(α, β), p.isPath ∧ p.InGraph G

/-- **(T1 ∧ T2) → T4**: a tree has unique paths. -/
theorem uniquePaths_of_connected_acyclic (G : SimpleGraph α β)
    (hconn : PreConnected (G : Graph α β))
    (hacyc : Acyclic (G : Graph α β)) :
    UniquePaths G := by
  sorry

/-- **(T4) → (T1 ∧ T2)**: unique paths imply connected and acyclic. -/
theorem connected_acyclic_of_uniquePaths (G : SimpleGraph α β)
    (huniq : UniquePaths G) :
    PreConnected (G : Graph α β) ∧ Acyclic (G : Graph α β) := by
  sorry

/-- A tree is equivalently: every pair of vertices is connected by a unique path. -/
theorem isTree_iff_uniquePaths (G : SimpleGraph α β) :
    isTree G ↔ UniquePaths G :=
  ⟨fun ⟨hconn, hacyc⟩ => uniquePaths_of_connected_acyclic G hconn hacyc,
   fun huniq => connected_acyclic_of_uniquePaths G huniq⟩

/-! ## Graph parameters -/

/-- A set `S ⊆ V(G)` is a **clique** if every two distinct vertices in `S` are adjacent. -/
def IsClique (G : SimpleGraph α β) (S : Finset α) : Prop :=
  (S : Set α) ⊆ V(G) ∧
  ∀ u ∈ S, ∀ v ∈ S, u ≠ v → ∃ e ∈ E(G), u ∈ e.endpoints ∧ v ∈ e.endpoints

/-- `ω(G)` — the **clique number**: the cardinality of a largest clique. -/
noncomputable def cliqueNr (G : SimpleGraph α β) : ℕ :=
  sSup { n : ℕ | ∃ S : Finset α, IsClique G S ∧ S.card = n }

scoped notation "ω(" G ")" => cliqueNr G

/-- A set `S ⊆ V(G)` is **independent** if no two vertices of `S` share an edge. -/
def IsIndependentSet (G : SimpleGraph α β) (S : Finset α) : Prop :=
  (S : Set α) ⊆ V(G) ∧
  ∀ u ∈ S, ∀ v ∈ S, u ≠ v → ¬∃ e ∈ E(G), u ∈ e.endpoints ∧ v ∈ e.endpoints

/-- `α(G)` — the **independence number**: the cardinality of a largest independent set. -/
noncomputable def independenceNr (G : SimpleGraph α β) : ℕ :=
  sSup { n : ℕ | ∃ S : Finset α, IsIndependentSet G S ∧ S.card = n }

scoped notation "α(" G ")" => independenceNr G

/-! ## Special graph classes -/

/-- `G` is **complete** if every pair of distinct vertices is joined by an edge. -/
def IsComplete (G : SimpleGraph α β) : Prop :=
  ∀ u ∈ V(G), ∀ v ∈ V(G), u ≠ v → ∃ e ∈ E(G), u ∈ e.endpoints ∧ v ∈ e.endpoints

/-- `G` is **bipartite** if `V(G)` can be partitioned into two independent sets. -/
def IsBipartite (G : SimpleGraph α β) : Prop :=
  ∃ A B : Finset α, (A : Set α) ∪ B = V(G) ∧ Disjoint A B ∧
    ∀ e ∈ E(G), (∃ u ∈ A, u ∈ e.endpoints) ∧ (∃ v ∈ B, v ∈ e.endpoints)

/-- `G` is **`k`-regular** if every vertex has degree exactly `k`. -/
def IsKRegular (G : SimpleGraph α β) (k : ℕ) : Prop :=
  ∀ v ∈ V(G), deg((G : FinGraph α β), v) = k

/-- A graph is bipartite iff it contains no odd cycle. -/
theorem bipartite_iff_no_odd_cycle (G : SimpleGraph α β) :
    IsBipartite G ↔
    ∀ u ∈ V(G), ¬∃ (p : (u, u)-Walk-(α, β)), p.InGraph G ∧ p.isCycle ∧ ¬2 ∣ p.length := by
  sorry

/-! ## Connected components -/

/-
  **TODO**: This should be in the same space as connected.
-/

/-- The connected-component equivalence relation on `V(G)`: two vertices are
    related iff they are reachable from one another. -/
def connSetoid (G : Graph α β) : Setoid { v // v ∈ V(G) } where
  r u v := Reachable G u v
  iseqv := {
    refl  := fun ⟨v, hv⟩ => ⟨Walk.nil, hv⟩
    symm  := fun ⟨p, hp⟩ => ⟨p.reverse, sorry⟩
    trans := fun ⟨p, hp⟩ ⟨q, hq⟩ => ⟨p.append q, sorry⟩
  }

/-- The set of connected components of `G`. -/
def ConnectedComponents (G : Graph α β) := Quotient (connSetoid G)

/-- The number of connected components of a finite graph. -/
noncomputable def numComponents (G : FinGraph α β) : ℕ := sorry

/-! ## Vertex and edge separators -/

/-
  **TODO**: Inconsistency with `FinGraph` and `SimpleGraph`.
  Need to change.
-/

/-- `S` is a **vertex separator** for `u` and `v` in `G`: removing `S` from `G`
    disconnects `u` from `v`. -/
def IsVertexSeparator (G : SimpleGraph α β) (S : Finset α) (u v : α) : Prop :=
  u ∉ S ∧ v ∉ S ∧ ¬Reachable (G[V(G) \ ↑S] : Graph α β) u v

/-- `F` is an **edge separator** for `u` and `v` in `G`: removing the edges
    in `F` disconnects `u` from `v`. -/
def IsEdgeSeparator (G : SimpleGraph α β) (F : Finset (Edge α β)) (u v : α) : Prop :=
  ¬Reachable
    ({ vertices := V(G), edges := E(G) \ ↑F,
       incidence := fun e he w hw => G.incidence e (Set.diff_subset he) w hw } :
     Graph α β) u v

/-! ## Vertex and edge connectivity -/

/-- `κ(G)` — the **vertex connectivity**: minimum size of a vertex separator
    over all non-adjacent pairs, or `|V(G)| - 1` if `G` is complete. -/
noncomputable def vertexConnectivity (G : SimpleGraph α β) : ℕ :=
  sInf { k : ℕ | ∃ S : Finset α, S.card = k ∧
    ∃ u ∈ V(G), ∃ v ∈ V(G), u ≠ v ∧ IsVertexSeparator G S u v }

scoped notation "κ(" G ")" => vertexConnectivity G

/-- `κ'(G)` — the **edge connectivity**: minimum size of an edge separator
    that disconnects some pair of vertices. -/
noncomputable def edgeConnectivity (G : SimpleGraph α β) : ℕ :=
  sInf { k : ℕ | ∃ F : Finset (Edge α β), F.card = k ∧
    ∃ u ∈ V(G), ∃ v ∈ V(G), u ≠ v ∧ IsEdgeSeparator G F u v }

scoped notation "κ'(" G ")" => edgeConnectivity G

/-- **Whitney's inequality**: `κ(G) ≤ κ'(G)`. -/
theorem whitney_inequality (G : SimpleGraph α β) : κ(G) ≤ κ'(G) := sorry

/-- **Menger's theorem** (vertex version): the maximum number of internally
    vertex-disjoint `u`-`v` paths equals the minimum vertex separator size. -/
theorem Menger_vertex (G : SimpleGraph α β) (u v : α)
    (hu : u ∈ V(G)) (hv : v ∈ V(G)) (huv : u ≠ v) (hna : ¬adj (G : Graph α β) u v) :
    sInf { k | ∃ S : Finset α, S.card = k ∧ IsVertexSeparator G S u v } =
    sSup { k | ∃ paths : Fin k → { p : Walk α β u v // p.isPath },
      (∀ i, (paths i).1.InGraph (G : Graph α β)) ∧
      ∀ i j, i ≠ j → Disjoint
        ((paths i).1.support.tail.dropLast.toFinset)
        ((paths j).1.support.tail.dropLast.toFinset) } := sorry

/-! ## Induced cycles, holes, and antiholes -/

/-- `G` has an **induced cycle** of length `n ≥ 3`: a cycle on `n` vertices
    such that the only edges of `G` among those vertices are the cycle edges. -/
def HasInducedCycle (G : SimpleGraph α β) (n : ℕ) : Prop :=
  n ≥ 3 ∧ ∃ (u : α) (p : (u, u)-Walk-(α, β)),
    p.InGraph (G : Graph α β) ∧ p.isCycle ∧ p.length = n ∧
    ∀ x ∈ p.support.tail, ∀ y ∈ p.support.tail, x ≠ y →
      adj (G : Graph α β) x y →
      ∃ e ∈ p.edges, x ∈ e.endpoints ∧ y ∈ e.endpoints

/-- A **hole** of length `n ≥ 5` in `G`. -/
def HasHole (G : SimpleGraph α β) (n : ℕ) : Prop :=
  HasInducedCycle G n ∧ n ≥ 5

/-- `G` has an **odd hole**: an induced cycle of odd length ≥ 5. -/
def HasOddHole (G : SimpleGraph α β) : Prop :=
  ∃ n, HasHole G n ∧ ¬2 ∣ n

/-- `G` has an **antihole** of length `n ≥ 5`: an induced subgraph on `n`
    vertices whose complement is a cycle `Cₙ`.  Equivalently, `n` vertices
    `v₀, …, vₙ₋₁` where `vᵢ` and `vⱼ` are adjacent in `G` iff `|i-j| ≥ 2`
    (indices mod `n`). -/
def HasAntihole (G : SimpleGraph α β) (n : ℕ) : Prop :=
  n ≥ 5 ∧ ∃ (verts : ZMod n → α),
    Function.Injective verts ∧
    (∀ i, verts i ∈ V(G)) ∧
    (∀ i j : ZMod n, i ≠ j →
      (adj (G : Graph α β) (verts i) (verts j) ↔
        ¬(j = i + 1 ∨ i = j + 1)))

/-
  Note: I have this here to formalize the **Strong Perfect Graph Theorem**.
-/

/-- `G` has an **odd antihole**: an antihole of odd length ≥ 5. -/
def HasOddAntihole (G : SimpleGraph α β) : Prop :=
  ∃ n, HasAntihole G n ∧ ¬2 ∣ n

/-! ## Tree decomposition and tree-width -/

/-- A **tree decomposition** of `G` consists of a tree `T` and a map `bag`
    associating to each node of `T` a subset of `V(G)`, satisfying:
    1. Every vertex of `G` appears in some bag.
    2. For every edge of `G`, both endpoints appear together in some bag.
    3. For each vertex `v`, the set of nodes whose bags contain `v` induces
       a connected subtree of `T`. -/
structure TreeDecomp (α β : Type*) [DecidableEq α] [DecidableEq β]
    (G : SimpleGraph α β)
    (γ : Type*) (δ : Type*) [DecidableEq γ] [DecidableEq δ] where
  tree : Tree γ δ
  bag : γ → Finset α
  covers_vertices : ∀ v ∈ V(G), ∃ t ∈ V(tree.1), v ∈ bag t
  covers_edges : ∀ e ∈ E(G), ∃ t ∈ V(tree.1),
    ∀ v ∈ e.endpoints, v ∈ bag t
  connected_bags : ∀ v ∈ V(G),
    ∀ t₁ ∈ V(tree.1), ∀ t₂ ∈ V(tree.1),
      v ∈ bag t₁ → v ∈ bag t₂ →
      ∀ (p : { p : Walk γ δ t₁ t₂ // p.isPath }),
        p.1.InGraph (tree.1 : Graph γ δ) →
        ∀ t₃ ∈ p.1.support, v ∈ bag t₃

/-- The **width** of a tree decomposition: max bag size minus one. -/
noncomputable def TreeDecomp.width
    {α β γ δ : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq γ] [DecidableEq δ]
    {G : SimpleGraph α β} (td : TreeDecomp α β G γ δ) : ℕ :=
  sSup { n : ℕ | ∃ t ∈ V(td.tree.1), (td.bag t).card = n + 1 }

/-- `tw(G)` — the **tree-width**: minimum width over all tree decompositions.
    Uses `ℕ` rather than `WithTop ℕ` (convention: `tw(∅) = 0`). -/
noncomputable def treeWidth (G : SimpleGraph α β) : ℕ :=
  sInf { n : ℕ | ∃ (γ δ : Type) (_ : DecidableEq γ) (_ : DecidableEq δ)
    (td : TreeDecomp α β G γ δ), td.width = n }

scoped notation "tw(" G ")" => treeWidth G

/-! ## Brambles -/

/-- A **bramble** in `G` is a family of connected subgraphs that pairwise
    **touch**: their vertex sets intersect, or there is an edge between them. -/
def IsBramble (G : SimpleGraph α β) (B : Set (Set α)) : Prop :=
  (∀ S ∈ B, S ⊆ V(G) ∧ S.Nonempty ∧ PreConnected (G[S] : Graph α β)) ∧
  (∀ S ∈ B, ∀ T ∈ B,
    (S ∩ T).Nonempty ∨ ∃ u ∈ S, ∃ v ∈ T, adj (G : Graph α β) u v)

/-- A **hitting set** of a bramble: a vertex set that intersects every
    bramble element. -/
def IsHittingSet (B : Set (Set α)) (X : Finset α) : Prop :=
  ∀ S ∈ B, ∃ v ∈ X, v ∈ S

/-- The **order** of a bramble: the minimum size of a hitting set. -/
noncomputable def brambleOrder (G : SimpleGraph α β) (B : Set (Set α)) : ℕ :=
  sInf { k : ℕ | ∃ X : Finset α, X.card = k ∧ IsHittingSet B X }

/-- The **bramble number** of `G`: maximum order of a bramble in `G`. -/
noncomputable def brambleNr (G : SimpleGraph α β) : ℕ :=
  sSup { k : ℕ | ∃ B, IsBramble G B ∧ brambleOrder G B = k }

/-- **Seymour–Thomas duality**: `tw(G) + 1 = bramble number`. -/
theorem treeWidth_bramble_duality (G : SimpleGraph α β) :
    brambleNr G = tw(G) + 1 := sorry

/-! ### Classical tree-width results -/

/-- The tree-width of a tree is at most 1. -/
theorem treeWidth_tree (G : SimpleGraph α β) (hG : isTree G) :
    tw(G) ≤ 1 := by
  sorry

/-- The tree-width of a cycle is exactly 2. -/
theorem treeWidth_cycle (G : SimpleGraph α β)
    (hconn : PreConnected (G : Graph α β))
    (hcyc : ∃ u ∈ V(G), ∃ (p : (u, u)-Walk-(α, β)), p.InGraph G ∧ p.isCycle ∧
      ∀ v ∈ V(G), v ∈ p.support)
    (hcard : VF((G : FinGraph α β)).card ≥ 3) :
    tw(G) = 2 := by
  sorry

/-- The tree-width of a complete graph on `n` vertices is `n - 1`. -/
theorem treeWidth_complete (G : SimpleGraph α β) (hG : IsComplete G) (n : ℕ)
    (hn : VF((G : FinGraph α β)).card = n) (hn1 : n ≥ 1) :
    tw(G) = n - 1 := by
  sorry

/-- Tree-width is monotone under subgraphs. -/
theorem treeWidth_subgraph (G H : SimpleGraph α β)
    (hsub : (H : Graph α β) ⊆ᴳ (G : Graph α β)) :
    tw(H) ≤ tw(G) := by
  sorry

/-! ## Separations and tangles -/

/-- A **separation** of `G` is a pair `(A, B)` with `A ∪ B = V(G)` and
    no edge from `A \ B` to `B \ A`. -/
structure Separation {α β : Type*} [DecidableEq α] [DecidableEq β]
    (G : SimpleGraph α β) where
  left : Finset α
  right : Finset α
  covers : (↑left : Set α) ∪ ↑right = V(G)
  no_cross : ∀ e ∈ E(G), ∀ u ∈ e.endpoints, ∀ v ∈ e.endpoints,
    u ∈ left → v ∈ right → u ∈ left ∩ right ∨ v ∈ left ∩ right

/-- The **order** of a separation: `|A ∩ B|`. -/
def Separation.order {α β : Type*} [DecidableEq α] [DecidableEq β]
    {G : SimpleGraph α β} (s : Separation G) : ℕ :=
  (s.left ∩ s.right).card

/-- A **tangle of order `k`** in `G` orients every separation of order < `k`
    consistently, pointing each one towards the "big side". -/
structure Tangle {α β : Type*} [DecidableEq α] [DecidableEq β]
    (G : SimpleGraph α β) (k : ℕ) where
  /-- For each separation of order < k, `orient s` selects a side:
      `true` means `s.left` is the small side. -/
  orient : (s : Separation G) → s.order < k → Bool
  /-- Totality: one side is always small. -/
  total : ∀ (s : Separation G) (h : s.order < k),
    orient s h = true ∨ orient s h = false
  /-- Consistency: no three small sides cover `V(G)`. -/
  consistent : ∀ (s₁ s₂ s₃ : Separation G)
    (h₁ : s₁.order < k) (h₂ : s₂.order < k) (h₃ : s₃.order < k),
    orient s₁ h₁ = true → orient s₂ h₂ = true → orient s₃ h₃ = true →
    ¬((↑s₁.left : Set α) ∪ ↑s₂.left ∪ ↑s₃.left = V(G))
  /-- No singleton is a small side. -/
  no_singleton : ∀ (s : Separation G) (h : s.order < k),
    orient s h = true → s.left.card > 1

/-! ## Linkage -/

/-- A **`k`-linkage** in `G` routes `k` terminal pairs via pairwise
    internally vertex-disjoint paths. -/
def IsLinkage {α β : Type*} [DecidableEq α] [DecidableEq β]
    (G : SimpleGraph α β) (k : ℕ)
    (terminals : Fin k → α × α)
    (paths : (i : Fin k) →
      ((terminals i).1, (terminals i).2)-Walk-(α, β)) : Prop :=
  (∀ i, (paths i).InGraph (G : Graph α β)) ∧
  (∀ i, (paths i).isPath) ∧
  (∀ i j, i ≠ j → Disjoint
    ((paths i).support.tail.dropLast.toFinset : Finset α)
    ((paths j).support.tail.dropLast.toFinset))

/-- `G` is **`k`-linked** if every set of `k` disjoint terminal pairs can
    be linked by internally vertex-disjoint paths. -/
def IsKLinked (G : SimpleGraph α β) (k : ℕ) : Prop :=
  ∀ terminals : Fin k → α × α,
    (∀ i, (terminals i).1 ∈ V(G) ∧ (terminals i).2 ∈ V(G)) →
    (∀ i, (terminals i).1 ≠ (terminals i).2) →
    (Function.Injective (fun i => (terminals i).1)) →
    (Function.Injective (fun i => (terminals i).2)) →
    (∀ i j, (terminals i).1 ≠ (terminals j).2) →
    ∃ paths, IsLinkage G k terminals paths

end Set.graphOn_nonempty
