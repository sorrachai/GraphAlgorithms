import Mathlib.Tactic
import Mathlib.Order.WithBot
import Mathlib.Data.Sym.Sym2

-- Undirected Graphs
-- Authors: Sorrachai Yingchareonthawornchai

set_option tactic.hygienic false
variable {α β : Type*} [DecidableEq α] [DecidableEq β]


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

/-- `δ(G,v)` denotes the `edge-incident-set` of a graph `G`. -/
scoped notation "δ(" G "," v ")" => UndirectedGraph.IncidentEdgeSet G v

abbrev Neighbors (G : UndirectedGraph α β) (s : α) :
  Finset α := {u ∈ V(G) | ∃ e ∈ E(G), s ∈ e.endpoints ∧ u ∉ e.endpoints}

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
      v ∈ e.endpoints → w ∈ e.endpoints → Walk α β w u → Walk α β v u

scoped notation:50 "(" u "," v ")-Walk-("a "," b ")" => Walk a b u v

namespace Walk

@[trans]
def append {u v w : α} : (u,v)-Walk-(α,β) → (v,w)-Walk-(α,β) → (u,w)-Walk-(α,β)
  | nil, q => q
  | cons e ht hh p, q => cons e ht hh (p.append q)

def InGraph {u v} (G : UndirectedGraph α β) :  (u,v)-Walk-(α,β) → Prop
  | nil => u ∈ V(G)  --
  | cons e _ _ rest => e ∈ E(G) ∧ rest.InGraph G

example {H G u v} (h : H ⊆ᴳ G) (p : (u,v)-Walk-(α,β)) (hp : p.InGraph H) : p.InGraph G := by
  induction p <;> aesop (add simp [subgraphOf, Walk.InGraph])

def Reachable (G : UndirectedGraph α β) (u v : α) : Prop := ∃ p : (u,v)-Walk-(α,β), p.InGraph G
def PreConnected (G : UndirectedGraph α β) : Prop := ∀ u v : α, Reachable G u v

/-- The number of edges in the walk. -/
def length {u v : α} : (u,v)-Walk-(α,β) → ℕ
  | Walk.nil => 0
  | Walk.cons _ _ _ p => 1 + p.length

/-- The list of vertices visited by the walk, in order. -/
def support {u v : α} : (u,v)-Walk-(α,β)  → List α
  | nil => [u]
  -- We explicitly capture 'v' (the current start) and 'p' (the rest of the walk)
  | @cons _ _ _ v _ _ _ _ p => v :: p.support

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

end Walk

end UndirectedGraph
