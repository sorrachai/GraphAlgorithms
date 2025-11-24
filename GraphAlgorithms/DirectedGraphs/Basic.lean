import Mathlib.Tactic
import Mathlib.Order.WithBot
import Mathlib.Data.Sym.Sym2

-- Directed Graphs
-- Authors: Sorrachai Yingchareonthawornchai

set_option tactic.hygienic false

variable {α β : Type*} [DecidableEq α] [DecidableEq β]
open Finset

structure DirectedEdge (α β : Type*) where
  id : β
  head : α
  tail : α
deriving DecidableEq

abbrev diEdge := DirectedEdge

abbrev DirectedEdge.sameEndpointsAs (e e' : diEdge α β):= (e'.head = e.head) ∧ (e'.tail = e.tail)

structure DirectedGraph (α β : Type*) where
  vertexSet : Finset α
  edgeSet : Finset (diEdge α β)
  incidence : ∀ e ∈ edgeSet, e.head ∈ vertexSet ∧ e.tail ∈ vertexSet

def DirectedGraph.noParallel (G : DirectedGraph α β) : Prop :=
  ∀ e ∈ G.edgeSet, ∀ e' ∈ G.edgeSet, e.sameEndpointsAs e' → e = e'

def DirectedGraph.LoopLess (G : DirectedGraph α β) : Prop :=
  ∀ e ∈ G.edgeSet, e.head ≠ e.tail

def DirectedGraph.Symmetric (G : DirectedGraph α β) : Prop :=
  ∀ e ∈ G.edgeSet , (∃ e', e'∈ G.edgeSet ∧ (e'.head = e.tail) ∧ (e'.tail = e.head))

def DirectedGraph.Simple (G : DirectedGraph α β) : Prop := G.noParallel ∧ G.LoopLess

-- One advantage on working on this type is we have access to specialized notations.
abbrev NoParallelDirectedGraph (α : Type*) := DirectedGraph α Unit

--#eva someAlgorithm
namespace DirectedGraph

/-- `V(G)` denotes the `vertexSet` of a graph `G`. -/
scoped notation "V(" G ")" => DirectedGraph.vertexSet G

/-- `E(G)` denotes the `edgeSet` of a graph `G`. -/
scoped notation "E(" G ")" => DirectedGraph.edgeSet G

abbrev outIncidentEdgeSet (G : DirectedGraph α β) (s : α) :
  Finset (DirectedEdge α β) := {e ∈ E(G) | e.tail = s}

/-- `δ_out(G,v)` denotes the `out-edge-incident-set` of a graph `G`. -/
scoped notation "δ_out(" G "," v ")" => DirectedGraph.outIncidentEdgeSet G v

-- #check δ_out(G,v)

abbrev outNeighbors (G : DirectedGraph α β) (s : α) :
  Finset α := {u ∈ V(G) | ∃ e ∈ E(G), e.head = u ∧ e.tail = s}

/-- `N_out(G,v)` denotes the `out-neighbors` of a graph `G`. -/
scoped notation "N_out(" G "," v ")" => DirectedGraph.outNeighbors G v

/-- `deg_out(G)` denotes the `out-degree` of a graph `G`. -/
scoped notation "deg_out(" G "," v ")" => #δ_out(G,v)

abbrev subgraphOf (H G : DirectedGraph α β) : Prop :=
  V(H) ⊆ V(G) ∧ E(H) ⊆ E(G)

scoped infix:50 " ⊆ᴳ " => DirectedGraph.subgraphOf

-- Vertex-induced subgraph
abbrev induce (G : DirectedGraph α β) (S : Finset α) : DirectedGraph α β where
  vertexSet := S ∩ V(G)
  edgeSet := { e ∈ E(G) | e.head ∈ S ∧ e.tail ∈ S }
  incidence := by aesop (add simp [G.incidence])

/-- A walk is an alternating sequence of vertices and incident edges.  For vertices `u v : V`,
the type `walk u v` consists of all walks starting at `u` and ending at `v`.
Note that this definition does not depend on the graph.
-/

inductive Walk (α β : Type*) : α → α → Type _
  | nil {v : α} : Walk α β v v
  | cons {u v w : α} (e : DirectedEdge α β)
         (h_tail : e.tail = u)
         (h_head : e.head = v)
         (rest : Walk α β v w) :
         Walk α β u w

scoped notation:50 "(" u "," v ")-Walk-("a "," b ")" => Walk a b u v

@[trans]
def Walk.append {u v w : α} : (u,v)-Walk-(α,β) → (v,w)-Walk-(α,β) → (u,w)-Walk-(α,β)
  | nil, q => q
  | cons e ht hh p, q => cons e ht hh (p.append q)

def Walk.InGraph {u v} (G : DirectedGraph α β) :  (u,v)-Walk-(α,β) → Prop
  | Walk.nil => u ∈ V(G)  --
  | Walk.cons e _ _ rest => e ∈ E(G) ∧ rest.InGraph G

example {H G u v} (h : H ⊆ᴳ G) (p : (u,v)-Walk-(α,β)) (hp : p.InGraph H) : p.InGraph G := by
  induction p <;> aesop (add simp [subgraphOf, Walk.InGraph])


def Reachable (G : DirectedGraph α β) (u v : α) : Prop := ∃ p : (u,v)-Walk-(α,β), p.InGraph G
def PreConnected (G : DirectedGraph α β) : Prop := ∀ u v : α, Reachable G u v

section NegativeWeight

variable {R} [AddCommMonoid R] [InfSet (WithBot (WithTop R))] [LinearOrder R]

def Walk.weight {u v} [AddCommMonoid R] (w : DirectedEdge α β → R) : (u,v)-Walk-(α,β) → R
  | nil => 0
  | cons e _ _ p => w e + p.weight w

def ewdist (G : DirectedGraph α β) (w : DirectedEdge α β → R) (u v : α) : WithBot (WithTop R) :=
  sInf ((fun p : (u,v)-Walk-(α,β) ↦ ↑(p.weight w)) '' {p | p.InGraph G})

def SSSP_ewdist (G : DirectedGraph α β) (w : DirectedEdge α β → R) (s : α)
  : α → WithBot (WithTop R) := fun v ↦ G.ewdist w s v

def ewdist_nonneg [CovariantClass R R (· + ·) (· ≤ ·)] [InfSet ((WithTop R))]
(G : DirectedGraph α β) (w : DirectedEdge α β → R) (u v : α)
: (WithTop R) := sInf ((fun p : (u,v)-Walk-(α,β) ↦ ↑(p.weight w)) '' {p | p.InGraph G})

def SSSP_ewdist_nonneg [CovariantClass R R (· + ·) (· ≤ ·)] [InfSet ((WithTop R))]
(G : DirectedGraph α β) (w : DirectedEdge α β → R) (s : α)
   : α → (WithTop R) := fun v ↦ G.ewdist_nonneg w s v

end DirectedGraph.NegativeWeight
