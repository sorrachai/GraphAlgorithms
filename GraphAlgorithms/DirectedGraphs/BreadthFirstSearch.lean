import Mathlib.Tactic
import Mathlib.Order.WithBot
import Mathlib.Data.Sym.Sym2
import Mathlib.Data.Finset.Basic

import GraphAlgorithms.DirectedGraphs.SimpleDiGraphs
import GraphAlgorithms.DirectedGraphs.Walk

-- Breadth-first Search
-- Authors: Huang, JiangYi

set_option tactic.hygienic false
variable {α : Type*} [DecidableEq α]

open SimpleDiGraph
open Walk

/-- A path is a walk whose support (the list of vertices from VertexSeq.toList)
    has no duplicate vertices — List.Nodup. -/
def IsPathIn (G : SimpleDiGraph α) (w : Walk α) : Prop := IsWalkIn G w ∧ w.IsPath

/-- Analytical definition of distace:
    the length of minimum path between two vertices `v₁` and `v₂` in graph `G` -/
noncomputable def Distance_spec (G : SimpleDiGraph α) (v₁ : α) (v₂ : α) : ℕ∞ :=
  /- ⨅: the indexed infimum (greatest lower bound) operator.
     - `⨅ (x : T), f x` is `iInf f`
     - `⨅ (x : T) (_ : P x), f x` is `iInf (fun x => iInf (fun _ : P x => f x))`,
       a nested `iInf` where the inner one ranges over proofs of `P x`.
       When `P x` is False (no proof exists), `iInf` over an empty type gives `⊤`.
     Here it means the infimum (minimum) of `w.length` over all walks `w` satisfying the condition.
     When the condition is empty (no such path exists), ⨅ over an empty set
     in ℕ∞ gives ⊤ (infinity) automatically. -/
  ⨅ (w : Walk α) (_ : IsPathIn G w ∧ w.head = v₁ ∧ w.tail = v₂), (w.length : ℕ∞)

namespace BreadthFirstSearch

/-- Core BFS traversal over a directed graph `G` searching for `dst_vertex`.
    Processes one frontier level per recursive call.

    Parameters:
    - `G`           : the directed graph being searched
    - `dst_vertex`  : the target vertex we are looking for
    - `n`           : termination counter, initialised to `Fintype.card α`;
                      decreases by 1 each call so Lean accepts the recursion without a proof.
                      Since any shortest path in a graph `G` visits at most `|V|` vertices,
                      `|V|` rounds always suffice.
    - `visited`     : the set of vertices seen across all previous levels;
                      used to avoid revisiting vertices
    - `frontier`    : the set of vertices at the current BFS level, i.e. all
                      vertices at distance `d` from the source
    - `d`           : the distance of the current `frontier` from the source
-/
def bfs [Fintype α] (G : SimpleDiGraph α) (dst_vertex : α) :
    ℕ → Finset α → Finset α → ℕ → Option ℕ
  /- **Base case** (`n = 0`): return `none` — the counter `n` exhausted,
    `dst_vertex` is unreachable. This branch is never reached for reachable vertices
    when the counter `n` is initialised to `Fintype.card α`.-/
  | 0,     _,       _,        _ => none
  /- **Recursion case** when called with arguments
    `(n+1, visited, frontier, d)`, do the following... -/
  | n + 1, visited, frontier, d =>
    /- *Found*: if `dst_vertex ∈ frontier`, return `some d`. Because BFS
       expands levels in order of increasing distance, this is the shortest
       distance. -/
    if dst_vertex ∈ frontier then some d
    else
      /- *Expand*: compute `next`, the next frontier, as the out-neighbors of
         every vertex in `frontier`, minus all already-visited vertices:
         `next = (⋃ v ∈ frontier, N⁺(G, v)) \ visited` -/
      let next := (Finset.biUnion frontier (fun v ↦ N⁺(G, v))) \ visited
      /- *Exhausted*: if `next = ∅`, no new vertices are reachable, so
        `dst_vertex` is unreachable — return `none`. -/
      if next = ∅ then none
      /- *Recurse*: otherwise advance one level — new `visited` absorbs `next`,
        `frontier` becomes `next`, and `d` increments by 1. -/
      else bfs G dst_vertex n (visited ∪ next) next (d + 1)

/-- Computes the shortest distance from `v₀` to `v'` in `G` using BFS.
    Returns `some d` if `v'` is reachable from `v₀` at distance `d`,
    or `none` if `v'` is unreachable from `v₀`.
    The trivial case `v₀ = v'` is handled directly with distance `0`. -/
def bfsDistance [Fintype α] (G : SimpleDiGraph α) (v₀ v' : α) : Option ℕ :=
  if v₀ = v' then some 0
  else bfs G v' (Fintype.card α) {v₀} {v₀} 0

end BreadthFirstSearch

/-- The shortest distance from `v₁` to `v₂` in directed graph `G`.
    Returns `some d` if `v₂` is reachable from `v₁` at distance `d`,
    or `none` if unreachable. Computed via BFS. -/
def Distance [Fintype α]
    (G : SimpleDiGraph α) (v₁ : α) (v₂ : α) : Option ℕ :=
  BreadthFirstSearch.bfsDistance G v₁ v₂
