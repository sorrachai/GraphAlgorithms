# GraphLib

A [Lean 4](https://lean-lang.org/) library for **formal graph theory and graph algorithms**, built on top of [Mathlib](https://github.com/leanprover-community/mathlib4). GraphLib aims to provide machine-checked definitions, theorems, and algorithm implementations covering the standard undergraduate-through-graduate curriculum on graphs.

The graph definitions intentionally diverge from Mathlib's: vertex and edge sets are both carried as `Set`s with minimal axioms, so that dynamic operations (adding/removing vertices and edges, contractions, minors) and algorithmic reasoning stay close to their textbook formulations.

## Roadmap — v1

### Theory

Among others:

- **Walks & connectivity.** Walks, paths, cycles, Eulerian walks, components.
- **Trees.** Trees and forests, Cayley's theorem on the number of labeled trees.
- **Spectral graph theory.** Laplacian, Cheeger's inequality (upper and lower bounds), expansion / expander graphs.
- **Matchings.** Matchings, augmenting paths, Hall's theorem, König's theorem.
- **Colorings.** Proper vertex and edge colorings, chromatic number, basic bounds.
- **Contractions, minors, topological minors.** Edge/vertex contractions and the minor and topological-minor relations.
- **Embeddings & planarity.** Planar graphs, Euler's formula, Kuratowski's theorem, toroidal graphs.

### Algorithms

- **Flows.** Ford–Fulkerson, Edmonds–Karp, Push–Relabel.
- **Graph traversal.** BFS, DFS.
- **Shortest paths.** Dijkstra, Bellman–Ford, Floyd–Warshall.
- **Minimum spanning trees.** Kruskal, Prim, Borůvka.
- **Strongly connected components.** Tarjan / Kosaraju.
- **Union–Find.** Disjoint-set forests with union-by-rank and path compression.

Every algorithm comes with a proof of correctness and a proof of runtime.

## Repository layout

```
GraphLib/
├── Basic/          -- core graph structures (Graph, SimpleGraph, DiGraph, SimpleDiGraph)
├── Theory/         -- mathematical results (walks, trees, spectral, matching, …)
└── Algorithms/     -- algorithm implementations and correctness proofs
```

## Building

```
lake build
```

Requires the Lean toolchain pinned in `lean-toolchain`. `elan` will install it automatically.
