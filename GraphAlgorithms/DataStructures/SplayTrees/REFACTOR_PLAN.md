# Refactor plan: `SplaySequential.lean` onto `BottomUp.splayBU`

## Goal

Retire the duplicated definitions at the top of `SplaySequential.lean` and
rebase the Elmasry sequential-access proof on the canonical bottom-up
splay (`splayBU`) living in `BottomUp.lean`. This makes the proof operate
on the formulation actually analysed by Tarjan 1985 / Sundar 1989 /
Elmasry 2004, rather than the recursive top-down `splay'` plus a parity
wrapper.

## Target end-state

`SplaySequential.lean` opens with

```lean
import GraphAlgorithms.DataStructures.SplayTrees.Basic
import GraphAlgorithms.DataStructures.SplayTrees.BottomUp
import GraphAlgorithms.DataStructures.SplayTrees.Correctness
```

and contains no `inductive BinaryTree`, no `rotateRight/Left`, no `Rot`,
no `rotate`, no `splay'/splay`, no `splay.cost'/splay.cost`, no
`ForallTree`, `IsBST`, `rank`, `φ`, `subtree_rooted_at`. Everything
comes from the three imports. The only `splay` the file talks about is
`splayBU`; the only cost is `splayBU.cost`.

## Duplication inventory (to delete)

| SplaySequential line | Symbol | Replacement |
|---|---|---|
| 5 | `BinaryTree` | `BinaryTree` from `BinaryTree.lean` |
| 10 | `BinaryTree.num_nodes` | same |
| 17 | `rotateRight` | `Basic.rotateRight` |
| 21 | `rotateLeft` | `Basic.rotateLeft` |
| 28 | `Rot` | `Basic.Rot` (unused after refactor) |
| 31 | `rotate` | `Basic.rotate` (unused after refactor) |
| 49 | `BinaryTree.search_path_len` | keep (local helper) or drop if unused |
| 60 | `splay'` | `Basic.splay` (unused after refactor) |
| 109 | `splay` | `BottomUp.splayBU` |
| 126 | `subtree_rooted_at` | `Basic.subtree_rooted_at` |
| 137 | `splay.cost'` | `Basic.splay.cost` (unused) |
| 169 | `splay.cost` | `BottomUp.splayBU.cost` |
| 184 | `ForallTree` | `BinaryTree.ForallTree` |
| 192 | `IsBST` | `BinaryTree.IsBST` |
| 202 | `rank` | `Basic.rank` |
| 205 | `φ` | `Basic.φ` |

## Semantics check — are `splay` and `splayBU` the same function?

Both are bottom-up in effect but constructed differently:
- Current `splay` = "if path length odd, run `splay'`; else do one
  single rotation at the root and then `splay'` on the appropriate
  child". This reproduces the classical paired-from-the-bottom order.
- `splayBU` = descend, then pair frames from the bottom with
  `splayUp`.

They should be extensionally equal, but we are **not** going to rely on
that equality. The strategy below reproves everything against
`splayBU` directly.

## Architectural choices — Strategy A (chosen)

We rebuild the sequential-access proof on top of `splayBU` by frame
induction on `splayUp`. Each rotation in the coloring argument becomes
a single `Dir.bringUp` step (or inner `applyChild (bringUp)` step),
which is *structurally* much closer to how the paper reasons
("consider the link incident to `w` and its parent `z`") than the
nested top-down recursion of `splay'`.

Pros:
- The final theorem and every intermediate lemma operate on the
  formulation the literature actually analyses.
- Each lemma's induction structure matches the paper's "walk over the
  sequence of links" argument.
- We shed dependencies on `splay'`/`splay.cost'`/`Rot` entirely; those
  symbols disappear from `SplaySequential.lean`.

Cons:
- Essentially every structural lemma needs a new proof (≈30 lemmas,
  itemised below). Each individual proof is expected to be shorter
  than the current one, but the aggregate work is the largest part of
  the refactor.

## Step-by-step plan

### Phase 0 — groundwork in `BottomUp.lean`

The purpose of Phase 0 is to set up the reasoning primitives we'll
reuse in every subsequent proof.

- [ ] **P0.1** Basic invariants:
      - `num_nodes_splayUp : (splayUp c path).num_nodes = c.num_nodes + pathCost path`
        or a cleaner variant: reattaching + splaying preserves node count.
      - `num_nodes_splayBU : (splayBU t q).num_nodes = t.num_nodes`.
      - `splayBU_empty_iff : splayBU t q = .empty ↔ t = .empty`.
- [ ] **P0.2** Induction principle / unfolding lemmas for `splayUp`
      (three cases: nil, singleton, pair-cons). Prefer `fun_induction splayUp`
      if it behaves; otherwise state an explicit recursor.
- [ ] **P0.3** `descend` characterisations:
      - `descend_nil : descend .empty q = (.empty, [])`.
      - `descend_node_eq / lt / gt` unfolding one step.
      - `descend_path_keys_lt` / `descend_path_keys_gt` (frame key vs
        `q` relation, needed for BST arguments).
      - `descend_preserves_tree : reassemble (descend t q) = t`
        (i.e. folding the frames back over the reached subtree yields
        the original tree). **Key lemma for every proof below.**
- [ ] **P0.4** Cost and search-path length:
      - `splayBU.cost_eq : splayBU.cost t q = (t.search_path_len q : ℝ)`
        (after moving `search_path_len` into `BottomUp.lean`; see P0.5).
      - `splayBU.cost_nonneg`.
- [ ] **P0.5** Move `BinaryTree.search_path_len` from
      `SplaySequential.lean` into `BottomUp.lean` (or `Basic.lean`);
      prove it equals `(descend t q).2.length`.
- [ ] **P0.6** Key-list / toKeyList preservation:
      - `bringUp_toKeyList_perm`, `applyChild_toKeyList_perm`,
        `splayUp_toKeyList_perm`, `splayBU_toKeyList_perm`.
        (Permutation, not equality — splay permutes keys.)
- [ ] **P0.7** BST preservation for the primitives:
      - `IsBST_bringUp`, `IsBST_applyChild` (under direction-aware
        hypotheses on frame keys), `IsBST_splayUp`, `IsBST_splayBU`.
      Replaces `Correctness.splay_preserves_BST` for `splayBU`.
- [ ] **P0.8** Root-after-splay:
      - `splayBU_root_of_contains : t.contains q → ∃ l r, splayBU t q = .node l q r`.
      Replaces `Correctness.splay_root_of_contains`.

### Phase 1 — spine / search-path primitives (in `BottomUp.lean`)

The coloring argument reasons about the right spine of the tree before
and after each splay, and about the search path. We prove everything
we need in terms of `descend` and `splayUp`.

- [ ] **P1.1** `searchPath_eq_descend_keys : t.searchPath q =
      (reached keys) ++ (descend t q).2.keys.reverse` (exact form
      TBD; statement says the top-down search path equals the frame
      keys read in root-first order, optionally plus the target).
- [ ] **P1.2** `splayingSpine_eq` — parallel statement for
      `splayingSpine` (searchPath.tail).
- [ ] **P1.3** `rightSpine` after one `bringUp` (Elmasry §2 relations
      (1)–(5) at the primitive level): small lemmas relating the
      right-spine of the post-rotation tree to the pre-rotation tree
      and the rotation direction.
- [ ] **P1.4** `rightSpine` after one `applyChild (bringUp)` step.
- [ ] **P1.5** `rightSpine` after `splayUp` — by frame induction on
      P1.3/P1.4.
- [ ] **P1.6** Off-path invariance:
      `subtree_rooted_at_splayBU_off_path :
      (¬ z ∈ t.searchPath q) → subtree_rooted_at (splayBU t q) z =
      subtree_rooted_at t z`. Reproves L1847 + L2346 in one shot.

### Phase 2 — migrate `SplaySequential.lean`: drop duplicates, use `splayBU`

- [ ] **P2.1** Add imports `Basic`, `BottomUp`, `Correctness` at the
      top. Remove the local `import Mathlib.Algebra.Ring.Parity` once
      parity reasoning is gone (P4).
- [ ] **P2.2** Delete lines 5–223 from `SplaySequential.lean` (all
      duplicated defs: `BinaryTree`, `num_nodes`, rotations, `Rot`,
      `rotate`, `search_path_len`, `splay'`, `splay`,
      `subtree_rooted_at`, `splay.cost'`, `splay.cost`, `ForallTree`,
      `IsBST`, `rank`, `φ`). Keep `splay.sequence_cost`, `one_to_n`,
      `BinaryTree.toKeyList` (these are sequential-access specific).
- [ ] **P2.3** Rewrite `splay.sequence_cost` in terms of `splayBU` /
      `splayBU.cost`.
- [ ] **P2.4** Global replace in the remaining body:
      `splay ` → `splayBU `, `splay.cost` → `splayBU.cost`.
- [ ] **P2.5** Expect the file to fail to build; every structural
      lemma is now wrong. That's Phase 3.

### Phase 3 — reprove the coloring / counter machinery

The definitions `Color`, `ColorState`, `LinkCounters`, `gVal`, `hVal`,
`vVal`, `stepColor`, `processLink`, `processLinks`, `colorSequence`,
`totalCounters`, `bigVset`, `aTargetsOf`, `ColorInvariant` don't
reference splay internals — they're parameterised by arbitrary
`(t_before, t_after)` pairs. They should survive P2 unchanged.

The lemmas that DO reference splay internals need frame-induction
rewrites. Work bottom-up in dependency order:

- [ ] **P3.1** `splay_cost_eq_path_len` (L740) → `splayBU.cost_eq`
      (direct from P0.4). Delete old `splay_cost'_eq` (L596).
- [ ] **P3.2** `cost_eq_step_total` (L795) — relate
      `splayBU.cost t q` to `linksOfSpine (splayingSpine t q)`.
      Uses P0.4 + P1.2.
- [ ] **P3.3** `sequence_cost_foldl_eq` (L801) — straightforward
      after P3.2.
- [ ] **P3.4** toKeyList family (L839–899): reprove
      `splayBU_toKeyList_perm` via P0.6 and kill the intermediate
      `rotate*_toKeyList`, `splay'_toKeyList` lemmas. Update
      `splay_toKeyList` to be `splayBU_toKeyList_perm`.
- [ ] **P3.5** `searchPath_subset_toKeyList` (L899) — should transfer
      unchanged (it's about `searchPath` and `toKeyList`, no splay).
- [ ] **P3.6** `splay'_root_in_searchPath` (L1698) → replace with
      `splayBU_root_in_searchPath` by direct frame induction (or via
      P0.8 if `contains`).
- [ ] **P3.7** `subtree_rooted_at_splay'_off_path` (L1847) and
      `subtree_rooted_at_splay_off_path` (L2346) — both collapse to
      P1.6; delete both, replace with `subtree_rooted_at_splayBU_off_path`.
- [ ] **P3.8** `vVal_rotate{Right,Left}_{pivot,nonpivot}` (L1531,
      L1599, L1612, L1624) — these become
      `vVal_bringUp_pivot` / `vVal_bringUp_nonpivot` (parameterised
      by `Dir`). Each is one symmetric statement instead of four.
- [ ] **P3.9** `vVal_splay_off_path` (L2470) — reprove by frame
      induction on `splayUp`, using P3.8 at each pair.
- [ ] **P3.10** `stepColor_color_eq_of_not_mem_searchPath` (L2552),
      `vVal_stepColor_splay_off_path` (L2757) — should transfer once
      P1.6 and P3.9 are in place.
- [ ] **P3.11** `lemma1c_monotone` (L2805) — the standing `sorry`
      with the known issue around K-links / black rotations. Under
      `splayBU` the K-link bucket is exactly the rotations where
      `f1.dir ≠ f2.dir` with one side on the current right spine;
      the frame-level formulation makes this distinction explicit
      and should let the lemma be restricted cleanly to non-black
      nodes. (This is the main technical content; separate sub-plan
      needed before we try it.)
- [ ] **P3.12** `stepColor_A_*` (L2858, L2873), `colorSequence_A_le`
      (L2900) — transfer once the above are green.

### Phase 4 — polish and close

- [ ] **P4.1** Remove unused imports from `SplaySequential.lean`
      (`Mathlib.Algebra.Ring.Parity`, `Real.logb` if φ stays in
      `Basic.lean`).
- [ ] **P4.2** Verify `grep -nE 'splay['\\'']|splay\\.cost['\\'']|rotateRight|rotateLeft|\\bRot\\b' SplaySequential.lean`
      returns nothing.
- [ ] **P4.3** `lake build` green end-to-end; commit.
- [ ] **P4.4** Consider splitting `SplaySequential.lean` (~3k lines)
      into `SplaySequential/Colors.lean`,
      `SplaySequential/Counters.lean`,
      `SplaySequential/Structural.lean`, `SplaySequential/Main.lean`
      once the refactor dust has settled.

## Risks and open questions

1. **Induction on `splayUp`**: the natural pattern-match is three
   cases (nil / singleton / pair-cons). `fun_induction splayUp` may or
   may not produce usable IH shapes; if not, state an explicit
   recursor in P0.2.
2. **BST invariants under frame induction**: a frame carries a key
   `k` and a `sibling` subtree. Maintaining BST-ness as we walk
   through `splayUp` means carrying hypotheses like "every key in
   `sibling` is on the correct side of every remaining frame's key".
   Plan: define an auxiliary predicate `BSTPath : BinaryTree →
   List Frame → Prop` and prove `IsBST (reassemble c path) ↔ IsBST c
   ∧ BSTPath c path` once, then every subsequent lemma uses this.
3. **K-link bucket in `lemma1c_monotone`**: the current `sorry` is
   the hardest part. Under `splayBU` the "black node" condition
   becomes a frame-level predicate about the grandparent's right
   spine, which makes the case analysis explicit. Expect a separate
   sub-plan before tackling P3.11.
4. **Test coverage**: once P0/P1 are in place, add a small `#eval`
   test demonstrating `splayBU` on a concrete tree for a handful of
   queries (to sanity-check the definitions before building a
   mountain of proofs on them).

## Milestones / success criteria

- **M0** (end of Phase 0): `BottomUp.lean` exports the invariant kit —
  `num_nodes_splayBU`, `splayBU_empty_iff`, `splayBU.cost_eq`,
  `IsBST_splayBU`, `splayBU_root_of_contains`. Library builds.
- **M1** (end of Phase 1): all spine / search-path / off-path
  structural facts available as lemmas about `descend` and `splayUp`.
  Library builds.
- **M2** (end of Phase 2): `SplaySequential.lean` no longer defines
  any of the duplicated symbols. Library may still fail to build; all
  remaining failures are in structural lemmas (Phase 3).
- **M3** (end of Phase 3): `SplaySequential.lean` builds and
  `sequential_theorem` type-checks and proves against `splayBU` (with
  `lemma1c_monotone` possibly still `sorry` — track separately).
- **M4** (end of Phase 4): No residual references to `splay'`,
  `splay.cost'`, `rotate`, `Rot` in `SplaySequential.lean`. Full build
  green.

## Changelog

- 2026-04-18: initial plan drafted.
- 2026-04-18: Phase 0 progress.
  - **P0.1** done: `Frame.nodes`, `pathNodes`, `num_nodes_bringUp`,
    `num_nodes_applyChild`, `num_nodes_Frame_attach`, `num_nodes_splayUp`,
    `num_nodes_descend` (+ `_go`), `num_nodes_splayBU`, `splayBU_empty_iff`
    in `BottomUp.lean`.
  - **P0.2** done: `splayUp_nil`, `splayUp_singleton`, `splayUp_cons_cons`,
    `splayUp_cons_cons_same/_opp`, `splayUp_induction`.
  - **P0.3** done: `reassemble`, `reassemble_nil/_cons/_append`,
    `descend_empty/_eq/_lt/_gt`, `descend_go_append`,
    `descend_go_preserves_tree`, `descend_preserves_tree`,
    `descend_go_length_le`.
  - **P0.4** done: `splayBU_cost_eq_length`, `splayBU_cost_nonneg`.
    Note: the cost equals `(descend t q).2.length`, not `search_path_len`
    (they differ by 1 in the node-reached case).
  - **P0.5** done: `BinaryTree.search_path_len` moved to `BinaryTree.lean`;
    `search_path_len_eq_descend_length` relates it to descend length plus
    an indicator for reaching a node.
  - **P0.6** done as *equality* (not merely permutation):
    `BinaryTree.toKeyList` moved to `BinaryTree.lean`;
    `toKeyList_rotateRight/_rotateLeft/_bringUp/_applyChild/_Frame_attach`,
    `reassemble_toKeyList_congr`, `toKeyList_splayUp`, `toKeyList_splayBU`.
  - **P0.7** deferred.
  - **P0.8** deferred.
  - Side-effects: `BinaryTree` now derives `DecidableEq`.
  - `GraphAlgorithms.lean` now also imports `BottomUp` so `lake build`
    covers this file.
