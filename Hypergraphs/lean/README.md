# Kalai's tight-tree conjecture in Lean

This independent Lean 4.19.0 project uses only the bundled `Std` library.
The [paper](../kalai_hypergraphs.pdf) gives the mathematical argument.
Start with [Statements.lean](Statements.lean) for the public theorem surface.
Each statement has a proof supplied by the library.

## Main results

| Public statement | Underlying declaration | Conclusion for a tree-free host |
| --- | --- | --- |
| `KalaiResults.shadow_bound` | `Kalai.kalai_shadow_bound` | `r * edges(H) ≤ (edges(T) - 1) * shadowCount(H, r - 1)` |
| `KalaiResults.binomial_bound` | `Kalai.kalai_bound` | `r * edges(H) ≤ (edges(T) - 1) * binomial(vertices(H), r - 1)` |
| `KalaiResults.contains_tree` | `Kalai.kalai_contains_tree` | A strict violation of the binomial bound gives an embedding |

`Kalai.kalai_master` is the stronger supporting-state inequality at any
ordered target root edge. All arithmetic is in natural numbers, with the
factor `r` clearing the denominator. The hypotheses require `r ≥ 2`.
Empty hosts and hosts with fewer than `r` vertices are included.

## Definitions to review

- [Hypergraph.lean](Kalai/Hypergraph.lean): `FiniteHypergraph` lists vertices
  and edges without duplicates and forbids edges equal up to permutation.
  `HasEdge` ignores the order of edge vertices. `Embedding` is injective on
  all listed target vertices and preserves edges; it need not preserve nonedges.
- [TightTree.lean](Kalai/TightTree.lean): `TightEdgeOrder` requires a nonempty
  edge ordering in which each later edge introduces a fresh vertex and has
  all its other vertices in an earlier parent edge. `IsTightTree` requires
  uniformity, this edge order, and no isolated target vertices.
- [ShadowCounts.lean](Kalai/ShadowCounts.lean): `shadowCount` counts canonical
  shadow faces. `faceInShadow_iff_subset_edge` identifies them with the
  appropriate subsets of host edges in a uniform hypergraph.
- [KalaiTheorem.lean](Kalai/KalaiTheorem.lean): `binomial` has the ordinary
  boundary values and Pascal recurrence; `subsetsOfSize_length` proves its
  counting interpretation and yields the binomial bound.

Embeddings are total maps on the ambient label types, with constraints on
the listed target vertices. Values outside the target list are irrelevant.
The host need not be partite, and embeddings need not preserve a vertex order.

## Proof structure

The library proves a shortest-prefix rotation and its recovery map, glues
actual injective embeddings with disjoint images outside the root, and
proves the earlier-mark leaf transfer. Finite enumeration and bijections
then give the exact global counts

```text
M = r! * edges(H) * (n - r + 1)!
Q = (r - 1)! * shadowCount(H, r - 1) * (n - r + 1)!
M ≤ supportCount(T, root) + (edges(T) - 1) * Q.
```

For the structural step, [LeafInsertion.lean](Kalai/LeafInsertion.lean),
[TightGrowth.lean](Kalai/TightGrowth.lean), and
[TightTree.lean](Kalai/TightTree.lean) construct rooted certificates at every
edge from the ordinary edge ordering. The final theorems assume neither a
certificate nor a transfer inequality. This rerooting argument differs
from the paper's running-intersection proof. The separate path warm-up is
not translated line by line.

Support is an existence proposition: states are counted once, independently
of the number of embedding witnesses. The definitions use classical choice
and finite enumerations; they are not efficient embedding-search algorithms.

## Build and audit

With the pinned toolchain and `lake` available, run inside this directory:

```sh
lake build
lake env lean Audit.lean
```

These commands build the formalization and print its selected transitive axiom
dependencies. Python is not required. To automate a clean build and enforce
the permitted axiom list, run the optional Python 3 helper from the repository root:

```sh
python3 scripts/check_lean.py --project hypergraphs --clean
```

Or use `--lake /path/to/lake`. The Python checker runs [Audit.lean](Audit.lean),
requires all public results in the audit, and permits only `propext`,
`Classical.choice`, and `Quot.sound` as transitive axioms.

A clean build on September 6, 2026 checked **38 Lean files and 98 audited
declarations**. See [provenance](../../provenance/README.md). The formal
examples cover empty blocks, both divider endpoints, leaf transfers,
branches through different faces, root reorderings, empty hosts, a sharp
graph-path instance, and rejection of a triangle and an isolated target vertex.

The ordinary `.lean` files and pinned configuration are the complete source.
No recovery bundle or package download is needed after the toolchain is installed.
