# Antidirected trees: Lean development

Checked September 6, 2026 with Lean 4.19.0 and its bundled `Std` library.
There is no Mathlib or external package dependency.

## Result and precise scope

The development proves the signed leaf and branch inequalities, the exact
finite-state normalizations, the master inequality, and the resulting bound

```text
number of arcs in D ≤ (number of vertices in T - 2) * number of vertices in D
```

when `D` has no injective, arc-preserving copy of the target. Strict inequality
in the other direction gives an embedding. Both empty hosts and hosts with
opposite arcs are covered.

The public theorem accepts conventional hypotheses: the target has at
least two vertices, is antidirected, and its underlying undirected graph is
connected and has no simple cycle. The structural bridge
is proved in `Digraph/TreeBridge.lean`.

Internally the density proof uses an **explicit recursive representation**.
The bridge constructs it from the graph hypotheses:

- `RootedTree.edge` starts with exactly one arc and its two endpoints.
- `RootedTree.leaf` adds one fresh vertex and its single incident arc, makes
  that new leaf the root, and reverses the root sign.
- `RootedTree.branch` joins two trees at their common root, with the same sign,
  exactly that one vertex in common, and exactly the union of their arc sets.

The index `k` is proved equal to the actual number of vertices minus two.
A source/sink coloring is also constructed and checked: every arc goes from
`plus` to `minus`. Embedding injectivity applies across all target vertices,
not independently within the source and sink classes.

**Completed representation bridge:** `UnderlyingConnected` is defined by
walks in the relation `G.Arc a b ∨ G.Arc b a`. `NoSimpleCycle` excludes a
vertex-simple path on at least three vertices together with its closing edge.
`SimplePath.nodup` proves that the path vertices are distinct.
`acyclic_iff_no_simple_cycle` proves equivalence with the edge-bypass
formulation of acyclicity used in the decomposition. These definitions do
not mention recursive tree certificates or the density inequality.

`conventional_rooted` constructs a recursive certificate for every listed
root, with its source/sink sign. Its strong induction on the vertex count
cuts an edge into two components, extends one by the other endpoint, and
glues at the root when both branches are nontrivial. Singleton components
are handled explicitly. `ConventionalTree.to_recursive` supplies the
unrooted bridge; callers need not provide any recursive certificate.

These are independently defined conventional graph predicates in this
Std-only project. An adapter from Mathlib or another library's graph types
is not included. `IsAntidirectedTree` remains the older recursive API for
compatibility; `ConventionalTree` is the separate graph-theoretic API.

## Main declarations

[`Statements.lean`](Statements.lean) collects the public results as
`AntidirectedResults.density_bound` and `AntidirectedResults.contains_tree`,
with the four explicit graph hypotheses below.

`Digraph/TreeBridge.lean` provides the conventional interface:

```lean
theorem addarioBerry_bound_of_no_simple_cycle
    (T : FiniteDigraph A) (D : FiniteDigraph B)
    (size : 2 ≤ T.vertices.length) (anti : Antidirected T)
    (connected : UnderlyingConnected T) (acyclic : NoSimpleCycle T)
    (free : ¬ Nonempty (Embedding T D)) :
    D.arcs.length ≤ (T.vertices.length - 2) * D.vertices.length

theorem addarioBerry_contains_of_no_simple_cycle
    (T : FiniteDigraph A) (D : FiniteDigraph B)
    (size : 2 ≤ T.vertices.length) (anti : Antidirected T)
    (connected : UnderlyingConnected T) (acyclic : NoSimpleCycle T)
    (dense : (T.vertices.length - 2) * D.vertices.length < D.arcs.length) :
    Nonempty (Embedding T D)
```

The variants `addarioBerry_bound_of_connected_acyclic` and
`addarioBerry_contains_of_connected_acyclic` accept the bundled
`ConventionalTree` hypotheses. `conventionalTree_iff` relates that bundle
to the four explicit hypotheses above.

`Digraph/TreeSemantics.lean` retains the original recursive interface:

```lean
def IsAntidirectedTree (T : FiniteDigraph A) : Prop :=
  ∃ r s k, RootedTree T r s k

theorem addarioBerry_bound
    (T : FiniteDigraph A) (D : FiniteDigraph B)
    (tree : IsAntidirectedTree T)
    (free : ¬ Nonempty (Embedding T D)) :
    D.arcs.length ≤ (T.vertices.length - 2) * D.vertices.length

theorem addarioBerry_contains
    (T : FiniteDigraph A) (D : FiniteDigraph B)
    (tree : IsAntidirectedTree T)
    (dense : (T.vertices.length - 2) * D.vertices.length < D.arcs.length) :
    Nonempty (Embedding T D)
```

The rooted statements `rooted_master`, `antidirected_density`, and
`antidirected_contains_tree` are in `Digraph/RootedTree.lean`.

## Proof chain

| Module | Checked content |
| --- | --- |
| `Basic` | Finite loopless simple digraphs, signed adjacency, embeddings, leaf extension |
| `SignedStates` | Marked/supportive states and equality of positive and negative populations |
| `SignedLeaf` | Leaf transfer, inverse/injectivity, and the exceptional-state count |
| `BranchSupport` | Gluing actual embeddings with disjoint images outside the common root |
| `SignedBranch` | Earliest-mark rotation, decoding/injectivity, and the branch count |
| `Normalization` | Arc/cut bijection, factorial normalizations, and density cancellation |
| `RootedTree` | Recursive target representation, vertex count, master induction, density theorem |
| `TreeSemantics` | Source/sink coloring and recursive unrooted theorem interface |
| `GraphStructure` | Independent graph predicates, induced components, edge cuts, leaf extension and root amalgam |
| `SimpleCycles` | Simple paths, elimination of repeats, equivalence of cycle exclusion and edge-bypass acyclicity |
| `TreeBridge` | Conventional trees have recursive certificates; density and embedding interfaces |

`M D s` is the cardinality of the actual finite signed state population;
`R T D r s` counts its supportive states; `Q D` counts all vertex orderings.
The checked identities and inequalities are:

```text
M(D,+) = M(D,-) = |arcs(D)| * (|vertices(D)| - 1)!
Q(D) = |vertices(D)|!
R(S,p,flip(s)) ≤ R(T,newRoot,s) + Q(D)
R(S,r,s) + R(U,r,s) ≤ M(D,s) + Q(D) + R(T,r,s)
M(D,s) ≤ R(T,r,s) + k * Q(D)
```

The leaf transfer swaps the first vertex and the marked vertex, leaving the
intervening block fixed. This replaces the manuscript's prefix reversal with
another indexed involution having the same prefix vertex set. The branch
rotation follows the manuscript's earliest **marked** supportive prefix,
including the empty-block/root-only exception. Its inverse ignores the
intervening block when recovering the earliest prefix.

The generic rotation, finite-list counting, enumeration, and factorial modules
were adapted from `Hypergraphs/lean/Kalai/`. They are copied here under the
`Digraph` namespace, so this project builds independently of that project.
No Kalai extremal theorem is imported or assumed.

## Build, tests, and trust audit

The source files are provided directly. With the pinned Lean 4.19.0
`lake` on `PATH`, run these commands inside `Digraphs/lean/`:

```sh
lake build
lake env lean Audit.lean
```

The first checks the library, `DigraphTests.lean`, and `Statements.lean`.
The second prints the audited declarations' transitive axiom dependencies.
Neither command requires Python.

For a clean build with automatic enforcement of the axiom whitelist, run
the optional helper from the repository root:

```sh
python3 scripts/check_lean.py --project digraphs --clean
```

Use `--lake /path/to/lake` to select an existing installation. The helper
rejects proof placeholders and selected unchecked constructs. All audited
declarations use only `propext`, `Classical.choice`, and `Quot.sound`.
The public results and structural bridge must be present in the audit.

Tests include:

- a tree with its source root and with a sink leaf root;
- a genuine three-branch out-star;
- the density theorem applied to concrete constructed targets;
- both signs on a host with opposite arcs;
- empty-host normalization;
- a strict-density embedding consequence in a complete bidirected host;
- rejection of the mixed directed path `0 -> 1 -> 2` as antidirected;
- a star and a four-vertex alternating path supplied through independently
  proved conventional graph hypotheses;
- reconstruction at an internal sink and at a leaf source;
- density and strict-density consequences through the conventional interface;
- an explicit simple cycle excluding an alternating square as a tree;
- rejection of a disconnected pair of arcs as connected.

The build and audit check the structural bridge as well as the density
proof. The manuscript's tournament corollary is not separately formalized.
See the [verification record](../../provenance/README.md) for the checked
source snapshots and local build results.
