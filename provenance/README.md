# Provenance and verification

## Mathematical attribution

Louis DeBiasio is the author of the three papers. AI tools assisted in
developing the exposition and the hypergraph and digraph formalizations;
the acknowledgments disclose this assistance.

The author selected MIT licensing for the code and repository documentation,
and CC BY 4.0 for the papers and LaTeX sources. [LICENSE.md](../LICENSE.md)
specifies the scope and links to the complete license texts.

The original graph proof is the GPT-6 Astra proof from the
[FrontierMath Erdős benchmark](https://epoch.ai/files/frontiermath-erdos.pdf).
Its upstream Lean source and benchmark provenance are available in
[tadamcz/erdos548](https://github.com/tadamcz/erdos548). This collection's
graph paper is an exposition. The hypergraph and digraph arguments extend
the marked-position method and are presented separately here.

The supplied materials do not establish a complete model-by-model history
for the two extension projects; no such history is inferred in this record.
The digraph counting utilities were adapted from the hypergraph project and
retained under their own namespace, without importing the Kalai theorem.

## Source recovery and publication edits

The supplied snapshot stored the Lean sources and pinned toolchain files in
JSON recovery bundles. Their recorded SHA-256 values were verified before
restoring them to ordinary files. The bundles and redundant recovery helpers
were removed from the public layout after a successful clean build.

[original-source-sha256.json](original-source-sha256.json) records the
pre-edit hashes of all **55 initially supplied Lean source files**. Of these,
51 remain unchanged. The two audit files include checks for the public
wrappers; the completed digraph submission also updates `Digraph.lean` to
import the structural bridge and extends `DigraphTests.lean`.

The author subsequently supplied the completed digraph formalization.
[completed-digraph-source-sha256.json](completed-digraph-source-sha256.json)
records the verified hashes of its **21 supplied Lean files**, before
integration. Its three new modules, `GraphStructure`, `SimpleCycles`, and
`TreeBridge`, prove the passage from conventional graph hypotheses to the
recursive construction. All 20 library and test files from this submission
are unchanged; only `Audit.lean` was extended with an import and checks for
the public wrappers. No supplied proof body was edited during integration.

Each project adds `Statements.lean`, whose explicitly typed theorems are
proved by the accompanying library, and includes it among the default Lake
targets. The digraph wrappers now take connectedness and absence of simple
cycles as explicit hypotheses. After successful verification, the completed
project replaced `lean_incomplete/`; JSON bundles and duplicate recovery
and checking programs were removed from the public layout.

The publication layout retains one paper per topic. The graph exposition
uses the proof and warm-up from `main_sep4.tex`; the hypergraph paper uses
`kalai_hypergraphs.tex`; the digraph paper uses `antidirected_trees.tex`.
Older versions, speculative extensions, exploratory check output, and the
copied upstream PDF were removed. Author information, attribution,
cross-references, equation numbering, the graph proof's empty-host boundary,
and the hypergraph source's missing document terminator were corrected.
The digraph density result is now stated as a theorem, with its direct
tournament corollary retained. The papers describe the formal scope;
operational instructions are in the READMEs.

The author's revised hypergraph and digraph expositions were subsequently
reread in full, including the counting injections, induction, boundary
cases, and descriptions of the formal statements. Two minor clarifications
make uniformity explicit in the tight-tree definition and specify that a
simple undirected cycle has at least three vertices. The revised proofs
and author acknowledgments were retained; no speculative extensions were
added.

Build and audit helpers are consolidated in `scripts/`. The GitHub workflow
is configured for future pushes; it has not been run on GitHub as part of
this local preparation. No Comparator, NanoDa, Palomar registration, or
independent proof review is claimed.

## Local verification: September 6, 2026

The official Lean 4.19.0 macOS arm64 release was used:

```text
Lean 4.19.0, arm64-apple-darwin23.6.0
Compiler commit: 6caaee842e94
Hypergraphs: 38 Lean files; 98 transitive axiom audits — PASS
Digraphs:    22 Lean files; 43 transitive axiom audits — PASS
```

Both were clean builds, including every default library/test target and
the public statement files. All audited declarations use only `propext`,
`Classical.choice`, and `Quot.sound`. The source scan found no `sorry`,
`admit`, project `axiom`, `unsafe`, or `native_decide` constructs.
During the initial organization, the combined verification command also
passed in a fresh copy without build caches or recovery bundles, in a
directory whose path contains spaces. Both projects were clean-built again
after integrating the completed digraph proof. The audit parser was checked to reject missing,
duplicate, mismatched, and nonstandard-axiom reports.
Reproduce the check with:

```sh
python3 scripts/check_lean.py --clean
```

The revised hypergraph and digraph PDFs compile with resolved references
and no overfull boxes. All 20 pages were rendered and visually inspected:
thirteen hypergraph pages and seven digraph pages. The unchanged graph
PDF's eight pages were compiled and visually inspected during the initial
organization. Author and title metadata, local documentation links, and
paper cross-references were also checked.

## Formal scope

The hypergraph development proves the full shadow and binomial bounds
from `IsTightTree`, the fresh-vertex edge-order definition, including the
structural passage to rooted constructions. Its decomposition proof takes
a different route from the paper's running-intersection lemmas.

The digraph development proves the density and embedding theorems from
four explicit hypotheses: at least two target vertices, an antidirected
source/sink coloring, connectedness of the underlying undirected graph,
and absence of simple cycles. Connectedness is defined by walks; cycle
exclusion is defined using vertex-simple paths with a closing edge.
`acyclic_iff_no_simple_cycle` proves equivalence with edge-bypass acyclicity,
and `conventional_rooted` constructs a `RootedTree` at any listed vertex.
Thus the final theorem requires no recursive certificate from the caller.
The older recursive interface remains available. The paper's tournament
corollary is not separately formalized.
