# Tree embeddings in graphs, hypergraphs, and digraphs

Papers by Louis DeBiasio using ChatGPT 6 Astra.

| Topic | Paper | Source | Formal statements |
| --- | --- | --- | --- |
| Kalai's tight-tree conjecture | [PDF](Hypergraphs/kalai_hypergraphs.pdf) | [LaTeX](Hypergraphs/kalai_hypergraphs.tex) | [Lean](Hypergraphs/lean/Statements.lean) |
| Antidirected trees in digraphs | [PDF](Digraphs/antidirected_trees.pdf) | [LaTeX](Digraphs/antidirected_trees.tex) | [Lean](Digraphs/lean/Statements.lean) |
| Erdős–Sós proof exposition | [PDF](Graphs/erdos_sos.pdf) | [LaTeX](Graphs/erdos_sos.tex) | [Original proof repository](https://github.com/tadamcz/erdos548) |

## Results

**Hypergraphs.** If a finite simple, uniform hypergraph $H$ contains no copy
of a tight $r$-uniform tree with $m\geq1$ edges, where $r\geq2$, then

$$r\,|E(H)|\leq(m-1)|\partial H|\leq(m-1)\binom{|V(H)|}{r-1}.$$

Here $\partial H$ is the set of $(r-1)$-subsets contained in host edges.
The Lean theorem uses the usual fresh-vertex edge-order definition of a tight
tree, with no isolated target vertices. The structural decomposition,
counting inequalities, and binomial bound are proved in the project.
See the [formalization guide](Hypergraphs/lean/README.md).

**Digraphs.** If a finite loopless digraph $D$ contains no copy of an
antidirected tree $T$ on $t\geq2$ vertices, then

$$|A(D)|\leq(t-2)|V(D)|.$$

Opposite arcs are allowed. Copies are injective across all target vertices
and need not be induced. The Lean theorem assumes that the target is
antidirected, has at least two vertices, and has a connected underlying
graph with no simple cycle. The bridge from these graph hypotheses to the
recursive construction used in the counting proof is proved in Lean.
The paper also gives the tournament consequence, which is not separately
formalized. See the [formalization guide](Digraphs/lean/README.md).

**Graphs.** The graph paper expounds the marked-position proof of
Erdős–Sós from the [FrontierMath Erdős benchmark](https://epoch.ai/files/frontiermath-erdos.pdf),
whose original Lean proof and provenance are maintained in
[tadamcz/erdos548](https://github.com/tadamcz/erdos548). The graph theorem
and its original proof are attributed to that work.

## Verification

Both Lean projects pin **Lean 4.19.0** and use its bundled **Std** library.
There are no external Lean package dependencies. Install the pinned toolchain
with [elan](https://github.com/leanprover/elan), or use an existing installation.
The `.lean` files are provided directly. With `lake` on `PATH`, run these
commands inside either `Hypergraphs/lean/` or `Digraphs/lean/`:

```sh
lake build
lake env lean Audit.lean
```

The first command checks the libraries, formal examples, and public theorem
statements. The second prints the selected theorems' transitive axiom
dependencies. Neither command requires Python.

For an automated clean build and axiom check of both projects, the optional
Python 3 helper can be run from the repository root:

```sh
python3 scripts/check_lean.py --clean
```

The script builds both libraries, their formal examples, and their public
statement files. It rejects proof placeholders and selected unchecked
constructs, then audits the transitive axiom dependencies in each
`Audit.lean`. Only `propext`, `Classical.choice`, and `Quot.sound` are permitted.
The public results must be present in the audit.

To check one project or select an existing Lake executable:

```sh
python3 scripts/check_lean.py --project hypergraphs --clean
python3 scripts/check_lean.py --project digraphs --clean --lake /path/to/lake
```

The [verification record](provenance/README.md) reports the local clean builds.
The [GitHub workflow](.github/workflows/ci.yml) is configured to repeat the
builds and audits after the repository is uploaded. These checks certify the
encoded Lean statements; they do not establish independent mathematical
review or equivalence with definitions outside the stated formal scope.

## Building the papers

With Python 3 and a TeX distribution providing `pdflatex` and the standard
packages used by the sources, the document-build helper is:

```sh
python3 scripts/build_papers.py
```

Each PDF is written next to its LaTeX source. Auxiliary files go into the
ignored `.build/papers/` directory. The script fails on compilation errors,
unresolved references, or overfull boxes. To build just one paper, use
`--paper graphs`, `--paper hypergraphs`, or `--paper digraphs`.

## Attribution and licensing

[CITATION.cff](CITATION.cff) supplies author and collection metadata; cite the
individual paper title when referring to one result. The
[provenance record](provenance/README.md) documents source recovery and the
publication edits. The papers contain the mathematical exposition; the
repository does not include the exploratory extension notes or older drafts.

The papers and their LaTeX sources are licensed under **CC BY 4.0**.
The Lean code, scripts, build configuration, and repository documentation
are licensed under **MIT**. See [LICENSE.md](LICENSE.md) for the scope and
full license texts. Cited works and Lean retain their respective licenses.
