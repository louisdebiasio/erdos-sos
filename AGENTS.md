# Maintaining the papers and formalizations

- Keep the papers focused on proved results and their proofs. Put any
  proposed extensions in separate working material, outside the public papers.
- Both Lean projects pin Lean 4.19.0 and use its bundled Std library.
  Add no external Lean dependencies without an explicit task requiring them.
- Ordinary `.lean` files are the source of truth. Do not reintroduce JSON
  recovery bundles or duplicate maintenance programs.
- After changing Lean sources or build configuration, run
  `python3 scripts/check_lean.py --clean`; use `--lake` for an existing toolchain.
  Keep the public statement wrappers and mandatory audit declarations in sync.
- Preserve globally injective embeddings and allow opposite host arcs.
  Keep the public digraph theorem stated using connectedness and absence of
  simple cycles. The proved bridge in `Digraph/TreeBridge.lean` supplies the
  recursive construction internally; preserve its mandatory axiom audits.
- After paper edits, run `python3 scripts/build_papers.py` and inspect the PDFs.
- Update provenance only from checks actually performed. Preserve the original
  source hashes as a historical baseline; do not refresh them after edits.
