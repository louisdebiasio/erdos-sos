#!/usr/bin/env python3
"""Build the pinned Lean projects and audit their exported theorems."""

import argparse
from pathlib import Path
import re
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
PROJECTS = {
    "hypergraphs": ("Hypergraphs", {
        "Kalai.kalai_master", "Kalai.kalai_shadow_bound", "Kalai.kalai_bound",
        "Kalai.kalai_contains_tree", "KalaiResults.shadow_bound",
        "KalaiResults.binomial_bound", "KalaiResults.contains_tree",
    }),
    "digraphs": ("Digraphs", {
        "Digraph.rooted_master", "Digraph.signed_leaf_count",
        "Digraph.signed_branch_count", "Digraph.addarioBerry_bound",
        "Digraph.addarioBerry_contains", "AntidirectedResults.density_bound",
        "AntidirectedResults.contains_tree",
        "Digraph.conventional_rooted", "Digraph.ConventionalTree.to_recursive",
        "Digraph.acyclic_iff_no_simple_cycle", "Digraph.conventionalTree_iff",
        "Digraph.addarioBerry_bound_of_no_simple_cycle",
        "Digraph.addarioBerry_contains_of_no_simple_cycle",
    }),
}
PERMITTED = {"propext", "Classical.choice", "Quot.sound"}
FORBIDDEN = re.compile(r"\b(sorry|admit|axiom|unsafe|native_decide)\b")


def audit_results(output, declarations):
    """Require exactly one axiom report for every requested declaration."""
    reports = re.findall(
        r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", output, re.DOTALL
    )
    reports += [(name, "") for name in re.findall(
        r"'([^']+)' does not depend on any axioms", output
    )]
    names = [name for name, _ in reports]
    if len(names) != len(set(names)) or set(names) != set(declarations):
        raise RuntimeError("Axiom output does not match the requested declarations")
    for name, axioms in reports:
        dependencies = {item.strip() for item in axioms.split(",") if item.strip()}
        if dependencies - PERMITTED:
            raise RuntimeError(f"Unexpected axioms for {name}: {sorted(dependencies - PERMITTED)}")


def check_project(name, lake, clean):
    directory, mandatory = PROJECTS[name]
    project = ROOT / directory / "lean"
    for filename in ("lean-toolchain", "lakefile.toml", "lake-manifest.json",
                     "Statements.lean", "Audit.lean"):
        if not (project / filename).is_file():
            raise RuntimeError(f"Missing {project / filename}")
    toolchain = (project / "lean-toolchain").read_text().strip()
    if toolchain != "leanprover/lean4:v4.19.0":
        raise RuntimeError(f"Unexpected toolchain: {toolchain}")
    sources = sorted(p for p in project.rglob("*.lean")
                     if ".lake" not in p.relative_to(project).parts)
    for source in sources:
        if FORBIDDEN.search(source.read_text()):
            raise RuntimeError(f"Forbidden proof placeholder or construct in {source}")
    declarations = re.findall(r"^#print axioms (\S+)\s*$",
                              (project / "Audit.lean").read_text(), re.MULTILINE)
    if len(declarations) != len(set(declarations)) or not mandatory <= set(declarations):
        raise RuntimeError("Audit must include each public result and have no duplicate declarations")

    def run(arguments, capture=False):
        return subprocess.run([lake] + arguments, cwd=project, check=True,
                              text=True, capture_output=capture)

    version = run(["env", "lean", "--version"], capture=True).stdout.strip()
    if not re.match(r"Lean \(version 4\.19\.0(?:,|\s|\))", version):
        raise RuntimeError(f"The selected executable uses the wrong Lean version: {version}")
    print(f"{directory}: {version}", flush=True)
    if clean:
        run(["clean"])
    run(["build"])
    audit = run(["env", "lean", "Audit.lean"], capture=True)
    print(audit.stdout, end="", flush=True)
    if audit.stderr:
        print(audit.stderr, end="", file=sys.stderr)
    audit_results(audit.stdout, declarations)
    print(f"PASS: {directory}: {len(sources)} Lean files; {len(declarations)} axiom audits.",
          flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--project", choices=["all", *PROJECTS], default="all")
    parser.add_argument("--lake", default="lake", help="Lake executable or absolute path")
    parser.add_argument("--clean", action="store_true", help="Remove project build outputs first")
    args = parser.parse_args()
    executable = shutil.which(args.lake)
    if executable is None:
        parser.error("Lake was not found. Install Lean 4.19.0 or pass --lake /path/to/lake.")
    # Keep the executable name: an elan shim may be a symlink to a multicall binary.
    lake = str(Path(executable).absolute())
    selected = PROJECTS if args.project == "all" else [args.project]
    for name in selected:
        check_project(name, lake, args.clean)


if __name__ == "__main__":
    try:
        main()
    except (RuntimeError, subprocess.CalledProcessError) as error:
        raise SystemExit(f"FAIL: {error}") from error
