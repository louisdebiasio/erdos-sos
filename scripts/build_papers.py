#!/usr/bin/env python3
"""Compile the three papers; keep auxiliary files in .build/papers/."""

import argparse
from pathlib import Path
import re
import shutil
import subprocess

ROOT = Path(__file__).resolve().parents[1]
PAPERS = {
    "graphs": "Graphs/erdos_sos.tex",
    "hypergraphs": "Hypergraphs/kalai_hypergraphs.tex",
    "digraphs": "Digraphs/antidirected_trees.tex",
}


def build(name):
    source = ROOT / PAPERS[name]
    output = ROOT / ".build" / "papers" / source.parent.name
    output.mkdir(parents=True, exist_ok=True)
    for _ in range(3):
        result = subprocess.run(
            ["pdflatex", "-no-shell-escape", "-halt-on-error", "-interaction=nonstopmode",
             f"-output-directory={output}", source.name],
            cwd=source.parent, text=True, capture_output=True,
        )
        if result.returncode:
            raise RuntimeError(result.stdout[-6000:] + result.stderr)
    log = (output / source.with_suffix(".log").name).read_text(errors="replace")
    problems = re.findall(
        r"^.*(?:undefined|multiply defined|Overfull \\[hv]box|Rerun to get).*$",
        log, re.MULTILINE,
    )
    if problems:
        raise RuntimeError(f"{source}: unresolved LaTeX diagnostics:\n" + "\n".join(problems))
    destination = source.with_suffix(".pdf")
    shutil.copyfile(output / destination.name, destination)
    print(f"PASS: {destination.relative_to(ROOT)}", flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--paper", choices=["all", *PAPERS], default="all")
    args = parser.parse_args()
    if not shutil.which("pdflatex"):
        parser.error("pdflatex was not found. Install a TeX distribution first.")
    for name in PAPERS if args.paper == "all" else [args.paper]:
        build(name)


if __name__ == "__main__":
    try:
        main()
    except RuntimeError as error:
        raise SystemExit(str(error)) from error
