#!/usr/bin/env python3
"""nla-16 parity harness — merge scanner + z3/lean run logs into the site table.

Usage:
  harness.py <crate-name> <crate-src-dir> [--z3-log LOG] [--lean-log LOG] [--csv OUT] [--summary]

Attribution model (Slice-0 recon, pinned in board/nla-16-plan.md):
- z3 side: a site fails iff an `error: assert_nonlinear_by:` carries a span at
  exactly its file:line. Non-nonlinear errors are attributed to enclosing fns
  and recorded as `z3_other_error` notes (a function may fail for reasons
  outside the nonlinear sites; the nonlinear site itself still closed).
- lean side: failures are per-FUNCTION: `error: Lean ... failed for <fn>:` plus
  any other error span attributed to the enclosing fn. A site's lean status is
  `open` iff its enclosing function is in the failed set.
- Gate (per plan): z3-closed ∧ lean-open = VIOLATION. z3-open ∧ lean-open is
  per-function granularity — flagged `both-open-bisect` for the decision-3
  bisection queue (a function may contain several independent sites).
"""

from __future__ import annotations

import argparse
import csv
import io
import re
import subprocess
import sys
from collections import defaultdict
from pathlib import Path

ASSERT_NL_RE = re.compile(r"^error: (?:assert_nonlinear_by|.*nonlinear.*):", re.I)
SPAN_RE = re.compile(r"^\s*-->\s+(.+?):(\d+):(\d+)\s*$")
LEAN_FAIL_RE = re.compile(
    r"^error: Lean [^\n]*failed for ([A-Za-z0-9_:]+):", re.I)
RESULTS_RE = re.compile(r"verification results::\s*(\d+) verified,\s*(\d+) errors")
ERROR_RE = re.compile(r"^error[:\[]")


def scan_sites(crate_src: Path) -> list[dict]:
    tools = Path(__file__).parent / "sites.py"
    out = subprocess.run(
        ["python3", str(tools), str(crate_src)],
        capture_output=True, text=True, check=True)
    rows = list(csv.reader(io.StringIO(out.stdout)))
    header = rows[0]
    sites = []
    for r in rows[1:]:
        d = dict(zip(header, r))
        for k in ("line", "col", "fn_start", "fn_end"):
            d[k] = int(d[k])
        sites.append(d)
    return sites


def parse_z3_log(path: Path):
    """Returns (failed_site_spans:set[(file,line)], other_error_spans:list[(file,line)], summary)."""
    failed_sites = set()
    other_spans = []
    summary = None
    lines = path.read_text(errors="replace").splitlines()
    i = 0
    while i < len(lines):
        ln = lines[i]
        m = RESULTS_RE.search(ln)
        if m:
            summary = (int(m.group(1)), int(m.group(2)))
        if ERROR_RE.match(ln):
            span = None
            for j in range(i + 1, min(i + 12, len(lines))):
                sm = SPAN_RE.match(lines[j])
                if sm:
                    span = (sm.group(1), int(sm.group(2)))
                    break
            if span:
                if ASSERT_NL_RE.match(ln):
                    failed_sites.add(span)
                else:
                    other_spans.append(span)
        i += 1
    return failed_sites, other_spans, summary


def parse_lean_log(path: Path):
    """Returns (failed_fn_names:set, other_error_spans:list, summary)."""
    failed_fns = set()
    other_spans = []
    summary = None
    lines = path.read_text(errors="replace").splitlines()
    for i, ln in enumerate(lines):
        m = LEAN_FAIL_RE.match(ln)
        if m:
            failed_fns.add(m.group(1))
            continue
        m = RESULTS_RE.search(ln)
        if m:
            summary = (int(m.group(1)), int(m.group(2)))
            continue
        if ERROR_RE.match(ln):
            for j in range(i + 1, min(i + 12, len(lines))):
                sm = SPAN_RE.match(lines[j])
                if sm:
                    other_spans.append((sm.group(1), int(sm.group(2))))
                    break
    return failed_fns, other_spans, summary


def norm_span_file(span_file: str, sites_files: set[str]) -> str | None:
    """Map a log span path to one of the scanned site files (suffix match)."""
    if span_file in sites_files:
        return span_file
    matches = [f for f in sites_files if span_file.endswith(f) or f.endswith(span_file)]
    return matches[0] if len(matches) == 1 else None


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("crate")
    ap.add_argument("crate_src")
    ap.add_argument("--z3-log")
    ap.add_argument("--lean-log")
    ap.add_argument("--csv")
    ap.add_argument("--summary", action="store_true")
    args = ap.parse_args()

    crate_src = Path(args.crate_src).resolve()
    sites = scan_sites(crate_src)
    site_files = {s["file"] for s in sites}

    z3_failed_sites, z3_other_spans, z3_summary = set(), [], None
    if args.z3_log:
        z3_failed_sites, z3_other_spans, z3_summary = parse_z3_log(Path(args.z3_log))
    lean_failed_fns, lean_other_spans, lean_summary = set(), [], None
    if args.lean_log:
        lean_failed_fns, lean_other_spans, lean_summary = parse_lean_log(Path(args.lean_log))

    # attribute "other" spans to fns
    def attr_fn(fspan):
        nf = norm_span_file(fspan[0], site_files)
        if nf is None:
            return None
        best = None
        for s in sites:
            if s["file"] == nf and s["fn_start"] <= fspan[1] <= s["fn_end"]:
                if best is None or s["fn_start"] >= best["fn_start"]:
                    best = s
        return best["fn"] if best else "<module>"

    z3_other_fns = {a for a in (attr_fn(s) for s in z3_other_spans) if a}
    lean_other_fns = {a for a in (attr_fn(s) for s in lean_other_spans) if a}

    failed_norm = {
        nf
        for f, l in z3_failed_sites
        if (nf := (norm_span_file(f, site_files), l))[0] is not None
    }
    rows = []
    counts = defaultdict(int)
    for s in sites:
        z3 = "-"
        if args.z3_log:
            z3 = "open" if (s["file"], s["line"]) in failed_norm else "closed"
        lean = "-"
        if args.lean_log:
            lean = "open" if s["fn"] in lean_failed_fns else "closed"
        notes = []
        if z3 == "open" and s["fn"] in z3_other_fns:
            notes.append("z3_other_error")
        if lean == "open" and s["fn"] in lean_other_fns:
            notes.append("lean_other_error")
        verdict = ""
        if z3 != "-" and lean != "-":
            if z3 == "closed" and lean == "open":
                verdict = "violation"
            elif z3 == "open" and lean == "open":
                verdict = "both-open-bisect"
            elif z3 == "open" and lean == "closed":
                verdict = "lean-better"
            else:
                verdict = "agree-closed"
            counts[verdict] += 1
        rows.append([args.crate, s["file"], s["line"], s["fn"],
                     z3, lean, verdict, ";".join(notes)])

    out = sys.stdout
    if args.csv:
        out = open(args.csv, "w", newline="")
    try:
        w = csv.writer(out)
        w.writerow(["crate", "file", "line", "fn", "z3", "lean", "verdict", "notes"])
        w.writerows(rows)
    finally:
        if args.csv:
            out.close()

    if args.summary:
        print(f"sites: {len(sites)}")
        if z3_summary:
            print(f"z3 fn-results: {z3_summary[0]} verified / {z3_summary[1]} errors")
        if lean_summary:
            print(f"lean fn-results: {lean_summary[0]} verified / {lean_summary[1]} errors")
        for k in sorted(counts):
            print(f"{k}: {counts[k]}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
