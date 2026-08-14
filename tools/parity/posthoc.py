#!/usr/bin/env python3
"""nla-16 parity harness — post-hoc stats harvest.

Re-elaborates per-fn pkg modules with NLA16_STATS=1 and harvests the
`[nla16-stats]` channel per obligation. This is THE layer-attribution
mechanism for the census: verus drops warning-severity diagnostics on
green runs (sorry-filtered, generate.rs:2558 area), so the stats cannot
travel through the verus log on success — but the persisted pkg modules
(target/tactus-lean/<crate-stem>/pkg/*.lean) elaborate standalone.

Requires: `verus --lean-backend` already ran for the crate (pkg modules
+ deps/Stmts oleans exist under the crate-root target/tactus-lean/).

Protocol (all sequential — host ≤4-thread rule):
  posthoc.py <crate-src-dir> <tactus-lean-lib-dir> [options]
    scans sites; locates pkg modules whose leaf matches site fn names;
    for each (uncached) module: NLA16_STATS=1 lean <pkg.lean>;
    parses stats lines; maps each to the nearest preceding `@rust:` span
    in the pkg module;
    writes rows to <out-csv>: crate,file,line,fn,site_line,payload,rust_span

Prelude: verus computes a prelude-cache hash per run; the matching
~/.cache/tactus/prelude-<hash>/ dir must hold a compatible
TactusDefs.olean (module-ROOT resolution needs it). Auto-selection:
probe each prelude dir in the cache with an `import TactusDefs_lib_exec`
test and use the ones that pass (try most-recent first). Override with
--prelude-dir.

Caching: results keyed by pkg file content-hash + prelude dir +
LeanNonlinearArith olean fingerprint in a cache dir (default
<tactus-lean-lib-dir>/../nla16-posthoc-cache/). A failed elaboration is
cached too (class from the error text) — the layer column for a fn that
honestly fails post-hoc is its expected outcome anyway.
"""

from __future__ import annotations

import argparse
import csv
import hashlib
import os
import re
import subprocess
import sys
from pathlib import Path

STATS_RE = re.compile(r"^(.+?):(\d+):(\d+): warning: \[nla16-stats\] (.*)$")
RUST_SPAN_RE = re.compile(r"@rust:([^:\s]+(?:\.rs)):(\d+):(\d+)")
THEOREM_RE = re.compile(r"^theorem\s+(\S+)")


def find_prelude_dirs(lib_dir: Path, crates_test_file: Path) -> list[Path]:
    """Probe ~/.cache/tactus/prelude-* dirs with a TactusDefs import probe."""
    cache_root = Path.home() / ".cache" / "tactus"
    probe = Path(os.environ.get("TMPDIR", "/tmp")) / "nla16_posthoc_probe.lean"
    # module name of the crate defs = TactusDefs_<stem>
    stems = [p.name.replace("TactusDefs_", "").replace(".olean", "")
             for p in lib_dir.glob("TactusDefs_*.olean")
             if "__" not in p.name]
    if not stems:
        return []
    probe.write_text(f"import TactusDefs_{stems[0]}\n#check 1\n")
    base_lp = subprocess.run(
        ["lake", "env", "printenv", "LEAN_PATH"],
        cwd=str(Path.home() / "prog/verus-cad/tactus/lean-project"),
        capture_output=True, text=True, check=True).stdout.strip()
    candidates = sorted(
        cache_root.glob("prelude-*"),
        key=lambda p: p.stat().st_mtime, reverse=True)
    good = []
    for cand in candidates:
        env = dict(os.environ)
        env["LEAN_PATH"] = f"{cand}:{lib_dir}:{base_lp}"
        r = subprocess.run(["lean", str(probe)], capture_output=True,
                           text=True, env=env)
        if r.returncode == 0 and "error" not in r.stdout + r.stderr:
            good.append(cand)
    return good


def map_rust_spans(pkg_text: str, stats_line: int):
    """Nearest preceding `@rust:path:line:col` comment above the stats line."""
    best = None
    for m in RUST_SPAN_RE.finditer(pkg_text):
        line = pkg_text.count("\n", 0, m.start()) + 1
        if line <= stats_line and (best is None or line > best[0]):
            best = (line, m.group(1), int(m.group(2)), int(m.group(3)))
    return best


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("crate_src")
    ap.add_argument("lib_dir")  # target/tactus-lean/<stem> containing pkg/
    ap.add_argument("--prelude-dir")
    ap.add_argument("--out-csv", required=True)
    ap.add_argument("--module", action="append",
                    help="restrict to these pkg module leaves (no .lean)")
    ap.add_argument("--no-cache", action="store_true")
    args = ap.parse_args()

    crate_src = Path(args.crate_src).resolve()
    lib_dir = Path(args.lib_dir).resolve()
    pkg_dir = lib_dir / "pkg"
    if not pkg_dir.is_dir():
        print(f"no pkg dir at {pkg_dir}", file=sys.stderr)
        return 2

    # sites via scanner
    sites_out = subprocess.run(
        ["python3", str(Path(__file__).parent / "sites.py"), str(crate_src)],
        capture_output=True, text=True, check=True).stdout
    site_rows = list(csv.reader(sites_out.splitlines()))[1:]
    site_fns = {r[3] for r in site_rows}

    # pkg modules matching site fns (leaf ends with __<fn>; ambiguity ok)
    modules = []
    for f in sorted(pkg_dir.glob("*.lean")):
        leaf = f.stem
        if args.module and leaf not in args.module:
            continue
        fn = leaf.split("__")[-1]
        if fn in site_fns:
            modules.append((leaf, fn, f))

    if args.prelude_dir:
        preludes = [Path(args.prelude_dir)]
    else:
        preludes = find_prelude_dirs(lib_dir, crate_src)
        if not preludes:
            print("no compatible prelude dir found", file=sys.stderr)
            return 2
    prelude = preludes[0]

    base_lp = subprocess.run(
        ["lake", "env", "printenv", "LEAN_PATH"],
        cwd=str(Path.home() / "prog/verus-cad/tactus/lean-project"),
        capture_output=True, text=True, check=True).stdout.strip()

    cache_dir = lib_dir.parent / "nla16-posthoc-cache"
    cache_dir.mkdir(exist_ok=True)
    rows_out = []
    for leaf, fn, pkg in modules:
        text = pkg.read_text()
        fingerprint = hashlib.sha256(
            text.encode() + str(prelude).encode()).hexdigest()[:16]
        cache_file = cache_dir / f"{leaf}.{fingerprint}.txt"
        if cache_file.exists() and not args.no_cache:
            out = cache_file.read_text()
        else:
            env = dict(os.environ)
            env["LEAN_PATH"] = f"{prelude}:{lib_dir}:{base_lp}"
            env["NLA16_STATS"] = "1"
            print(f"[posthoc] elaborating {leaf} ...", flush=True)
            r = subprocess.run(["lean", str(pkg)], capture_output=True,
                               text=True, env=env, timeout=3600)
            out = r.stdout + r.stderr
            cache_file.write_text(out)
        fsite_rows = [r for r in site_rows if r[3] == fn]
        n_stats = 0
        for line in out.splitlines():
            m = STATS_RE.match(line)
            if not m:
                continue
            n_stats += 1
            pline = int(m.group(2))
            payload = m.group(4).strip()
            span = map_rust_spans(text, pline)
            rust_span = f"{span[1]}:{span[2]}" if span else ""
            f0 = fsite_rows[0][0] if fsite_rows else ""
            # site-line attribution: exact rust-span match if available,
            # else fn-granularity (multiple closes per fn)
            site_line = ""
            for r in fsite_rows:
                if span and r[0] == span[1] and int(r[1]) == span[2]:
                    site_line = r[1]
                    break
            rows_out.append([f0, site_line, fn, payload, rust_span])
        print(f"[posthoc] {leaf}: {n_stats} stats lines", flush=True)

    with open(args.out_csv, "w", newline="") as f:
        w = csv.writer(f)
        w.writerow(["crate_file", "site_line", "fn", "payload", "rust_span"])
        w.writerows(rows_out)
    print(f"[posthoc] wrote {len(rows_out)} rows to {args.out_csv}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
