#!/usr/bin/env python3
"""nla-16 parity harness — nonlinear-site scanner.

Scans a crate's src/ for `nonlinear_arith` sites and maps each to its
enclosing `fn` item. Line numbers are 1-based, matching verus error spans.

Rough Rust lexer: handles line/block comments (nested), strings (with
escapes + multiline), raw strings, char literals vs lifetimes. Deliberately
approximate — a verus workspace idiom; files it cannot handle get flagged
(UNBALANCED) rather than silently misattributed.

Usage: sites.py <crate-src-dir>
CSV output per site: file,line,col,fn_name,fn_start_line,fn_end_line
"""

from __future__ import annotations

import csv
import re
import sys
from pathlib import Path

SITE_RE = re.compile(r"nonlinear_arith\s*\)")
IDENT_RE = re.compile(r"[A-Za-z_][A-Za-z0-9_]*")


def structural_tokens(text: str):
    """Yield ('{'|'}'|'fn', char_offset). Skips comments/strings/chars."""
    n = len(text)
    i = 0
    while i < n:
        c = text[i]
        if c == "/" and text[i + 1 : i + 2] == "/":
            j = text.find("\n", i)
            i = n if j == -1 else j + 1
            continue
        if c == "/" and text[i + 1 : i + 2] == "*":
            depth = 1
            j = i + 2
            while j < n and depth > 0:
                two = text[j : j + 2]
                if two == "/*":
                    depth += 1
                    j += 2
                elif two == "*/":
                    depth -= 1
                    j += 2
                else:
                    j += 1
            i = j
            continue
        if c == '"':
            j = i + 1
            while j < n:
                if text[j] == "\\":
                    j += 2
                elif text[j] == '"':
                    j += 1
                    break
                else:
                    j += 1
            i = j
            continue
        if c == "r" and (text[i + 1 : i + 2] in ('"', "#")):
            k = i + 1
            hashes = 0
            while k < n and text[k] == "#":
                hashes += 1
                k += 1
            if k < n and text[k] == '"' and (i == 0 or not re.match(r"[A-Za-z0-9_]", text[i - 1])):
                end = '"' + "#" * hashes
                j = text.find(end, k + 1)
                i = n if j == -1 else j + len(end)
                continue
            i += 1
            continue
        if c == "'":
            # char literal: 'a' | '\x' | '\u{..}'  — otherwise a lifetime tick
            m = re.match(r"'(\\.|[^\\'])'", text[i:])
            if not m:
                m = re.match(r"'\\u\{[0-9a-fA-F]+\}'", text[i:])
            if m:
                i += m.end()
            else:
                i += 1
            continue
        if c == "{":
            yield ("{", i)
            i += 1
            continue
        if c == "}":
            yield ("}", i)
            i += 1
            continue
        if c.isalpha() or c == "_":
            m = IDENT_RE.match(text, i)
            if m:
                if m.group(0) == "fn":
                    yield ("fn", i)
                i = m.end()
            else:
                i += 1
            continue
        i += 1


def blank_noise(text: str) -> str:
    """Return text with comments/strings/chars replaced by spaces.

    Offsets are preserved (newlines kept), so positions computed on the
    blanked text are valid in the original. Site/keyword matching MUST run
    on this, not the raw text — crate comments mention `by(nonlinear_arith)`
    frequently (verus-qext instances.rs was the pilot catch).
    """
    out = list(text)
    n = len(text)
    i = 0

    def blank(a: int, b: int):
        for k in range(a, b):
            if out[k] != "\n":
                out[k] = " "

    while i < n:
        c = text[i]
        if c == "/" and text[i + 1 : i + 2] == "/":
            j = text.find("\n", i)
            end = n if j == -1 else j
            blank(i, end)
            i = end
            continue
        if c == "/" and text[i + 1 : i + 2] == "*":
            depth = 1
            j = i + 2
            while j < n and depth > 0:
                two = text[j : j + 2]
                if two == "/*":
                    depth += 1
                    j += 2
                elif two == "*/":
                    depth -= 1
                    j += 2
                else:
                    j += 1
            blank(i, j)
            i = j
            continue
        if c == '"':
            j = i + 1
            while j < n:
                if text[j] == "\\":
                    j += 2
                elif text[j] == '"':
                    j += 1
                    break
                else:
                    j += 1
            blank(i, j)
            i = j
            continue
        if c == "r" and (text[i + 1 : i + 2] in ('"', "#")):
            k = i + 1
            hashes = 0
            while k < n and text[k] == "#":
                hashes += 1
                k += 1
            if k < n and text[k] == '"' and (i == 0 or not re.match(r"[A-Za-z0-9_]", text[i - 1])):
                end = '"' + "#" * hashes
                j = text.find(end, k + 1)
                jend = n if j == -1 else j + len(end)
                blank(i, jend)
                i = jend
                continue
            i += 1
            continue
        if c == "'":
            m = re.match(r"'(\\.|[^\\'])'", text[i:])
            if not m:
                m = re.match(r"'\\u\{[0-9a-fA-F]+\}'", text[i:])
            if m:
                blank(i, i + m.end())
                i += m.end()
            else:
                i += 1
            continue
        i += 1
    return "".join(out)


class LineMap:
    def __init__(self, text: str):
        self.starts = [0]
        for m in re.finditer(r"\n", text):
            self.starts.append(m.end())

    def line_col(self, idx: int) -> tuple[int, int]:
        import bisect
        k = bisect.bisect_right(self.starts, idx) - 1
        return k + 1, idx - self.starts[k] + 1


def scan_file(path: Path, crate_src: Path):
    """Returns (sites, warnings). Each site: (line, col, fn_name, fn_start, fn_end)."""
    text = path.read_text()
    text = blank_noise(text)
    lm = LineMap(text)
    warnings: list[str] = []
    sites = []
    depth = 0
    fn_spans = []  # [start_line, end_line or None, name]
    stack = []  # (fn_spans index, opening depth)
    pending_fn = None  # (start_line, name)

    for kind, idx in structural_tokens(text):
        if kind == "fn":
            line, _ = lm.line_col(idx)
            m = re.match(r"\s*([A-Za-z_][A-Za-z0-9_]*)", text[idx + 2 :])
            name = m.group(1) if m else "<unknown>"
            pending_fn = (line, name)
        elif kind == "{":
            depth += 1
            if pending_fn is not None:
                fn_spans.append([pending_fn[0], None, pending_fn[1]])
                stack.append((len(fn_spans) - 1, depth))
                pending_fn = None
        elif kind == "}":
            depth -= 1
            # close fns whose bodies opened at (depth + 1)
            while stack and stack[-1][1] == depth + 1:
                fn_idx, _ = stack.pop()
                end_line, _ = lm.line_col(idx)
                fn_spans[fn_idx][1] = end_line
            pending_fn = None

    if stack:
        warnings.append(f"{path}: UNBALANCED fn stack ({len(stack)} open)")

    for m in SITE_RE.finditer(text):
        line, col = lm.line_col(m.start())
        best = None
        for s, e, name in fn_spans:
            if s <= line and (e is None or line <= e):
                if best is None or s >= best[0]:
                    best = (s, e, name)
        if best is None:
            name, s, e = "<module>", 0, 0
        else:
            s, e, name = best
        sites.append((line, col, name, s, e if e else -1))
    return sites, warnings


def main() -> int:
    if len(sys.argv) != 2:
        print(__doc__)
        return 2
    crate_src = Path(sys.argv[1]).resolve()
    all_sites = []
    warnings = []
    for path in sorted(crate_src.rglob("*.rs")):
        text = path.read_text()
        if "nonlinear_arith" not in text:
            continue
        sites, warns = scan_file(path, crate_src)
        rel = str(path.relative_to(crate_src))
        for line, col, name, s, e in sites:
            all_sites.append([rel, line, col, name, s, e])
        warnings.extend(warns)
    try:
        w = csv.writer(sys.stdout)
        w.writerow(["file", "line", "col", "fn", "fn_start", "fn_end"])
        for row in all_sites:
            w.writerow(row)
    except BrokenPipeError:
        sys.stdout.close()
        return 0
    for warn in warnings:
        print(f"# WARNING: {warn}", file=sys.stderr)
    return 0


if __name__ == "__main__":
    sys.exit(main())
