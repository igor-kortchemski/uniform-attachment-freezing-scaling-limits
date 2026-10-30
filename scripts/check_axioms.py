#!/usr/bin/env python3
"""Build the library and inspect current public declarations' transitive axioms.

This is a local Lean/axiom check, not Comparator or an independent kernel replay.
Run from any directory. Standard-library Python 3 and the pinned Lake are required.
"""
from pathlib import Path
import argparse
import hashlib
import re
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parent.parent
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}

def without_comments(source):
    """Preserve line layout while ignoring nested Lean comments and docstrings."""
    result = []
    i, depth, in_string = 0, 0, False
    while i < len(source):
        pair = source[i:i + 2]
        if depth:
            if pair == "/-":
                depth += 1
                result.extend("  ")
                i += 2
            elif pair == "-/":
                depth -= 1
                result.extend("  ")
                i += 2
            else:
                result.append("\n" if source[i] == "\n" else " ")
                i += 1
        elif in_string:
            result.append(source[i])
            if source[i] == "\\" and i + 1 < len(source):
                result.append(source[i + 1])
                i += 2
            else:
                if source[i] == '"':
                    in_string = False
                i += 1
        elif pair == "/-":
            depth = 1
            result.extend("  ")
            i += 2
        elif pair == "--":
            end = source.find("\n", i)
            if end == -1:
                end = len(source)
            result.extend(" " * (end - i))
            i = end
        else:
            in_string = source[i] == '"'
            result.append(source[i])
            i += 1
    if depth or in_string:
        raise SystemExit("Unclosed comment/string in Lean source; audit the scanner.")
    return "".join(result)

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("--integrated", action="store_true",
                    help="development checkpoint: check only the entry point's local import closure")
args = parser.parse_args()
all_paths = set((ROOT / "Freezing2").rglob("*.lean"))
paths = all_paths
if args.integrated:
    paths = set()
    pending = [ROOT / "Freezing2.lean"]
    visited = set()
    while pending:
        path = pending.pop()
        if path in visited:
            continue
        visited.add(path)
        if path != ROOT / "Freezing2.lean":
            paths.add(path)
        for module in re.findall(r"^(?:public )?import (Freezing2(?:\.[\w]+)*)\s*$",
                                 without_comments(path.read_text()), re.MULTILINE):
            pending.append(ROOT / (module.replace(".", "/") + ".lean"))
    print("DEVELOPMENT SCOPE: integrated import closure only.", flush=True)
    for path in sorted(all_paths - paths):
        print(f"Excluded unintegrated source: {path.relative_to(ROOT)}", flush=True)

checked_paths = paths | {ROOT / name for name in
    ("Freezing2.lean", "lean-toolchain", "lakefile.toml", "lake-manifest.json")}
snapshot = {path: hashlib.sha256(path.read_bytes()).hexdigest() for path in checked_paths}
subprocess.run(["lake", "build"], cwd=ROOT, check=True)

names = []
for path in sorted(paths):
    source = without_comments(path.read_text())
    # Track named sections separately from namespaces. The vendored forest
    # definitions use a nested namespace; flattening to one prefix misses them.
    scopes = []
    for line in source.splitlines():
        scope = re.fullmatch(r"(namespace|section)\s+(\S+)\s*", line)
        if scope:
            scopes.append((scope[1], scope[2]))
            continue
        end = re.fullmatch(r"end(?:\s+(\S+))?\s*", line)
        if end:
            if not scopes or (end[1] is not None and scopes[-1][1] != end[1]):
                raise SystemExit(f"Unrecognized scope ending in {path.relative_to(ROOT)}: {line}")
            scopes.pop()
            continue
        declaration = re.match(
            r"^(?:@\[[^\n]*\]\s*)?(?:noncomputable\s+)?(?:def|abbrev|lemma|theorem)\s+([^\s({:]+)",
            line,
        )
        if declaration:
            prefix = ".".join(name for kind, name in scopes if kind == "namespace")
            if not prefix:
                raise SystemExit(f"Unqualified declaration in {path.relative_to(ROOT)}; audit the scanner.")
            names.append(f"{prefix}.{declaration[1]}")
    if scopes:
        raise SystemExit(f"Unclosed scopes in {path.relative_to(ROOT)}; audit the scanner.")

if not names or len(names) != len(set(names)):
    raise SystemExit("Empty or duplicate declaration list: check the source scan.")

probe = "module\nimport Freezing2\n\n" + "\n".join(f"#print axioms {n}" for n in names) + "\n"
with tempfile.TemporaryDirectory(prefix="freezing2-axioms-") as tmp:
    path = Path(tmp) / "Audit.lean"
    path.write_text(probe)
    result = subprocess.run(
        ["lake", "env", "lean", str(path)], cwd=ROOT, text=True,
        stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
    )
print(result.stdout, end="")
if result.returncode:
    raise SystemExit(result.returncode)

seen = set()
# Lean wraps long axiom lists across lines. Match complete records, not lines,
# while still requiring the exact declaration inventory below.
for match in re.finditer(
    r"^'([^']+)' depends on axioms: \[([^\]]*)\]$", result.stdout, re.MULTILINE
):
    name, axioms = match.groups()
    found = {a.strip() for a in axioms.split(",") if a.strip()}
    if found - ALLOWED:
        raise SystemExit(f"Forbidden axioms for {name}: {sorted(found - ALLOWED)}")
    seen.add(name)
seen.update(re.findall(
    r"^'([^']+)' does not depend on any axioms$", result.stdout, re.MULTILINE
))
if seen != set(names):
    raise SystemExit(f"Incomplete axiom output: missing {sorted(set(names) - seen)}")
changed = [str(path.relative_to(ROOT)) for path, digest in snapshot.items()
           if hashlib.sha256(path.read_bytes()).hexdigest() != digest]
if changed:
    raise SystemExit(f"Sources changed during verification; repeat the checkpoint: {changed}")
print(f"PASS: {len(names)} definitions/theorems in {len(paths)} modules; "
      f"only {', '.join(sorted(ALLOWED))} permitted.")
print("This does not establish source coverage, Comparator acceptance, or Palomar verification.")
