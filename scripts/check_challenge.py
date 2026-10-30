#!/usr/bin/env python3
"""Check that Challenge.lean is a faithful, Mathlib-only copy of the interface.

The definitions used by the Comparator statement interface live in the library
module `Freezing2/Interface/Defs.lean`, between the marker comments
`-- BEGIN SHARED DEFINITIONS` and `-- END SHARED DEFINITIONS`. This script checks:

* `Challenge.lean` contains that block verbatim, preceded by exactly the same
  `public import` lines, all of which are Mathlib modules;
* the shared block contains no proof hole, axiom or native evaluation, and the
  part of `Challenge.lean` after the block declares only theorems
  (the deliberate Challenge holes are `sorry` proofs there);
* no other Lean file imports `Challenge`, and `Solution.lean` imports the library;
* Palomar size limits: Challenge at most 1,000 lines and 100 KiB; every Lean file
  is a `module` with at most 10,000 lines.

Standard-library Python 3 only. Run from any directory. Exit status 0 on success.
"""
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parent.parent
DEFS = ROOT / "Freezing2" / "Interface" / "Defs.lean"
CHALLENGE = ROOT / "Challenge.lean"
SOLUTION = ROOT / "Solution.lean"
BEGIN = "-- BEGIN SHARED DEFINITIONS"
END = "-- END SHARED DEFINITIONS"
FORBIDDEN = re.compile(r"\b(sorry|admit|axiom|native_decide|bv_decide|implemented_by|extern)\b")

errors = []


def fail(message):
    errors.append(message)


def imports(text):
    return [line.strip() for line in text.splitlines()
            if re.match(r"^\s*(public\s+)?import\s", line)]


def shared_block(text, name):
    start, end = text.find(BEGIN), text.find(END)
    if start < 0 or end < 0 or end < start:
        fail(f"{name}: missing or misordered shared-definition markers")
        return None, None
    end += len(END)
    return text[start:end], end


def strip_comments(text):
    """Remove Lean comments and docstrings (nesting-aware) before keyword scans."""
    out, i, depth = [], 0, 0
    while i < len(text):
        pair = text[i:i + 2]
        if depth:
            if pair == "/-":
                depth, i = depth + 1, i + 2
            elif pair == "-/":
                depth, i = depth - 1, i + 2
            else:
                out.append("\n" if text[i] == "\n" else " ")
                i += 1
        elif pair == "/-":
            depth, i = 1, i + 2
        elif pair == "--":
            j = text.find("\n", i)
            i = len(text) if j < 0 else j
        else:
            out.append(text[i])
            i += 1
    return "".join(out)


defs_text = DEFS.read_text(encoding="utf-8")
chal_text = CHALLENGE.read_text(encoding="utf-8")

# 1. Identical Mathlib-only imports.
defs_imports, chal_imports = imports(defs_text), imports(chal_text)
if defs_imports != chal_imports:
    fail("Challenge.lean and Defs.lean have different import lists")
for line in chal_imports:
    if not re.fullmatch(r"public import Mathlib(\.[A-Za-z0-9_]+)+", line):
        fail(f"Challenge.lean has a non-Mathlib or non-public import: {line}")
if not chal_text.startswith("module\n"):
    fail("Challenge.lean must start with `module`")

# 2. Verbatim shared block.
defs_block, _ = shared_block(defs_text, "Defs.lean")
chal_block, chal_end = shared_block(chal_text, "Challenge.lean")
if defs_block is not None and chal_block is not None:
    if defs_block != chal_block:
        fail("the shared-definition block of Challenge.lean differs from Defs.lean")
    if FORBIDDEN.search(strip_comments(defs_block)):
        fail("the shared-definition block contains a forbidden keyword")
    # Defs.lean must not contain anything but the shared block after its header.
    if defs_text.rstrip().endswith(END) is False:
        fail("Defs.lean has content after the shared-definition block")
    # 3. After the block, Challenge.lean may only declare theorems.
    tail = strip_comments(chal_text[chal_end:])
    for match in re.finditer(r"^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+)*"
                             r"(def|abbrev|instance|structure|class|inductive|axiom|opaque|"
                             r"example|lemma|theorem)\b", tail, re.MULTILINE):
        if match.group(1) != "theorem":
            fail(f"Challenge.lean declares a `{match.group(1)}` after the shared block")
    theorems = re.findall(r"^theorem\s+([A-Za-z0-9_'.]+)", tail, re.MULTILINE)
    print("Challenge theorems:", ", ".join(theorems))

# 4. Import discipline.
for path in sorted(ROOT.rglob("*.lean")):
    rel = path.relative_to(ROOT)
    if rel.parts[0] == ".lake":
        continue
    text = path.read_text(encoding="utf-8")
    if path != CHALLENGE and any(re.fullmatch(r"(public\s+)?import\s+Challenge", line)
                                 for line in imports(text)):
        fail(f"{rel} imports Challenge")
    if path.name != "lakefile.lean" and not strip_comments(text).lstrip().startswith("module"):
        fail(f"{rel} is not a module")
    n_lines = text.count("\n") + (0 if text.endswith("\n") else 1)
    if n_lines > 10_000:
        fail(f"{rel} has {n_lines} lines (limit 10,000)")
if not any(re.fullmatch(r"public import Freezing2(\.[A-Za-z0-9_.]+)?", line)
           for line in imports(SOLUTION.read_text(encoding="utf-8"))):
    fail("Solution.lean does not import the library")

# 5. Challenge size limits.
n_lines = chal_text.count("\n") + (0 if chal_text.endswith("\n") else 1)
n_bytes = len(chal_text.encode("utf-8"))
print(f"Challenge.lean: {n_lines} lines, {n_bytes} bytes ({n_bytes / 1024:.1f} KiB)")
if n_lines > 1000:
    fail("Challenge.lean exceeds 1,000 lines")
if n_bytes > 100 * 1024:
    fail("Challenge.lean exceeds 100 KiB")

if errors:
    for message in errors:
        print("ERROR:", message)
    sys.exit(1)
print("OK: Challenge.lean contains a verbatim copy of the shared definitions "
      "of Freezing2/Interface/Defs.lean and satisfies the checked constraints.")
