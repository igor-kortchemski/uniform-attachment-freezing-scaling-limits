# Publication readiness

Status on 30 October 2026: **pushed to a private GitHub repository; CI and
the sandboxed Comparator pass. Not yet public, Palomar-preflighted or
submitted.**

## Decisions recorded (from the user, 30 October 2026)

- Licence Apache-2.0; contributor and responsible maintainer Igor Kortchemski.
- `Challenge.lean` may use `sorry` as deliberate placeholders for the theorem
  proofs only; the library and `Solution.lean` keep the no-`sorry` policy.
- The CRT corollary M05 is excluded from the advertised scope and documented.
- GitHub destination: `igor-kortchemski/uniform-attachment-freezing-scaling-limits`,
  pushed privately first and made public after CI passes.
- The source manuscript stays in the repository (the user's decision as an
  author; its rights are reserved in NOTICE).

## Candidate contents

- Advertised results: M01, M02, M03 with M04, corrected M06, and N09, stated in
  [Challenge.lean](../Challenge.lean) (Mathlib-only, 429 lines) and proved via
  [Solution.lean](../Solution.lean); the encoding is explained in
  [statement-interface.md](statement-interface.md). The full scope, corrections
  and open items are in the [formalization report](../FORMALIZATION_REPORT.md).
- [comparator.json](../comparator.json), [formalization.yaml](../formalization.yaml)
  (schema v0.4), [LICENSE](../LICENSE), [NOTICE](../NOTICE),
  [CITATION.cff](../CITATION.cff), and the workflows
  [ci.yml](../.github/workflows/ci.yml) (build, axioms, Challenge check,
  sandboxed Comparator) and [palomar.yml](../.github/workflows/palomar.yml)
  (manual full preflight).
- Pinned Lean/Mathlib v4.35.0 and the committed manifest; one Lakefile; every
  Lean file is a `module` with at most 10,000 lines.

## Evidence (local)

- `lake build`: 4,177 jobs; the only warnings are the five `sorry` holes of
  `Challenge.lean`.
- `scripts/check_axioms.py`: PASS for 3,724 definitions and theorems in all 289
  modules ([log](../evidence/publication-candidate-axioms.log)).
- `scripts/check_challenge.py`: OK
  ([log](../evidence/publication-candidate-challenge-check.log)).
- Comparator: a **preliminary, unsandboxed** local run accepted the solution
  ([output](../evidence/comparator-local-unsandboxed.txt)). It is not a
  trustworthy Comparator certificate.
- Hashes: [publication-candidate-context.txt](../evidence/publication-candidate-context.txt).

## Evidence (GitHub CI)

- [Run 41033233038](https://github.com/igor-kortchemski/uniform-attachment-freezing-scaling-limits/actions/runs/41033233038)
  on commit `41aa125`: the `build` job (build, axiom check, Challenge check) and
  the `comparator` job both passed. The **sandboxed** Comparator, with
  bubblewrap 0.12.0 built by Palomar's pinned `install_bwrap.sh`, accepted the
  solution ([record](../evidence/comparator-ci-sandboxed.txt)).
- The first run failed before comparing anything: the distribution's `bwrap`
  cannot create user namespaces on Ubuntu 24.04 runners. `ci.yml` now uses
  Palomar's installer, which loads an AppArmor profile for its own binary.
- This is a standalone Comparator check, not the Palomar full preflight.

## Policy checked (30 October 2026)

- [toolchains.json](https://raw.githubusercontent.com/PalomarRegistry/PalomarSubmission/main/toolchains.json):
  minimum v4.35.0-rc2 (project: v4.35.0).
- [allowed-challenge-repositories.json](https://raw.githubusercontent.com/PalomarRegistry/PalomarSubmission/main/allowed-challenge-repositories.json):
  Mathlib with semver release tags (project: v4.35.0).
- Metadata schema v0.4 (permissive; checked fields and enums).
- These reads are not a policy-revision-pinned compliance certificate.

## Remaining steps (each needs the user's go-ahead)

1. Done: pushed to the private repository; CI and the sandboxed Comparator
   pass.
2. Make the repository public.
3. Refresh the Palomar pipeline commit pinned in `palomar.yml`, dispatch the
   full preflight on the exact public commit, and inspect its report.
4. Decide on submission; registration is a separate decision after review.
