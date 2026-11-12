# Uniform attachment with freezing: Scaling limits

[![CI](https://github.com/igor-kortchemski/uniform-attachment-freezing-scaling-limits/actions/workflows/ci.yml/badge.svg?branch=main)](https://github.com/igor-kortchemski/uniform-attachment-freezing-scaling-limits/actions/workflows/ci.yml?query=branch%3Amain)
[![Comparator](https://github.com/igor-kortchemski/uniform-attachment-freezing-scaling-limits/actions/workflows/comparator.yml/badge.svg?branch=main)](https://github.com/igor-kortchemski/uniform-attachment-freezing-scaling-limits/actions/workflows/comparator.yml?query=branch%3Amain)

A Lean 4 and Mathlib formalization of *Uniform attachment with freezing: Scaling
limits* ([arXiv:2308.00484](https://arxiv.org/abs/2308.00484)) by Étienne Bellin,
Arthur Blanc-Renaudie, Emmanuel Kammerer and Igor Kortchemski, Ann. Inst. H.
Poincaré Probab. Statist. **61**(4) 2679–2708 (2025),
[doi:10.1214/24-AIHP1497](https://doi.org/10.1214/24-AIHP1497).
**The five main statements below are proved for the actual random trees, using
only the axioms `propext`, `Classical.choice` and `Quot.sound`, with no `sorry`
outside the deliberate placeholders of `Challenge.lean`; the CRT corollary is not
formalized.**

Registered as **[PALOMAR-2026-10-30-000012, version 1](https://palomar-registry.org/entry.html?id=PALOMAR-2026-10-30-000012&version=1)**
for the five main statements; the registered snapshot is commit
[`8bace72`](https://github.com/igor-kortchemski/uniform-attachment-freezing-scaling-limits/commit/8bace72d36cdf7d250414f3d98acfaa415de23d9).

Statements: [Challenge.lean](Challenge.lean) · Correspondence record:
[FORMALIZATION_REPORT.md](FORMALIZATION_REPORT.md) · Verification: [Verify](#verify)

## Main results

A sign sequence $X^n\in\{-1,1\}^n$ drives a random tree $\mathcal T_n$: at step
$i$, a uniform active vertex receives a new active child if $X^n_i=1$ and is
frozen otherwise. The number $S^n_k=1+\sum_{i\le k}X^n_i$ of active vertices is
assumed positive up to time $n$, and $n^\alpha/S^n_{\lfloor nt\rfloor}$ converges
to $1/f(t)$ in the sense of the paper's hypotheses $(\mathsf{Lim}^\alpha_{1/f})$
and, where needed, $(\mathsf{Lim}^\alpha_{1/f^2})$. The theorems are in the
namespace `FreezingStatements` and are listed in [comparator.json](comparator.json).

| Paper result | Lean statement | Statement |
| --- | --- | --- |
| `thm:heightalpha` (M01) | [`height_scaling_limit`](Challenge.lean#L342) | For $0<\alpha<1$, $\mathrm{Height}(\mathcal T_n)/n^{1-\alpha}\to\int_0^1\frac{dt}{2f(t)}$ in $L^p$ for every $p\ge1$. |
| `thm:sous-critique` (M02) | [`subcritical_scaling_limit`](Challenge.lean#L358) | For $0<\alpha<1/2$, $\mathcal T_n/n^{1-\alpha}$ with its uniform measure converges in GHP distribution to the segment $[0,\int_0^1\frac{dt}{2f(t)}]$ carrying the image of the uniform measure on $[0,1]$ under $u\mapsto\int_0^u\frac{dt}{2f(t)}$. |
| `thm:critique` + `thm:properties` (M03, M04) | [`critical_scaling_limit`](Challenge.lean#L382) | For $\alpha=1/2$ and $\max_k S_k^n=O(\sqrt n)$, $\mathcal T_n/\sqrt n$ converges in GHP distribution to a random tree $\mathcal T(f)$ depending only on $f$; almost surely $\mathcal T(f)$ is a compact real tree whose measure has full support and charges only leaves, it is binary if and only if $\int_0^{1/2}f^{-2}=\infty$, and otherwise it has a point of infinite degree, all other branch points having degree three. |
| `thm:sur-critique` (M06), corrected | [`supercritical_distance_matrix_limit`](Challenge.lean#L409) | For $1/2<\alpha<1$ and every $k$, the distance matrix of the root $V_0$ and $k$ uniform vertices $V_1,\dots,V_k$, divided by $n^{1-\alpha}$, converges in law to $\big(\mathbf 1_{i\ne j}\,(\int_0^{U_i}\frac{dt}{2f}+\int_0^{U_j}\frac{dt}{2f})\big)_{0\le i,j\le k}$, where $U_0=0$ and $U_1,\dots,U_k$ are independent uniform on $[0,1]$. |
| `thm:alpha0` (N09) | [`bounded_population_GH_limit`](Challenge.lean#L421) | If $S^n_k\le M$ for all $k\le n$, then $\mathcal T_n/h_n^+\to[0,1]$ in probability for the Gromov–Hausdorff distance, where $h_n^+=\sum_{i\le n}\mathbf 1_{\{X^n_i=1\}}/S^n_i$. |

The printed `thm:sur-critique` lacks the indicator $\mathbf 1_{i\ne j}$ and is
false on the diagonal; the height theorem holds without
$(\mathsf{Lim}^\alpha_{1/f^2})$. All numbered results N01–N17 and most unnumbered
claims are also proved, several in corrected or qualified forms (23 source issues
S01–S23 in the [inventory](docs/source-inventory.md#source-issues-requiring-explicit-treatment);
[manuscript recommendations](MANUSCRIPT_RECOMMENDATIONS.md)). The GHP topology is
put on compact measured spaces rather than on their isometry classes, so
$\mathcal T(f)$ is unique only up to isometry ([statement interface](docs/statement-interface.md)).

**Not formalized:** the CRT corollary (`cor:CRT`, M05), which needs Brownian
excursion and CRT theory, invariance principles, Skorokhod representation and
random-walk local limit theorems absent from Mathlib (two printed estimates of its
proof are [refuted in Lean](Freezing2/Audit/ExcursionCounterexamples.lean)); the
dimension lower bounds (no proof in the source); long-dendron convergence; and
Aldous's time change. No whole-paper completion is claimed. The
[report](FORMALIZATION_REPORT.md) maps every result to the paper and records
proof-route differences; a [whole-source omission scan](docs/omission-scan-2026-10-30.md)
records coverage.

## Where to start

- [Challenge.lean](Challenge.lean): the five statements and their definitions,
  readable without installing Lean.
- [Interface/Statements.lean](Freezing2/Interface/Statements.lean) derives them
  from [Height](Freezing2/MainResults/Height.lean), [SubcriticalDistribution](Freezing2/MainResults/SubcriticalDistribution.lean),
  [CriticalRealTree](Freezing2/Probability/CriticalRealTree.lean), [CriticalBranching](Freezing2/Probability/CriticalBranching.lean),
  [Supercritical](Freezing2/MainResults/Supercritical.lean) and [BoundedPopulation](Freezing2/MainResults/BoundedPopulation.lean).
- [Freezing2.lean](Freezing2.lean) imports all 289 library modules, directly or
  transitively; the [module map](docs/MODULES.md) describes the main ones.

## Verify

Install Elan following the [Lean project setup guide](https://leanprover-community.github.io/install/project.html),
then open this folder in VS Code with the Lean extension. Lean and Mathlib are
pinned to **v4.35.0**; keep the committed `lake-manifest.json` and do not run
`lake update`.

```sh
git clone https://github.com/igor-kortchemski/uniform-attachment-freezing-scaling-limits.git
cd uniform-attachment-freezing-scaling-limits
lake exe cache get
lake build
python3 scripts/check_axioms.py
python3 scripts/check_challenge.py
lake comparator --config comparator.json   # Linux, requires bubblewrap
```

`lake build` warns only about the five `sorry` placeholders of `Challenge.lean`,
which neither the library nor `Solution` imports. `check_axioms.py` accepts only
the three axioms above as transitive axioms of every module under `Freezing2/`;
`check_challenge.py` checks that `Challenge.lean` copies
[Defs.lean](Freezing2/Interface/Defs.lean) verbatim and meets Palomar's size
limits; Comparator checks that `Solution` proves exactly the `Challenge`
statements with only those axioms.

On 30 October 2026, on commit `8bace72`, the
[CI workflow](https://github.com/igor-kortchemski/uniform-attachment-freezing-scaling-limits/actions/runs/41041088018)
(build, axiom and Challenge checks) and the sandboxed
[Comparator workflow](https://github.com/igor-kortchemski/uniform-attachment-freezing-scaling-limits/actions/runs/41041088024)
passed, and a manually dispatched
[Palomar full mechanical preflight](https://github.com/igor-kortchemski/uniform-attachment-freezing-scaling-limits/actions/runs/41041877221)
succeeded; that workflow does not submit or register a result. The local check of
the same Lean sources ([hashes](evidence/publication-candidate-context.txt)) built
4,177 jobs and passed the axiom check for 3,724 definitions and theorems in 289
modules ([log](evidence/publication-candidate-axioms.log)) and the Challenge check
([log](evidence/publication-candidate-challenge-check.log)); an earlier sandboxed
Comparator run in CI (commit `41aa125`) is [recorded](evidence/comparator-ci-sandboxed.txt).

## How it was made

The development was produced with Codex and Claude Code agents, using Lean,
Mathlib and source-file search; model build identifiers are not recorded. Each
advertised statement and its definitions were compared with the source by a
separate agent that did not write them ([review log](docs/milestone-audit.md)),
and an agent carried out the omission scan. No human line-by-line review of the
proofs and no human peer review is claimed.

## License and citation

Code and documentation: [Apache-2.0](LICENSE), see [NOTICE](NOTICE); the license
does not cover the paper's TeX source [attachement-uniforme-2-final.tex](attachement-uniforme-2-final.tex).
`Freezing2/Companion` is adapted from the companion formalization of *Uniform
attachment with freezing* by the same contributor ([provenance](docs/companion-provenance.md)).
Cite the paper for its mathematics ([CITATION.cff](CITATION.cff),
[CITATION.bib](CITATION.bib)); the citation does not assert that its authors wrote
or endorse the Lean code. Maintainer: Igor Kortchemski. Issues and pull requests are
welcome: keep the pinned toolchain, add no axioms or `sorry` outside
`Challenge.lean`, update the report, and run the checks above.
