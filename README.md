# Uniform attachment with freezing: Scaling limits

[![CI](https://github.com/igor-kortchemski/uniform-attachment-freezing-scaling-limits/actions/workflows/ci.yml/badge.svg?branch=main)](https://github.com/igor-kortchemski/uniform-attachment-freezing-scaling-limits/actions/workflows/ci.yml?query=branch%3Amain)
[![Comparator](https://github.com/igor-kortchemski/uniform-attachment-freezing-scaling-limits/actions/workflows/ci.yml/badge.svg?branch=main&event=push)](https://github.com/igor-kortchemski/uniform-attachment-freezing-scaling-limits/actions/workflows/ci.yml?query=branch%3Amain)

> Both badges show the single `ci.yml` workflow, whose `build` job builds the
> library and checks axioms and whose `comparator` job runs the sandboxed
> Comparator; they are not separate signals.

This repository is a Lean 4 and Mathlib formalization of
[arXiv:2308.00484](https://arxiv.org/abs/2308.00484), *Uniform attachment with
freezing: Scaling limits* by Étienne Bellin, Arthur Blanc-Renaudie, Emmanuel
Kammerer and Igor Kortchemski, published in Ann. Inst. H. Poincaré Probab.
Statist. **61**(4) 2679–2708 (2025),
[doi:10.1214/24-AIHP1497](https://doi.org/10.1214/24-AIHP1497).

## What is proved

For the actual random trees $\mathcal T_n$ of uniform attachment with freezing,
the main statements are restated with Mathlib-only definitions in
[Challenge.lean](Challenge.lean) and proved in the library (via
[Solution.lean](Solution.lean)); [comparator.json](comparator.json) lists them:

| Challenge theorem | Source | Statement |
| --- | --- | --- |
| `height_scaling_limit` | `thm:heightalpha` (M01) | For $0<\alpha<1$, $\mathrm{Height}(\mathcal T_n)/n^{1-\alpha}\to\int_0^1\frac{dt}{2f(t)}$ in $L^p$ for every $p\ge1$. |
| `subcritical_scaling_limit` | `thm:sous-critique` (M02) | For $0<\alpha<1/2$, $\mathcal T_n/n^{1-\alpha}$ with its uniform measure converges in GHP distribution to the segment $[0,\int_0^1\frac{dt}{2f(t)}]$ carrying the image of the uniform measure on $[0,1]$ under $t\mapsto\int_0^t\frac{ds}{2f(s)}$. |
| `critical_scaling_limit` | `thm:critique` + `thm:properties` (M03, M04) | For $\alpha=1/2$ and $\max_k S_k^n=O(\sqrt n)$, $\mathcal T_n/\sqrt n$ converges in GHP distribution to a random tree $\mathcal T(f)$ depending only on $f$; almost surely $\mathcal T(f)$ is a compact real tree whose measure has full support and charges only leaves, it is binary if and only if $\int_0^{1/2}f^{-2}=\infty$, and otherwise it has a point of infinite degree, all other branch points having degree three. |
| `supercritical_distance_matrix_limit` | `thm:sur-critique` (M06) | For $1/2<\alpha<1$, the root-inclusive distance matrix of $k$ uniform vertices, divided by $n^{1-\alpha}$, converges in law to the star matrix (with the zero diagonal correction approved by the user). |
| `bounded_population_GH_limit` | `thm:alpha0` (N09) | With bounded population, $\mathcal T_n/h_n^+\to[0,1]$ in probability for the Gromov–Hausdorff distance. |

All numbered results N01–N17 and most unnumbered claims of the paper are also
proved in the library, several in corrected or qualified forms. **The CRT
corollary (`cor:CRT`, M05) is not formalized**: it needs Brownian excursion and
CRT theory, invariance principles, Skorokhod representation and random-walk local
limit theorems that are absent from Mathlib, and two printed estimates of its
proof are refuted in Lean ([Audit/ExcursionCounterexamples.lean](Freezing2/Audit/ExcursionCounterexamples.lean)).
Also open: the dimension lower bounds (no proof in the source), long-dendron
convergence and Aldous's time change. The
[formalization report](FORMALIZATION_REPORT.md) maps every result to the paper,
records each correction and proof-route difference, and lists what remains; the
[statement interface](docs/statement-interface.md) explains each Challenge
encoding (in particular, the GHP topology is put on compact measured spaces
rather than on their isometry classes, so $\mathcal T(f)$ is unique only up to
isometry). The [inventory](docs/source-inventory.md) and a
[whole-source omission scan](docs/omission-scan-2026-10-30.md) record coverage.
No whole-paper completion is claimed.

## Read the development

Start with [Challenge.lean](Challenge.lean) for the main statements, then [Freezing2/Interface/Statements.lean](Freezing2/Interface/Statements.lean), which derives them from the library; [Freezing2.lean](Freezing2.lean) imports every maintained module.

| Module | Content |
| --- | --- |
| [Walk](Freezing2/Discrete/Walk.lean) | Signed paths, counts, survival, and faithful natural-number representation |
| [Labels](Freezing2/Discrete/Labels.lean) | Disjoint vertex labels, birth times, actual uniform measure, `uniformVertex_birth_lt_before_extinction` |
| [WeightedWalk](Freezing2/Discrete/WeightedWalk.lean) | Exact harmonic and coalescence weighted balances |
| [Estimates](Freezing2/Discrete/Estimates.lean) | Specialization to the paper's surviving signed paths and uniform logarithmic boundary bound |
| [Bennett](Freezing2/Probability/Bennett.lean) | Both strict concentration tails and absolute deviation, derived from exact Bernoulli MGFs |
| [BennettFunction](Freezing2/Analysis/BennettFunction.lean) | Positivity and monotonicity of Bennett's rate function |
| [ExponentialDecay](Freezing2/Analysis/ExponentialDecay.lean) | Polynomial versus stretched-exponential and geometric decay |
| [SourceHypotheses](Freezing2/Analysis/SourceHypotheses.lean) | Source profile conventions and sublinear population, N06(i) |
| [SignMeasures](Freezing2/Analysis/SignMeasures.lean) | Weak convergence of both empirical sign measures, N06(ii) |
| [HarmonicConclusions](Freezing2/Analysis/HarmonicConclusions.lean) | Harmonic asymptotic equivalences and the uniform interval maximum, N06(iii–iv) |
| [LocalSquareProfiles](Freezing2/Analysis/LocalSquareProfiles.lean) | Equivalence of the source's local square-moment and squared-$L^1$ hypotheses |
| [InteriorMinimumLimit](Freezing2/Analysis/InteriorMinimumLimit.lean) | Interior minimum growth needed by N06(v) |
| [PopulationLemma](Freezing2/Analysis/PopulationLemma.lean) | All five parts of the population-profile lemma in source notation |
| [Height](Freezing2/MainResults/Height.lean) | Introduction height theorem for the actual forward tree law |
| [SubcriticalDistribution](Freezing2/MainResults/SubcriticalDistribution.lean) | Actual forward subcritical measured-tree convergence in the GHP topology |
| [Supercritical](Freezing2/MainResults/Supercritical.lean) | Corrected root-inclusive forward supercritical matrix limit |
| [CriticalRealTree](Freezing2/Probability/CriticalRealTree.lean) | Critical GHP limit to a random compact measured real tree, M03 |
| [CriticalLeaves](Freezing2/Probability/CriticalLeaves.lean) | The limit's mass measure charges only leaves, M04a |
| [CriticalBranching](Freezing2/Probability/CriticalBranching.lean) | Binary criterion and infinite-degree point (unpointed), M04b–c |
| [BoundedPopulation](Freezing2/MainResults/BoundedPopulation.lean) | Bounded-population GH limit to a segment, N09 |
| [BoundedPopulationMeasure](Freezing2/MainResults/BoundedPopulationMeasure.lean) | GHP nonuniversality for bounded populations, U20 (new formulation) |
| [RecursiveNoLimit](Freezing2/MainResults/RecursiveNoLimit.lean) | Recursive trees have no nondegenerate GHP limit, U04b (S19-qualified) |
| [SupercriticalNonTight](Freezing2/MainResults/SupercriticalNonTight.lean) | Supercritical GHP non-tightness, U04b (S08-corrected) |
| [ReversePaper](Freezing2/Probability/ReversePaper.lean) | Actual conditional increments in original labels, including extinction |
| [CoalescenceHistory](Freezing2/Probability/CoalescenceHistory.lean) | Corrected exact coalescence distribution for distinct vertices |
| [DistanceApproximation](Freezing2/Probability/DistanceApproximation.lean) | Uniform approximation of actual reverse-tree distances |
| [SubcriticalCoalescenceLaw](Freezing2/Probability/SubcriticalCoalescenceLaw.lean) | Uniform maximum coalescence delay is sublinear |
| [BirthTimeLimit](Freezing2/Probability/BirthTimeLimit.lean) | Actual normalized birth measures converge weakly to uniform measure |
| [BranchLengthLimit](Freezing2/Probability/BranchLengthLimit.lean) | Actual scalar and fixed-$k$ iid harmonic branch limits |
| [SupercriticalCoalescenceLaw](Freezing2/Probability/SupercriticalCoalescenceLaw.lean) | Actual iid sampled coalescence time is sublinear |
| [SubcriticalDistanceApproximation](Freezing2/Probability/SubcriticalDistanceApproximation.lean) | Uniform graph-distance approximation under harmonic coordinates |
| [SubcriticalGHLimit](Freezing2/Probability/SubcriticalGHLimit.lean) | Actual reverse-tree GH convergence to the source segment |
| [ForwardTerminalLaw](Freezing2/Probability/ForwardTerminalLaw.lean) | Exact masses on the fixed schedule's reachable terminal support |
| [CoalescentForests](Freezing2/Probability/CoalescentForests.lean) | Continuous coalescent forest density in source form, N11 |
| [CriticalLocalLimitPlane](Freezing2/Probability/CriticalLocalLimitPlane.lean) | Corrected local limit in tracked-chain form, N12a |
| [CriticalGenealogyLaw](Freezing2/Probability/CriticalGenealogyLaw.lean) | Convergence of sampled birth and coalescence times, N12b |
| [CriticalSampledCover](Freezing2/Probability/CriticalSampledCover.lean) | Tightness time estimate with repaired constants, N13 |
| [OneStepTightnessAsymptotic](Freezing2/Probability/OneStepTightnessAsymptotic.lean) | One-block tightness estimate for positive block indices, N14 |
| [GPMatrixCharacterization](Freezing2/Probability/GPMatrixCharacterization.lean) | GP convergence iff convergence of sampled distance matrices, N15 |
| [GPGHtoGHP](Freezing2/Probability/GPGHtoGHP.lean) | GP plus GH weak convergence gives GHP weak convergence, N16 |
| [SampledReconstruction](Freezing2/Probability/SampledReconstruction.lean) | Leaf-tightness criterion `C.1`, N17 |
| [GromovProkhorov](Freezing2/Geometry/GromovProkhorov.lean) | Polish Gromov–Prokhorov space and the GHP-to-GP projection |
| [Obstructions](Freezing2/Audit/Obstructions.lean) | Zero-diagonal correction, distributional obstruction, and other precise source issues |
| [ExcursionCounterexamples](Freezing2/Audit/ExcursionCounterexamples.lean) | Lean refutations of the printed CRT estimates S15 and S16 |

The corrected supercritical candidate matrix has zero diagonal and retains the
sum of branch lengths off the diagonal, as authorized by the user. Its root-inclusive scaling limit is proved for the actual forward tree,
with the source normalization and limiting branch laws. See [manuscript recommendations](MANUSCRIPT_RECOMMENDATIONS.md)
for this and other source defects; the supplied TeX is unchanged.

## Verify locally

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

`lake build` builds the library, `Challenge` and `Solution`; the only warnings
are the five deliberate `sorry` placeholders of `Challenge.lean`, which states
the theorems and is never imported by the library or by `Solution`.
`check_axioms.py` inspects the transitive axioms of every module under
`Freezing2/` and accepts only `propext`, `Classical.choice` and `Quot.sound`.
`check_challenge.py` checks that `Challenge.lean` copies the shared definitions
of [Freezing2/Interface/Defs.lean](Freezing2/Interface/Defs.lean) verbatim and
meets Palomar's size limits. Comparator then checks that `Solution` proves
exactly the `Challenge` statements with only those three axioms.

Local evidence for the current candidate
([context and hashes](evidence/publication-candidate-context.txt)): `lake build`
4,177 jobs; the axiom check passed for 3,724 definitions and theorems in all
289 modules ([log](evidence/publication-candidate-axioms.log)); the Challenge
check passed; and a **preliminary, unsandboxed** local Comparator run accepted
the solution ([output](evidence/comparator-local-unsandboxed.txt)).

In CI on GitHub ([run 41033233038](https://github.com/igor-kortchemski/uniform-attachment-freezing-scaling-limits/actions/runs/41033233038),
commit `41aa125`), the build, axiom and Challenge checks passed again, and the
**sandboxed** Comparator (bubblewrap 0.12.0, built by Palomar's pinned installer)
accepted the solution ([record](evidence/comparator-ci-sandboxed.txt)). No
Palomar preflight, submission or registration has taken place.

## Source, citation, and contribution

The audited source is [attachement-uniforme-2-final.tex](attachement-uniforme-2-final.tex)
(SHA-256 recorded in the report). Cite the paper for its mathematics,
[DOI 10.1214/24-AIHP1497](https://doi.org/10.1214/24-AIHP1497); see
[CITATION.cff](CITATION.cff) and [CITATION.bib](CITATION.bib). The citation does
not assign the paper's authors authorship or endorsement of the Lean code.

The code and documentation are licensed under [Apache-2.0](LICENSE); see
[NOTICE](NOTICE). The manuscript retains its own rights. The modules under
`Freezing2/Companion` are adapted from the companion formalization of *Uniform
attachment with freezing* by the same contributor
([provenance](docs/companion-provenance.md)). The development was produced with
Codex and Claude agents; statement fidelity was checked by separate automated
reviewers ([audit log](docs/milestone-audit.md)). No human peer review is claimed.
Maintainer: Igor Kortchemski. Issues and pull requests are welcome; please keep
the pinned toolchain, avoid new axioms or `sorry` outside `Challenge.lean`, and
update the report and run the checks above.
