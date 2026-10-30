# Handoff — updated 30 October 2026 (Claude session)

## Current state (supersedes the sections below where they conflict)

Authoritative status: the result tables, the latest-checkpoint paragraph and the
final "Remaining mathematical work" list of
[FORMALIZATION_REPORT.md](FORMALIZATION_REPORT.md), and the dated sections at the
end of [docs/milestone-audit.md](docs/milestone-audit.md). Classification of the
inventory items without a dedicated report row:
[docs/coverage-gaps.md](docs/coverage-gaps.md).

Proved and integrated (every maintained module is imported by `Freezing2.lean`):

- **Main results:** M01, M02, M03 (`critical_scaling_limit_realTree`, real-tree
  limit `criticalTreeLaw (1/f)`), M04 (`critical_tree_properties`; M04c in
  unpointed form) and M06 with the authorized zero diagonal.
- **All numbered results N01–N17**, in the qualified forms of the report: N04 for
  distinct vertices; N09 (`bounded_population_GH_limit`); N11 in source form
  (`sourceForest_law`; S09 roots ordered by label, a working interpretation);
  N12a in corrected tracked-chain form (`critical_local_limit_plane`); N12b in an
  equivalent form; N13 with repaired constants; N14 for positive block indices;
  N15 (`GPSpace.equivGP`, by empirical reconstruction rather than Loh13's route);
  N16 (`MeasuredGHSpace.tendsto_ghp_of_gp_of_gh`); N17
  (`MeasuredGHSpace.leafTightCriterion`).
- **Unnumbered claims:** U01 first clause (`treeLaw_allPlus_eq_urtLaw`); U04b
  supercritical non-tightness (S08, `supercritical_not_tight`) and recursive-tree
  clause (S19-qualified, `MainResults/RecursiveNoLimit.lean`); U20 nonuniversality
  (new formulation, `MainResults/BoundedPopulationMeasure.lean`); U23 in law
  (`Probability/CoalescentDensity.lean`, `CoalescentDecoding.lean`); U25, U26,
  U31, U32, U36–U41; U49/E09 with the Polish GP space and S18 as a projection
  (`Geometry/GromovProkhorov.lean`); E10 through N15 and N16.
- **Lean refutations** of the false displays S15 and S16
  (`Audit/ExcursionCounterexamples.lean`).
- Statement reviews by separate Claude agents: PASS or PASS with notes for each
  of the above (agent review, not human peer review).

Latest evidence (default all-source checker): `evidence/plane-tree-axioms.log` and
`evidence/plane-tree-context.txt`: `lake build` 4,168 jobs, no warnings; 3,645
explicit declarations in all 285 modules; only `propext`, `Classical.choice`,
`Quot.sound`. Earlier checkpoints are listed in the report's "Verification and
review" section. These are local checks only: no public repository, Comparator
run, independent kernel replay or Palomar submission exists.

Open (details in the report's final section):

- **M05** (`cor:CRT`) with U42–U48, E02, E05, E07, E08: blocked by external
  mathematics (Brownian excursion and CRT, invariance principles, Skorokhod
  representation, local limit theorems), plus measurability of
  $f\mapsto$ `criticalTreeLaw (1/f)`, a terminal-horizon M03 (S14) and valid
  replacements for S15–S17.
- **U04a** dimension lower bounds (no proof in the source).
- **U04b** long dendron convergence (ET21/Jan21 topology); comparisons E11 are
  external background (classification (d)), not obligations.
- **U24** stochastic time change to Aldous's coalescent (E04).
- **U01** second clause, conditioned uniform plane tree (E02; the source's
  "Theorem 2" citation is the companion's Examples paragraph, S20).
- Residual qualifications: U34 count with unborn vertices (bypassed), N12a finite
  decoding to $\mathcal F^n_r$, explicit Markov path process for U23, the pointed
  "root of degree one" remark of M04, and printed false statements that cannot be
  certified literally.
- Bypassed or unexported intermediate claims (report item 8): U28's source
  route, U29's density normalization (line 1419), U32's intermediate displays,
  U24's "$g_{0,k}$ determines the law", U06's monotonicity/stationarity clause
  (line 480) and prefix dependence, U27's full local density, U20's unexported
  array and the $L^p$ height form (line 1046).

Omission scan: [docs/omission-scan-2026-10-30.md](docs/omission-scan-2026-10-30.md)
(30 October 2026, agent scan). Its findings are now inventory rows U53–U58
(heuristics, background, source slips; U55 derivable but not stated) and
S20–S23, and minor slips in
[MANUSCRIPT_RECOMMENDATIONS.md](MANUSCRIPT_RECOMMENDATIONS.md). No new Lean
obligation beyond M05.

Build gotcha: `lake env lean File.lean` does not apply the lakefile's
`autoImplicit = false`, so an undeclared universe or variable can pass a focused
check and then fail `lake build`. Finish each new module with
`lake build Freezing2.<Module>`.

Checker gotcha: `scripts/check_axioms.py` parses `#print axioms` output with a
regex that cannot read declaration names containing `'`. Do not give new
declarations primed names (a primed lemma made one run fail with "Incomplete
axiom output"; it was renamed to `ghpDistance_le_of_isometries_borel`).

Suggested next targets (none blocked by Brownian-motion infrastructure unless
stated):

1. U01 second clause / E02: iid symmetric signs give the conditioned uniform
   plane tree, by direct counting (also an input to M05).
2. U43 deterministic part and a valid replacement for the S16 estimate with
   $C=C(\varepsilon)$ (discrete E08): the parts of the CRT section that need no
   Brownian excursion.
3. U24 / E04: the stochastic time change to Aldous's inhomogeneous coalescent.
4. E05: Skorokhod representation on Polish spaces (used only in the CRT
   section).
5. U04a: dimension lower bounds (large; needs Minkowski and packing dimensions
   and a Frostman-type lemma, absent from Mathlib).
6. Blocked: M05 and the probabilistic parts of U42–U48 (Brownian excursion and
   CRT); U04b long dendron (ET21/Jan21 topology).
7. Before any coverage claim: repeat the whole-source omission scan if the
   source or the claimed coverage has changed since 30 October 2026; then the
   publication steps in [docs/publication-readiness.md](docs/publication-readiness.md).

The rest of this file is the previous agent's handoff, kept for history. Its
status statements (for example that M03, M04, N09, N11–N13 or N15–N17 are open,
or that modules lie outside `Freezing2.lean`) are out of date.

---

# Handoff to Claude — 29 October 2026

Work was **stopped at the user's explicit request** at approximately 16:26 UTC
(17:26 Paris). Do not resume automatically; this document is for the user's
next agent. All agents stopped and all known checks finished. No build or proof
process is knowingly left running. Files are saved in the shared checkout.

## Start here

Working directory for **every Lean/Lake command**:

```sh
cd <project root>
```

Read these existing records before changing mathematics:

1. [AGENTS.md](AGENTS.md), including pinned versions and publication policy.
2. [FORMALIZATION_REPORT.md](FORMALIZATION_REPORT.md): authoritative integrated
   result coverage, corrections, and unresolved obligations.
3. [Source inventory](docs/source-inventory.md) and
   [milestone audit](docs/milestone-audit.md): independently reconstructed source
   inventory and scoped mathematical reviews, including newer unintegrated work.
4. [Publication readiness](docs/publication-readiness.md) and
   [manuscript recommendations](MANUSCRIPT_RECOMMENDATIONS.md).
5. Local skills requested by the user:
   [lean-workflow](.agents/skills/lean-workflow/SKILL.md) and
   [lean-statement-audit](.agents/skills/lean-statement-audit/SKILL.md).
   Also read the local architecture, orchestrator, and publication skills when
   their corresponding tasks arise. They are under `.agents/skills/`.

The user requested every theorem, proposition, lemma, corollary and substantive
claim in `attachement-uniforme-2-final.tex`, prioritizing the Introduction and
dependencies without dropping other obligations. The final destination is
GitHub and Palomar, with a verified publication candidate. **This is not complete.**

The TeX is unchanged. SHA-256:

```text
23a485d5a5dfaca01a05db28377d015fb1456c194a543d0cbf56f77619ad0cbf
```

## Rules and author decisions

- Preserve Lean and Mathlib `v4.35.0`, `lean-toolchain`, `lakefile.toml`, and the
  original `lake-manifest.json`. `autoImplicit = false`.
- No `sorry`, custom axioms, `native_decide`, or `bv_decide` in maintained proof
  code. Palomar's permitted transitive axioms are only `propext`,
  `Classical.choice`, and `Quot.sound`.
- New modules use `module`, `public import`, and `@[expose] public section`.
- Coordinate **one dependency-writing Lake build/checker at a time**. Focused
  `lake env lean path.lean` checks do not write shared module artifacts.
- Do not clean caches or update dependency pins to repair errors.
- `../freezing1` is read-only. The needed companion proof closure is vendored
  under `Freezing2/Companion/`; provenance is in `docs/companion-provenance.md`.
- The user explicitly approved M06's **zero diagonal**, preserving sums of
  branch lengths for distinct indices. This is the only explicit author
  correction approval in this chat. The printed all-entry formula is false.
- Canonical chronological ordering of residual coalescent roots is the adopted
  working interpretation of source ambiguity S09, **not a separate user ruling**.
  Arbitrary residual-component order would need a factor $1/(r+1)!$. Record
  this interpretation and do not claim the arbitrary-order formula proved.
- Markdown mathematics use `$...$` and `$$` on separate lines, with blank lines
  around displays, compatible with MacDown and QLMarkdown.

## Last fully integrated proof evidence

The unchanged entry point `Freezing2.lean` imports **199 modules**. The last
combined check passed for **1,806 explicit definitions/theorems**, with
**4,045 build jobs**, and only the permitted axioms:

- [Axiom output](evidence/critical-topology-axioms.log)
- [Exact source/configuration hashes and scope](evidence/critical-topology-context.txt)

This checkpoint includes M01, M02, corrected M06, full N01, N02–N08,
N10, corrected positive-index N14, genuine Polish GHP topology, compact GH
preimages, deterministic chaining, and critical sampling/analytic foundations.
Consult the report for exact qualifications; corrected statements are not proofs
of the corresponding false printed statements.

**All additions listed below remain outside `Freezing2.lean` and that axiom
snapshot.** Their local checks/builds are real progress, but no new combined
axiom audit was run before stopping. No numeric claim about a larger integrated
closure should be made until the checker runs successfully.

Current completed Introduction results:

- M01: actual forward height scaling limit.
- M02: actual forward subcritical uniformly measured GHP limit, in the exact
  whole-carrier measured-isometry quotient.
- M06: actual forward root-inclusive sampled matrix limit, authorized zero
  diagonal, iid samples with collisions retained.

M03 (critical tree limit), M04 (tree properties), and M05 (CRT) remain open.
About 13 of the 23 named source environments are covered with the report's
qualifications. **N13 is still unproved at this handoff**, despite a nearly
complete draft pipeline.

## Immediate continuation: finish N13

The critical probability proof now follows this route:

1. Actual iid frozen-block occupancy with repaired block length
   $16\lceil Mn/\sqrt{k}\rceil$; the named N14 retains its original factor four.
2. Actual reverse continuation from an arbitrary valid forest, its marked-count
   recurrence and oldest-isolation comparison.
3. The true conditional endpoint law given the complete actual history.
4. Conditional isolation probability at most $3/4$, iterated by the tower
   property. **No independence of different blocks is assumed.**
5. Deterministic birth-block geometry: being far from every sample implies all
   selected alternating-block isolation events.
6. Integrate over the real iid sample law, retaining the occupancy error and
   collisions. The query vertex is independently uniformly sampled too.
7. With $p=\lfloor100\log k\rfloor$, the geometric error is $o(k^{-4})$ and
   $2p\cdot16\lceil Mn/\sqrt{k}\rceil\leq n\log(k)^2/\sqrt{k}$ eventually,
   uniformly in $n\geq k$. This yields the exact N13 conclusion for $k^3\leq n$.

### First file to repair

`Freezing2/Probability/CriticalBlockCover.lean` is a complete draft. Its last
focused command was:

```sh
lake env lean Freezing2/Probability/CriticalBlockCover.lean
```

Session 82053 finished **exit 1**. Exact outstanding diagnostics:

```text
Freezing2/Probability/CriticalBlockCover.lean:142:21: error:
After simplification, hlength has type
  tightnessBlockLength M n k ≤ d
but is expected to have type
  tightnessBlockLength M n k ≤ i j * d - criticalTrialPhase i₀ d (j + 1)

Freezing2/Probability/CriticalBlockCover.lean:148:49: warning:
Set.mem_setOf_eq is deprecated; use Set.mem_ofPred_eq.
```

Likely repair: explicitly unfold/change the local alias `i :=
criticalTrialBlock i₀` at the length goal, rewrite
`criticalTrialBlock_middle_gap hm hj`, then use `hlength`. This proposed repair
was **not made or checked**, because the user requested stopping.

The exported draft theorem is
`ReverseCoalescence.probability_far_le_geometric_of_birth_occupancy`.
It is uniform over a fixed legal query vertex and any nonempty fixed finite
sample set satisfying the birth-block occupancy condition. It proves the far
event has probability at most $(3/4)^{(p-1)/2}$ with natural division in the
exponent. Its mathematical content received independent review. The last Lean
run reported only the error and warning above; this is still not a passing check.

After repairing and building that file, check:

```sh
lake env lean Freezing2/Probability/CriticalSampledCover.lean
```

`CriticalSampledCover.lean` is a **complete but not fully checked draft**. It has:

- exact source-label to companion-label and sampled birth-cardinality bridges;
- actual history × (independent query vertex × iid covering tuple) law;
- the nonempty sampled minimum and its event identity;
- the occupancy error plus geometric error bound;
- the combined scaled error tending to zero;
- `eventually_uniform_sampledCriticalCover_probability_le`;
- `critical_sampled_cover_probability_uniform_positive_horizons`, with the
  literal source range $k\leq n^{1/3}$ and only positive horizons constrained.

Helper-only extraction 37528 passed before later additions. Extraction 24458
found a minimum-event simplification problem; it was replaced by an attainment
proof but **not rechecked**. The full file awaits the Cover dependency. It has
independent mathematical review, not mechanical completion.

Then build affected modules, integrate stable imports, run the integrated axiom
checker, and update the report's N13/U36/U37 entries and exact evidence. The
source's conditional independence assertion is replaced by the proved conditional
bound/tower route; the original assertion is not certified.

## New files with successful checks

Paths in this section are relative to `Freezing2/`. The session numbers are
historical tool references, **not running jobs or portable evidence handles**.
Recheck if source/dependency identity is uncertain.

### Sampling and occupancy

| File | Last check/build status | Content |
| --- | --- | --- |
| `Analysis/SuccessorSquareProfile.lean` | Focused clean; parent 10376 passed | Local L1 limit for literal successor population square |
| `Probability/AuxiliaryAttachmentRate.lean` | Focused clean; parent 10376 passed | Actual joint time and ordered attachment-rate laws and finite products |
| `Probability/AuxiliaryAttachmentSquare.lean` | Focused 35788 clean; parent 67909 passed | Literal $n/S_{i+1}^2$ marked sampler and finite products |
| `Analysis/CriticalOccupancyRate.lean` | Focused clean; earlier parent 43040 passed | Uniform $k^4$ occupancy error tends to zero |
| `Probability/FrozenBlockOccupancy.lean` | Focused 45974 clean; parent 10376 passed | Actual iid frozen occupancy and frozen-only fourfold collisions |
| `Probability/CriticalBlockOccupancy.lean` | Focused 64330 clean; parent 21656 passed | Uniform repaired U36, exact source distinct-birth event, cutoff before horizon/row |

Occupancy retains the one-vertex birth-index endpoint loss. It uses factor 16
and Bennett's $g(1/4)$ to repair the printed constants. Active vertices share
birth time $n$ and are not subjected to the false frozen collision bound.
The original iid law, including its active atom and collisions, is retained.

### Conditional blocks and their arithmetic

| File | Last check/build status |
| --- | --- |
| `Probability/ReverseContinuation.lean` | Focused 73449 clean; parent 22934 passed |
| `Probability/ContinuationCount.lean` | Focused 63780 clean; parent 99404 passed |
| `Probability/ContinuationIsolation.lean` | Focused 95418 clean; parent 51486 passed |
| `Probability/ContinuationConditional.lean` | Focused 22024 clean; parent 51486 passed |
| `Probability/ContinuationBlockIsolation.lean` | Focused 74997 clean; parent 26445 passed |
| `Probability/ConditionalBlockIsolation.lean` | Focused 23178 clean; parent 55368 passed |
| `Probability/ConditionalEventBounds.lean` | Focused 93966 clean; parent 20251 passed |
| `Probability/FiniteConditionalEventBounds.lean` | Focused 46762 clean; parent 26445 passed |
| `Probability/ConditionalIsolationChain.lean` | Focused 20224 clean; parent 71850 passed |
| `Probability/CriticalBlockGeometry.lean` | Focused 46770 clean; parent 51486 passed |
| `Analysis/CriticalIsolationRate.lean` | Focused 33366 clean; parent 82798 passed |
| `Analysis/CriticalBlockSchedule.lean` | Focused passed; unused assumptions removed; parent 32719 clean |
| `Analysis/CriticalBlockRadius.lean` | Focused 43188 clean; parent 85428 passed |

Important APIs and boundary conditions:

- `ReverseContinuation.law x s F j` is the actual kernel law starting from
  forest `F` at phase `s`, held fixed after zero.
- `expectedCountFrom` is literally the integral of `componentCount` under that
  law. Its block bound has an **offset** `j₀`; all marks need only be born by
  `s-j₀`. This is essential for blocks that first wait for younger births.
- The oldest-isolation continuation comparison allows younger birth equal to
  the starting phase, requiring initial singleton isolation only at that
  boundary. `ConditionalBlockIsolation` discharges it from actual-history support.
- `conditional_endpoint_indicator` is derived from actual `Kernel.traj` and
  the whole-past filtration; it is not a Markov assumption.
- The kernel and conditional bounds accept final all-born interval length at
  least `tightnessBlockLength = 4*ceil(...)`, so the repaired factor-16 blocks apply.
- `ConditionalIsolationChain` uses an antitone phase sequence and the increasing
  filtration `piLE (n-s_j)`. Only the finitely used event bounds are required.
- The rounding loss in `(floor(100 log k)-1)/2` is explicitly retained.

### Compact measured-space topology

| File | Last check/build status | Content |
| --- | --- | --- |
| `Probability/GHPTightness.lean` | Focused 79500 clean; earlier parent 43040 passed | Tightness of probability-law families iff underlying GH families are tight |
| `Probability/SampledDistanceLaw.lean` | Focused 1603 clean; parent 22934 passed | Actual iid distance matrices, invariance, quotient law |
| `Probability/SampledDistanceContinuity.lean` | Focused 81878 clean; parent 21656 passed | All finite sampled-distance laws continuous in GHP; bounded tests for random spaces |
| `Probability/SampledCoverRadius.lean` | Focused 99308 clean; parent 75697 passed | Actual full-carrier covering-radius laws and joint ambient continuity |
| `Geometry/CompactMeasuredRepresentation.lean` | Focused 18344 clean; parent 29933 passed | Common compact ambient subsequence with full carriers and pushed measures converging |
| `Probability/SampledCoverRadiusContinuity.lean` | Focused 29640 clean; **not parent-built** | Quotient GHP continuity and random-space bounded tests |
| `Probability/CoverRadiusSupport.lean` | Focused 31233 clean; **not parent-built or independently reviewed** | Null-ball obstruction, deterministic full-support criterion, quotient `HasFullSupport` |

All whole-carrier constructions retain zero-mass points. Sampled distance
matrices alone cannot identify those points. Full support must be established
before the relevant reconstruction/uniqueness step. Do not identify the source's
whole-carrier GHP quotient with a support-based GP quotient.

Next topology work is **planning only**, no additional file started:

1. Use covering-law continuity and Portmanteau/Markov bounds with countably many
   radii to transfer random leaf-tightness to almost-sure full support.
2. Consider finite iid empirical sampled-space approximation for compact
   reconstruction/uniqueness in N17. This is a proposed departure from the
   paper's GP route; it does not discharge standalone noncompact GP/N15.

### Continuous coalescent clocks

| File | Last check/build status | Content |
| --- | --- | --- |
| `Probability/ContinuousCoalescentHazard.lean` | Focused 81800 clean; parent 32719 passed; independent review clean | Normalized finite-cutoff event density plus survival atom using absolute continuity, without hazard continuity |
| `Probability/ContinuousCoalescentEndpoint.lean` | Focused 13900 clean; parent 71850 passed; independent review clean | Actual normalized law down to zero, endpoint atom, divergent extended hazard implies zero atom |

`Probability/ContinuousCoalescentKernel.lean` is a **failing draft**. Its last
focused session 31079 finished exit 1. Agent-reported diagnostics:

- Line 29: `StronglyMeasurable.integral_prod_right'` needs explicit
  `(ν := volume)`; the `SFinite` metavariable is stuck.
- Line 76: annotate `hA` with
  `Measurable (fun p : ℝ × ℝ => Measure.dirac p.1 E)`.
- Line 80: `measurable_positiveEventMeasure` reaches a 200000-heartbeat
  definitional-equality timeout; replace the implicit conversion with explicit
  `change`/unfolding/casts, rather than raising limits blindly.
- Line 90: final simplification misses `Function.comp_def` / `Pi.add_apply`.
- Line 110: `instance nextEventKernel_isMarkov` cannot infer `h0,hInt`; make it
  a theorem and instantiate locally in consumers.

No repair was made after the stop request. The draft defines measurable event
windows and a next-event kernel, but **none of this file is certified yet**.

`Probability/ContinuousCoalescentSurvival.lean` is a complete **unchecked draft**,
importing only the built Endpoint module. It targets finite hazard implies a
positive endpoint atom, zero hazard gives a Dirac cutoff, cluster hazard
$\binom m2 g^2$, and specialization from local square integrability.

Next clock work: repair/check Kernel, check Survival, prove clock support and
absence of positive-time atoms, and obtain the ordered pair density factor.
The generic hazard still needs actual cluster-count/profile instantiation.

No finite genealogy ledger file exists. Proposed parallel work:

- Finite events: `birth (Fin k)` or an **ordered** merger of two current root IDs.
- Root IDs are chronological node/event IDs; timestamps are stored separately.
- Prove legal partition/forest invariants and a bijection to the source's plane
  binary forest with canonically ordered residual roots.
- Establish support, multiplicities, and normalization from the actual kernel
  construction; do not assume the desired density as a premise.
- N11/N12 remain open despite the verified survival and sampling ingredients.

## Important remaining source issues

The complete list remains in the inventory, report, and recommendations.

- N14's printed index zero uses a negative forest phase. The positive-index
  correction is proved; the undefined literal case is not.
- U34's global count including unborn vertices is still a separate obligation.
  Existing all-born estimates suffice for N14 and the new block proof. A possible
  route is to prove actual forests have `root v = v` outside their vertex set,
  then decompose `componentCount` into present components plus unborn labels.
  This is only a proposal, not an established invariant.
- Time-only Skorokhod convergence cannot evaluate a merely measurable profile.
  The proved route first obtains joint time/mark convergence through mesh jitter,
  bounded density, and local L1 convergence.
- Rescaled local genealogy probabilities need the exact multiplicative
  frozen-distinct correction, not merely an additive collision error.
- The inclusive harmonic surrogate has a positive diagonal; the approximation
  proof uses a primitive modulus, not a claim that this surrogate is a metric.
- Finite graph vertex sets are not real trees; edge realizations or an equivalent
  rigorous bridge are needed for the critical limit's real-tree property.
- The CRT appendix has false auxiliary estimates S14–S17. A valid replacement
  is needed; no Brownian-excursion/CRT theorem is proved by current helpers.
- N09 bounded population and its measure nonuniversality, N15–N17 general
  topology, M04 properties, and other unnumbered/appendix obligations remain.

The inventory contains all 23 named environments, M01–M06, N01–N17, U01–U52
(53 rows after splits), E01–E11, S01–S19, and the two stated open questions.
The most recent full omission scan used the unchanged TeX. Reconcile scope and
scan again if source/scope changes and before claiming complete coverage.

## Integration and publication after resuming

Build missing dependency artifacts serially, then add only completed modules
to `Freezing2.lean`. At the next coherent milestone run:

```sh
python3 scripts/check_axioms.py --integrated
```

Save the real output and an exact input/scope record as done for the existing
checkpoints. Preserve historical evidence. The checker rejects source changes
during the run. New files may be developed outside the checked closure, but
keep integrated inputs frozen until the check completes.

The default stricter command is required for a publication candidate:

```sh
python3 scripts/check_axioms.py
```

It must eventually cover all maintained sources. A focused pass is not an axiom
audit, source review, Comparator result, or independent kernel replay.

The workspace is not currently a publication Git repository. No repository
license/maintainer/remote or public commit has been chosen. No final
Challenge/Solution pair, Comparator pass, independent kernel replay, clean public
checkout verification, full Palomar mechanical report, submission, or registration
exists. Do not publish or describe this partial library as the requested verified
whole-paper candidate. Follow the local publication skill when ready.

## Lean details that saved time

- Use `Freezing1.activeCount` explicitly when integer `Freezing2.activeCount`
  is also imported.
- Module opacity sometimes requires `Function.comp_def` rather than
  `Function.comp_apply` inside `Tendsto` expressions.
- For a final `EventuallyLE`/a.e. inequality mismatch, `filter_upwards [hc]`
  followed by a pointwise `simpa` can avoid hidden instance reductions.
- `integral_dirac'` takes function, point, and strong-measurability proof.
- Sets use `mem_ae_iff_prob_eq_one`; predicate form has a different API.
- Use explicit subtype inclusion types when rewriting measure comaps/maps.
- `Real.sqrt_le_self_iff.mpr (Or.inr h)` is available; `Real.sqrt_le_self` is not.
- `Real.rpow_ofNat` handles literal numeral exponents; `rpow_natCast` may not
  match those literals.
- `field_simp`, `congr`, or simplification can already close a goal; remove
  redundant trailing tactics instead of adding more automation.

The original task remains open. The pause is the user's decision, not a claim
that the mathematics or publication preparation is finished.
