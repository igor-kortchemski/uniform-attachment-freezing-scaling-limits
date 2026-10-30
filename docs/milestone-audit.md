# Independent source reviews at formalization milestones

Date: 29 October 2026. This is an independent mathematical/source review by an
agent that did not write the declarations reviewed here, using
[lean-statement-audit](../.agents/skills/lean-statement-audit/SKILL.md).
The review is scoped to the modules below and their source-facing dependencies.
It is not independent kernel replay or a whole-paper completion review.

Source: [attachement-uniforme-2-final.tex](../attachement-uniforme-2-final.tex),
SHA-256 `23a485d5a5dfaca01a05db28377d015fb1456c194a543d0cbf56f77619ad0cbf`.
The independently reconstructed [inventory](source-inventory.md) contains all
23 named environments and the substantive prose/proof obligations. The manuscript
was not changed. The user-approved zero-diagonal correction to the supercritical
statement is distinguished from the original false formula.

## First milestone: verdict and coverage boundaries

At the first milestone, the reviewed finite definitions and source-facing theorem types preserve the
source's sign indexing, frozen-birth shift, finite counts, and surviving-walk
arithmetic. The uniform birth law is an exact realization of the named lemma
`lem:bunif` on the manuscript's deterministic label carrier, including its
extinction boundary. The weighted-walk modules prove finite identities and
bounds that support `lem:hnalpha`; **none of its five asymptotic assertions is
thereby proved**. The analytic Bennett module proves the monotonicity used in
`height=ok`; it does not prove Bennett's probability inequality or the graph
approximation theorem. The audit module proves abstract mathematical obstructions
and basic properties of the corrected star matrix; it does not prove the
supercritical scaling limit.

No hidden probabilistic estimate, convergence premise, or unfinished main result
is bundled into the reviewed finite assumptions. The source's random forward
and reverse tree constructions, equality in law, height laws, concentration,
scaling limits and metric-measure topology infrastructure remain separate
obligations. No GitHub/Palomar publication verdict follows from this review.

## First milestone: exact source comparisons

| Module / declarations | Source correspondence | Review result |
| --- | --- | --- |
| `Discrete/Walk.lean`: `IsSigned`, `activeCount`, `upSteps`, `downSteps` | Source 263–266, 464–466, 770 (`eq:pn`) | Positive-time indexing agrees: $S_0=1$ and $S_n=1+\sum_{i=1}^n x_i$. `x 0` is intentionally unconstrained and unused. `Finset.Ioc a b` is $(a,b]$. Counts are natural but signed differences use integers, avoiding truncated subtraction. |
| `twice_upSteps_card`, `twice_downSteps_card`, `twice_frozen_count`, `twice_vertex_count` | Exact combinatorial parts of source 478 and 770 | Correct doubled forms of the source's halves; endpoints and $a=b$ included. No asymptotic count is assumed. The vertex-count theorem counts one root plus attachment signs; identification with an implemented forward tree remains to be proved when that process exists. |
| `SurvivesThrough`, `activeCount_pos_of_no_zero`, `activeCount_nonneg_of_no_zero_before` | Source survival and $n\leq\tau$ boundary | `SurvivesThrough x n` includes positivity at $n$, suitable for $n<\tau$. In contrast, the no-zero-before theorem includes $n=\tau$ and derives nonnegativity, permitting zero at the terminal time. Skip-free signed increments and the initial value are used rather than assuming this consequence. |
| `activeCount_nat_cast`, `activeCount_nat_steps`, `activeCount_nat_up_iff`, `activeCount_nat_down_iff`, `activeCount_nat_pos` | Bridge to natural-valued path sums | On a surviving prefix, integer-to-natural conversion preserves all heights and exactly characterizes the original sign of each step. These ingredients are explicitly applied in `Discrete/Estimates.lean` to transport the finite identities and bounds to the paper's walk. No asymptotic conclusion is asserted. |
| `Discrete/Labels.lean`: `vertexLabels`, `birthTime` | Source 607–618 (`eq:labels`) | Disjoint sum prevents an active index from colliding with a frozen time. Frozen side is exactly ${i\in[1,n]:x_i=-1\}$; active side exactly indices $1,\ldots,S_n$. Frozen birth is $i-1$, active birth is $n$. Natural subtraction is safe because frozen labels have $i\geq1$. |
| `vertexLabels_card`, `vertexLabels_nonempty`, `early_vertexLabels` | Source 478, 638–641 | The total labels equal attachments plus one. Even at extinction the frozen side is nonempty. For every $m\leq n$, labels with birth strictly below $m$ are exactly freezing indices through $m$; active labels are excluded at $m=n$. |
| `uniformVertex`, `uniformVertex_isProbabilityMeasure` | Uniform vertex sampling in `lem:bunif` | Mathlib's actual uniform finite-set measure is used, with its probability property proved for nonnegative terminal count. The carrier is the source-defined deterministic label space, so this law does not require a prior random-edge construction. It does not establish Algorithm 2's existence or law. |
| `uniformVertex_birth_lt`, `uniformVertex_birth_lt_before_extinction` | Named lemma `lem:bunif`, source 637–643 | Exact formula $P(b_n(V)<m)=(m+1-S_m)/(n+1+S_n)$. The source-specialized wrapper assumes no zero strictly before $n$, which is equivalent to being at or before the first zero for a signed path started at one. Hence it covers $n=\tau$; zero terminal active labels are not excluded. The formal result also covers harmless boundary cases $m=0$ and $n=0$. |
| `Discrete/WeightedWalk.lean`: `weighted_crossing_balance`, `harmonic_crossing_balance` | Source global pairing 792–797 and interval argument 806–826 | Correct endpoint-potential telescoping on steps $(a,a+n]$. The source interval $[a,b]$ corresponds to starting time $a-1$ and length $b-a+1$ for $1\leq a\leq b$. This fixes the source's incorrect use of the post-step left height. Proof route is finite telescoping rather than the manuscript's minimum-height pairing. |
| `reciprocal_up_sub_down`, `reciprocal_balance_bound` | Source 812–825 | Exact correction and absolute bound use positivity of each arrival height. This follows from source survival. The endpoint potentials and reciprocal correction are explicit terms, not assumed small errors. No endpoint-dependent hidden constant occurs. |
| `harmonicPotential_eq_harmonic`, `harmonicPotential_le_one_add_log` | Logarithmic boundary estimate at 795, 817 | Reuses Mathlib harmonic numbers and logarithmic bound. The generic potential permits zero height and has zero at zero. The source's positive-height interval application is within the characterized domain. |
| `coalescence_crossing_balance` | Source 829–834 (`eq:lemme h point cinq1`) | The exact boundary is $1/S_a-1/S_{a+n}$ for a half-open time interval. Positive endpoint assumptions permit the closed-form potential. On a fully surviving source path every positive-step denominator $S_i(S_i-1)$ is nonzero. The generic formula permits intermediate zero heights under Lean's total inverse, so downstream source applications must retain the surviving-path characterization and must not infer a probabilistic hazard for such zero crossings. |
| `Discrete/Estimates.lean`: `activeCount_le_time_add_one`, `driver_harmonic_endpoint_bound`, `driver_reciprocal_pairing`, `driver_reciprocal_balance_bound` | Source 792–825 | Explicit specialization to the actual signed driver establishes the finite global reciprocal identity and an interval bound with a common $2(1+\log(N+1))$ correction for every interval inside the surviving horizon $N$. The remaining reciprocal error is explicit and still unbounded asymptotically. The source convention $[a,b]$ translates to the half-open interval $(a-1,b]$ as above. |
| `Analysis/BennettFunction.lean` | Source 681–683 and 904 | Definition of $g$ is exact; derivative and positivity are proved on valid domains. For fixed $t>0$, the exponent $xg(t/x)$ is decreasing on $x>0$, and its negative exponential increases with $x$. These are precisely the signs required by the paper's bound. Zero interval mean is outside the helper's domain and still requires a separate deterministic case in a future concentration proof. |
| `Audit/Obstructions.lean`: `additiveMatrix`, `starDistance`, metric properties | Source 411, approved correction | `additiveMatrix` records the uncorrected all-entry formula. `starDistance` has zero diagonal and keeps every off-diagonal sum. Nonnegative lengths give a pseudometric. Strict-positive-length separation is a helper; because the source root length is zero, that particular separation theorem is not yet the full rooted-star metric theorem. |
| `zeroDiagonal_of_tendstoInDistribution`, `not_tendstoInDistribution_additive_of_dist` | Source defect S01 | For varying probability spaces and finite matrix indices, evaluation is continuous, a zero diagonal survives weak convergence, and almost surely positive lengths contradict the additive all-entry limit. The source profile integral's strict positivity for uniform nonzero birth times is not separately established in this module; the obstruction theorem openly takes it as its mathematical hypothesis. This is not a conditional substitute for the corrected scaling theorem. |
| `measure_self_coalescence_eq_zero`, `oneStep_self_coalescence_formula_false` | Source defect S02 | Abstract self-coalescence consequence and the one-step numerical contradiction are correct. The concrete forest model has not been implemented; the source definition supplies the self-coalescence characterization in the explanatory audit. The theorems do not pretend to establish the corrected distinct-pair stochastic law. |
| `inclusive_reciprocal_self`, `inclusive_reciprocal_self_pos` | Source defect S03 | Substituting the same birth/coalescence index into the inclusive sums gives exactly $1/S_b$, positive for $S_b>0$. This establishes the algebraic defect in calling $D^n$ a metric; it leaves the uniform approximation theorem open. |

## First milestone: proof correspondence and departures

The counting proofs check the finite counting argument used in the manuscript.
The uniform birth-law proof checks the argument behind `lem:bunif` directly from
its source-defined label set; it does not depend on an unproved assumption about
a random tree. The harmonic/coalescence weighted identities follow the same
crossing-balance idea as the paper but use a telescoping potential, which makes
the correct boundary explicit. This is a substantive correction to the printed
interval equality at line 808. It does not validate that false equality.

The Bennett derivative calculation checks the monotonicity assertion at source
line 904 directly, using Mathlib calculus. The obstruction proofs verify why
the original supercritical all-pairs formula and inclusive-distance terminology
cannot be literal. The user-approved zero-diagonal correction has a faithful
basic encoding, but its proposed limiting random lengths and convergence remain
unproved.

## First milestone: reviewed source snapshot and mechanical evidence

The read-only review covered the following source bytes. This snapshot identifies
what was read; it is not a new frozen manifest or an axiom-evidence cache.
Changes to mathematical interfaces or proof routes require reassessment of the
affected findings.

| File | SHA-256 at review |
| --- | --- |
| `Freezing2/Discrete/Walk.lean` | `5bbc02bb258cf9a0370bbe6a50c3e34323cea6f485720d713cf195b899b33d74` |
| `Freezing2/Discrete/WeightedWalk.lean` | `5c442fb7c3bbc24f7bf8b38a2b305b9166b4669075b555c8b894eaa20a3ea4a9` |
| `Freezing2/Discrete/Labels.lean` | `ff6bfef6a58c6c824c48b8e0cc8f67950c56a56a7b32db14e5070cbab28415ec` |
| `Freezing2/Audit/Obstructions.lean` | `97c4ad0b2a72a29afd40eb343e2f1b988ad4c9f19f81d3efa81635cedca161bc` |
| `Freezing2/Analysis/BennettFunction.lean` | `69f265055545c2b10b91685fdc157af6960f393747ca22a6234029c653d9eb8a` |
| `Freezing2/Discrete/Estimates.lean` | `2731eec6501e150f60ae7592c7d88d57e95638365c74e9287f6990b0f1f752e2` |

Build and axiom checks were coordinated by the parent worker to avoid competing
writes to shared artifacts. At the first milestone those checks were pending;
the final parent-run evidence has since been inspected independently, as recorded
in the final section below. This reviewer did not independently rerun Lean. No Comparator,
full Palomar mechanical preflight, or independent kernel replay was supplied to
this reviewer, so those dimensions remain unverified here.

## Second milestone: exponential-decay estimates

Independent source/type review on 29 October 2026 adds
`Freezing2/Analysis/ExponentialDecay.lean`, SHA-256
`3560ea4abec340a28b1ca62aeda42bc7ee4bd9410a7fa533c88b396e216750a8`.
The parent reports a successful focused compile; the reviewer did not run a
competing build. The final section below records inspection of the parent's integrated
build and axiom logs.

The declarations prove genuine analytic limit claims, corresponding to the
last numerical step of the paper's union bounds, without assuming their
conclusions. For fixed real $k$ and positive constants $a,c$,
$x^k\exp(-cx^a)\to0$; natural-index and ordinary-polynomial versions are correct
specializations. The prefactors $2n^2$ and $(n+1)^2$ match source lines 910–915
and 940–950. The condition $\alpha<1/2$ yields positive exponent $1-2\alpha$;
the additional source condition $\alpha>0$ is unnecessary for this numerical
sublemma and is not silently removed from the stochastic theorem.

The geometric-floor estimate matches source lines 1065–1066: for fixed
$0\leq q<1$, $\varepsilon>0$, and real $M$,
$(n+1)^2 q^{\lfloor\varepsilon n\rfloor/2-M}\to0$.
Natural-number floor equals the ordinary floor on the nonnegative arguments
used. For $q=0$, the exponent is eventually strictly positive, so the proof does
not rely on a totalized meaning of an undefined finite-prefix power to justify
the source application. For $0<q<1$, the logarithmic comparison preserves the
correct inequality direction and a single constant independent of $n$.

Coverage added: the numerical decay portions of U16, U17 and U20. The preceding
probability bounds, uniform positive hazard coefficient, and the hypotheses of
the companion height theorem remain unresolved. No new main theorem or named
coalescence lemma is completed by these analytic estimates.

## Second milestone: Bernoulli concentration

The named export `Freezing2.bennett_inequality` in
`Freezing2/Probability/Bennett.lean` was independently compared with source
Proposition `prop:bennett` (679–684). **Its statement faithfully covers N05**.
The parent reports that its focused compile passed without warnings. The final module, including the absolute-deviation corollary, has SHA-256
`1af9bd38156af8eaaae13495d61add7432638f5b84007c0ccc121733dcc6851f`.
The parent also reports a successful focused compile of that final module
without warnings. The final section below records the parent's completed integrated build and
axiom check; additional publication checks remain unperformed.

The source's indices $1,\ldots,n$ are relabelled by `Fin n`. The parameters have
type `unitInterval`, the closed real interval $[0,1]$, so both deterministic
Bernoulli endpoints are retained. Inspection of the installed Mathlib definition
confirms that `bernoulliMeasure 1 0 p` gives mass $p$ to 1 and $1-p$ to 0.
`HasLaw` asserts that exact pushforward law and almost-everywhere measurability;
it contains no extra tail estimate. `iIndepFun` supplies the source's mutual
independence, without requiring equal parameters or identical distributions.

The real finite sum $m=\sum_i p_i$ is used consistently in both conclusions.
Its positivity and every $t>0$ are the source's assumptions. Both strict events
are retained: $\sum_iY_i>m+t$ and $\sum_iY_i<m-t$. There is no added restriction
$t<m$ for the lower tail. In particular, the boundary and negative-threshold
cases are covered. The conjunction supplies the two bounds for the same family,
mean, and deviation parameter rather than using unrelated witnesses.

The proof establishes exponential integrability from the Bernoulli laws,
computes each moment generating function, bounds the product using independence,
and applies Mathlib's upper and lower Chernoff bounds. Evaluation at
$\log(1+t/m)$ gives the displayed function $g(t/m)$. For the common lower-tail
bound it proves $e^{-s}+2s\leq e^s$ for $s\geq0$, which compares the two centered
exponents in the correct direction. These are checked proof steps rather than
extra premises. This proves the proposition by a standard MGF argument; the
manuscript states this Bennett variant without giving a proof, so there is no
manuscript derivation of N05 being independently reproduced here.

The added `bennett_abs_deviation` states the two-sided bound with factor 2 and
follows by a union bound on those same events. Its mathematical statement matches
the concentration ingredient at source lines 904–909. Applying it to a tree
height still requires the unproved Bernoulli-sum representation and, for an
interval of zero mean, an explicit deterministic case. Neither the random-tree
model nor N07 is completed by this theorem.

The second milestone source review is closed for the recorded source bytes.
No source-fidelity defect was found in these additions. N05 is covered by an
exact source-matching export; U16 has an additional two-sided Bernoulli bound.
The main scaling theorems and the prior unresolved obligations remain open.

At second-milestone closure, `Labels.lean` was reread after a proof-only edit to
`early_vertexLabels` (explicit finite-set extensionality). The definitions,
theorem statements, and finite-counting route are unchanged; the snapshot hash
in the first table is refreshed to the reviewed final bytes. All other entries
in that table remain unchanged.


## Second milestone: integrated evidence inspection

This section records the eight-module snapshot checked before the subsequent
population-profile work. Its counts and matching-source assertions refer to
that historical snapshot; they do not certify the later modules below.

On 29 October 2026 this independent source reviewer read the actual parent-run
[evidence/build.log](../evidence/build.log),
[evidence/axioms.log](../evidence/axioms.log),
[evidence/check-context.txt](../evidence/check-context.txt), the entry module,
and the checker source. The reviewer then performed a separate **read-only
inspection of these files**, without rerunning the build:

- The dependency-aware `lake build` completed successfully and reported 3,719
  jobs. This is an integrated incremental build, not a claim that every job was
  rebuilt from scratch. The entry module imports all eight implementation
  modules, so the default target includes the full maintained library.
- The parent-run `python3 scripts/check_axioms.py` build/probe completed with
  `PASS: 117 definitions/theorems`. Independent parsing confirmed that its
  reported declarations exactly match the current explicit declaration scan.
  Every printed transitive axiom closure is contained in
  `{propext, Classical.choice, Quot.sound}`. In particular, neither `sorryAx`
  nor a native-evaluation axiom appears in any of those closures.
- The 13 proof, entry-module, toolchain, Lake-configuration, manifest, and
  checker SHA-256 entries in the context file all match the current files.
  The eight module hashes also agree with the source-review snapshots above.
  The manuscript remains the same source version as the initial inventory.
- The exact source-facing exports `uniformVertex_birth_lt_before_extinction`,
  `bennett_inequality`, and `bennett_abs_deviation` occur in the checked axiom
  output. Finite helper and obstruction declarations are included as well.

Thus the current Lean build and the reported transitive axiom checks **pass**
for the recorded local source state. The checks were executed by the parent;
this reviewer independently checked their supplied evidence and its source
identity. The mathematical review above is independent of the declaration
writers. Neither activity is human peer review or independent kernel replay.

No Comparator execution, clean public-checkout verification, full Palomar
mechanical report, public Git commit, submission, or registration was supplied.
Those claims remain unverified. The evidence does not prove missing source
claims, repair the unresolved manuscript arguments, or turn the partial library
into a complete verified publication candidate.

## Third milestone: population-profile source review

Review date: 29 October 2026. The reviewer for this section did not author
`PopulationProfile`, `StepProfile`, `LocalL1`, `ProfileIntegrals`,
`SublinearPopulation`, `ReciprocalCorrection`, `ProfileCorrection`,
`HarmonicAsymptotics`, `HarmonicConclusions`, `SquareL1`,
`LocalSquareProfiles`, `SmallSetL1`, `PopulationMinimum`,
`InteriorMinimum`, `InteriorMinimumLimit`, `SquareCorrection`, or
`MeshIntervals`. The mathematical findings for those modules are independent
source review. The reviewer did author `SourceHypotheses`, `SignCounts`,
`IntervalWeakConvergence`, and `SignMeasures`; those four modules require the
separate review coordinated by the parent and are not independently certified
by this section.

The source SHA-256 was recomputed and remains
`23a485d5a5dfaca01a05db28377d015fb1456c194a543d0cbf56f77619ad0cbf`.
The previously reconstructed full inventory remains applicable. This milestone
reviews changed results and affected dependencies; it does not repeat or claim
a new whole-paper omission scan. The local-square equivalence and minimum
remark at source line 325 are **U03** in that inventory. U01 concerns different
tree specializations and remains an independent obligation.

### Definitions and source assumptions

`reciprocalProfile x α n t` is exactly
$n^\alpha/S^n_{\lfloor nt\rfloor}$, integrated against Lebesgue measure
restricted to $[0,1]$. The floor convention agrees with source line 309.
`integrable_reciprocalProfile` proves integrability of every finite mesh
profile, including horizon zero. Consequently the absolute-integral condition
in `HasL1ReciprocalProfile` is genuine $L^1$ convergence; a totalized integral
cannot make a nonintegrable profile satisfy the intended hypothesis.

`PositiveProfile g` requires $g>0$ almost everywhere. In the source
specialization $g=1/f$, this expresses the finite positive reciprocal required
by the manuscript while permitting zeros of $f$ at endpoints or other null
sets. Without this condition, interpreting Lean's reciprocal of zero as zero
would admit different mathematics. The stronger N06(i) theorem correctly needs
only $\alpha<1$ and global $L^1$ convergence to this positive limit; neither
$\alpha>0$ nor the local square-moment assumption is used in its proof.

`HasLocalSquareMomentProfile` retains the hypothesis actually printed at
319–322: for every $0<a<b<1$, the squared reciprocal limit is integrable on
$[a,b]$ and the integrals of the squared mesh profiles converge to its integral.
It does **not** assume $L^1$ convergence of the squares. That implication and
its converse are proved. The local integrability clause is the standing
$1/f\in L^2_{\mathrm{loc}}((0,1))$ condition at line 314, not a new estimate.
Closed versus open integration endpoints do not change the Lebesgue integrals;
the code retains the original mesh value at time one and handles null endpoints
through proved integral identities.

### Changed conclusions and affected dependencies

| Modules / principal exports | Source obligation | Independent mathematical finding |
| --- | --- | --- |
| `PopulationProfile`: `activeCount_floor_lower`, `reciprocalProfile_le_of_spike`; `SublinearPopulation`: `population_sublinear_at` | N06(i), U11, S05 | The skip-free estimate includes the floor-rounding loss. A fixed interval $[a-\min(a,\varepsilon)/4,a]$ has positive measure and gives a vanishing reciprocal upper bound under a macroscopic spike. Its limiting integral is positive by `LocalL1`, yielding the required contradiction. The smaller interval repairs S05; the inadequate printed range is not certified. |
| `StepProfile`; `ProfileIntegrals`: `integral_reciprocalProfile`, `harmonicTotal_profile_difference`, `tendsto_normalized_harmonicTotal` | N06(iii), U12–U13 | The integral uses indices $0,\ldots,n-1$, while the source harmonic sum uses $1,\ldots,n$. Their exact difference is $(n^\alpha/n)(S_n^{-1}-1)$, whose absolute value is at most $n^\alpha/n$ under survival. Thus no endpoint is silently discarded. |
| `ReciprocalCorrection`; `ProfileCorrection`: `tendsto_reciprocalErrorTotal`, `tendsto_rpow_mul_reciprocalErrorTotal` | U13, source 798–804 | The scalar map $u\mapsto u^2/(c+u)$ is nonnegative, bounded by $u$, and has Lipschitz constant one on nonnegative inputs for $c>0$. Contraction plus dominated convergence proves the vanishing correction. Both source normalizations and the one-based sum are exported with the mesh shift proved. |
| `ProfileCorrection`: `driver_reciprocalErrorSum_le_total`; `HarmonicAsymptotics`: `harmonicInterval_deviation_bound`, `eventually_uniform_harmonic_balance` | N06(iv), U14, S06 | Every interval error is bounded by the same full-horizon nonnegative correction and logarithmic endpoint term. The eventual quantifier precedes both interval endpoints, so the conclusion is genuinely uniform. Natural-height and signed-step representations are connected by proved survival bridges. |
| `HarmonicConclusions`: `harmonicDeviationMax`, `tendsto_harmonicDeviationMax` | N06(iv) | The finite maximum enumerates exactly all inclusive intervals $1\leq a\leq b\leq n$, using start $a-1$ and length $b+1-a$. Invalid pairs contribute zero; since every valid error is nonnegative, these extra entries do not change a positive-horizon maximum. The exported normalization is the printed division by $n^{1-\alpha}$. |
| `HarmonicConclusions`: `reciprocalProfile_integral_pos`, `harmonicTotal_asymptotic`, `harmonicUpTotal_asymptotic` | N06(iii) | Strict positivity of the limiting integral is proved before converting convergence into the two source asymptotic equivalences. The source's symbol $\sim$ is not weakened to convergence to a possibly zero limit. |
| `SquareL1`: `tendsto_second_moments_iff_l1_squares`; `LocalSquareProfiles`: `hasLocalSquareMomentProfile_iff_l1_squares` | U03, source 325 | The forward implication derives convergence in measure from $L^1$, extracts almost-everywhere convergent subsequences, and applies dominated convergence to $\min(q_n^2,g^2)$. The identity $|q_n^2-g^2|=q_n^2+g^2-2\min(q_n^2,g^2)$ supplies the conclusion. The reverse implication follows by controlling integral error. Every required integrability premise is explicit and supplied for the mesh profiles. |
| `SmallSetL1`: `tendsto_integral_on_small_sets_of_l1` | Moving-set step in U15 | For varying sets whose measures tend to zero, the fixed integrable limit has vanishing set integral and the family-limit difference is bounded by its global $L^1$ error. No nesting, sign, or finite-total-measure assumption is hidden. |
| `PopulationMinimum`: `population_window_integral_lower_bound`, `tendsto_rpow_reciprocal_population_of_sublinear` | Mechanism of U15, `eq:cvminSinfini` | The finite lower bound and moving-window argument are correct. The final helper openly assumes a selected interior population is sublinear; it does not present that premise as part of the original source theorem. `InteriorMinimum` supplies the intended minimum selection and sublinearity. |
| `InteriorMinimum`: `interiorMinimizer_mem`, `interiorMinimizer_min`, `eventually_interiorMinimizer_window`, `interiorMinimizer_population_sublinear` | Minimum selection in U15 | The selection minimizes over exactly the integer inequalities $an\leq k\leq bn$ inside the horizon. A fixed midpoint proves eventual nonemptiness and bounds the minimum by a fixed-time population. Default index zero is used only for empty windows; eventual membership and actual minimality are proved, so the default cannot bypass the minimum argument. |
| `InteriorMinimumLimit`: `tendsto_scaled_reciprocal_interiorMinimum`, `tendsto_interiorMinimum_atTop` | U15 minimum estimate and U03 minimum-divergence remark | The wrapper supplies every selected-sequence premise of `PopulationMinimum` using the genuine minimizer. Thus $n^{2\alpha-1}/\min S\to0$ is obtained without assuming the minimum estimate. For $\alpha\geq1/2$, $n^{2\alpha-1}\geq1$ eventually, so the reciprocal minimum tends to zero; strict positivity then gives divergence to infinity. |
| `SquareCorrection`: `squareCorrection_div`, `tendsto_integral_abs_sq_profile_sub_shifted`, `tendsto_integral_abs_shiftedSquareProfile_sub_local` | Part of U15 denominator approximation | With $c=n^\alpha$ and $u=c/S$, the exact error between $c^2/S^2$ and $c^2/[S(S+1)]$ is $u^3/(c+u)$. It is bounded by $u^2$ and controlled by $2|u^2-v^2|+8v^3/(c+v)$, with constants independent of $c>0$. Local $L^1$ convergence of squares and dominated convergence give a negligible error; a proved triangle bound gives the same limit $g^2$ for the shifted profile. This does not yet cover the positive-step denominator $S(S-1)$ or the full uniform conclusion. |
| `MeshIntervals`: `integral_stepProfile_meshInterval`, `integral_stepProfile_inclusive_meshInterval` | Endpoint bookkeeping in U15 | Integration over $[a/n,b/n]$ corresponds to indices $a,\ldots,b-1$; the inclusive source sum through $b$ instead ends at $(b+1)/n$. The finite-cell decomposition proves these identities even for reversed or empty index intervals. The remaining endpoint integral must still be shown uniformly negligible in N06(v). |

No mathematical defect was found in these reviewed interfaces or routes.
The latest mechanical completion of the modules is a separate check, recorded
below rather than inferred from this source comparison.

### The precise departure in the minimum argument

The formal proof replaces the manuscript's auxiliary sequence $\eta_n$ and
asymptotic reciprocal-square summation at lines 840–847. At a selected integer
time $k$, let $M=S_k$, a positive integer under survival. For the next $M$ steps,
the skip-free estimate gives $S_j\leq2M$. Once $k+M\leq n$, the corresponding
closed mesh window satisfies

$$
\int_{k/n}^{(k+M)/n}
\left(\frac{n^\alpha}{S_{\lfloor nt\rfloor}}\right)^2\,dt
\geq \frac{n^{2\alpha}}{4nM}.
$$

This is an exact bound with constant $1/4$; no asymptotic evaluation of a
reciprocal-square series is assumed. If $M/n\to0$ and $k/n$ stays in a fixed
interior interval $[a,b]$, the window has length $M/n\to0$ and eventually lies
inside the fixed larger compact interval $[a/2,(b+1)/2]\subset(0,1)$.
Local $L^1$ convergence of the squares and `SmallSetL1` then force its integral
to zero. This proves $n^{2\alpha-1}/M\to0$ for the selected sequence.
For a minimizing sequence, comparison with the fixed midpoint supplies
$M/n\to0$; it is not an added assumption of the intended minimum conclusion.

This checks the paper's skip-free shrinking-window mechanism while replacing
the $\eta_n$ selection and reciprocal-square asymptotic calculation. Those
literal displayed steps are bypassed, not separately verified. The later
`InteriorMinimumLimit` wrapper was also read and correctly composes the minimum
selection and window theorem; its mechanical validation remains part of the
parent's integration below. The minimum-divergence wrapper treats
$\alpha\geq1/2$ as described in the table. These results use nondegenerate
fixed interior windows $0<a<b<1$; empty or single-point cutoff ranges in the
final maximum require their own boundary treatment.

The $S^2$-versus-$S(S+1)$ correction is supplied by `SquareCorrection`, but the
$S(S-1)$ positive-step replacement, uniform local sum/integral approximation,
and maximum in N06(v) remain separate obligations at this snapshot.

### Third-milestone evidence boundary

The parent and proof workers report successful focused checks for the profile,
correction, square-convergence, and population-window modules. The reviewer
personally ran successful focused checks for the four modules it authored,
which is mechanical evidence but does not make their source review independent.
At the writing of this section, the parent's current `HarmonicConclusions`
integration and the first `InteriorMinimum` check were pending. The parent is
responsible for recording their final diagnostics, importing all completed
modules into `Freezing2.lean`, and refreshing the integrated build and transitive
axiom evidence for the same final source bytes.

The historical 117-declaration check above does not cover these additions.
No current full-build or axiom-pass claim is made for the expanded library by
this section. Likewise, these findings are not Comparator evidence, independent
kernel replay, a full Palomar mechanical report, or a whole-paper completion
verdict. All unchanged unresolved inventory entries, including the main scaling
results, remain in scope.

### Recorded population-profile integration

After the review above, the parent integrated N06(i)–(iv), the local square-profile
equivalence, and the concrete interior-minimum estimate. `lake build` exited 0
(3,740 jobs). A fresh batched probe imported that entry point and queried every
explicit declaration in its 28 directly imported proof modules: **257 declarations
passed**, with only `propext`, `Classical.choice`, and `Quot.sound` in their
transitive axiom closures. The output and exact checked source/configuration
hashes are in [profile-milestone-axioms.log](../evidence/profile-milestone-axioms.log)
and [profile-milestone-context.txt](../evidence/profile-milestone-context.txt).
The axiom probe does not certify ongoing modules outside that snapshot.
The review findings for unchanged declarations remain applicable; additions
for the full N06(v) conclusion require subsequent integration and review.

## Fourth milestone: the main height theorem and its companion dependency

This review independently reread the source hypotheses at lines 308–325 and
Theorem `thm:heightalpha` at lines 331–338 (M01), together with the actual
declarations in `MainResults/Height.lean`, `Probability/CompanionModel.lean`,
`Analysis/HeightNormalization.lean`, and `Analysis/LpScaling.lean`. It also
checked the companion Theorem `thm:height` (III) at lines 293–309 of
`attachement-uniforme-1-final.tex` and the semantic dependency closure of its
new maximum-height proof. The reviewer did not author these mathematical
modules or the original companion proofs; its mechanical copying of the
companion sources did not change their statements or proof bodies.

The scaling-paper SHA-256 was recomputed and is still
`23a485d5a5dfaca01a05db28377d015fb1456c194a543d0cbf56f77619ad0cbf`.
The full inventory is retained unchanged. This is a review of changed results
and affected dependencies, not a whole-paper completion or omission-scan claim.
The exact companion snapshot, complete module hashes, source hash, license,
and import relocation are recorded in [companion-provenance.md](companion-provenance.md).

### Exact source conclusion and premises

`height_scaling_limit_source` retains the printed denominator
$n^{1-\alpha}$, the limiting constant
$\int_0^1 1/(2f(t))\,dt$, and every finite real exponent $p\geq1$.
Its conclusion is convergence to zero of the error `eLpNorm` under
`freezingTreeLaw x n`. This is the required $L^p$ convergence to a deterministic
constant, with the actual probability measure allowed to depend on $n$; it
does not require an artificial common coupling. The general
`height_scaling_limit` uses a positive reciprocal limit $g$ and constant
$(\int g)/2$. `reciprocal_half_integral` proves the exact source-integrand
identity for $g=1/f$.

The hypotheses retain signed schedules, survival through each horizon,
$0<\alpha<1$, a finite positive profile almost everywhere, and genuine global
reciprocal $L^1$ convergence. They contain no concentration, moment, growth-rate,
or tree-height estimate. `HasL1ReciprocalProfile` includes integrability of the
limit, while integrability of each mesh profile was proved separately. The
source's additional local square-moment condition is unused: this proves a
stronger height statement, not a conditional replacement for M01. Measurability
outside $[0,1]$ is immaterial because the profile measure is restricted Lebesgue
measure. Almost-everywhere positivity permits endpoint zeros without treating
Lean's total reciprocal at zero as a positive reciprocal on a set of positive
measure.

`height_scaling_limit_positive_horizons` removes the unused zero-row condition
from `AdmissibleArray`. It applies the canonical all-up zero-row extension and
then transports the conclusion back to the **original** tree laws by eventual
row equality. Its premise asks for signedness and survival only for $n>0$,
exactly as in the source. The review of this new wrapper is independent; the
older `SourceHypotheses` extension helpers were authored by this reviewer and
retain their separately coordinated review status.

### Tree semantics and proof dependencies

| Export or dependency | Source-fidelity finding |
| --- | --- |
| `companionSchedule_value`, `companion_activeCount` | Boolean `true` means exactly an integer $+1$ step. The two integer walks agree by their zero value and successor recurrence; only positive sign indices are used. The value of either schedule at index zero is irrelevant. |
| `companion_before_extinction` | Survival translates to the companion's exact condition $n<\tau$, using its proved first-zero characterization. It is not replaced by positivity only at the final time. |
| `companion_heightScale` | The normalizing sum is exactly $\sum_{i=1}^n S_i^{-1}\mathbf{1}_{\{x_i=1\}}$, with the population after each step. It equals `harmonicUpTotal` without an asymptotic endpoint correction. |
| `freezingTreeLaw`, `freezingTreeLaw_valid` | The law iterates uniform choice among currently active vertices through attachment/freezing transitions. Validity of the finite rooted tree is proved almost surely. Absorbing empty states are irrelevant under the supplied survival condition. |
| `treeHeight_le_iff_graph_distance` | The statistic is characterized as the maximum root distance in the finite induced graph, including both active and frozen vertices. This uses the proved companion identity `ValidAt.height_eq_tree_dist`; the result is not about an unrelated numerical height process. |
| `harmonicUp_limit_pos`, `tendsto_harmonicUpTotal_div_rpow` | The limiting deterministic scale is finite and strictly positive. The printed polynomial denominator is recovered through valid positive-horizon real-power identities. |
| `tendsto_log_div_harmonicUpTotal` | The companion's required $\log(n)/h_n^+\to0$ is proved from polynomial normalization and $\alpha<1$, rather than added to the M01 hypotheses. Eventual nonzero denominators are supplied before rescaling. |
| `Freezing1.maximum_height_tendsto_Lp` | The companion statement has only survival, logarithmic negligibility, and $p\geq1$ as substantive premises. Actual forward MGF bounds provide its tails and higher moments. No unproved Bernoulli representation, reverse-law identity, or generic concentration hypothesis is used. |
| `tendsto_eLpNorm_change_normalization` | A proved triangle inequality transfers convergence using the deterministic ratio of scales. Probability-measure constant norms and finite scalar norms justify the extended-real arithmetic, including the limit when the error norm tends to zero. |

No source-statement mismatch or hidden assumption was found in these exact
declarations and their reviewed semantic dependencies. The source's suggested
combination of companion height concentration with harmonic asymptotics is
implemented. The proof of that companion concentration is a substantive
alternative: direct forward active-height averaging and total exponential
vertex weights replace the reverse-forest Bernoulli representation. Bennett
tails, Jensen's inequality, and a cutoff/Hölder argument give all real finite
$L^p$ limits. The finite $n+1$ vertex factor and one-edge shift remain explicit
until the asymptotic estimates absorb them. This checks the resulting height
theorem, but does not check the manuscript's reverse construction or equality
in law. N01–N04/E03 and the other corresponding source obligations remain open.

### Fourth-milestone evidence boundary

The parent reports that the fresh destination build of the 16-module companion
closure through `Freezing2.Companion.MainMaximum` passed with exit 0, 3,788 jobs,
and no warnings. The sibling checkout was neither edited nor built. At the
writing of this review, compilation of the new model bridges and final height
wrappers is still running, and the fresh transitive axiom audit has not yet
been reported. Therefore this section approves statement fidelity and records
the dependency build; it does **not yet** declare M01 mechanically certified.
The parent must append the final build and permitted-axiom evidence for the
same final source bytes before recording M01 as proved.

No result here proves the metric scaling limits M02, M03, or later main results.
All other unresolved inventory entries remain in scope, and neither the
companion build nor this review is Palomar Comparator evidence or a complete
publication verification report.


### M01/N06 mechanical integration

The parent’s current integration built all 54 imported modules successfully
(3,810 jobs). The complete axiom probe covered 535 explicit definitions and
theorems, including M01 and the companion dependency closure, with only the
three permitted axioms. Two long axiom lists wrapped across lines; the checker’s
parser was repaired, and the successful Lean output was revalidated against all
captured proof hashes. See `evidence/axioms.log` and `evidence/check-context.txt`.
This establishes the local mechanical checkpoint; it is not Comparator,
independent kernel replay, or full Palomar verification. Later files require
new evidence.

## Fifth milestone: joint reverse laws and their analytic consumers

The source SHA-256 remains
`23a485d5a5dfaca01a05db28377d015fb1456c194a543d0cbf56f77619ad0cbf`.
The unchanged full inventory is retained. This review reread N02/E03 at source
lines 622–634, N04 at lines 645–649, N07 and its proof at lines 882–916, and N08
at lines 930–952. It does not certify the remaining inventory.

The milestone reviewer wrote `ReverseHistory`, `ReverseConditional`,
`ReverseHeightIncrements`, `ReverseObservations`, `ReverseLegalSteps`, and the
new paper-facing wrapper. Their descriptions below are authorship records and
self-review, not independent review. The parent independently reviewed the
joint law, conditional expectation, adaptedness, and support-transfer interfaces.
The following reviews of `ConditionalBernoulli`, `ReverseHeightLaw`,
`ReverseHeightConcentration`, `CoalescenceHistory`, and `SubcriticalCoalescence`
are independent of their authors.

### Independence and the actual height law

`Freezing2.iIndepSet_of_condExp_indicator` (at
`Probability/ConditionalBernoulli.lean:50`) assumes
only measurability when each event is revealed and a deterministic conditional
indicator expectation given the preceding filtration. Finite-intersection
induction factors the event with maximal index against earlier measurable
events. The conversion from real probabilities to extended nonnegative
probabilities uses finite probability mass. Independence is derived rather
than assumed.

`ReverseHeightLaw.lean` applies this theorem to the constructed reverse history.
Events before a vertex's birth and after the construction horizon are empty.
The deterministic event probability is identified with its source expression;
the `unitInterval` parameter is not left as an unspecified probability. Actual
kernel support proves that each height increment is zero or one. Active labels
start at depth zero, and every frozen label is inserted at depth zero. The
telescoping identity `heightAt_eq_sum_heightBernoulli` at line 285 therefore
covers the empty sum at birth, including birth time zero. The reindexed sum
uses exactly the source indices $(a,\operatorname{birth}(v)]$. Independence
is proved separately for each fixed vertex's increments; no independence
between different vertices is required or asserted.

The recorded source issue S04 requires an endpoint interpretation. At
$n=\tau$, the last step is a freezing step and $S_n=0$, so the manuscript's
description of an unmasked Bernoulli variable with parameter $1/S_n$ is
undefined. The formalization gives freezing increments Bernoulli parameter
zero. This proves the meaningful masked sum and retains the extinction
endpoint; it does not validate an undefined all-index parameterization.

`tendsto_reverseHeightErrorMax` at
`Probability/ReverseHeightConcentration.lean:86` discharges the concentration
engine's former model premises using these actual laws, exact deterministic
means, and the proved label bijection. Its index family contains every vertex
and every source time through its birth, including both zero and the birth
endpoint, and has cardinality at most $(n+1)^2$. The inclusive harmonic centre
and its endpoint discrepancy are handled by the established deterministic
recentering result. Only the global reciprocal $L^1$ assumption is needed for
this height component, which is stronger than using the paper's additional
local square assumption. The graph-distance identity needed to complete N07
remains separate; this height maximum alone is not N07.

### The corrected coalescence law

`Probability/CoalescenceHistory.lean` defines coalescence as a finite maximum
over source phases at which both labels are present. The apparent zero default
is justified on actual histories by terminal connectivity. The explicit
`root_eq_iff_reachable` lemma in `CoalescenceTransition` proves that root equality
means graph connectivity. Membership, monotone coarsening, and the maximum
characterization are established almost surely from the actual transition law.

`jointLaw_distinct_at_commonBirth` at line 254 supplies the survival recursion's
initial condition. Equal terminal birth times are handled by the isolated
initial forest. A smaller birth time identifies its unique frozen label, and
fresh insertion separates it from every older component. Distinct frozen
labels cannot have equal subterminal birth times. These cases also cover the
extinction horizon.

`coalescenceTime_probability` at line 427 and
`sourceCoalescenceTime_probability` at line 511 have precisely the required
hazard at $c+1$ followed by the survival product from $c+2$ through the common
birth phase. The binomial conversion and the original integer-sign/one-based
label conversion preserve the populations and endpoints. No conditional law,
Markov property, or independent-merger model is assumed. The distinct-label
premise is the recorded S02 correction to the printed N04 statement. The
separate diagonal theorem gives
$\operatorname{coal}(u,u)=\operatorname{birth}(u)$ and prevents counting the
incorrect printed diagonal formula as proved.

### The deterministic part of fast coalescence

`Analysis/SubcriticalCoalescence.lean:148` proves a positive polynomial lower
bound uniformly over all macroscopic windows. It clips each window into
$[\varepsilon/8,1-\varepsilon/8]$, retaining length at least $\varepsilon/2$
after rounding. Continuity of the integral primitive on this compact region
and almost-everywhere positivity provide a single positive lower bound
independent of the window and the row. The inclusive coalescence sum and its
factor $1/2$ agree with N06(v).

This repairs a substantive endpoint step in the manuscript: its direct use of
local N06(v) on windows ending at $1$ is not justified by the local hypothesis.
The clipping argument supplies the needed uniform interior estimate.
`eventually_uniform_floor_coalescence_bound` at line 270 explicitly absorbs
the floor error. The resulting $(n+1)^2$ exponential bound is deterministic;
the actual N04 survival law and a probabilistic union bound must still be
combined before recording N08 as complete.

### Further independent distance and sampling review

`Discrete/ForestDistances.lean`, `Probability/ForestGeometry.lean`, and
`Probability/DistanceApproximation.lean` were reviewed against N07 and U16.
At the first merger, the old root paths are disjoint because their roots
differ; the unique added edge joins them into the required path. Acyclicity
then identifies its length with graph distance. Subsequent acyclic graph
growth preserves that distance. This gives the exact sum of heights at the
coalescence phase without assuming an ancestor identity. The diagonal is
proved separately from zero depth at birth. The inclusive harmonic expression
retains its nonzero diagonal and is not claimed to be a metric.

The all-pairs error is bounded by twice the actual height-error maximum,
including birth endpoints. The probability squeeze with threshold
$\varepsilon/2$ establishes the uniform approximation on the actual reverse
history, using only the global reciprocal $L^1$ condition. The conservative
family bound $(n+1)^2$ verifies the corresponding Bennett union bound; this
does not check the manuscript's exact printed coefficient $2n^2$ in
`4/9/14h`. The final `forest_toGraph_dist_eq` bridge was independently reviewed:
every ambient walk stays within the forest's actual vertices, its induced
walk has the same length, and finite-graph walks map back without length
change. Disconnected totalized distances are treated consistently. This
closes the finite-tree metric representation gap. The positive-horizon
source-profile wrapper transports both the row and its actual measure by
eventual equality. The parent reports a warning-free final focused check.
Forward-tree N07 still requires N01 law transport and remains distinct from
this reverse construction result.

`Probability/BirthTimeLimit.lean` proves the CDF of normalized birth time using
the frozen-count endpoint $\lfloor na\rfloor+1$ for $0\leq a<1$. Thus the
frozen-label minus-one shift and the active atom at time one are retained.
The total-count normalization tends to one after multiplication by $2/n$;
the CDF outside $[0,1]$ and total probability are checked. This yields weak
convergence of the actual uniform-label birth distribution to uniform
Lebesgue probability. The time-zero totalized division affects only the
initial term of the sequence. `Probability/VertexSampling.lean` proves the
exact two-sample collision probability $1/|\mathbb V_n|$, including the
one-vertex case, and its vanishing limit. It addresses S07 without treating
independent samples as automatically distinct. These declarations alone do
not prove fixed-$k$ joint birth convergence or the later continuous-mapping
arguments for distance matrices.

### New joint-history evidence boundary

`ReverseHistory` constructs Mathlib's trajectory measure from the actual
uniform-root-pair kernels, proves its probability property and every coordinate
marginal, and retains the extinction endpoint. `ReverseConditional` derives
the full-prefix conditional transition formula, transition-event adaptedness,
kernel-support transfer, and the tower transfer to smaller observations.
`ReverseObservations` reconstructs edge labels from adjacency changes, and
records vertices, roots, adjacency, and labels without auxiliary parent/depth
fields. `ReverseLegalSteps` proves that the sampled history starts edgeless and
simultaneously follows the actual graph actions used by that reconstruction.
No extra labelling randomness or assumed history law is added.

Focused checks passed without warnings for these history, conditional,
increment, observation, legal-step, original-label N02, and actual uniform-label
N03 modules. The parent has reported coordinated destination builds through
`ReverseLegalSteps`, `ReversePaper`, and `ReverseUniformVertex` (the last build
completed with 3,861 jobs). The independent reviews above concern source
fidelity and proof correspondence. Their authors' focused passes, the parent's
integration builds, and a fresh complete transitive axiom audit are distinct
evidence obligations. The preceding 54-module/535-declaration checkpoint does
not certify these new files. Comparator and full Palomar verification remain
outstanding, as do N01 and the remaining mathematical inventory.

### Parent's independent N08 assembly review

After the analytic review above, the parent independently read the full
`Probability/SubcriticalCoalescenceLaw.lean` implementation. It derives the
actual survival bound from the proved N04 law and hazards bounded by one,
handles the diagonal and short common births separately, and uses the window
$\lfloor\varepsilon n/2\rfloor$ so the strict tail inclusion remains valid
when $\varepsilon n$ is an integer. The surviving window has length at least
$\varepsilon n/4$ eventually. The union uses the actual ordered-pair count,
bounded by $(n+1)^2$. The maximum's natural subtraction is characterized as
the absolute birth-minus-coalescence gap, and the positive-horizon wrapper
uses the original source profile assumptions.

The parent found no mathematical mismatch in these declarations. A duplicate
local-square initial-row-extension helper was identified for removal in favor
of the existing `PopulationLemma` result; this is an integration edit requiring
a fresh consumer check. The file author's focused check passed without
warnings. Current integration and axiom evidence remain the parent's separate
responsibility. This advances the full actual reverse-process N08 statement;
it is no longer only a deterministic hazard estimate. Transport to a forward
tree formulation still requires N01.

### Independent supercritical hazard review

The parent-authored `Analysis/SupercriticalCoalescence.lean` was independently
reviewed against N10/U21. The uniform N06(v) error bound and the integral of
$g^2$ on one fixed compact interior interval bound twice the unscaled hazard
sum by $(2+K)/C_n$, where $C_n=n^{2\alpha-1}\to\infty$. This proves the
exported uniform vanishing estimate without applying a local hypothesis at
either endpoint. The explicit $O(n^{1-2\alpha})$ formulation in U21 is stronger
than the currently exported vanishing statement and remains a distinct
coverage item unless an appropriate rate declaration is exported. The new
sampled-law assembly is authored by this milestone reviewer; any review of
that assembly recorded as independent must come from another reviewer.

### Independently reviewed N10 sampled-law assembly

The `profile_correction` reviewer independently read the completed
`Probability/SupercriticalCoalescenceLaw.lean` and `ProductEventBound.lean`.
The milestone reviewer authored both files and does not count this as
self-independent review. The independent review found no source or dependency
defect in the actual product law of one reverse history and two independent
uniform labels.

The bad-sample split retains the exact collision contribution
$1/|\mathbb V_n|$. A late first birth safely bounds a late common birth; its
limit is $\delta$ rather than the manuscript's sharper $\delta^2$. This
weaker bound still vanishes when the auxiliary cutoff tends to zero. For
distinct interior pairs, the proof uses the exact N04 survival product,
$1-\prod(1-p_i)\leq\sum p_i$, and the local window beginning at
$\lfloor\varepsilon n\rfloor+1$. Its inclusive hazard indices agree with
the supplied N06(v) estimate. Product integration averages these genuine
section probabilities over the independent samples. The normalized absolute
event is equivalent at every positive horizon, and the source-facing wrapper
requires admissibility only for positive rows and uses $g=1/f$.

The final focused check of the complete file passed with exit 0 and no
warnings. Coordinated destination integration and its current transitive
axiom audit remain separate. The checked route adds the S07 collision term
and uses a weaker late-birth bound; it does not certify the manuscript's
uncorrected application of a distinct-label formula to repeated samples or
its exact displayed late-birth asymptotic. This establishes N10 under the
actual reverse construction while retaining those intermediate coverage
distinctions.


## Sixth milestone: noncritical dependencies and the rooted M06 candidate

### Current checked dependency closure

The coordinated integrated check recorded in
[`noncritical-dependencies-context.txt`](../evidence/noncritical-dependencies-context.txt)
completed with 3,937 build jobs and an axiom scan of 1,115 explicit definitions
and theorems in 104 integrated modules. The corresponding
[`axiom log`](../evidence/noncritical-dependencies-axioms.log) permits only
`propext`, `Classical.choice`, and `Quot.sound`. Its context file gives the exact
source hashes and excluded unintegrated files. In particular, the four new
M06 candidate files discussed below were excluded. This checkpoint supersedes
the earlier 87-module/963-declaration reverse-process checkpoint for its stated
closure; neither checkpoint is a claim of complete manuscript coverage or
completed Palomar publication verification.

The source TeX remains unchanged at SHA-256
`23a485d5a5dfaca01a05db28377d015fb1456c194a543d0cbf56f77619ad0cbf`.
The full inventory and all unresolved source issues remain in scope.

### Independent branch-law and perturbation review

The milestone reviewer independently read the frozen `BranchLengthLimit` and
`WeakPerturbation` modules authored by the `profile_correction` reviewer. The
parent separately reviewed and built both. Actual uniform labels retain the
frozen birth shift and the active atom. The global prefix estimate applies to
every legal birth, and the finite vector law is exactly the pushforward of the
product uniform-label measure; repeated labels are allowed. The limit consists
of independent uniform times mapped by the source branch integral. The
positive-horizon statements use $n+1$ and impose no condition on row zero.

The perturbation theorem genuinely allows different probability spaces at
different horizons. For a bounded Lipschitz test it bounds the difference of
integrals by $L\delta+B\mathbb P(d(F_n,G_n)>\delta)$, where $B$ bounds the
image diameter of the test function. Consequently no extra factor of two is
missing. The proof then makes both terms small. It assumes neither a common
coupling across horizons nor the desired limiting law of $F_n$.

### Independently reviewed rooted M06 draft; mechanical gate still open

The milestone reviewer authored `SupercriticalDistanceApproximation`,
`SupercriticalMatrixApproximation`, `RootedSampledMatrix`, and
`SupercriticalDistanceLimit`. The `profile_correction` reviewer independently
read all four drafts and found their mathematical and source interfaces
consistent. The parent also reviewed the pair approximation. These are source
and proof-design reviews, not substitutes for successful Lean checks.

The exact inclusive harmonic comparison differs from the sum of the two
branch prefixes by the reciprocal population at coalescence minus the prefix
below coalescence. The draft bounds the normalized error using N07, N10,
uniform prefix convergence, continuity of the primitive at zero, and one
vanishing endpoint term. N10 already retains the collision correction, so
projecting distinct sample coordinates does not silently condition their
vertex labels to be different. A finite union controls the sampled matrix.
Only the index diagonal is set to zero, following the user's correction.

The Introduction includes the root $V_0$, not just the iid samples. The draft
therefore uses `Option (Fin k)`: `none` is the root and `some i` a sampled
vertex. It proves terminal heights are graph distances from one common actual
root, selected as the terminal root of the always-present active label 1.
Root entries use the uniform height estimate and retain the exact inclusive
endpoint correction $n^{\alpha-1}/2$. The limiting root branch is zero. The
continuous matrix map is identified with the existing corrected
`Audit.starDistance`; the target laws use independent source branch integrals.

At this audit update the complete pair approximation, including the original
positive-horizon source wrapper, had a focused pass with exit 0 and no warnings
(51.45 seconds). Its earlier elaboration timeout was traced to an unspecified
event argument under a concrete trajectory probability; making the event
explicit resolved the failure without changing mathematical statements or
heartbeat limits. The matrix, root, and final weak-limit files were still
unintegrated drafts. Therefore no
complete M06 proof or current axiom closure is claimed here. Even after those
checks, their conclusion concerns the actual reverse construction; the
forward-tree statement still requires the N01 transport, including preservation
of the root and conditional uniform sampling.

### N01 history and support correction

The parent independently reviewed the newly checked forward history law,
support, and uniqueness arguments, and the reverse choice support,
uniqueness, and canonical-order arguments. The forward legal-history measure
projects to the actual forward tree law. A legal history has the exact product
mass; the terminal parent at each birth records its attachment choice, while
the unique freezing timestamp records its freezing choice. Thus a terminal
state determines its complete legal forward history. The reverse proof keeps
actual ordered root choices and stamped terminal states, and establishes the
canonical inequalities between parent, child, and freezing timestamps needed
for a valid forward reconstruction.

This checks substantive parts of the companion proof while correcting its
support argument: aggregate vertex and label counts alone are too broad a
class for asserting reachability. The formalization uses actual legal-history
support and proves the additional temporal order conditions instead of
assuming every object with the right counts can be reconstructed. The final
forward/reverse law equality and the active-label permutation fibre count
remain separate obligations; the partial history and uniqueness results are
not treated as their conclusion.


### Subcritical genuine GH milestone

The `profile_correction` reviewer independently checked the parent-authored
`GraphMetric`, `ForestGH`, `BirthDensity`, `ProfileSegment`,
`SubcriticalProfileApproximation`, and `SubcriticalGHLimit` chain. The parent
reported a successful coordinated build of
`tendsto_reverseGHDistance_probability_positive_horizons`. The conclusion uses
the genuine `GHSpace` distance between the scaled finite graph metric and the
source profile segment. Almost-sure validity and connectivity ensure that the
definition's fallback singleton is not used on actual histories. The finite
birth-profile approximation includes both endpoints and gives the required
density; the checked GH comparison combines density $\varepsilon/4$ and
distortion $\varepsilon$ to obtain $3\varepsilon/4$.

This is a substantive subcritical main-result dependency, not a proxy named
“GH distance.” It remains a statement for the reverse graph and the GH
metric. The measured GHP assertion and forward-law transport are separate
obligations. Its build and independent review do not retroactively enlarge the
104-module axiom checkpoint; later changed and newly integrated files require
a new complete transitive scan.


### Rooted approximation and next exact checkpoint

The full nonroot sampled-matrix approximation and its positive-horizon wrapper
passed a focused check; its deprecation warning was removed before a successful
coordinated build. `RootedSampledMatrix` then passed its first focused check
with exit 0 and no warnings (29.42 seconds), followed by a successful parent
build. This checks the common-root graph interpretation and the full
root-inclusive probability approximation. The final weak-limit file and the
publication-facing $0,\ldots,k$ reindexing were still awaiting their own checks
at this update.

The next integrated checkpoint is recorded in
[`geometry-history-context.txt`](../evidence/geometry-history-context.txt) and
its [`axiom log`](../evidence/geometry-history-axioms.log): 3,955 successful build
jobs, 1,272 explicit definitions/theorems, and 122 integrated modules, with
only the three permitted axioms. Its exact hash scope includes the genuine GH
result, new N01 structures, and the unrooted M06 approximation. It excludes the
rooted and final weak-limit files, whose later build does not enlarge that
recorded axiom scope.

Source issue S01 already included the proof display at lines 1107–1109. Its
entry now explicitly identifies `eq2 thm sur-critique` as requiring the same
approved diagonal correction. For an identical sample coordinate,
coalescence equals birth, so applying N10 there would be invalid. The checked
matrix proof uses N10 only for distinct coordinates and makes the diagonal
exactly zero. This clarifies an existing inventory item; it does not change the
source, omit an obligation, or expand the formalization scope.

### N01 unconditional law comparison

The `milestone_review` agent independently read the final `ForwardReverseLaw`
assembly and the affected canonical permutation, active-history equivariance,
finite-fibre mass, countable atom comparison, terminal-law, and canonical graph
interfaces. The final `forward_reverse_same_law` assumes only a sign sequence,
a horizon, and $n\leq\tau$. Its conclusion compares the actual stamped reverse
law, pushed through the explicitly defined canonical forward state, with the
actual forward tree law. There is no assumed equality of laws, fibre formula,
Markov property, or reconstruction hypothesis in that final theorem.

The fibre calculation is now proved. Unique incoming timestamps match active
vertices, while freezing labels remain fixed. Equal canonical parent and
freezing records determine the entire forest on its vertices. The proved
outside normal form handles the representation away from those vertices.
Active relabelling acts on actual legal reverse histories, so every member of
the orbit is reachable. Timestamp injectivity makes the action free and gives
exactly $S_n!$ states, including the zero-active-vertex case. Their exact reverse
atom masses cancel this factorial to give the forward history mass.

The graph comparison is substantive: the timestamp map is a finite vertex
bijection preserving adjacency in both directions, the root has timestamp
zero, active membership is preserved, and a reverse frozen index $j$ records
the forward freezing time $j+1$. The final pushforward therefore represents
the intended erasure of active names and recovery of birth identifiers.

This completes the previously separated N01 law and fibre obligations. The
parent reported a successful full build and fresh axiom scan of 1,312
declarations in 127 modules, using only the permitted axioms; the corresponding
exact context record controls its mechanical scope. The integer sign-sequence
source wrapper was still undergoing its own coordinated build at this audit
update.

The proof departure from the companion paper is retained: aggregate counts
are not asserted to characterize reachable trees. Instead, actual legal
support supplies the temporal constraints. On the countable forward-history
carrier, agreement at every positive atom of the reverse pushforward and total
mass one give equality, avoiding an unproved converse reachability claim.
This verifies the paper's history uniqueness, product mass, factorial fibre,
and graph identification arguments with that support correction.

N01 alone does not yet identify a law obtained by adjoining iid sampled
vertices. For M06 and measured limits, the remaining transport must show that
the finite vertex bijection also carries the conditional uniform product law
and the distinguished root. The reverse-history matrix results are not counted
as forward sampled-matrix results until that bridge is proved.

### Root-inclusive M06 weak law and measured coordinate review

`SupercriticalDistanceLimit` has now passed a focused check with exit 0 and no
warnings (85.73 seconds). It combines the actual root-inclusive probability
approximation with the proved iid branch-vector weak convergence and the
varying-measure perturbation theorem. The resulting law has the deterministic
root branch zero, independent source branch integrals, and the approved zero
diagonal. Its positive-horizon wrapper retains the manuscript's original
assumptions. The $0,\ldots,k$ source-index wrapper and forward conditional
sampling transport remain separately checked integration steps.

The `milestone_review` agent independently reviewed the complete
`ProfileCoordinateLaw` module by `profile_correction`. The clamp is a continuous
extension to all real times and equals the identity on every actual normalized
birth and on uniform time almost surely. Frozen birth $i-1$, active birth $n$,
and the zero root coordinate are preserved. Thus the genuine probability
measure on the Euclidean subtype segment has precisely the source primitive
pushforward. Continuous mapping of the actual uniform-birth laws gives weak
convergence on that segment, followed by convergence for the genuine
Lévy–Prokhorov distance. The source-integral identity and positive-horizon
wrapper introduce no endpoint mass or additional limit premise. This is the
measured-coordinate part of M02; it is not by itself the complete GHP result.

`SupercriticalSourceMatrix` subsequently passed its focused check with exit 0
and no warnings (87.90 seconds). The independent `profile_correction` review
checked the `Fin (k+1)` reindexing: index zero is precisely the distinguished
root, successors are the original iid samples, the bijection preserves the
index-diagonal correction, and the $k=0$ boundary also remains valid. The
almost-sure observed matrix is the actual graph distance divided by
$n^{1-\alpha}$, not merely an asymptotic replacement of that normalization.
Continuous reindexing preserves the source branch-integral law. This completes
the source-indexed reverse-tree M06 statement, subject to the coordinated
integration and fresh transitive axiom evidence; forward conditional-sampling
transport remains separate at this point.

### Explicit U21 hazard rate

`SupercriticalHazardRate`, authored by `milestone_review`, passed its final
focused check with exit 0 and no warnings (22.40 seconds). The independent
`profile_correction` review checked the actual source rate and its N06(v)
dependency. With $\delta=\min(\varepsilon,1/4)$, the constant
$C=2+\int_\delta^{1-\delta}g(t)^2\,\mathrm{d}t$ is finite, positive, and
independent of the horizon and both endpoints. The normalized error bound
less than one gives the exact uniform bound by $Cn^{1-2\alpha}$ for the
inclusive hazard on every admissible compact interval. Nonnegativity of the
actual upward-step hazards then supplies the formal absolute-norm big-O
statement for arbitrary varying admissible endpoints.

This explicitly verifies the $O(n^{1-2\alpha})$ step at source lines 1093–1094,
previously implicit in the proved vanishing bound. The rate estimate is valid
for all $0<\alpha<1$; only its vanishing requires $\alpha>1/2$. It does not
certify the source's uncorrected repeated-sample split. The separate exact
late-common-birth limit $\delta^2$ remains a proof-correspondence obligation:
the checked N10 argument uses the sufficient first-birth bound with limit
$\delta$, together with the explicit collision correction.

### Final forward M06 export

The exact sampled-law bridge `SampledMatrixTransport` passed its author's
focused check and the coordinated parent build. The `milestone_review` agent
independently checked its complete finite-law argument: the actual joint
history projects to the terminal reverse tree, the finite label bijection
transports the iid product measure, and the canonical timestamp isomorphism
preserves every matrix entry. The root is mapped to identifier zero. Repeated
sampled vertices and diagonal entries are retained, and the active-label root
representative is justified by the source survival hypothesis.

`MainResults/Supercritical.lean` then passed its focused check with exit 0 and
no warnings (99.29 seconds). Its final
`supercritical_distance_matrix_limit` concerns the actual forward Algorithm 1
tree and the conditional iid sampling law, with the literal normalization
$d/n^{1-\alpha}$. The limit uses independent source branch integrals and the
approved zero-diagonal correction. Only positive-horizon admissibility is
required; the finite-prefix shift is removed from the final limit. All fixed
$k$ are allowed, hence in particular the manuscript's $k\geq2$.

The `profile_integrals` agent independently reviewed this final statement
against M06. The printed $U_1,\ldots,U_n$ in a fixed-$k$ assertion is read as
the intended $k$ iid uniforms, consistently with the matrix indices. The proof
uses N07, corrected N10, uniform reciprocal primitives, iid branch convergence,
and exact N01 sampling transport. It does not assume any of these limits or a
coupling of the forward and reverse constructions. The final export still
requires the coordinated integration and fresh transitive axiom checkpoint;
earlier checkpoint hashes are not enlarged by this focused pass. No claim of
whole-paper coverage follows: critical results, CRT, and the other retained
inventory obligations remain distinct.

### GHP distribution interface and critical survival factors

The `milestone_review` agent independently reviewed `PointMassLimit`,
`CompactMeasuredSpace`, `TreeMeasuredSpaces`, `MeasuredGHSpace`,
`MainResults/Subcritical`, and `SubcriticalDistribution`. The compact-space
bundle binds compactness and its Borel structure to its own stored metric.
The quotient identifies whole spaces by measure-preserving isometry, retaining
points outside the measure support. The exact summed ambient-isometry GHP
infimum descends to that quotient; its proved self, symmetry, and triangle
properties provide the pseudometric topology used in the convergence statement.
Separation, completeness, and separability are not assumed and remain separate
background obligations.

The finite forward bundle uses the true scaled graph and uniform measure on
all vertices. The fallback singleton is excluded almost surely at every
positive horizon. The limit is the actual source segment with its prescribed
primitive image measure. The fixed-point weak-convergence proof uses bounded
continuous tests, continuity at the target point, and vanishing distance tails
on the varying actual probability spaces; it does not need a separable target.
For a general pseudometric target, the Dirac integral is evaluated using
strong measurability rather than an unavailable measurable-singleton premise.
This direct route proves the deterministic-limit distribution interface and
bypasses the general GP-plus-GH argument; it does not discharge N15, N16, or
the full Polish-space background merely by proving M02's interface.

The same reviewer checked `GHPTransport`, `GHPTriangle`, and
`ForwardGHPTransport`. Every existential ambient metric explicitly supplies
its topology and Borel structure. Gluing identifies the full shared middle
space and its pushed measure; Prokhorov contraction and triangle estimates,
and compact Hausdorff estimates, bound actual ambient costs. Approximating
the infima then proves the true GHP triangle inequality. The canonical finite
vertex bijection preserves the exact uniform measure and positive scaled
graph metric. Actual stamped support, timestamp erasure, and unconditional
N01 give equality in law of the forward and reverse GHP observables.

For the critical regime, `FiniteSurvivalProducts` and the complete
`CriticalSurvivalProduct` were independently reviewed against the survival
factor of N12's local genealogy argument. A vanishing maximal hazard and
convergent total hazard imply the exponential product limit through a uniform
logarithm remainder; no independence assertion is assumed. At $\alpha=1/2$,
N06(v) gives the actual pair-hazard limit $\int g^2$, and the proved divergent
interior population minimum makes the maximal hazard vanish. Multiplication
by $\binom r2$ gives exactly the source exponent
$-\int r(r-1)/(2f^2)$. Moving inclusive endpoints, coincident limiting
endpoints, fixed finite families of intervals, and $r=0,1$ are retained.
The author reported a final focused pass with no warnings. This proves the
survival-product factor, not the genealogy's actual event-product law,
birth/merger densities, N11, or the complete N12 convergence theorem.

### U30 coalescence geometry

`CoalescenceMetric`, authored by `milestone_review`, passed a focused check
with exit 0 and no warnings (40.83 seconds). The independent
`profile_correction` review checked source lines 1496–1502 and the actual
history dependencies. Connection transitivity at the smaller of two
coalescence phases gives the required minimum inequality; the two
coalescence times are at most the intermediate vertex's birth. Together these
prove the exact triangle inequality for
$\Delta(u,v)=(b(u)+b(v)-2c(u,v))/2$, with real subtraction and the factor one
half intact. Self-distance, symmetry, and nonnegativity are also proved.

The existing strict common-birth bound additionally proves separation for
distinct actual vertices. A finite/countable almost-sure intersection gives
one genuine metric on the entire actual finite subtype, including the zero
horizon and terminal extinction case. No metric is asserted for arbitrary
invalid histories or labels. The source label bridge retains the frozen birth
shift. Distance to a finite set requires explicit nonemptiness, has an
attained minimum, is nonnegative, and is measurable. Integration and current
axiom evidence remain distinct from this focused pass.

## Full inventory reconciliation after the forward supercritical milestone

This pass used the local `lean-statement-audit` workflow and the unchanged
1,921-line source with SHA-256
`23a485d5a5dfaca01a05db28377d015fb1456c194a543d0cbf56f77619ad0cbf`.
The active-environment scan again found exactly 23 named results: seven
theorems, ten lemmas, five propositions, and one corollary. Every active result
label, including both labels in the multipart critical convergence lemma,
appears in the inventory. The single definition and both remarks remain
mapped to substantive obligations. Commented-out material, the superseded
struck-out display, and open questions retain their previously recorded
dispositions.

The renewed prose and proof scan checked the Introduction, all three regimes,
the bounded-population discussion, the excursion application, and both
appendices against the named and unnumbered rows. It found an omitted
introductory clause at line 280: absence of GHP scaling limits for recursive
trees without freezing. This is now explicitly retained within U04b and
source issue S19. Its normalization and nondegeneracy qualification are
unresolved; arbitrary sufficiently fast shrinking gives a trivial point limit.
The U01 source range was corrected to include line 259. The explicit
bounded-population nonuniversality assertion at line 1034 is now retained as
an obligation in U20, rather than described merely as the absence of a claimed
universal measured limit. These additions do not remove or replace any older
obligation. The revised table has 30 named-result component rows, 53
unnumbered-claim rows, 11 external-dependency rows, and 19 source-issue rows;
all U01–U52 and N01–N17 base indices are present with no duplicate row IDs.

The reconciliation distinguishes the following achieved and unresolved scopes:

| Inventory scope | Reconciled status |
| --- | --- |
| M01, M06 | The actual forward height theorem and corrected root-inclusive sampled matrix theorem are proved. The fresh forward-supercritical checkpoint covers M06 and its transport dependencies. |
| M02 | The actual reverse GH/GHP-distance results and final forward distribution interface have undergone source review. The final interface uses whole-space measured-isometry classes with the exact GHP topology; its coordinated build and axiom status must be read from the subsequent integration record. It does not imply that every appendix theorem used by the paper's alternative route has been proved. |
| M03–M05 | Critical compact real-tree convergence, geometric properties, and the annealed Brownian CRT identification remain unresolved. Lower dimension bounds remain in U04a, not hidden inside M03. |
| N01–N06 | The actual model/law results and all five population-profile conclusions have checked exports, with the explicit source corrections and proof departures retained. |
| N07, N08, N10 | Actual reverse-history distance approximation and coalescence estimates are proved. N01 and sampled transport justify the specific forward main-result uses; separately advertised forward observable exports are not assumed automatically. |
| N09 | The bounded-population GH theorem and its U20 nonuniversality discussion remain unresolved. |
| N11–N14 | Continuous genealogy/density and critical finite-dimensional and tightness theorems remain unresolved. The new critical survival-product factor and U30 metric are dependencies, not substitutes for those conclusions. |
| N15–N17 | GP matrix characterization, the general random GP-plus-GH theorem, and leaf-tightness reconstruction remain unresolved despite the direct M02 route. |
| U01–U10 | The precise finite constructions, counts, actual histories, label bridges, and N01–N04 establish their recorded portions. Recursive/plane-tree specializations, stationarity and other separately worded prose subclaims are not all certified by those model definitions alone. The new recursive-tree no-limit clause stays open. |
| U03, U11–U15 | Local squared-profile equivalence, interval counts, reciprocal asymptotics, interior minimum estimates, and uniform coalescence integrals have checked exports. False printed pairing displays and bypassed uniform-integrability arguments remain identified. |
| U16–U21 | The recorded concentration, coalescence, approximation, and branch-limit arguments are checked to the extent explicitly mapped in the report. M02 and M06 do not retrospectively certify every printed intermediate identity or the original correspondence. U21's explicit compact hazard big-O is now proved; its separate exact late-common-birth limit $\delta^2$ remains unexported, because N10 uses a sufficient $\delta$ bound and a collision term. U20 remains open. |
| U22–U30 | Critical construction, joint densities, consistency, real-tree realization, and convergence arguments remain obligations. The proved local survival factor is partial progress; U30's actual coalescence metric and nonempty finite-set minimum now have focused proof evidence and independent review. |
| U31–U48 | Chaining, block estimates, corrected occupancy/conditional estimates, leaf support and branching, excursion approximation and couplings, and the reciprocal-excursion identity remain retained. The known S11–S17 defects are not bypassed by treating their final claims as assumptions. |
| U49–U52 | The exact represented GHP infimum, isometry invariance, triangle, and quotient topology are now constructed. GP foundations, full separation/Polish results, projections, compactness/tightness, sampled reconstruction and uniqueness remain distinct outstanding portions. |
| E01–E11 | Only matching verified companion and Mathlib dependencies actually used by the checked exports are credited. In particular, the plane-tree/CRT and continuous-density dependencies, general compactness/matrix characterizations, and comparative/long-dendron claims are not established merely by citation. |
| S01–S19; O01–O02 | All source defects and open questions remain visible. S01 is the user-approved changed theorem. Other repaired arguments are recorded as departures, and false literal claims are not certified. The two open questions are not reclassified as advertised theorems. |

Current mechanical evidence for the completed forward-supercritical milestone
is in [`forward-supercritical-context.txt`](../evidence/forward-supercritical-context.txt)
and its [`axiom log`](../evidence/forward-supercritical-axioms.log): 1,451
definitions/theorems in 143 integrated modules, using only the three permitted
axioms. That exact hash scope does not include later critical or final GHP
interface work merely because it has a focused pass. This reconciliation is
not a whole-paper coverage certificate, Comparator acceptance, or a Palomar
deposit check. The newly retained clauses require the same follow-up coverage
discipline as every prior obligation.

## Integrated noncritical main results and critical sampling interface

The subsequent coordinated checkpoint now includes M01, M02, and the corrected
M06, together with the whole-space measured-isometry quotient topology, the
critical survival-product dependencies, and U30's coalescence metric. The
[`noncritical-main-results-context.txt`](../evidence/noncritical-main-results-context.txt)
and [`axiom log`](../evidence/noncritical-main-results-axioms.log) record 1,517
explicit declarations in 153 modules and 3,986 successful build jobs, with
only the three permitted axioms. This supersedes the earlier mechanical
boundary for these included files; the 1,451-declaration/143-module record
above remains an accurate historical checkpoint. Neither checkpoint covers
later sampling or tracked-cluster files merely because they have been drafted
or checked separately. M03–M05 and the other unresolved inventory rows remain
open.

An independent source and dependency review of `FiniteDistinctSampling.lean`
and the complete `DistinctVertexSampling.lean` found the sampling correction
faithful. The actual iid vector has atom mass $N^{-k}$, while conditioning on
injectivity gives the uniform injection law with mass $1/(N)_k$. The injection
count is proved by a concrete equivalence with embeddings into the finite
population. Null conditioning uses the library's zero measure explicitly;
the asymptotic event comparison proves eventual positive conditioning mass.
All source labels, including active vertices, are retained. The collision
bound counts each unordered coordinate pair once and gives
$\binom{k}{2}/N$, including sample sizes zero and one.

The product-law lemma keeps an arbitrary independent random environment and
bounds every joint event's conditioning error by the same collision
probability. The final exact multiplicative identity for events already
implying distinctness is essential for the polynomial rescaling in N12:
vanishing additive error alone would not justify that rescaling. The
falling-factorial ratio tends to one. These statements repair the iid versus
without-replacement portion of S10; they do not establish the genealogy
factorization, the frozen-only auxiliary sampler identification, or the
local density limit. The author reported the generic file's focused pass;
current integration and axiom status for these new files must be read from
the next coordinated evidence record.

The independent review of `GHPSeparation.lean`,
`ApproximateIsometryLimit.lean`, and `ProkhorovIsometry.lean` also found the
source interpretation sound. Near-zero costs are actual realizations of the
same GHP infimum, with each ambient metric determining its topology and Borel
structure. Their Hausdorff bounds give approximate isometries on the complete
compact carriers. A compact product-space ultrafilter limit becomes uniform
by the finite-cover argument, and asymptotic density proves surjectivity.
The measure argument reuses those original ambient realizations: uniform
closeness and the exact invariance of Prokhorov distance under compact
isometric embeddings force preservation of the measures. Consequently the
zero-distance relation is whole-space measured isometry even without full
support. This is a proof of separation, not of quotient completeness or
separability. At this review the author's focused check and the parent's
integration evidence for these files were still pending; they are not
included retroactively in the 153-module checkpoint above.

The follow-up `FrozenDistinctSampling.lean` was also independently reviewed
through its final joint-event identity. Frozen labels are defined by actual
birth time less than the horizon and identified exactly with the down-step
labels, preserving the freezing-label-minus-one convention. The excluded
active mass is exactly $S_n/N_n$ and tends to zero by population sublinearity.
The finite union bound combines that mass with collisions, so the probability
of a frozen distinct vector tends to one. Its exact probability is
$(F_n)_k/N_n^k$, and its conditional atom is
$1/(k!\binom{F_n}{k})$. The joint-event identity is multiplicative and retains
an arbitrary independent history law; no rescaled limit is inferred from an
additive error. These results supply the frozen/distinct conditioning part of
U27 and S10. The separately iid auxiliary frozen times in N12 and the full
actual genealogical event still need their explicit connection to the density
calculation. Mechanical checking of this new file was pending at review.

## Actual tracked-cluster transitions

The new `ClusterTransition.lean` derives U27's one-step merger and survival
factors from the concrete reverse kernel. A finite subset $A$ of the current
roots represents distinct tracked components. On every supported ordered
choice, at least two tracked representatives become connected if and only if
both chosen roots belong to $A$. The retained choices are exactly
$A^{\mathrm{offDiag}}$, giving probability
$\binom{|A|}{2}/\binom{S}{2}$. Its complement is the source no-merger factor,
and each prescribed unordered pair has probability $1/\binom{S}{2}$.
The actual phase-transition wrappers make the source sign explicit: attachment
uses the proved current population, while freezing preserves every old root
and has merger probability zero. Empty and singleton tracked sets, the
positive attachment denominator, and the terminal-extinction boundary are
covered by the actual finite-state hypotheses.

The final focused Lean check passed with no warnings. A separate independent
review by the profile-correction agent found the source interpretation and
dependency proofs clean. No independence assumption or already-established
future genealogy distribution is used. This is a checked one-step dependency,
not the full N12 event-product calculation; the planar orientation factor and
the construction of the marked genealogy remain distinct interfaces. The
parent's coordinated build and axiom record are the integration authority.

The separate `GHPUnderlyingProjection.lean` review checks the appendix's
GHP-to-GH projection. Whole-space measured isometry supplies an isometry of
the entire carriers, so forgetting the measure is well-defined on the source
quotient. The already proved GH-versus-GHP bound makes this projection
1-Lipschitz, hence continuous and Borel measurable for the explicitly installed
Borel structure on `GHSpace`. This neither changes the source quotient nor
requires full support. The GP projection and Polishness assertions are still
separate obligations. The author subsequently reported a clean focused pass
for `GHPSeparation.lean`; projection checking and coordinated integration
remain separately recorded.

The tracked-cluster module was then extended with the exact planar factor.
For distinct current roots $u,v$, the actual forest event that the new root of
$v$ equals $u$ occurs exactly for ordered choice $(u,v)$. The reverse choice
and unchanged-root alternatives are excluded explicitly. Thus its probability
is $1/(S(S-1))=1/(2\binom{S}{2})$, with a zero freezing-step branch. The final
focused check of the complete extended file passed with no warnings, and the
separate extension review by the profile-correction agent was clean. This
replaces the earlier pending planar one-step interface above; encoding the
full marked planar genealogy and multiplying its events is still outstanding.

## Critical covering and count-recursion dependencies

The root-authored `CoalescenceMetricApproximation.lean` was independently
reviewed against the critical tightness argument and S03. The coalescence
metric bound, together with each coalescence time being no later than either
birth, bounds both time-interval lengths. The global reciprocal-profile
modulus then controls the literal inclusive harmonic sums, retaining their
endpoint corrections and the source comparison's nonzero diagonal. The
all-pairs N07 maximum transfers that bound to actual graph distance on its
explicit good event. Finally, the attained nonempty finite-set minimum gives
the graph-covering implication. No false endpoint-free inequality or
concentration premise is substituted for the source argument. The parent
reported a clean integrated build for this module.

The root-authored `CoalescentCountRecurrence.lean` deterministic argument was
also independently reviewed. If the terminal excess over one is zero, the
bound is immediate; otherwise monotonicity gives strict positivity at every
earlier step before reciprocals are used. Reciprocal increments telescope,
and $u(u-1)\geq(u-1)^2$ for $u\geq1$ gives the expected-count form. This resolves
the absorbing-state difficulty in that analytic argument. Applying it to the
actual stochastic process still requires its proved expectation recurrence;
the generic lemma does not supply or assume that model-specific fact.

The final `TrackedClusterCount.lean` focused check passed without warnings,
and its independent review found the semantics clean. The set is literally
the finite image of the current root map. The join update replaces the second
selected root by the first, decreasing cardinality exactly when both were
tracked. The freezing proof requires every tracked vertex to be present.
Boundedness by the tracked-set cardinality supplies integrability, and the
expectation formula is obtained by integrating the actual merger indicator.
The parent subsequently reported a clean build of this module. Passing from
this single-kernel identity to a multi-step expectation bound is subsequent
work; it is not credited merely from the analytic recurrence lemma.

The independent reviews of `AuxiliarySignSampling.lean` and
`FrozenBirthSampling.lean` verify the remaining frozen auxiliary-time sampler
identification. Normalizing the nonzero empirical sign measure gives exact
uniform sampling of the sign indices; subtraction of $1/n$ is the actual
zero-based index shift, whose predecessor map is injective on positive step
indices. The arbitrary probability completion for empty sign sets is explicit
and disappears eventually because their empirical masses tend to one. The
finite product law gives genuinely independent mixed-sign samples converging
weakly to independent uniform times. The frozen-label/birth-index bijection
transports both iid and distinct-conditioned vector laws exactly, with the
normalized version at every nonempty frozen horizon. This closes the earlier
pending sampler identification, but does not assert convergence of sampled
hazard rates merely from convergence of sampled locations.

The independently reviewed `GHPFiniteApproximation.lean` constructs its
measurable finite-net selector by finite measurable ball tests. The net covers
the complete compact carrier and retains centers of zero pushforward mass.
In the original carrier as common ambient space, both the Hausdorff and
Prokhorov costs are at most the net radius, giving the exact summed GHP bound
of twice that radius. No full-support hypothesis is used. Finite
approximations alone do not prove a countable dense family or Polishness.
The author subsequently reported a clean focused pass with the pushed-forward
probability-law assertion explicit; coordinated integration remains separate.

## Actual multi-step tracked-count bound

`TrackedClusterExpectation.lean` now defines the expectation under the actual
reverse marginal law and integrates its `lawAfter.bind` recursion. The
single-kernel formula is applied only after almost-sure validity and the
explicit birth-time premise establish presence of every tracked vertex.
Bounded first and second moments are proved. Nonnegative variance supplies
$\mathbb{E}[C(C-1)]\geq\mathbb{E}[C](\mathbb{E}[C]-1)$; it is not a model
assumption. On an attachment step, the genuine population is at least two,
and a bound $S^2\leq B$ gives the required quadratic decrement.

The final block theorem starts at elapsed reverse time $k_0$, takes $m$ steps
with $k_0+m\leq n$, requires a nonempty legal tracked set born by source phase
$n-k_0$, and counts the actual signs at $n-(k_0+j)$ for $0\leq j<m$.
For a positive number $q$ of those attachment steps, it proves that the
expected final tracked count is at most $1+B/q$. The source endpoint is
$n-(k_0+m)$, and the last tested sign is that endpoint plus one. The absorbing
case is handled by the separately checked analytic lemma, without reciprocals
of zero excess.

The complete file passed its final focused Lean check without warnings. An
independent review by the profile-correction agent found the actual marginal
law, phase indices, moment argument, and all-born restriction faithful to
source Step 2 at lines 1590–1608. The paper's count includes unborn vertices
globally; the proved count has the intended meaning on precisely this
all-born block. The oldest-singleton comparison in U34, quantitative block
specialization, and N14 itself remain separate obligations. This focused
result is awaiting the next coordinated build and axiom checkpoint and is
not retroactively included in the earlier 153-module evidence.

## Integrated critical foundations checkpoint

The new coordinated evidence is
[`critical-foundations-context.txt`](../evidence/critical-foundations-context.txt)
and its [`axiom log`](../evidence/critical-foundations-axioms.log): 1,683 explicit
declarations in 171 integrated modules, 4,004 successful build jobs, and only
the three permitted axioms. It includes the frozen geometry foundations,
profile time change, finite/frozen/sign sampling, actual tracked transitions,
component counts and expectation recurrence, the absorbing-safe estimate,
the coalescence-to-graph modulus, the exact U21 closed common-birth tail, and
finite atomic Prokhorov bounds. Later work remains outside this exact hash
scope until separately integrated.

The independent `CommonBirthTail.lean` audit verifies the separately retained
U21 claim. The closed tail uses a limiting boundary of measure zero, including
cutoffs zero and one. The minimum-birth event is exactly the intersection of
two iid label tails, giving the limit $\delta^2$. Coincident sampled labels
and the active-vertex atom at birth time $n$ remain in the finite model.
The source positive-horizon wrapper changes only the irrelevant initial row.
This closes the exact tail obligation without changing the previously
recorded sufficient $\delta$-bound route used for N10.

The independent `FiniteProkhorov.lean` audit verifies that summing absolute
atomic mass discrepancies bounds every event discrepancy. Thickening contains
the original set for a positive radius, so the actual Prokhorov
characterization gives the same bound. Equal floor codes bound each mass
difference by the mesh, and the mesh $\varepsilon/|X|$ gives total error at
most $\varepsilon$ for a nonempty finite carrier. Zero-mass atoms are retained.
This proves the weight-coding estimate; it does not by itself construct
rational metric approximations or prove Polishness.


## Critical chaining, birth-order comparison, and analytic dependencies

The independent review of `FiniteChaining.lean`, `CoalescenceChaining.lean`,
and `ChainingSeries.lean` verifies the finite witness argument on the actual
almost-sure coalescence metric. Repeated sampled vertices are permitted, and
the final covering radius remains in the deterministic bound. The series
constant is chosen before both integer parameters and controls the exact
sum of $(k+j)^2 2^{-(k+j)/2}$ by a constant times $2^{-k/3}$. These three
modules were reported built by the coordinating agent. The probability
bounds for the successive nets and the ordered limiting argument in N13
remain separate.

The independent review of `TrackedClusterBlock.lean` verifies the exact
identity $2q=m+S_{n-k_0}-S_{n-(k_0+m)}$ for the actual attachment count.
A population bound $M$ therefore gives $q\geq(m-M)/2$ and, for $M<m$, the
expected-count bound $1+2M^2/(m-M)$. The slightly stronger denominator than
the printed estimate follows from the explicit phase endpoints. The legal,
nonempty, all-born conditions are retained. Its coordinated build passed.

`TrackedRootCorrespondence.lean` and `TrackedIsolation.lean` were authored by
the milestone-review agent and independently reviewed by the
profile-correction agent. Their separate coordinate and current-root
permutations preserve tracked component relations without requiring equal
untracked tree shapes. Actual ordered-pair law transport proves equality of
future isolation probabilities when both swapped marked components are
isolated. Future freezing labels are absent from the current forest and are
fixed by the permutations. Non-isolation is absorbing by actual coarsening.
At the younger marked vertex's birth, the distinct-common-birth theorem makes
that vertex isolated relative to all presently born marked vertices; unborn
marked vertices are ignored exactly as in the source definition. Splitting
on whether the older vertex is still isolated, and integrating the genuine
reverse marginal recursion, proves that the oldest vertex has the smallest
isolation probability. Equal terminal birth times and coinciding compared
labels are included. Both modules passed focused checks and coordinated
builds. The final singleton-count averaging lemma in `OldestIsolation.lean`
is still being checked at this audit entry; N14 is not claimed from the
comparison alone.

The independent reviews of `FiniteFamilyScheffe.lean` and
`VariableDominatedConvergence.lean` verify the analytic U29 steps. Integrating
$\min(f_n,g)$ and using dominated convergence proves that convergence of a
finite family's total nonnegative mass forces each component to converge
in $L^1$. The component limit's integrability is an explicit hypothesis in
that lemma. The varying-domination theorem separately derives limit
integrability from an almost-everywhere subsequence of the $L^1$-converging
dominators. On every subsequence it applies the finite-family lemma to
$b_n+f_n$ and $b_n-f_n$. It does not assume almost-everywhere convergence of
the full dominating sequence. Both modules were reported built; construction
and conservation of the actual genealogy densities remain separate.

## Measurable profile marks at the actual auxiliary times

The independent review of `DominatedWeakConvergence.lean`, `MeshJitter.lean`,
`LocalProfileInMeasure.lean`, `AuxiliarySignJitter.lean`,
`MarkedProfileSampling.lean`, and `AuxiliaryAttachmentRate.lean` checks the
full mathematical dependency chain for sampling merely almost-everywhere
measurable profiles. Jittering a selected zero-based index uniformly over
its mesh cell gives exact floor recovery and density $n$ divided by the
number of selected indices. The empirical sign-mass limit proves eventual
density at most four. Local $L^1$ convergence on every interior interval
then gives global convergence in probability by discarding two short
endpoint strips. Uniform domination transfers that bound to the actual
jittered law.

The fixed measurable profile map is handled by approximation of integrable
tests under the dominating measure, not by an unjustified continuous mapping
argument. Its almost-everywhere measurable representative preserves the
stated limit law. On an attachment cell $[i/n,(i+1)/n)$, the exact discrete
rate is $n/[S_{i+1}(S_{i+1}-1)]$; the up-step identity $S_{i+1}=S_i+1$ makes
this precisely the shifted-square profile at exponent $1/2$. Flooring changes
only the time coordinate by less than $1/n$ and preserves that rate exactly.
The finite product construction retains independent marked samples. This
review checks the profile-rate dependency, not the genealogy event or N12
mass conservation. Mechanical status for these newer modules is recorded
by their separate focused checks and the next coordinated checkpoint.

## Whole-carrier GHP countability and completeness route

The independent reviews of `GHPFiniteCoding.lean` and `GHPSeparability.lean`
verify countability without a full-support assumption or a claim that rounded
distances themselves form a metric. Equal codes give an actual finite-carrier
bijection with distance distortion at most the mesh and atomic Prokhorov
error at most the mesh, hence GHP error at most three meshes. Finite-net
approximation of both quotient representatives contributes two further
meshes each. Choosing mesh $\delta/7$ and using countable distance-and-weight
codes proves separability of the whole-space quotient. The author reported
clean focused checks for both files.

The independent reviews of `GHPChainGluing.lean`, `GHPChainMeasures.lean`,
`CompactHausdorffHull.lean`, `CompactSupportLimit.lean`, and the complete
`GHPCompleteness.lean` draft verify the intended completeness proof. Recursive
gluing retains each supplied measured coupling through exact isometric
factorizations. Its simultaneous complete ambient space need not be separable.
The Hausdorff-Cauchy compact images and their limit all lie in a single
compact hull. Probability compactness and Prokhorov convergence are applied
on this compact hull; only continuous isometric pushforwards and contraction
are used in the larger ambient space. Closed-neighborhood Portmanteau bounds
put all limiting mass on the full Hausdorff limit, and the subtype comap
retains points of zero mass. The resulting subsequential measured limit,
together with the geometric Cauchy bound, gives convergence of the full
sequence. Near-infimum couplings provide the required strict geometric
budgets for arbitrary controlled Cauchy sequences. No circular completeness,
global ambient separability, or support-identification assumption was found.
This is a source/dependency audit of the current proof route; the final
completeness file was still awaiting its own mechanical checks when reviewed.
The previous 171-module hash scope is not expanded by these reviews.


The subsequent `OldestIsolation.lean` focused check passed without warnings.
Independent review by the profile-correction agent verified the actual root-map
injection of present singleton marked vertices, finite integral summation,
and use of the proved birth-order inequality for every marked label. The
nonempty marked set supplies the positive divisor, and the explicit target
phase ensures all its labels are present. This completes the U34 Step 1
bound used by N14 with the true divisor $|A|=K+1$, repairing the printed
summation endpoint. It does not replace the positive-block and numerical
specialization of N14. The coordinating build and next full axiom checkpoint
remain the mechanical integration record for this new file.


## Integrated critical topology checkpoint

The coordinated checkpoint
[`critical-topology-context.txt`](../evidence/critical-topology-context.txt)
and [`critical-topology-axioms.log`](../evidence/critical-topology-axioms.log)
passed 4,045 build jobs and checked 1,806 explicit definitions/theorems across
199 integrated modules. Only `propext`, `Classical.choice`, and `Quot.sound`
were reported. This exact hash scope includes the whole-carrier GHP Polish
space, compact preimages of compact GH sets, the actual oldest-isolation
comparison, corrected positive-index N14 with its uniform source quantifiers,
U29 analytic dependencies, the generic marked-profile theorem, and the finite
iid occupancy helper. New continuation kernels, the repaired frozen-block
occupancy assembly, literal auxiliary rate specializations, and GH tightness
transfer are separately listed outside that checkpoint. It is not evidence
of full source coverage or publication readiness.

The additional independent review of `OneStepTightness.lean` and
`OneStepTightnessAsymptotic.lean` verifies that one sample-size threshold is
chosen from the fixed population constant before the horizon, marked count,
block index, and vertex vector. The source cube-root range is proved equivalent
to $k^3\leq n$. The legal injective vector has exactly $K+1$ distinct labels;
its birth restrictions discharge the oldest and all-born hypotheses in the
actual law. The source's factor-four block length and coefficient
$3M\sqrt{k}/(4K)$ are retained. The explicit correction is $i\geq1$, avoiding
the undefined negative phase. Enlarging the blocks in the later U36 occupancy
repair does not change this proved N14 statement.

The independently reviewed `GHPCompactness.lean` requires only GH-Cauchy
underlying carriers and arbitrary probability measures. Actual optimal GH
couplings provide a geometric common-ambient realization, after which the
compact-hull measure argument gives a measured convergent subsequence. The
continuous underlying projection identifies the limit carrier and proves
compact inverse images. No measured Cauchy assumption is inserted. The
subsequent `GHPTightness.lean` review checks reflection of tightness using
those compact inverse images and exact pushforward masses of compact
complements; continuity gives preservation. Its indexed-family statement
and Prokhorov compact-closure conclusion retain the original laws. That file
had a reported focused pass but was outside the above integrated scope.

The independent review of `SuccessorSquareProfile.lean` and
`AuxiliaryAttachmentSquare.lean` checks the separately retained literal mark
$n/S_{i+1}^2$. For $a=c/S\geq b=c/(S+1)\geq0$,
$|b^2-ab|\leq|a^2-ab|$ transfers the already proved local correction. The actual
attachment-cell identity, measurable marked-law convergence, exact floor
recovery, and finite independent products then give the squared-denominator
assertion, alongside the distinct exact-merger mark
$n/[S_{i+1}(S_{i+1}-1)]$. This does not assert convergence under an arbitrary
coupling selected from time convergence alone. These source/dependency reviews
do not retroactively expand the checkpoint's hash scope.


## Repaired critical occupancy estimates under review

`FiniteOccupancy.lean` was authored by the milestone-review agent, passed its
focused check, and is included in the 199-module checkpoint. Independent
profile-correction review verifies actual product-law Bernoulli indicators,
not an assumed binomial model. The event with occupancy at most two thirds
of its positive mean lies strictly below the three-quarters threshold used
in the checked Bennett bound, giving the rate $g(1/4)$. The exact probability
for prescribed values at distinct coordinates yields an unconditioned
$r$-fold selected-value collision bound $k^r|B|/N^r$, including empty and
degenerate coordinate cases. Absence of fourfold selected-value repetition
implies that occupancy is at most three times the number of distinct selected
labels.

`FrozenBlockOccupancy.lean` and `CriticalOccupancyRate.lean` subsequently passed
focused Lean checks. The current `CriticalBlockOccupancy.lean` assembly has
also received independent mathematical/source review, but is awaiting its
own mechanical check. The repaired block length is
$16\lceil Mn/\sqrt{k}\rceil$, while the proved N14 keeps its original factor
four. The freezing label's birth is one less than its step, and the finite
block cardinality bound explicitly loses at most one vertex. For $M\geq1$,
$k\geq6$, and $k\leq n$, a repaired block has actual sample mean at least
$6M\sqrt{k}$. The threshold $4M\sqrt{k}$ is therefore justified.

All samples still use the full iid uniform vertex law. Only frozen labels
enter the fourfold-collision estimate, so the shared terminal birth time of
active labels receives no false reciprocal-cube bound. The resulting
collision error is at most $k^4/N^3\leq8/k^5$ for $k^3\leq n$. The number
of blocks is at most $\sqrt{k}/(16M)$; the explicit total error multiplied
by $k^4$ tends to zero. Frozen birth-time injectivity proves that the original
source distinct-birth-set failure is contained in this stronger frozen-label
failure. The proposed cutoff is chosen before the horizon and the signed
row. This checks the repaired route in S12; the printed factor-four and
$g(1/3)$ concentration display is not certified. Conditional block iteration
and N13 remain separate from this occupancy estimate.

The final `CriticalBlockOccupancy.lean` focused check subsequently passed
without warnings (session 64330). Its quantified conclusion now includes the
original distinct-birth-set failure, with one eventual sample cutoff before
every horizon and admissible signed row satisfying the finite population
bound. `FrozenBlockOccupancy.lean` and `CriticalOccupancyRate.lean` also passed
coordinating dependency builds. This closes the repaired U36 estimate at the
module level; the next integrated checkpoint must record their exact hashes.


## Conditional critical blocks and sampled observables

Independent review of the coordinating agent's `ConditionalEventBounds.lean`
checks the tower argument through equality of set integrals of conditional
expectations. Previously exposed events are measurable in the current past;
nonnegative bounds permit finite multiplication, and an arbitrary event
known at the initial time is retained. This proves a product upper bound.
It does not prove the independence asserted in the manuscript's U37 argument.

`ContinuationConditional.lean` derives the endpoint law from the actual
`Kernel.traj`, first at the initial coordinate and then by the real transition
kernel recurrence. It identifies the full-past conditional endpoint indicator
with the continuation probability from the current forest, including zero
elapsed steps and the terminal phase. No Markov or conditional-law premise
is inserted into the theorem. Both modules have coordinating build passes.

Independent review of `CriticalBlockGeometry.lean` retains the exact factor
one half in the coalescence distance. A connection is tested at phase
$(i-1)d$, with $i\geq1$ and explicit birth bounds; the integer window
$i_0\leq i+p+1$ and $p\geq2$ imply the required distance bound. Consequently,
being far from every mark implies the actual isolation event at that phase.
The small-birth case uses only nonnegativity of the coalescence time.
`CriticalIsolationRate.lean` retains both rounding losses in
$p_k=\lfloor100\log k\rfloor$ and the integer trial count
$\lfloor(p_k-1)/2\rfloor$. Its proved lower bound
$50\log k-2$ and $\log(3/4)\leq-1/4$ imply that the geometric error multiplied
by $k^4$ tends to zero. The geometry module has a coordinating build pass;
the rate module has a reported clean focused check. The actual alternating
block event assembly remains separate.

The milestone-review agent authored `ContinuationIsolation.lean` and
`ContinuationBlockIsolation.lean`; these are not counted as its independent
reviews. Both focused checks passed without warnings, and the first also
passed the coordinating build. The initial forest is arbitrary but valid.
Younger marks born strictly later in reverse time are inserted as singleton
components; a mark born exactly at the starting phase requires an explicit
initial singleton condition. This boundary is retained instead of silently
excluding the upper endpoint of the source birth interval. The actual count
contraction is applied only after all marks are present, with a general
offset in the continuation law. The resulting kernel bound permits any
final interval at least $4\lceil Mn/\sqrt{k}\rceil$ long, including the
repaired factor-sixteen blocks. `ConditionalBlockIsolation.lean` is drafted
to discharge the boundary condition from actual-history birth support and
the checked conditional endpoint identity; its mechanical verification is
still pending at this entry. N13 is not marked complete.

Subsequent independent profile-correction review of all three continuation
isolation modules and their conditional-law dependency is clean. It checked
the insertion transition from birth phase $b+1$ to $b$, the separate case
$b=s$ at the starting boundary, integration of the oldest comparison at the
younger birth, and the final count interval beginning only after every mark
exists. The elapsed indices $n-s$ and $n-t$ agree exactly with the source
phases. The conditional bound is given the entire actual past. The alternating
block product still requires the coordinating agent's tower and adaptedness
assembly; this independent review does not assume that step.

Independent review of `SampledDistanceLaw.lean` and
`SampledDistanceContinuity.lean` checks the actual iid product law, including
sample collisions and the empty sample. Measured isometries preserve each
finite sampled distance law. A common compact-hull realization supplies one
subsequence on which every finite sampled matrix law converges; uniqueness
of the GHP limit and the subsequence criterion then prove continuity of the
quotient observable. The probability-law target has its Borel structure
explicitly fixed, and bounded continuous test integrals are continuous.
These statements do not reconstruct a full carrier from its sampled laws:
null-mass carrier points remain invisible to the samples. The author reports
a final clean focused check for the continuity module; its coordinating
integration is separate from the 199-module checkpoint above.

The subsequent independent read of `CompactMeasuredRepresentation.lean`
and `SampledCoverRadius.lean` is also clean. The exposed subsequence
representation keeps both the whole carrier images and the original pushed
probability measures in one actual compact ambient hull. The covering radius
is the Hausdorff distance from the entire carrier to a nonempty $k+1$ tuple;
repetitions remain in the iid law and null-mass carrier points remain visible.
In a fixed ambient space, joint Hausdorff and weak convergence gives covering
law convergence by the continuous carrier/tuple map and the product of a
Dirac carrier law with the iid sampling law. Measured isometries preserve
that law exactly. These reviewed statements are infrastructure for the
later covering and support arguments; they do not themselves establish
full support or reconstruction. Mechanical checks and integration of these
new modules were still pending when this review was recorded.

The coordinating build of `ContinuationBlockIsolation.lean` subsequently
passed, and `ConditionalBlockIsolation.lean` passed both its focused check
(session 23178) and the coordinating build. Thus the actual-history
conditional $3/4$ bound is mechanically checked, with the independent review
above. The fixed-mark covering and final iid sampling assembly are new
dependent work and are not included in that conclusion.

For the separate continuous critical-coalescent construction, independent
profile-correction review of `ContinuousCoalescentHazard.lean` is recorded
with its limited scope. The backward survival function is
$\exp(-\int_t^b h)$, its derivative has the positive sign $h(t)S(t)$, and
the density on $(a,b]$ has mass $1-S(a)$. The remaining mass is an atom of
size $S(a)$ at the cutoff, including the degenerate interval $a=b$. Absolute
continuity and Lebesgue differentiation require only interval integrability,
not continuity of the rate. This is the normalized finite-cutoff next-event
law; the actual cluster-rate instantiation, possibly divergent endpoint at
zero, and full marked genealogy remain separate obligations.

## N13 completion and full-closure integration (29 October 2026, resumed)

Reviewer: Claude, resuming from the Codex handoff. Claude did not author the N13
declarations; it repaired two proof-body elaboration errors (`CriticalBlockCover.lean`
length goal, `CriticalSampledCover.lean` addition monotonicity and radius rewrite)
and added the bridge `exists_uniform_population_bound` and the wrapper
`critical_sampled_cover_probability_of_isBigO`.

Statement fidelity. Source lines 1506–1510 state, under the hypotheses of
`thm:critique`, that for every sufficiently large $k,n$ with $k\leq n^{1/3}$,
$P(\Delta^n(V,\{V_1,\ldots,V_k\})>n\ln(k)^2/\sqrt k)\leq k^{-4}$, where
$V,V_1,\ldots$ are independent uniform vertices of $\mathcal V_n$ (lines
1496–1500) and $\tau(X^n)>n$ (line 695). The Lean export quantifies one $K$
before $k$ and $n$; every $n$ with $k\leq n^{1/3}$ is allowed, which is at least
as strong as "sufficiently large $k,n$". The law is the actual reverse-history
law times an independent uniform query vertex times the iid uniform $k$-tuple,
on the literal label set $\mathcal V_n$, keeping collisions and the active atom.
The event is the strict inequality for every sampled coordinate, proved equal
to the strict inequality for the attained minimum. `sourceCoalescenceDistance`
is the exact $(b_n(u)+b_n(v)-2c_n(u,v))/2$ in the source's one-based labels.
The population hypothesis is the literal
$\max_{1\leq k\leq n}S^n_k=O(\sqrt n)$, encoded with a clipped finite supremum
that agrees with the source on surviving rows; the profile hypotheses are not
needed. Verdict: **faithful**.

Proof correspondence. The occupancy step, alternating-block step and final
comparison follow the paper's structure with the S12 repairs recorded in the
report. The conditional-independence assertion at line 1677 is replaced by a
proved conditional bound and tower-property iteration; the paper's assertion
itself is not certified.

Mechanical evidence. Focused checks of both files passed with no diagnostics;
`lake build Freezing2.Probability.CriticalSampledCover` passed. After the
continuous-kernel and survival drafts were repaired, all 232 maintained modules
were imported by `Freezing2.lean` and `python3 scripts/check_axioms.py
--integrated` passed for 2,044 declarations with 4,098 build jobs and only the
three permitted axioms; see `evidence/critical-cover-axioms.log` and
`evidence/critical-cover-context.txt`.

## Critical tightness: `eq:stepone` and leaf-tightness `eq:GH` (29 October 2026)

Author: Claude. Reviewer: a separate Claude agent that did not write the
declarations, working read-only from the TeX, the elaborated statements and
their semantic definitions (no Lean runs by the reviewer).

- `critical_sampleNet_tightness` (`Probability/CriticalSampleNet.lean`) against
  `eq:stepone`, lines 1517–1534 with notation at 1493–1504: **PASS with notes.**
  Survival encodes $\tau(X^n)>n$; profile hypotheses are unnecessary (the source
  proof only uses $M_n\leq M\sqrt n$, line 1562); quantifiers are $\varepsilon$
  first, then a limit in $k$ of a $\limsup$ in $n$; the event equals
  $\max_v\min_i\Delta^n/n>\varepsilon$ for $k\geq1$, and the vacuous $k=0$
  event cannot affect the limit; the ENNReal formulation is equivalent for
  probabilities.
- `rowMaxPopulation`, `exists_uniform_population_bound`
  (`Analysis/CriticalPopulationBound.lean`) against the hypothesis
  $\max_{1\leq k\leq n}S^n_k=O(\sqrt n)$ of `thm:critique`: **PASS.**
- `critical_graphSampleNet_tightness` (`Probability/CriticalGraphNet.lean`):
  **PASS with notes.** Finding: the source display `16/01/11h` (line 1538) is
  stated for the harmonic surrogate $D^n$ (macro `\dc`, line 133), not for the
  graph distance. The Lean theorem is the graph-distance display `eq:GH`
  (line 1154), which is what the source ultimately needs; docstrings and the
  report were corrected accordingly. `16/01/11h` itself is bypassed, not proved.
  Premises match N07's encoding at $\alpha=1/2$; $\mathrm{Lim}_{1/f^2}$ is not
  used. `reverseDistance` is the graph distance in the final forest $F^n_0=T^n$
  of Algorithm 2, connected on actual histories.

Proof correspondence. Step 1 follows the paper's dyadic chaining, with
explicit block error $(8/7)8^{-J}$ and last-net error $8\cdot2^{-N_n}$, where
$8^{N_n}\leq n<8^{N_n+1}$. The last net uses N13 for each fixed query vertex,
which the conditional block bound supports directly. Step 2 replaces the
printed $D^n$ comparison by the proved uniform harmonic modulus and N07.

## Forward leaf-tightness and Proposition `C.1` (29 October 2026)

Author: Claude. Reviewer for statement fidelity: a separate Claude agent that did
not write the declarations (read-only, no Lean runs).

- `forward_critical_leaf_tightness` (`Probability/ForwardLeafTightness.lean`):
  `eq:GH` for the actual forward tree `Freezing1.Forward.treeLaw` with
  conditionally iid uniform vertices. It is proved from the reverse statement by
  N01: the canonical timestamp isomorphism maps the whole reverse vertex set onto
  the forward vertex set (`canonicalForwardState_vertices`) and preserves graph
  distance, so the event, which quantifies over every vertex, is transported
  exactly. Its hypotheses and event are those of the reviewed reverse theorem.
- `MeasuredGHSpace.LeafTightCriterion` (`Probability/AnnealedSampling.lean`)
  against Proposition `C.1` (lines 1888–1899) and `eq:leaf-tight`: **PASS with
  notes.** Annealed laws are genuine mixtures `P.bind L` of the conditional
  sampled laws. Block-wise convergence of the annealed matrices is equivalent to
  weak convergence of the infinite matrices; leaf-tightness for each `δ > 0` is
  equivalent to the iterated limit by monotonicity in `δ` and in the number of
  samples; equality of all block laws is equivalent to `M^X =^(d) M`. Notes:
  the GHP quotient carries a genuine metric elsewhere in the project, so limits
  are unique; working in a fixed universe loses nothing.

Proof route. Tightness follows the source (diameters and covering numbers,
Gromov compactness, Prokhorov), with the finitely many early laws handled
through open covering sets and closed diameter sets. Identification of
subsequential limits departs from the source: instead of the GP topology,
Lemma `equivGP` (N15) and Lemma `GP+GH=GHP` (N16), a fully supported compact
space is reconstructed almost surely from its iid sample matrix (finite row
spaces in the sup metric, density of the samples, strong law for the cells of
fine partitions), so the law of a random fully supported space is determined
by its annealed matrices. N15 and N16 themselves remain unproved.

## Critical `eq:GP` and M03 (up to the real-tree clause), 29 October 2026

Author: Claude. Reviewer for statement fidelity: a separate Claude agent that did
not write the declarations (read-only, no builds). Source SHA-256 `23a485d5…`.

- `critical_scaling_limit` (`Probability/CriticalScalingLimit.lean`) against
  `thm:critique` (lines 360–365), `sec:deflim` (1141–1162), the continuous
  coalescent (1164–1200) and `eq:GP`: **PASS with notes.**
  - Premises are exactly the source's: ±1 rows surviving to the horizon for
    positive `n`; `f > 0` a.e. (needed because Lean has `1/0 = 0`);
    $\mathsf{Lim}^{1/2}_{1/f}$ (with $1/f\in L^1$); $\mathsf{Lim}^{1/2}_{1/f^2}$
    on every $0<a<b<1$; $\max_{1\le k\le n}S^n_k=O(\sqrt n)$. Only a.e.
    measurability of $1/f$ is used and row 0 is unconstrained, which strengthens
    the result.
  - The limit `criticalTreeLaw (1/f)` mirrors the source's indirect definition of
    $\mathcal T(f)$ (the `C.1` limit): the unique law with a.s. full support and
    annealed blocks `criticalDistanceLaw (1/f) k`. That family depends only on
    $f$, through `IsGenealogyLimit` and `upperLimit`. Uniqueness is
    `IsGenealogyLimit.unique` together with `eq_of_annealedDistanceLaw_eq`.
  - `distanceOfGenealogy` is $P(b)+P(b')-2P(c)$ with $P=\tfrac12\int_0^\cdot
    1/f$. This is exactly $\int_C^{B_j}(2f)^{-1}+\int_C^{B_l}(2f)^{-1}$, with a
    zero diagonal ($C_{jj}=B_j$).
  - The continuous model's encoding matches the source:
    - births are uniform on the cube;
    - each pair of current clusters merges at rate $1/f(t)^2$ as time decreases;
    - there is no factor-2 error (hazard $1/\binom S2$ at up-steps, which are
      half of all steps);
    - thresholds and endpoints affect only null sets;
    - hazard integrals stay inside $(0,1)$.
  - No vacuity: both epsilon specifications are proved satisfiable under the
    hypotheses, and the conclusion restates the characterization.
  - Only the real-tree clause (U26) of the source conclusion is missing.
  - Non-blocking notes: there is no formal example satisfying the hypotheses
    (informally, $f\equiv1$ with a walk climbing to $\lceil\sqrt n\rceil$ and
    then alternating), and the GHP encoding relies on the earlier M02 ruling.
- `tendsto_forward_annealedDistanceLaw_critical` is `eq:GP` without the
  $O(\sqrt n)$ assumption, consistent with the source's remark after
  `thm:critique`.

Proof route.
- N12b is proved by the exact Markov law of the tracked connectivity chain,
  convergence of its matrix products to matrix exponentials over birth-free
  windows, a quantile coupling of the iid births, dominated convergence, and
  identification on a co-countable π-system of upper sets.
- The plane-forest density N11 and the local limit N12a are not used.
- `C.1` was generalized to a family of block laws (`leafTightFamily`).

## Real-tree clause U26 and the complete M03, 29 October 2026

Author: Claude. Reviewer for statement fidelity: a separate Claude agent that did
not write the declarations (read-only, no builds).

- `RealTree.IsRealTree` (`Geometry/RealTree.lean`): **PASS.**
  - It is equivalent to the standard definition of Evans and Le Gall: a unique
    isometric segment $[0,d(s,t)]\to T$ between any two points, and every
    injective continuous arc from $s$ to $t$ having the segment's image.
  - Functions on ℝ constrained to `Icc` are equivalent to functions on the
    interval.
  - The case $s=t$ is vacuous exactly as in the standard definition, and the
    definition is not vacuous (a two-point space fails it).
- `critical_scaling_limit_realTree` (`Probability/CriticalRealTree.lean`):
  **PASS with notes.**
  - The hypotheses are identical to `critical_scaling_limit`.
  - The new conclusion `∀ᵐ X, IsRealTree (underlyingGH X).Rep` is faithful,
    because the representative is isometric to every carrier of the class.
  - Notes, non-blocking:
    - A docstring said "compact" where the hypothesis is completeness; fixed.
    - An `IsRealTree.of_isometryEquiv` corollary would make the statement
      literal on carriers; optional.
    - The proof route differs from the source's edge-realization argument
      (recorded in report row U26).

## M04a statement checkpoint, 29 October 2026

Author: Claude. Reviewer: a separate Claude agent (read-only).

- `RealTree.degree`, `RealTree.IsLeaf` (`Geometry/RealTreeDegree.lean`) and
  `LeavesCarryMass` (`Probability/CriticalLeaves.lean`), with the planned statement
  `∀ᵐ X ∂criticalTreeLaw (1/f), HasFullSupport X ∧ LeavesCarryMass X` under the
  hypotheses of `thm:critique`: **PASS with notes.**
  - The degree counts the components of $T\setminus\{x\}$, and a leaf has
    degree one (Evans' convention).
  - "Full measure on leaves" is expressed as almost every point being a leaf,
    for every representative.
  - Notes, applied:
    - The one-point convention is now stated in the docstring.
    - The real-tree clause is included in the final conjunction
      (`criticalTreeLaw_ae_leaves`).

## M04b–c statement design review, 29 October 2026

Author: Claude. Reviewer: a separate Claude agent (read-only), comparing the
planned statements with `thm:properties` (2) and its proof.

- Planned statements, under the hypotheses of `thm:critique`:
  - `IsBinaryTree X := ∀ x, degree x ≤ 3`;
  - M04b: almost surely, `IsBinaryTree (underlyingGH X).Rep` iff
    $\int_0^{1/2} f(t)^{-2}\,dt=\infty$ (as a lower Lebesgue integral of
    `(1 / f t) ^ 2` on `Ioc 0 (1/2)`);
  - M04c: if that integral is finite, almost surely some ρ has `degree ρ = ⊤`
    and every other branch point has degree exactly 3.
- Verdict: **PASS with notes.**
  - Docstrings must say that ρ represents the source's root only up to the
    unpointed Gromov–Hausdorff–Prokhorov encoding, and that ρ is automatically
    unique (two points of infinite degree are impossible in the second clause).
  - The source's "degree two" for branch points counts children; in the metric
    degree used here a binary branch point has degree 3. The source's "root of
    degree 1" (infinite-integral case) cannot be expressed without a pointed
    limit and is not claimed.
  - `IsBinaryTree` should be documented as "all degrees at most 3".

## M04b–c final statement checkpoint, 29 October 2026

Author: Claude (statements); proofs of the triple-merger, root-merger and star
geometry lemmas by Claude subagents. Reviewer: a separate Claude agent (read-only).

- `RealTree.IsBinaryTree`, `criticalTreeLaw_ae_binary_iff` (M04b),
  `criticalTreeLaw_ae_rootDegree` (M04c) and `critical_tree_properties`
  (`Probability/CriticalBranching.lean`): **PASS with notes.**
  - The hypotheses are token-for-token those of `critical_scaling_limit`, and the
    integral is the source's $\int_0^{1/2}f^{-2}$.
  - Quantifier order and almost-sure scope are faithful; ρ depends on the tree.
  - Binary means metric degree at most three. A rooted reading would also cap the
    root at two children, which cannot be stated for unpointed limits; the reverse
    direction is strengthened (a degree-⊤ point witnesses non-binarity).
  - "Root of infinite degree, other branch points binary" is rendered in the
    strongest unpointed form; ρ is automatically unique.
  - Notes, applied:
    - The "root has degree 1" remark of the proof is stated as not claimed in the
      docstrings of `criticalTreeLaw_ae_binary_iff` and `critical_tree_properties`.
    - The proof heading "(3)" is recorded in `MANUSCRIPT_RECOMMENDATIONS.md`.
    - The report row and entry-point imports are updated.

## N09 statement checkpoint, 29 October 2026

Author: Claude subagent (proof); statement fixed in advance by Claude. Reviewer:
a separate Claude agent (read-only). This section supersedes the N09 and
M03–M05 rows of the older reconciliation table above.

- `bounded_population_GH_limit` (`MainResults/BoundedPopulation.lean`):
  **PASS with notes.**
  - Hypotheses match `thm:alpha0`: ±1 signs, $\tau(X^n)>n$ as positivity of
    $S^n_k$ for $k\le n$, and one constant $M$ bounding $S^n_k$ (natural-number
    $M$ loses nothing).
  - The scaling is exactly $1/h_n^+$ (`Freezing1.heightScale` of the companion
    schedule, equal to the source's $h_n^+$), the tree is the actual forward tree
    with graph distance, and the target is Mathlib's `unitInterval`.
  - Convergence in probability of the GH distance to a deterministic limit is
    faithful. At $n=0$ the scale is $1/0=0$ and the space falls back to a point,
    irrelevant for the limit; disconnected trees occur only on a null set.
  - Not covered: the GHP nonuniversality remark (U20, open). The proof's
    $h_n^+=\Theta(n)$ is used only through $h_n^+\ge n/(2M)$; the companion $L^p$
    height theorem is replaced by convergence in probability, which suffices.
- Status since the older table: M03 and M04 (all of `thm:properties`) and N09
  are proved; M05 remains open (external mathematics, see
  `docs/coverage-gaps.md`).

## N11, U23 and U04b statement checkpoint, 30 October 2026

Authors: Claude subagents (proofs); statements fixed in advance by Claude, decoding
statements added on request. Reviewer: a separate Claude agent (read-only), in two
passes (density file, then decoding file).

- U04b, `supercritical_not_coverable` and `supercritical_not_tight`
  (`MainResults/SupercriticalNonTight.lean`): **PASS with notes.** Hypotheses are
  those of M06; "not tight" is `¬ IsTightMeasureSet` on the GHP space. The radius is
  one small fixed $r$ (S08 correction, recorded in docstrings); failure at $r$ implies
  failure at every smaller radius. Not stated: no subsequential weak limit (follows
  by the portmanteau theorem).
- N11 (`CoalescentDensity.lean`, `CoalescentDecoding.lean`): **PASS with notes.**
  Density, admissibility, zero-time count and hypotheses are faithful. The joint law
  of the decoded $(F,B,C)$ is literal in history form, non-plane and plane; S09 root
  order by label is a working interpretation. Remaining: the bijection with the
  source's labelled forests $\mathfrak F^+_{r,k}$ and the equivalence with
  increasing-bijection admissibility (prose only). Applied: the docstrings now say
  "history form" instead of "source form".
- U23: **PASS with notes.** Existence in law for every measurable locally
  square-integrable $g$; distinct merge times; no merger with positive probability
  when $\int_0 f^{-2}<\infty$; one final cluster when it diverges. No explicit
  path process.

## N11 source form, U01 and no-weak-limit checkpoint, 30 October 2026

Reviewer: a separate Claude agent (read-only).

- N11 in source form (`CoalescentForests.lean`): **PASS with notes.** Labelled
  forests $\mathfrak F^+_{r,k}$ with root-label order (S09), the increasing-bijection
  admissibility (relabelling forced to be the rank map), the bijection with plane
  histories, and the event-level law with density $1_{[0,1]^k}g_{r,k}$. Notes applied:
  docstrings no longer call the admissibility "literal" (it adds the Proposition's
  range $0<c<1$; births enter through the reference measure); `sourceForest_law`
  cites `planeLaw_eq_uniformOrders`; the decoding header points to the encoding.
  Optional, not done: a corollary that the densities sum to one over $r$ and $F_0$.
  U24's forest and admissibility clauses are now substantially covered; its
  time-change clauses are separate.
- U01 first clause (`urtLaw`, `treeLaw_allPlus_eq_urtLaw`): **PASS.** `urtLaw` is
  an independent uniform-recursive-tree law; stated for the Bool schedule.
- `supercritical_no_weak_limit`: **PASS.** No subsequence converges weakly at the
  source's normalization $n^{1-\alpha}$; faster normalizations (S19) not claimed.

## N12a statement checkpoint, 30 October 2026

Author: Claude subagent (statement corrected from S10, proof). Reviewer: a separate
Claude agent (read-only).

- `critical_local_limit_plane` (`CriticalLocalLimitPlane.lean`), with
  `critical_local_limit_forest_of_profile` and `critical_local_limit`
  (`CriticalLocalLimit.lean`): **PASS with notes.** Record as "proved in corrected,
  tracked-chain form".
  - Content kept: the normalized conditional pattern probability at iid uniform
    down-/up-step samples converges in law ($n\to\infty$, then $\varepsilon\downarrow0$)
    to $g_{r,k}(\mathcal F_0,\widetilde B,\widetilde C)$.
  - Corrections (S10): all $k$ births conditioned on; collisions give $0$; iid
    normalization $N^{-k}$; cutoff event $R^n(\varepsilon)=r$ (differs from the printed
    event only on $\{\widetilde C^n_{r+1}\le\varepsilon n\}$); merge rates as marks, since
    the source's location-only step is invalid for measurable $1/f$.
  - Plane convention (left child = surviving root) is the source's discrete order;
    any fixed rule gives the same law.
  - Remaining: finite decoding of the discrete event to $\mathcal F^n_r$ and the
    ordered $C^n_j$; the rest of the source proof belongs to N12b/U28 (bypassed).
  - Applied: the `CriticalLocalLimit.lean` header now points to the plane form.

## U20 statement checkpoint, 30 October 2026

Reviewer: a separate Claude agent (read-only). `BoundedPopulationMeasure.lean`:
**PASS with notes.** New formulation of the line-1034 remark (no precise source
statement or proof): two admissible bounded-population arrays with the same GH limit
and GHP limits at positive distance, and no universal deterministic GHP limit. The
general theorem `bounded_population_GHP_limit` is a supporting extension (profile
convergence hypothesis, essentially necessary by Arzelà–Ascoli). Not exported: an
array with no GHP limit and the exclusion of random universal limits (immediate).
The example arrays were checked by hand (signs, survival, population at most 3,
height scales, limit profiles and the separating band).

## U04b recursive-tree clause checkpoint, 30 October 2026

Reviewer: a separate Claude agent (read-only). `RecursiveNoLimit.lean`: **PASS with
notes.** S19-qualified rendering: any weak GHP limit of $T_n/a_n$ is the point; a limit
exists iff $a_n/\log n\to\infty$; non-tightness and no subsequential limit when
$a_n\le C\log n$ eventually. `urtLaw` is the paper's no-freezing tree with $n+1$
vertices and the uniform vertex measure; edge cases ($\log 0$, $\log 1$, singleton
fallback) are harmless and not exploited. Notes applied: stale S19, coverage and
report lines updated; module docstring now says the diameter is at most twice the
height. Optional, not done: frequently-bounded and subsequential extensions.

## S15/S16 refutation checkpoint, 30 October 2026

Reviewer: a separate Claude agent (read-only). `ExcursionCounterexamples.lean`:
**PASS with notes.** The conditioned-walk model is faithful (`excursionLaw_eq_cond`);
the Kemperman right side and $X_n(\delta)$ are exact transcriptions; the S16 ranges
match the source. Notes applied: the S15 refutation is restricted to $n\ge1$, $k\ge1$
so that every failure is in the source's domain; the S16 rows state that the
counterexample does not refute a $C(\varepsilon)$ version. Not Lean-checked: the
reviewer's corrected local formula (enumeration for $n\le6$) and the replacement
bound $C\delta/\varepsilon$ (paper sketch).

## GP space checkpoint (U49/E09 GP part, S18), 30 October 2026

Reviewer: a separate Claude agent (read-only). `GromovProkhorov.lean`: **PASS with
notes.** Faithful GP equivalence (Mathlib support, equivalent to the source's
not-necessarily-onto isometry form); exact source infimum for $d_{GP}$ with the
Lévy–Prokhorov convention; separation for arbitrary Polish spaces; Polishness for
$d_{GP}$ itself; S18 as a projection with a non-injectivity witness. Notes: "Polish"
read as complete separable metric (the only reading under which separation holds:
$((0,1),\mathrm{Leb})$ vs $([0,1],\mathrm{Leb})$); ambient spaces restricted to the
carriers' universe (harmless, not proved in Lean); sampled-matrix laws not yet
descended to GP classes (N15 setup); even (GP class, GH class) is not injective
($[0,1]$ with $\delta_0$ vs $\delta_{1/2}$), which is why N16 needs full support. This
section supersedes the U49–U52 row of the older reconciliation table.

## N15 and N16 statement checkpoint, 30 October 2026

Reviewers: separate Claude agents (read-only).

- N16, `MeasuredGHSpace.tendsto_ghp_of_gp_of_gh` (`GPGHtoGHP.lean`): **PASS with
  notes.** Exact source hypotheses (a.s. full support of the limit, weak GP and GH
  convergence) and conclusion; GP sense via `gpProjection` (S18 reading); Borel
  structure on `GHSpace` as instance arguments (equivalent to the Borel case, and
  suppliable as in `GHPTightness.lean`). Full support is necessary.
- N15, `GPSpace.equivGP` (`GPMatrixCharacterization.lean`): **PASS with notes.**
  Faithful $M^X$ on $\mathbb R^{\mathbb N\times\mathbb N}$ (product topology), descended to
  GP classes; statement for arbitrary Polish measured spaces, no hidden hypotheses;
  Gromov reconstruction (`matrixLaw_injective`) genuinely proved for Polish spaces.
  Route differs from Löhr 2013 (empirical reconstruction, no □λ comparison or GPW
  criterion). Only the deterministic lemma; random uses are handled by N16/N17.
- Evidence: `evidence/gp-lemmas-axioms.log` (3,524 declarations, 283 modules).

## Documentation reconciliation, 30 October 2026

A reconciliation pass checked every "proved" claim in `FORMALIZATION_REPORT.md`,
`docs/coverage-gaps.md`, `docs/publication-readiness.md` and `HANDOFF_CLAUDE.md`
against the import closure of `Freezing2.lean` (283 modules). Earlier sections of
this append-only log are superseded where later dated sections differ (for example,
U20 is proved after the N09 section, and the U04b no-weak-limit corollary is proved
after the U04b section). S09 and S18 now carry dispositions in the inventory.

## U01 second clause and model facts checkpoint, 30 October 2026

Reviewer: a separate Claude agent (read-only). `UniformPlaneTree.lean`: **PASS with
notes** (correct Neveu encoding, uniform law, faithful conditioning; birth-time
order is stronger than the companion's random order; the "random compact metric
space" law equality in `MeasuredGHSpace` is not stated; docstrings reworded to
"pathwise", line references fixed). `ModelFacts.lean`: **PASS** for U06 and U20
($L^p$), **PASS with notes** for U29 (limit-side normalization only; line labels).
Evidence: `evidence/plane-tree-axioms.log` (3,645 declarations, 285 modules).

## Publication Challenge review, 30 October 2026

Reviewer: a separate Claude agent that did not write the interface (read-only).
`Challenge.lean` (M01, M02, M03 with M04, corrected M06, N09): **PASS with notes**,
no required fixes. Model (Algorithm 1), hypotheses, GHP distance and the
representative-level topology are faithful; no degenerate `T` satisfies the
M03/M04 statement; M01 drops an unneeded hypothesis (stronger); M06 holds for
every k; the "root of degree one" remark cannot be stated unpointed. Optional
docstring notes applied (topology, unpointed root).
