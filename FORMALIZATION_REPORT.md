# Formalization report

## Source, scope, and status

This is a formalization of
[arXiv:2308.00484](https://arxiv.org/abs/2308.00484), *Uniform attachment with
freezing: Scaling limits* by Étienne Bellin, Arthur Blanc-Renaudie, Emmanuel
Kammerer and Igor Kortchemski, published in Ann. Inst. H. Poincaré Probab.
Statist. 61(4) 2679–2708 (2025),
[doi:10.1214/24-AIHP1497](https://doi.org/10.1214/24-AIHP1497).

The requested scope is every theorem, proposition, lemma, corollary, and
substantive mathematical claim in
[attachement-uniforme-2-final.tex](attachement-uniforme-2-final.tex), prioritizing
the Introduction's results. No claims have been excluded to make the project
appear complete. The source has 1,921 lines and SHA-256
`23a485d5a5dfaca01a05db28377d015fb1456c194a543d0cbf56f77619ad0cbf`.

**This is an incomplete formalization, not a verified publication candidate.**
The Introduction’s height theorem M01, subcritical GHP limit M02, and corrected supercritical matrix theorem M06 are proved. The critical tree limit M03 is proved: `critical_scaling_limit_realTree` gives Gromov–Hausdorff–Prokhorov convergence of the actual scaled forward trees to `criticalTreeLaw (1/f)`, a law depending only on $f$, of an almost surely fully supported random compact measured **real tree** (standard definition, U26). Its properties `thm:properties` are proved (`critical_tree_properties`): the mass measure charges only leaves (M04a); the tree is binary if and only if $\int_0^{1/2}f^{-2}=\infty$ (M04b); and otherwise some point has infinite degree while all other branch points have degree three (M04c, unpointed form). The CRT corollary M05 remains unproved; it depends on external mathematics absent from the pinned Mathlib and the companion project (see [docs/coverage-gaps.md](docs/coverage-gaps.md)). Every other named result environment now has a proved Lean counterpart, in the qualified forms recorded in the table below: all numbered results N01–N17 are proved, with N04 for distinct vertices (S02), N11 in source form under the S09 root-order interpretation, N12a in corrected tracked-chain form (S10), N12b in an equivalent form, N13 with repaired constants (S12), N14 for positive block indices (S11), and N15 by a route different from the cited one. Among the unnumbered claims, the first clause of U01, U04b's supercritical non-tightness (S08-corrected) and recursive-tree clause (S19-qualified), U20's nonuniversality (new formulation), U23 (in law), U25–U26, U31, U32 (leaf-tightness `eq:GH` and its transfer only; the intermediate displays `16/01/11h` and `eq:delta` are bypassed), U36–U39, U40 (without the source's "root degree one" clause, which needs a pointed limit), U41, and the GP space of U49/E09 (with S18 as a projection) are proved, and the false displays S15 and S16 are refuted in Lean. The remaining obligations are listed in the final section. The independent initial
[source inventory](docs/source-inventory.md) records all **23 named result
environments**, multipart obligations, 58 groups of substantive claims (U53–U58
added from the 30 October 2026
[omission scan](docs/omission-scan-2026-10-30.md)), external dependencies,
source issues S01–S23, and open questions. Its stable IDs are used below. Every inventory
obligation not explicitly discharged here remains unresolved.

Lean and Mathlib remain pinned to **v4.35.0**, with the original
`lake-manifest.json`. The entry point is [Freezing2.lean](Freezing2.lean).
The selected destinations are **GitHub and Palomar**, for local preparation;
no remote publication or registry submission has been performed. The previous
“destination not selected” setup note is superseded by the user's request.

On 29 October 2026 the user authorized a **zero-diagonal correction** to M06,
`thm:sur-critique`: preserve the sum of branch lengths when $i\ne j$, set it to
zero when $i=j$. The supplied TeX has not been edited. This correction is not
counted as a proof of the originally printed false formula.

## Result correspondence

| Inventory ID | Paper claim | Lean correspondence | Coverage and proof correspondence |
| --- | --- | --- | --- |
| M01 | `thm:heightalpha` | `height_scaling_limit_positive_horizons` in [Height.lean](Freezing2/MainResults/Height.lean) | **Proved.** Actual forward uniform-attachment/freezing tree law, graph-distance height, every finite real $p\geq1$, exact $n^{1-\alpha}$ normalization and $\int_0^1(2f)^{-1}$. The companion theorem and logarithmic-growth hypothesis are proved dependencies. Only global reciprocal $L^1$ is needed; local $L^2$ is unnecessary. |
| M02 | `thm:sous-critique` | `subcritical_scaling_limit` in [SubcriticalDistribution.lean](Freezing2/MainResults/SubcriticalDistribution.lean) | **Proved.** Weak convergence of the actual forward uniformly measured tree, scaled by $1/n^{1-\alpha}$, to the exact segment with the specified image measure. The GHP topology is induced by the literal summed ambient-isometry infimum on whole-space measure-preserving-isometry classes. Original positive-horizon assumptions are retained. Zero-distance separation is now proved for the exact whole-space quotient, with a genuine metric preserving the previously constructed topology. The same exact topology is now proved Polish, by separate completeness and separability arguments; the deterministic-limit proof itself did not require them. |
| M03 | `thm:critique` | `critical_scaling_limit_realTree` in [CriticalRealTree.lean](Freezing2/Probability/CriticalRealTree.lean); `critical_scaling_limit` in [CriticalScalingLimit.lean](Freezing2/Probability/CriticalScalingLimit.lean) | **Proved.** Under the source hypotheses $\mathsf{Lim}^{1/2}_{1/f}$, $\mathsf{Lim}^{1/2}_{1/f^2}$ and $\max S=O(\sqrt n)$ (positive horizons), `forwardMeasuredTreeLaw x (1/2) n` converges weakly in GHP to `criticalTreeLaw (1/f)`, the unique law of an a.s. fully supported random compact measured space whose annealed sampled distance matrices are `criticalDistanceLaw (1/f) k`; it depends only on $f$, matching the source's indirect definition of $\mathcal T(f)$ through `C.1`. Almost surely the limit space is a real tree in the standard sense (`IsRealTree`: unique geodesic segments, and every injective arc has the segment's image), row U26. Ingredients: forward `eq:GH`, `C.1` for block-law families (`leafTightFamily`), the critical `eq:GP` (row U25). |
| M04a | `thm:properties` (1) | `criticalTreeLaw_ae_leaves` in [CriticalLeaves.lean](Freezing2/Probability/CriticalLeaves.lean) | **Proved.** Under the hypotheses of `thm:critique`, almost surely $\mathcal T(f)$ is a compact real tree whose mass measure has full support and gives full measure to its leaves (`LeavesCarryMass`: for every representative, almost every point has degree one; degree = number of components of $T\setminus\{x\}$). Route: limiting coalescence times differ almost surely from birth times (U38, `criticalGenealogyLimit_merge_ne_birth`), so three iid points form strict triangles; a non-leaf lies strictly inside a segment, and nearby points stay separated (Gromov-product argument), giving positive probability to a degenerate triangle by full support and Fubini. |
| M04b–c | `thm:properties` (2) | `criticalTreeLaw_ae_binary_iff`, `criticalTreeLaw_ae_rootDegree`, combined with M04a in `critical_tree_properties`, all in [CriticalBranching.lean](Freezing2/Probability/CriticalBranching.lean) | **Proved.** Under the hypotheses of `thm:critique`, almost surely: $\mathcal T(f)$ is binary (`IsBinaryTree`: every point has metric degree at most $3$) if and only if $\int_0^{1/2}f^{-2}=\infty$; and if $\int_0^{1/2}f^{-2}<\infty$ there is a point of infinite degree, every other point of degree at least $3$ having degree exactly $3$. The limit is unpointed, so this point represents the root only up to the GHP encoding; it is automatically unique. The source's "binary branch point" counts children, which is metric degree $3$. The source's remark that the root has degree $1$ when the integral is infinite needs a pointed limit and is not formalized. Route: degrees are detected by stars among iid samples ([RealTreeStar.lean](Freezing2/Geometry/RealTreeStar.lean)). A four-star in the limiting genealogy forces three samples with a common coalescence time (ultrametric argument); triple mergers at positive times are null (U41), so the common time is $0$ and the arms are the heights. Hence no four-star when coalescence at time $0$ is null (U40, infinite integral); two distinct points of degree $\ge4$ would give contradictory arms; and when the integral is finite, many early samples pairwise coalesce at time $0$ (U39), giving points of every finite degree. |
| M05 | `cor:CRT` | None | Unproved; Brownian-excursion approximation also has source defects S14–S17. |
| M06 | `thm:sur-critique`, corrected | `supercritical_distance_matrix_limit` in [Supercritical.lean](Freezing2/MainResults/Supercritical.lean) | **Proved with the authorized zero diagonal.** Actual forward tree, root at index zero, every fixed number of conditionally iid uniform vertices, literal graph distances divided by $n^{1-\alpha}$, repeated samples, exact independent source branch integrals, and original positive-horizon assumptions. Explicit sampled-law transport uses the proved N01 and canonical rooted graph isomorphism. Independently audited and included in the integration evidence below. |
| N01 | `thm:samelaw` | `forward_reverse_same_law` in [ForwardReverseLaw.lean](Freezing2/Probability/ForwardReverseLaw.lean); `source_forward_reverse_same_law` in [SourceSameLaw.lean](Freezing2/Probability/SourceSameLaw.lean) | **Proved.** Equality of the actual forward law and canonical pushforward of the stamped reverse law, preserving the rooted graph, edge labels and freezing times. Actual canonical fibres are exactly active-label permutation orbits; legal history uniqueness, exact atom masses and factorial cancellation give the law comparison. The original integer-sign wrapper includes extinction. |
| N02 | `lem:accroissementH` | `conditional_source_height_increment` in [ReversePaper.lean](Freezing2/Probability/ReversePaper.lean) | **Proved for the constructed reverse history.** Original integer signs and one-based labels, integer-subtraction event, conditional expectation given the edge-labelled history, and the full $n\leq\tau$ endpoint. Actual graph-step support, edge labels, forest membership, and graph-distance heights are proved dependencies. |
| N03 | `lem:bunif` | `sourceUniformVertexLaw_birth_lt` in [ReverseUniformVertex.lean](Freezing2/Probability/ReverseUniformVertex.lean) | **Proved for actual conditional uniform sampling from the reverse tree**, including extinction. The terminal marginal, canonical label transport, and exact finite birth CDF are proved. |
| N04 | `loi du temps de coalescence`, corrected | `sourceCoalescenceTime_probability` in [CoalescenceHistory.lean](Freezing2/Probability/CoalescenceHistory.lean) | **Corrected distinct-vertex law proved for the actual reverse history.** Coalescence is a maximum of connected forest phases; first merger, separation at common birth, terminal connection, conditional survival, and exact binomial product are proved. On the diagonal coalescence equals birth; the false missing-distinctness formula remains refuted. |
| N05 | `prop:bennett` | `Freezing2.bennett_inequality` in [Bennett.lean](Freezing2/Probability/Bennett.lean) | **Both strict tail bounds proved**, for independent Bernoulli variables with arbitrary parameters in $[0,1]$, positive mean, and every $t>0$. Uses MGF factorization and Chernoff; no additional integrability or $t<m$ assumption. |
| N06(i) | `lem:hnalpha(i)` | `population_sublinear_of_positive_horizons` in [SourceHypotheses.lean](Freezing2/Analysis/SourceHypotheses.lean); `population_sublinear_at` | **Proved.** Global reciprocal $L^1$ convergence to an a.e.-positive limit suffices; local $L^2$ and the lower exponent bound are unnecessary. The source's fixed preceding-interval argument is repaired quantitatively, including floor rounding. |
| N06(ii) | `lem:hnalpha(ii)` | `tendsto_upSteps_measure`, `tendsto_downSteps_measure` in [SignMeasures.lean](Freezing2/Analysis/SignMeasures.lean) | **Proved.** Actual finite measures with coefficient $2/n$, atoms at $i/n$, weak convergence to restricted Lebesgue measure; both signs and endpoint zero included. Exact counts followed by Portmanteau, as in the paper. |
| N06(iii) | `lem:hnalpha(iii)` | `harmonicTotal_asymptotic`, `harmonicUpTotal_asymptotic` in [HarmonicConclusions.lean](Freezing2/Analysis/HarmonicConclusions.lean) | **Proved.** The two genuine asymptotic equivalences use the printed power normalization and a proved strictly positive limiting integral. Mesh endpoint corrections and the reciprocal error limit are supplied. |
| N06(iv) | `lem:hnalpha(iv)` | `tendsto_harmonicDeviationMax` in [HarmonicConclusions.lean](Freezing2/Analysis/HarmonicConclusions.lean) | **Proved.** The exact finite maximum covers every inclusive interval $1\leq a\leq b\leq n$, with the original normalization. A corrected endpoint-potential identity replaces the false printed pairing display. |
| N06(v) | `lem:hnalpha(v)` | `tendsto_coalescenceIntervalErrorMax` in [CoalescenceLimit.lean](Freezing2/Analysis/CoalescenceLimit.lean); all five parts in `population_profile_lemma` | **Proved.** Exact finite maximum over every source interval, all $\varepsilon>0$, original normalization and integrand. Finite coalescence pairing, both denominator corrections, local square-profile convergence, actual minimum estimate, and uniform mesh endpoint errors are proved. |
| N07 | `height=ok` | `tendsto_reverseDistanceErrorMax_positive_horizons` in [DistanceApproximation.lean](Freezing2/Probability/DistanceApproximation.lean) | **Proved for actual reverse-tree graph distances.** Exact first-merger geometry, preservation under acyclic growth, equality with finite induced-tree distances, measurable all-pairs maximum, actual height concentration, and original positive-horizon profile assumptions. No local $L^2$ assumption is needed. N01 is now proved; the corresponding forward observable export remains separate. |
| N08 | `lemme ça coalesce vite` | `tendsto_normalized_coalescenceGapMax_probability_positive_horizons` in [SubcriticalCoalescenceLaw.lean](Freezing2/Probability/SubcriticalCoalescenceLaw.lean) | **Proved for the actual reverse history.** The literal maximum of absolute birth/coalescence gaps divided by $n$ tends to zero in probability. Exact survival products, all-pairs union bound, boundary clipping, safe integer rounding, and positive-horizon source notation are supplied. |
| N09 | `thm:alpha0` | `bounded_population_GH_limit` in [BoundedPopulation.lean](Freezing2/MainResults/BoundedPopulation.lean) | **Proved.** If $\tau(X^n)>n$ and $S^n_k\le M$ for all $k\le n$, the actual forward trees with graph distance rescaled by $1/h_n^+$ converge in probability to $[0,1]$ for the GH distance. Route as in the source: the height divided by $h_n^+$ tends to $1$ (companion height theorem, here in probability, using $h_n^+\ge n/(2M)$); a union bound over vertex pairs makes macroscopic side branches exponentially unlikely, via the reverse depth bound $d(u,w)\le b_n(u)-c_n(u,v)$ transported by N01; a tree whose pair excesses $d(u,v)-|h(u)-h(v)|$ are small is GH-close to the segment of its height. The GHP nonuniversality remark is proved separately (U20). |
| N10 | `lemme ça coalesce en zéro` | `tendsto_normalized_sampledCoalescence_probability_positive_horizons` in [SupercriticalCoalescenceLaw.lean](Freezing2/Probability/SupercriticalCoalescenceLaw.lean) | **Proved for actual independent uniform samples of the reverse tree.** The product law, collision correction, late-birth tail, compact-interior hazards, and exact absolute normalized event are supplied; original positive-horizon $f$ assumptions retained. Built, independently reviewed, and included in the 104-module axiom checkpoint. |
| N11 | `loi du coalescent généralisé` | `sourceForest_law`, `map_restrict_planeLaw`, `planeLaw_forestEvent`, `planeLaw_forestEvent_prod`, `sourceTripletEquiv`, `existsUnique_planeForest` in [CoalescentForests.lean](Freezing2/Probability/CoalescentForests.lean); history form in [CoalescentDecoding.lean](Freezing2/Probability/CoalescentDecoding.lean) and [CoalescentDensity.lean](Freezing2/Probability/CoalescentDensity.lean) | **Proved (source form).** For $k\ge1$, $r<k$ and $F_0\in\mathfrak F^+_{r,k}$ (`SourceForest`: $r+1$ plane binary trees on labels $r+1,\dots,2k-1$ increasing along branches, trees ordered by root label, S09), $P(\mathcal F=F_0,\ C_1=\dots=C_r=0,\ (B,C_{r+1},\dots,C_{k-1})\in S)=\int_S 1_{[0,1]^k}(b)\,g_{r,k}(F_0,b,c)\,db\,dc$, where $g_{r,k}=2^{-(k-1-r)}\exp(-\int_0^1\binom{a(t)}2f^{-2})\prod f(c_j)^{-2}$ on admissible triplets and $0$ elsewhere ($\exp(-\infty)=0$, $a(t)$ as in the source). Admissibility (`SourceAdmissible`) is the source's increasing-bijection definition combined with the Proposition's range $0<c<1$; the relabelling is necessarily the rank map (`phi_eq_countBelow`). The forest is a.s. defined, and the plane law is the decoded limiting genealogy with independent uniform child orders (`map_forgetOrders_planeLaw`, `planeLaw_eq_uniformOrders`). Route: the density law satisfies the semigroup characterization (path expansion of the propagators), hence equals the limit; a measurable decoding and an explicit bijection with labelled forests give the source form. Hypotheses: $g=1/f$ measurable and locally square-integrable on $(0,1)$ (a measurable modification suffices under the profile hypotheses). Independent reviews: PASS with notes. |
| N12a | `eq:cv locale`, corrected (S10) | `critical_local_limit_plane` (plane form), `critical_local_limit_forest_of_profile` (non-plane, limit $2^{k-1-r}g_{r,k}$) and the bridge `ae_patternEvent_iff_coalescenceTimes` in [CriticalLocalLimitPlane.lean](Freezing2/Probability/CriticalLocalLimitPlane.lean); `critical_local_limit` in [CriticalLocalLimit.lean](Freezing2/Probability/CriticalLocalLimit.lean) | **Proved in corrected tracked-chain form.** Under the source hypotheses ($\alpha=1/2$, no measurability of $g=1/f$), for $k>r\ge0$ and $\mathcal F_0\in\mathfrak F^+_{r,k}$: $(n/2)^{2k-1-r}$ times the probability, under one reverse history and $k$ iid uniform vertices, that the vertices are the frozen vertices born at $\widetilde B^n$ and that the merges above $\varepsilon n$ occur at $\widetilde C^n$ and form $\mathcal F_0$ (children ordered by root survival), evaluated at iid uniform down-step $\widetilde B^n$ and up-step $\widetilde C^n$, converges in law as $n\to\infty$ for each $\varepsilon>0$, and these limits converge as $\varepsilon\downarrow0$ to the law of $g_{r,k}(\mathcal F_0,\widetilde B,\widetilde C)$. Corrections: all $k$ births are conditioned on; colliding samples give $0$; the iid normalization is $N^{-k}$ with $((n/2)/N)^k\to1$; the cutoff event is $R^n(\varepsilon)=r$ (prescribed merges strictly above $\varepsilon n$), which differs from the printed event only on $\{\widetilde C^n_{r+1}\le\varepsilon n\}$ and leaves the iterated limit unchanged; exact merge rates enter as marks of the merge phases, since $1/f$ is only measurable (the source's location-only argument is invalid). The discrete event is the tracked connectivity chain with root-survival orientations, identified with the truncated pairwise coalescence times; the finite decoding to $\mathcal F^n_r$ and the ordered $C^n_j$ is not formalized. `eq:cv locale bis`, Fatou and Scheffé (N12b/U28 route) are bypassed. Independent review: PASS with notes. |
| N12b | `cv coalescent` | `exists_tendsto_genealogyLaw`, `tendsto_genealogyLaw_criticalGenealogyLimit` in [CriticalGenealogyLaw.lean](Freezing2/Probability/CriticalGenealogyLaw.lean), [CriticalDistanceLimit.lean](Freezing2/Probability/CriticalDistanceLimit.lean) | **Proved in an equivalent form.** The joint law of the scaled birth and pairwise coalescence times of $k$ iid uniform vertices converges, and the limit is characterized by explicit values on upper sets built from matrix exponentials of the Kingman generator with hazard $\int f^{-2}$ (continuous propagator); it depends only on $f$. The proof bypasses the local limit N12a: exact tracked-chain law (`TrackedChain`), matrix-product limit (`MatrixProductLimit`, `TrackedChainLimit`), quantile coupling of the iid births (`VertexQuantileCoupling`), dominated convergence (`CriticalSampledGenealogy`) and identification on a co-countable π-system (`CriticalGenealogyLaw`). The source's plane-forest labels are not used. |
| N13 | `tightness time estimate`, repaired proof | `critical_sampled_cover_probability_of_isBigO` and `critical_sampled_cover_probability_uniform_positive_horizons` in [CriticalSampledCover.lean](Freezing2/Probability/CriticalSampledCover.lean) | **Proved.** Actual reverse forest law, one query vertex and $k$ covering vertices independently uniform on $\mathcal V_n$ (collisions and active atom retained), literal minimum distance $\Delta^n$, strict event $>n\ln(k)^2/\sqrt k$, bound $k^{-4}$ for all $k\geq K$ and all $n$ with $k\leq n^{1/3}$, survival $\tau(X^n)>n$ at positive horizons. The first export assumes the source hypothesis $\max_{1\leq k\leq n}S^n_k=O(\sqrt n)$; the threshold depends only on the array through that bound. Profile hypotheses are unnecessary. The proof repairs S12 (see below); the printed conditional-independence assertion is bypassed, not certified. |
| N14 | `OneStepTightness`, positive-index correction | `one_step_tightness_uniform_positive_blocks` in [OneStepTightnessAsymptotic.lean](Freezing2/Probability/OneStepTightnessAsymptotic.lean) | **Proved for positive block indices.** Actual reverse forest law, original $4\lceil Mn/\sqrt{k}\rceil$ block, original $k\leq n^{1/3}$ range, every positive $K$, distinct marked vertices and source birth constraints, exact $3M\sqrt{k}/(4K)$ bound. One threshold depends only on $M$. The printed $i=0$ negative forest phase remains undefined and is not certified. |
| N15 | `equivGP` | `GPSpace.equivGP`, `GPSpace.tendsto_iff_tendsto_matrixLaw`, `GPSpace.tendsto_iff_forall_tendsto_blockLaw`; consequences `GPSpace.matrixLaw_injective`, `GPSpace.isEmbedding_matrixLaw` in [GPMatrixCharacterization.lean](Freezing2/Probability/GPMatrixCharacterization.lean) | **Proved (deterministic statement, route different from Loh13).** For GP classes $X^n,X\in\mathbb K_{GP}$ of arbitrary complete separable metric spaces with Borel probability laws (no compactness or full support), $X^n\to X$ for $d_{GP}$ iff the law of $M^{X^n}$ converges weakly to that of $M^X$ on $\mathbb R^{\mathbb N\times\mathbb N}$ (product topology). `matrixLaw` is the push-forward of the iid product by $(x_i)\mapsto(d(x_i,x_j))_{i,j}$; it depends only on the law on the support and descends to `GPSpace`. Weak convergence on $\mathbb R^{\mathbb N\times\mathbb N}$ is equivalent to convergence of all finite top-left blocks. Direct half: the $k$-block law is $2k$-Lipschitz from $d_{GP}$ to Lévy–Prokhorov. Converse: the finite space reconstructed from $m+1$ samples is GP-close on average, uniformly over Polish measured spaces, transferred by portmanteau. No □λ comparison, GPW compactness criterion or separate reconstruction theorem is used. Consequences: Gromov's reconstruction theorem for Polish measured spaces, and $X\mapsto\mathrm{law}(M^X)$ is a topological embedding. Only the deterministic lemma is proved; the random uses are covered directly by N16 and N17. Independent review: PASS with notes. |
| N16 | `GP+GH=GHP` | `MeasuredGHSpace.tendsto_ghp_of_gp_of_gh` in [GPGHtoGHP.lean](Freezing2/Probability/GPGHtoGHP.lean) | **Proved.** Laws $P_n$, $Q$ on the exact whole-carrier GHP quotient `MeasuredGHSpace` (Borel), with $Q$-a.s. full support of the measure on the whole carrier: weak convergence of the GP laws (push-forwards under the 1-Lipschitz projection `gpProjection`, the S18 reading of $\mathbb K_{GHP}\subset\mathbb K_{GP}$) and of the GH laws (push-forwards under `underlyingGH` into Mathlib's `GHSpace`, Borel σ-algebra supplied as instance arguments) implies weak GHP convergence. No extra hypotheses; universe-polymorphic. Proof: GH tightness gives GHP tightness and Prokhorov; subsequential limits are identified by `eq_of_map_gpProjection_eq_of_map_underlyingGH_eq` (equal GP and GH laws with one law fully supported force equality), via open separated-point events, Lusin separation and injectivity of the GP projection on fully supported spaces. The full-support hypothesis is necessary ($[0,1]$ with $\delta_0$ vs $\delta_{1/2}$). Does not use N15. Independent review: PASS with notes. |
| N17 | `C.1` | `MeasuredGHSpace.leafTightCriterion : LeafTightCriterion` in [SampledReconstruction.lean](Freezing2/Probability/SampledReconstruction.lean); statement in [AnnealedSampling.lean](Freezing2/Probability/AnnealedSampling.lean) | **Proved by a different identification step.** Laws of GHP-measurable random compact measured spaces (exact whole-carrier quotient); annealed iid sampled matrices converge block by block to those of a law $M$ on $\mathbb R^{\mathbb N\times\mathbb N}$; leaf-tightness for every $\delta>0$. Conclusion: weak GHP convergence to some $Q$ with the same annealed matrix blocks and $Q$-a.s. full support. Tightness follows from Gromov compactness ([GHCovering.lean](Freezing2/Geometry/GHCovering.lean), [GHTightCriterion.lean](Freezing2/Probability/GHTightCriterion.lean), [LeafTightTightness.lean](Freezing2/Probability/LeafTightTightness.lean)) and Prokhorov's theorem. The subsequential limits are identified ([LeafTightLimits.lean](Freezing2/Probability/LeafTightLimits.lean)) by reconstructing a fully supported compact space from its sample matrix: rows of the matrix give a finite measured space in $\ell^\infty$ ([RowSpace.lean](Freezing2/Geometry/RowSpace.lean)), and these converge almost surely to the space by density of the samples ([SampleDensity.lean](Freezing2/Probability/SampleDensity.lean)) and the strong law for empirical measures ([EmpiricalMeasure.lean](Freezing2/Probability/EmpiricalMeasure.lean)). The paper's route through N15 and N16 is bypassed. Statement reviewed independently (PASS with notes). |

The stronger finite-label birth theorem `uniformVertex_birth_lt` assumes only
nonnegative terminal population. The source-specialized wrapper derives this
condition from absence of a zero strictly before the horizon; it covers
$n=\tau$, when the active-label set is empty. The uniform measure is an actual
Mathlib finite-set probability measure, with normalization proved separately.

## Substantive unnumbered claims and checked arguments

| Inventory obligation | Checked declarations / argument | Remaining portion |
| --- | --- | --- |
| U02, U06, U08 | Signed walk arithmetic; actual forward and reverse laws; validity, tree and component invariants; phase labels and birth times; canonical rooted graph/label correspondence; exact legal history supports and canonical fibres. Forward counts in [ForwardLaw.lean](Freezing2/Companion/ForwardLaw.lean) (vendored companion): `treeLaw_counts` (for $n\le\tau$, almost surely $S_n$ active vertices and (number of $+1$ steps)$+1$ vertices; U02 and U06), `treeLaw_vertices_card_real` ($N_n=(n+1+S_n)/2$ for $n\le\tau$; U06), `treeLaw_active_nonempty` (an active vertex exists for $n<\tau$) and `transitionLaw_eq_dirac_of_empty` (with no active vertex the step leaves the tree unchanged). Reverse labels (U08): `vertexLabels`, `vertexLabels_card`, `birthTime_frozen` ($b_n(i)=i-1$), `birthTime_active` ($b_n(a_j)=n$) in [Labels.lean](Freezing2/Discrete/Labels.lean); `mem_phaseLabels_iff_birthTime` (a label is present at reverse time $i$ iff $i\le b_n$) in [ReverseForest.lean](Freezing2/Companion/ReverseForest.lean); `sourceCoalescenceTime_self` ($c_n(u,u)=b_n(u)$) in [CoalescenceHistory.lean](Freezing2/Probability/CoalescenceHistory.lean); `sourceCoalescenceTime_le_birth_left`, `sourceCoalescenceTime_le_birth_right` in [DistanceApproximation.lean](Freezing2/Probability/DistanceApproximation.lean). | Forward/reverse equality in law and the supporting history/orbit comparison are discharged by N01. The active and total counts, the label carrier, the birth times, the diagonal coalescence value and the bounds $c_n(u,v)\le b_n(u)\wedge b_n(v)$ are covered by the declarations listed. U06 (line 480) is now proved in [ModelFacts.lean](Freezing2/MainResults/ModelFacts.lean): the law of $\mathcal T_n$ depends only on $X_1,\dots,X_n$ (`forward_treeLaw_eq_of_eqOn`, `freezingTreeLaw_eq_of_eqOn`); the trees are non-decreasing on every realisation (`forward_run_extends`) and almost surely under the natural coupling of the laws at times $m$ and $m+j$ (`forward_treeLaw_add_eq_bind`, `forward_treeLaw_ae_evolve_extends`); and $\mathcal L(\mathcal T_{n+1})=\mathcal L(\mathcal T_n)$ iff $\tau\le n$ (`forward_treeLaw_succ_eq_self_iff`), with pathwise versions. No path-space law of the whole sequence is constructed. Independent review: PASS. |
| U11 (`eq:pn`) | Exact counts plus `tendsto_upSteps_macroscopic`, `tendsto_downSteps_macroscopic` and the weak measure limits in N06(ii). | Discharged, including floor terms and the initial endpoint. |
| U12–U13 | `driver_reciprocal_pairing`, `tendsto_reciprocalErrorTotal`, exact profile integrals, and N06(iii). | The resulting estimates are proved. The manuscript uniform-integrability/probability route is bypassed by a scalar contraction and dominated convergence. |
| U14 | Correct endpoint identity, uniform full-horizon correction bound, and N06(iv). | Uniform asymptotic conclusion discharged. The false printed equality at line 808 is not validated. |
| U03 | `hasLocalSquareMomentProfile_iff_l1_squares` in [LocalSquareProfiles.lean](Freezing2/Analysis/LocalSquareProfiles.lean), and `tendsto_interiorMinimum_atTop` in [InteriorMinimumLimit.lean](Freezing2/Analysis/InteriorMinimumLimit.lean). | Local moment/squared-$L^1$ equivalence and interior-minimum divergence for $\alpha\geq1/2$ proved. Other explanatory portions retain their inventory status. |
| U15 | Exact coalescence balance; `tendsto_scaled_reciprocal_interiorMinimum` proves `eq:cvminSinfini` for the actual minimum; exact arbitrary mesh integration. | Denominator approximations and the uniform local coalescence maximum are discharged by N06(v). |
| U16 | Actual per-vertex independent Bernoulli increments, zero depth at birth, telescoping height law, exact means, zero-mean case, Bennett and uniform height concentration. | The safe union coefficient is $2(n+1)^2$, with birth endpoints retained; the printed finite coefficient $2n^2$ is not certified. No independence between different vertices is assumed. |
| U17 | Polynomial/stretched-exponential and geometric-floor decay; positive constants and compact-interior subcritical hazard lower bounds; actual maximum convergence N08. | Subcritical maximum argument discharged; endpoint repairs are recorded below. |
| U20 | GH part proved as N09 (`bounded_population_GH_limit`), including $h_n^+\ge n/(2M)$, height asymptotics in probability and in $L^p$ for every $p\ge1$ (`bounded_population_height_tendsto_Lp`, line 1046), the descendant-distance bound and exponentially small side branches. Nonuniversality (line 1034) in [BoundedPopulationMeasure.lean](Freezing2/MainResults/BoundedPopulationMeasure.lean): `bounded_population_GHP_limit`, `bounded_population_GHP_nonuniversal`, `bounded_population_no_universal_GHP_limit`. | **Proved, new formulation** (the source gives no precise statement or proof). (i) Supporting extension: under N09's hypotheses, if $h_k^+/h_n^+\to H(k/n)$ uniformly for a continuous $H$, the uniformly measured forward trees scaled by $1/h_n^+$ converge in probability in GHP to $[0,1]$ carrying $H_*\mathrm{Leb}$. (ii) Two explicit arrays with $S^n_k\le3$ (alternating, $H(t)=t$; a switch at $\approx n/2$ to population in $\{2,3\}$, $H(t)=(4t+2\min(t,1/2))/5$) have GHP limits at positive GHP distance, while both GH limits are $[0,1]$. (iii) No single measured space is the GHP limit in probability for every admissible array. The tree measure is the uniform vertex measure. Not exported: an admissible array with no GHP limit (interleaving the examples) and the exclusion of a random universal limit; both follow immediately from (ii). The upper bound $h_n^+\le n$ is not stated separately (not needed). Independent review: PASS with notes. |
| U18, U21; S07 sampling ingredients | [BirthTimeLimit.lean](Freezing2/Probability/BirthTimeLimit.lean) proves actual normalized birth measures converge weakly to uniform measure, retaining the frozen-label shift and active atom. [VertexSampling.lean](Freezing2/Probability/VertexSampling.lean) proves collision probability $1/|\mathcal V_n|\to0$. [BranchLengthLimit.lean](Freezing2/Probability/BranchLengthLimit.lean) proves the actual scalar and fixed-$k$ iid branch limits, including the exact $1/(2S_i)$ normalization and source $f$ notation. | Corrected root-inclusive forward matrix convergence is discharged by M06. [SupercriticalHazardRate.lean](Freezing2/Analysis/SupercriticalHazardRate.lean) proves the explicit uniform compact-interval $O(n^{1-2\alpha})$ bound with a constant independent of interval endpoints. [CommonBirthTail.lean](Freezing2/Probability/CommonBirthTail.lean) proves the exact closed common-birth tail limit $\delta^2$, retaining collisions and active atoms. |
| S01 | `zeroDiagonal_of_tendstoInDistribution`, `not_tendstoInDistribution_additive_of_dist`: zero diagonals persist in law; positive branch lengths rule out the printed additive matrix. Actual limiting profile branch lengths are now proved. | Corrected root-inclusive forward M06 convergence proved. The originally printed diagonal formula remains refuted. |
| S02–S03 | Concrete coalescence maximum and corrected distinct-vertex law; diagonal coalescence equals birth; `inclusive_reciprocal_self_pos` verifies the positive diagonal of the surrogate $D^n$. | The harmonic comparison function is not asserted to be a metric; its diagonal must remain part of the approximation argument. |
| U19 | Actual birth-coordinate density, uniform distortion, exact segment image, actual finite uniform-measure pushforward, and the completed M02 proof. | The scaling-limit argument is discharged by the direct common-metric GHP proof. The paper's GP-plus-GH route is bypassed; N15 and N16 are proved separately and are not used for M02. |
| U27–U28, survival factors only | [FiniteSurvivalProducts.lean](Freezing2/Analysis/FiniteSurvivalProducts.lean) and [CriticalSurvivalProduct.lean](Freezing2/Probability/CriticalSurvivalProduct.lean): exact binomial hazards converge to exponential integrated rates at $\alpha=1/2$, including moving inclusive endpoints and finite families of intervals. | These factors feed the proofs of N11, N12a and M03 (rows above), which supply the genealogy laws, the density and the conditioning corrections. The source's own U28 route (`eq:cv locale bis`, Fatou and Scheffé) is bypassed by the tracked-chain proof of N12b and is not separately certified. No independence or event-product premise is silently assumed. |
| U23 (finite-particle continuous coalescent) | `coalescentLawPM`, `isGenealogyLimit_coalescentLaw` in [CoalescentDensity.lean](Freezing2/Probability/CoalescentDensity.lean); `ae_mergeTimes_strictAnti`, `coalescentLaw_noMerger_pos`, `coalescentLaw_allMerge` in [CoalescentDecoding.lean](Freezing2/Probability/CoalescentDecoding.lean) | **Proved in law.** For every measurable, locally square-integrable $g$ the genealogy law exists without a discrete approximation (the source's extra $\int f^{-1}<\infty$ is not needed); almost surely merges are binary with distinct times in $(0,1)$; if $\int_0^{1/2}f^{-2}<\infty$ there is no merger at all with positive probability (stronger than the source); if it diverges, all particles are in one cluster at time $0$. Not formalized: an explicit partition-valued path process with a stated Markov property (the rates enter through the density and the semigroup characterization). Independent review: PASS with notes. |
| U24, deterministic time change | [ProfileTimeChange.lean](Freezing2/Analysis/ProfileTimeChange.lean): the integrated reciprocal profile is strictly increasing and continuous, its unit-interval restriction is a homeomorphism onto the exact segment, and its inverse extends continuously as one above the endpoint. | The continuous genealogy and its density are proved (U23 and N11). The genealogy-as-increasing-binary-plane-forest, admissibility and planar-factor clauses of U24 are covered by N11 in source form ([CoalescentForests.lean](Freezing2/Probability/CoalescentForests.lean)). **Open:** the stochastic time change to Aldous's inhomogeneous coalescent with $\ell(t)=2f(H^{-1}(t))$ (`rem:timechange`, E04), hence the identification of $g_{0,k}$ with the time change of Aldous's density (2). The remark that $g_{0,k}$ determines the law in the divergent case follows from N11 with $r=0$ and `coalescentLaw_allMerge`, but is not stated separately. |
| U25 (`eq:cvdn`, `eq:GP`) | `tendsto_sampledDistanceLaw_critical` in [CriticalDistanceLimit.lean](Freezing2/Probability/CriticalDistanceLimit.lean); forward version `tendsto_forward_annealedDistanceLaw_critical` in [CriticalScalingLimit.lean](Freezing2/Probability/CriticalScalingLimit.lean) | **Proved.** Scaled reverse distances are uniformly within $n^{-1/2}\max\text{err}+n^{-1/2}+4\varepsilon_n$ of $P(B_i)+P(B_j)-2P(C_{ij})$, $P$ half the primitive of $1/f$ (N07 plus uniform harmonic prefixes); with N12b and a weak-perturbation lemma the sampled matrices converge to `criticalDistanceLaw (1/f) k`, zero diagonal exact. The forward annealed blocks equal the reverse sampled laws (sample block of the rooted source/forward matrix identity). |
| U26 (real-tree closure) | `criticalTreeLaw_ae_isRealTree` in [CriticalRealTree.lean](Freezing2/Probability/CriticalRealTree.lean); metric theory in [RealTree.lean](Freezing2/Geometry/RealTree.lean), [GHRealTree.lean](Freezing2/Geometry/GHRealTree.lean) | **Proved by a different route.** A complete metric space with the four-point condition and midpoints is a real tree (segments by dyadic midpoints; uniqueness and the arc property from $0$-hyperbolicity via a Gromov-product separation argument). The limiting sampled distances $P(b_i)+P(b_j)-2P(c_{ij})$ inherit the ultrametric structure of coalescence times, so iid samples, hence (full support) the whole limit space, are $0$-hyperbolic; approximate midpoints of the finite graphs form a closed GH set and pass to the limit by the portmanteau theorem. The source's edge-realization argument is not used. |
| U38 (merger strictly below births) | `criticalGenealogyLimit_merge_ne_birth` in [CriticalMergeAtoms.lean](Freezing2/Probability/CriticalMergeAtoms.lean) | **Proved for the limit genealogy law.** A merger within $\delta n$ phases below an interior birth has probability at most the hazard sum over that window, uniformly within $\sup_a\int_a^{a+\delta}f^{-2}+o(1)$ (N06(v) interval errors plus absolute continuity); repeated samples cost $1/N$. The portmanteau theorem for open sets transfers the bound, and the scaled births of the limit lie in $(0,1)$ almost surely. |
| U39 (infinitely many root clusters when $\int_0 f^{-2}<\infty$) | `criticalGenealogyLimit_early_merge_le`, `criticalGenealogyLimit_births_ge_le` in [CriticalRootMerges.lean](Freezing2/Probability/CriticalRootMerges.lean); `criticalDistanceLaw_starAmong_compl_le` in [CriticalBranching.lean](Freezing2/Probability/CriticalBranching.lean) | **Proved by a different route.** The source picks a subsequence of births in dyadic-type windows. Here, among $mL$ samples split into $m$ groups, each group has a sample born before $\delta$ except with probability $m(1-\delta/2)^L$, and two samples born before $\delta$ merge at a positive time with probability at most $\delta^2\int_0^\delta f^{-2}$; a union bound with $L\approx M/\delta$ makes the failure probability small. |
| U40 (no coalescence at time zero when $\int_0 f^{-2}=\infty$) | `criticalGenealogyLimit_coalescence_nonpos_null` in [CriticalRootMerges.lean](Freezing2/Probability/CriticalRootMerges.lean) | **Proved for the limit genealogy law.** Discrete survival products $\prod(1-h)\le\exp(-\sum h)$ on interior windows, the hazard-integral approximation and the portmanteau theorem give $\mu\{c_{ij}<\varepsilon\}\le e^{-\int_\varepsilon^\beta f^{-2}}+2\beta$. The source's "root degree one" needs a pointed limit and is not claimed; the extension from samples to the whole tree is done through stars and full support (M04b). |
| U41 (coalescences at distinct times; other branch points binary) | `criticalGenealogyLimit_tripleMerger_null` in [CriticalTripleMerger.lean](Freezing2/Probability/CriticalTripleMerger.lean) | **Proved for the limit genealogy law.** Three distinct samples almost surely have no common positive pairwise coalescence time. Discrete bound: in the tracked chain, two mergers among three lineages over a window have probability at most a constant times the squared hazard sum; summing over a mesh of windows and the portmanteau theorem give zero. Arbitrary branch points are reduced to sampled stars by full support and the openness of complement components in real trees ([RealTreeStar.lean](Freezing2/Geometry/RealTreeStar.lean)); "binary" is metric degree three. |
| U27, sampling and one-step ingredients | [FiniteDistinctSampling.lean](Freezing2/Probability/FiniteDistinctSampling.lean), [FrozenDistinctSampling.lean](Freezing2/Probability/FrozenDistinctSampling.lean), and [AuxiliarySignSampling.lean](Freezing2/Probability/AuxiliarySignSampling.lean): exact iid/conditioned atom masses, collision and active-label errors, multiplicative frozen-distinct ratio tending to one, and finite iid auxiliary sign-time convergence. [ClusterTransition.lean](Freezing2/Probability/ClusterTransition.lean) gives actual tracked-pair merger and orientation probabilities. | The genealogy event laws needed are supplied by the exact tracked-chain law (N12b) and by N12a in corrected tracked-chain form; the source's finite decoding to $\mathcal F^n_r$ is not formalized (row N12a). The generic measurable-mark convergence, the mesh jitter route and the discrete attachment-rate samplers ([AuxiliaryAttachmentRate.lean](Freezing2/Probability/AuxiliaryAttachmentRate.lean), [AuxiliaryAttachmentSquare.lean](Freezing2/Probability/AuxiliaryAttachmentSquare.lean)) are proved and integrated. Additive sampling error alone does not justify rescaled local probabilities. |
| U32, metric-transfer route | [CoalescenceMetricApproximation.lean](Freezing2/Probability/CoalescenceMetricApproximation.lean): uniform control of the inclusive harmonic distance by the coalescence-time metric, then actual graph distance outside the proved N07 error event; finite sample-cover transfer. | This replaces the false endpoint-free printed comparison by a uniform primitive modulus. **Leaf-tightness `eq:GH` (line 1154, graph distance) is proved** as `critical_graphSampleNet_tightness` in [CriticalGraphNet.lean](Freezing2/Probability/CriticalGraphNet.lean): actual reverse-tree graph distance divided by $\sqrt n$, independent uniform $V_1,\ldots,V_k$, under survival, $\mathrm{Lim}^{1/2}_{1/f}$ with $f>0$ a.e., and $\max_{1\leq k\leq n} S^n_k=O(\sqrt n)$; $\mathrm{Lim}^{1/2}_{1/f^2}$ is not needed. It combines `eq:stepone`, N07 and the transfer above. The source's intermediate display `16/01/11h`, which concerns the harmonic surrogate $D^n$ (macro `\dc`), its truncation display `eq:delta` and the uniform-integrability argument are bypassed and not separately certified. |
| U50–U52, leaf-tightness criterion | Proof of N17 (see above). U50: diameters are controlled by a covering radius and the largest sampled distance on the same samples, covering numbers by the covering radius, both through Markov bounds on the annealed laws; GH covering sets are open and diameter sets closed, so the finitely many early laws are controlled individually; Mathlib's Gromov compactness criterion then gives tightness. U51–U52: subsequential limits have the prescribed annealed matrices by continuity of mixtures, and full support almost surely because a space without full support has covering-radius tail one at a fixed scale for every sample size. | The source's coupled-matrix and completion argument (U51) and its appeal to N16 (U52) are replaced by direct empirical reconstruction for compact spaces. The criterion is stated with block-wise matrix convergence and leaf-tightness for each $\delta>0$, which the independent review found equivalent to the source formulation. |
| U34–U35 | [TrackedRootCorrespondence.lean](Freezing2/Probability/TrackedRootCorrespondence.lean), [TrackedIsolation.lean](Freezing2/Probability/TrackedIsolation.lean), [OldestIsolation.lean](Freezing2/Probability/OldestIsolation.lean), [TrackedClusterBlock.lean](Freezing2/Probability/TrackedClusterBlock.lean), and the completed corrected N14 theorem: actual kernel coupling proves oldest-isolation dominance; singleton counting, actual expectation recursion, variance, absorbing-safe reciprocal telescoping, exact sign counts, and uniform numerical constants complete the block bound. | The invalid negative-phase case remains a source defect. The marked count in the estimate is tracked once all marked vertices have been born; isolation before birth is handled explicitly by the coupling argument. The separate global identity and recursion for the paper's count that includes unborn marked vertices remain open and are retained in U34. |
| E09, GHP metric, Polish topology and compactness | [GHPSeparation.lean](Freezing2/Geometry/GHPSeparation.lean), [GHPSeparability.lean](Freezing2/Geometry/GHPSeparability.lean), [GHPCompleteness.lean](Freezing2/Geometry/GHPCompleteness.lean), and [GHPCompactness.lean](Freezing2/Geometry/GHPCompactness.lean): the exact whole-space quotient is a complete separable metric space; inverse images of compact GH families under the natural projection are compact. Measurable finite approximations, countable distance/weight codes, exact coupling gluing, compact carrier hulls, and weak-limit measure restriction are proved dependencies. | The noncompact GP space is now proved Polish (next row) and N15–N17 are proved (rows above). The ADH13 tightness criterion is proved in the sufficient direction that `C.1` uses: tight diameters and covering numbers give GH tightness (`isTightMeasureSet_range_of_coverable` in [GHTightCriterion.lean](Freezing2/Probability/GHTightCriterion.lean)), equivalent to GHP tightness ([GHPTightness.lean](Freezing2/Probability/GHPTightness.lean)). Zero-mass carrier points are retained. |
| U49/E09, GP part (`GPdef`), and S18 | [GromovProkhorov.lean](Freezing2/Geometry/GromovProkhorov.lean): `PolishMeasuredSpace`, `GPIsometric`, `gpIsometric_iff_exists_isometry`, `GPSpace`, `gpDistance`, `PolishMeasuredSpace.distance_eq_zero_iff`, `GPSpace.polishSpace`, `MeasuredGHSpace.gpProjection`, `lipschitzWith_gpProjection`, `not_injective_gpProjection` | **Proved.** `GPSpace` is the quotient of complete separable metric spaces with Borel probability laws by a measure-preserving isometry between the closed supports (Mathlib `Measure.support`); the source's form with an isometry not assumed onto is equivalent. $d_{GP}$ is the source's exact infimum, over common ambient metric spaces (in the carriers' universe) and isometric embeddings, of the Lévy–Prokhorov distance (same convention as the source); it is well defined, satisfies the triangle inequality, and vanishes exactly on GP-isometric pairs for arbitrary Polish spaces (no compactness or full-support hypothesis). $(\mathbb K_{GP},d_{GP})$ is separable and complete for $d_{GP}$ itself, hence Polish, proving the cited ADH13 claim. S18 is resolved by reformulation: the printed inclusion $\mathbb K_{GHP}\subset\mathbb K_{GP}$ is the 1-Lipschitz (continuous, measurable) projection `gpProjection`, and `not_injective_gpProjection` proves it is not an inclusion (a one-point space and $[0,1]$ with a Dirac mass at an endpoint). "Polish" is read as a complete separable metric (ADH13/GPW convention). N15 (including descent of sampled-matrix laws to GP classes) and N16 are now proved (rows above). Independent review: PASS with notes. |
| U31, deterministic chaining | [FiniteChaining.lean](Freezing2/Geometry/FiniteChaining.lean), [CoalescenceChaining.lean](Freezing2/Probability/CoalescenceChaining.lean), and [ChainingSeries.lean](Freezing2/Analysis/ChainingSeries.lean): actual coalescence-metric dyadic chaining with final-net error, repeated samples allowed, and one constant in the exact geometric tail bound. | **`eq:stepone` proved** as `critical_sampleNet_tightness` in [CriticalSampleNet.lean](Freezing2/Probability/CriticalSampleNet.lean), for the actual reverse tree with independent uniform $V_1,\ldots,V_k$, under survival and $\max_{1\leq k\leq n}S^n_k=O(\sqrt n)$. Blocks use N13 with a fresh coordinate of an iid sequence ([IidSequence.lean](Freezing2/Probability/IidSequence.lean)); the last net, of size $2^{N_n}$ with $8^{N_n}\leq n$, uses N13 for each fixed vertex ([CriticalChaining.lean](Freezing2/Probability/CriticalChaining.lean)) and a union bound over at most $n+1$ vertices; chaining uses the almost-sure triangle inequality. The printed probability $1-\sum_{i\geq k}2^{-3i}+o(1)$ is realized with an explicit $(8/7)8^{-J}$ block error and last-net error at most $8\cdot2^{-N_n}$. |
| U29, analytic implications | [FiniteFamilyScheffe.lean](Freezing2/Analysis/FiniteFamilyScheffe.lean) and [VariableDominatedConvergence.lean](Freezing2/Analysis/VariableDominatedConvergence.lean): a.e. convergence of finite nonnegative families plus total mass convergence gives component L1 and expectation convergence; a varying L1-convergent dominating sequence gives integrability of the limit and convergence of integrals. | The source's use of these implications (density normalization and recovery of pairwise merger times from the forest and births) is bypassed: N12b works directly with pairwise coalescence times, and N11 gives the genealogy law. The limit-side normalization $\sum_{r<k}\sum_{F_0}\int 1_{[0,1]^k}g_{r,k}=1$ (line 1419, the premise of the finite-family lemma at line 1430) is proved as `sum_lintegral_indicator_sourceDensity_eq_one` in [ModelFacts.lean](Freezing2/MainResults/ModelFacts.lean); the discrete-side normalization belongs to the bypassed route. The finite-family proof uses minimum functions and dominated convergence rather than separate Fatou inequalities. |
| U27, measurable profile sampling | [DominatedWeakConvergence.lean](Freezing2/Probability/DominatedWeakConvergence.lean), [MeshJitter.lean](Freezing2/Probability/MeshJitter.lean), [AuxiliarySignJitter.lean](Freezing2/Probability/AuxiliarySignJitter.lean), and [MarkedProfileSampling.lean](Freezing2/Probability/MarkedProfileSampling.lean): weak convergence under common finite-measure domination extends to integrable tests; exact jitter/floor identities and local L1 convergence give joint time-and-mark weak convergence with merely a.e. measurable profiles. | The actual discrete ordered/squared attachment-rate exports and the full local genealogy density remain separate. No continuity of the source profile is added. |
| U36, block occupancy | [FiniteOccupancy.lean](Freezing2/Probability/FiniteOccupancy.lean), [FrozenBlockOccupancy.lean](Freezing2/Probability/FrozenBlockOccupancy.lean), [CriticalOccupancyRate.lean](Freezing2/Analysis/CriticalOccupancyRate.lean), and [CriticalBlockOccupancy.lean](Freezing2/Probability/CriticalBlockOccupancy.lean): actual iid uniform samples, Bennett lower tails, frozen-only fourfold collisions, and the exact source event $E$ of distinct sampled birth times; $k^4P(E^c)\to0$ uniformly in $k^3\leq n$, all rows and the fixed bound $M$. | **Discharged with repaired constants (S12):** block length $16\lceil Mn/\sqrt k\rceil$ and Bennett $g(1/4)$ replace the printed $4\lceil Mn/\sqrt k\rceil$, mean $6M\sqrt k$ and $g(1/3)$; collisions are counted only among frozen births, since all active vertices share birth time $n$. |
| U37, alternating blocks | [ReverseContinuation.lean](Freezing2/Probability/ReverseContinuation.lean), [ContinuationCount.lean](Freezing2/Probability/ContinuationCount.lean), [ContinuationIsolation.lean](Freezing2/Probability/ContinuationIsolation.lean), [ContinuationConditional.lean](Freezing2/Probability/ContinuationConditional.lean), [ContinuationBlockIsolation.lean](Freezing2/Probability/ContinuationBlockIsolation.lean), [ConditionalBlockIsolation.lean](Freezing2/Probability/ConditionalBlockIsolation.lean), [ConditionalIsolationChain.lean](Freezing2/Probability/ConditionalIsolationChain.lean), [CriticalBlockGeometry.lean](Freezing2/Probability/CriticalBlockGeometry.lean), [CriticalBlockCover.lean](Freezing2/Probability/CriticalBlockCover.lean), [CriticalIsolationRate.lean](Freezing2/Analysis/CriticalIsolationRate.lean), [CriticalBlockRadius.lean](Freezing2/Analysis/CriticalBlockRadius.lean): actual reverse continuation from an arbitrary valid forest, the true conditional endpoint law given the whole past, conditional isolation probability at most $3/4$ per block, iterated by the tower property; small-birth case; deterministic block geometry; $p_k=\lfloor100\ln k\rfloor$ decay and the radius comparison $2p_k\delta\leq n\ln(k)^2/\sqrt k$. | **Discharged by a different route.** The printed conditional independence of the events $A_i$ (S12) is not proved; a conditional upper bound at each block suffices. The rounding loss in $(p_k-1)/2$ is retained, and the conclusion is $O((3/4)^{(p_k-1)/2})$, which is $o(k^{-4})$ by the choice of $p_k$. |
| U30, finite metric ingredients | [CoalescenceMetric.lean](Freezing2/Probability/CoalescenceMetric.lean): nested components give the coalescence inequality; the exact $\Delta=(b(u)+b(v)-2c(u,v))/2$ is a genuine metric on the actual finite labels; nonempty finite-set distances are attained and measurable. | The chaining and quantitative tightness arguments that use this metric are proved (U31, U32 and N13). This is distinct from the inclusive harmonic surrogate with positive diagonal. |
| U01 (recursive-tree specialization; conditioned uniform plane tree) | `treeLaw_allPlus_eq_urtLaw`, `urtLaw` in [RecursiveTrees.lean](Freezing2/MainResults/RecursiveTrees.lean); `map_planeTreeOf_excursionTreeLaw`, `excursionTreeLaw_planeTreeOf_eq`, `card_planeTrees`, `excursionTreeLaw_ae_iso`, `excursionTreeLaw_ae_isometry`, `excursionTreeLaw_eq_cond_bind`, `iidTreeLaw_planeTreeOf_eq` in [UniformPlaneTree.lean](Freezing2/MainResults/UniformPlaneTree.lean) | **Proved (both clauses; second clause in plane-tree and rooted-isometry form).** With all signs $+1$ the forward tree law equals `urtLaw` (each new vertex attaches to a uniform vertex among all existing ones), at every time. If the signs are the increments of a simple random walk from 1 conditioned to first hit $0$ at time $2n+1$, the Neveu plane tree of $\mathcal T_{2n+1}$ (children ordered by birth time) is uniform on the $C_n$ plane trees with $n+1$ vertices; almost surely $\mathcal T_{2n+1}$ is rooted-graph-isomorphic, hence isometric, to that plane tree; with unconditioned iid signs each such tree arises at time $2n+1$ with probability $2^{-(2n+1)}$. Proved by direct counting, not via companion Theorem 2 (S20). The birth-time order is a stronger choice than the companion's uniformly random order. Not formalized: the equality of laws "as a random compact metric space" as an identity in `MeasuredGHSpace` (with or without the uniform vertex measure), which follows by an unstated pushforward and which M05 would need; the $\alpha=1$ companion descriptions are background. Independent reviews: PASS. |
| U04b (recursive trees without freezing, S19-qualified) | `urt_weak_limit_eq_onePoint`, `urt_tendsto_iff`, `tendsto_urtMeasuredLaw_onePoint`, `urt_log_not_tight`, `urt_log_no_weak_limit` (with `urt_not_tight_of_le_log`, `urt_no_weak_limit_of_le_log`) in [RecursiveNoLimit.lean](Freezing2/MainResults/RecursiveNoLimit.lean) | **Proved (qualified form, S19).** For the uniform recursive tree $T_n$ ($n$ attachment steps, the source's case $X_i\equiv+1$, `treeLaw_allPlus_eq_urtLaw`) with graph distance divided by deterministic scales $a_n>0$ eventually and the uniform vertex probability: any weak GHP limit of the laws of $T_n/a_n$ is the Dirac mass at the one-point space; a limit exists if and only if $a_n/\log n\to\infty$; if $a_n\le C\log n$ eventually (in particular $a_n=\log n$), the laws are not tight and no subsequence converges. The source's unqualified sentence is false as stated (strong shrinking collapses the tree to a point, `tendsto_urtMeasuredLaw_onePoint`, with the sharp threshold $\log n$), so it is formalized as the absence of nondegenerate GHP scaling limits. Scope: uniform recursive trees, deterministic normalizations, uniform vertex measure. Route (the source gives none): companion height bound for the collapse; two-point separation by $\log n/4$ (merger hazard $\le 2/(i+1)$, Bennett lower tail) and the M06 covering-number argument at radius $1/(8C)$. Independent review: PASS with notes. |
| U04b (supercritical non-tightness, S08 corrected) | `supercritical_not_coverable`, `supercritical_not_tight` in [SupercriticalNonTight.lean](Freezing2/MainResults/SupercriticalNonTight.lean) | **Proved (corrected form).** Under the hypotheses of M06, for one small fixed radius $r=\tfrac12\int_0^{1/2}(2f)^{-1}$ (hence for every smaller radius) the number of $r$-balls needed to cover $\mathcal T_n/n^{1-\alpha}$ tends to infinity in probability, and the laws are not tight in the GHP space (`¬ IsTightMeasureSet`). The source's "every $\varepsilon$" fails for large radii (S08). Route: M06's star limit gives many samples pairwise farther than $2r$; compact sets of GH classes have uniformly bounded covering numbers. The source's remark that supercritical trees have no scaling limit is proved at its normalization $n^{1-\alpha}$: no subsequence of the GHP laws converges weakly (`supercritical_no_weak_limit` in [RecursiveTrees.lean](Freezing2/MainResults/RecursiveTrees.lean); review PASS); degenerate limits under faster normalizations (S19) are neither excluded nor claimed. Independent review: PASS with notes. The recursive-tree clause is proved separately (row above). Open: convergence to the long dendron in the ET21/Jan21 topology (absent from Mathlib); the comparisons with other random trees are external (E11). |
| U05, U07, U09, U10, U22, U33; E01, E03, E06 | Item-by-item evidence in [docs/coverage-gaps.md](docs/coverage-gaps.md) (read-only agent mapping, names spot-checked) | **Covered by existing declarations.** U09 is proved in the form that avoids S04; U10 is transferred observable by observable (no single law-equality theorem for all structures); U33 follows from `tightnessBlockLength_gap`; E03 is proved directly as N01–N04; E06 is Mathlib's `ghDist_le_of_approx_subsets`. |

All other portions of U01–U58 and E01–E11 remain unresolved unless identified
in a row above, in the classification of U53–U58 in the inventory, or in
[docs/coverage-gaps.md](docs/coverage-gaps.md), which
classifies the inventory items without a dedicated row and lists the external
mathematics missing for M05 (Brownian excursion, CRT, invariance principles,
Skorokhod representation, local limit theorems, the companion's plane-tree
example A03). After its 30 October 2026 revision, the items still open in whole
or in part there are U04a (dimensions), U04b (long dendron), U42–U48, E02
(only its measured-space pushforward; the plane-tree law is proved), E04 (Aldous time change and Theorem 2), E05 (Skorokhod
representation, needed only in the CRT section), E07 and E08; U01's first
clause, U04b's non-tightness and recursive-tree clauses, U23, U49, E09 and E10
are now covered. E11 is classified (d) there: the comparisons with other random
trees are external background and need no proof here. Lower dimension bounds,
long dendron convergence and the annealed measurability needed for M05 have not
disappeared from scope. Both appendices are covered: the GP, GH and GHP
background (U49, E09, N15, N16) and the leaf-tightness criterion `C.1` (N17,
U50–U52), the latter by a different identification step. O01–O02 are the
paper's open questions, not advertised theorems to prove.

The finite counting proofs verify the arithmetic argument in the paper. The
birth-law proof is a direct counting proof of the explicit label formulation;
it does **not** audit the companion paper's cited proof. The weighted proofs use
telescoping potentials instead of constructing the minimum-height pairing.
This preserves the crossing-balance idea and supplies correct endpoint terms.
The analytic Bennett proof follows the paper's calculus claim. The probability
proposition itself is proved by a standard moment-generating-function/Chernoff
argument; the source cites it without giving a proof. Numerical decay estimates
reuse Mathlib exponential domination. Other paper arguments remain unchecked except where explicitly recorded below.

## Source defects and proof departures

The [inventory's S01–S23](docs/source-inventory.md#source-issues-requiring-explicit-treatment)
give exact source locations and distinguish false formulas, ambiguous definitions,
and proof gaps. The major findings are also explained in
[MANUSCRIPT_RECOMMENDATIONS.md](MANUSCRIPT_RECOMMENDATIONS.md).

The population-profile development makes the zero-row convention explicit:
`initialRowExtension` supplies a canonical all-up row at index zero, proves
admissibility, and preserves the original array eventually and its $L^1$
hypothesis. The source-facing population theorem therefore requires survival
only at positive horizons, exactly as in the manuscript.

For the interior minimum, the formal proof retains the skip-free argument but
uses an interval of exactly $M=S_k$ cells. Its integral is at least
$n^{2\alpha}/(4nM)$; local squared-$L^1$ convergence on shrinking sets makes
this vanish. The actual minimizing index is constructed, and its sublinearity
is proved by comparison with a fixed midpoint. This replaces the paper's
auxiliary $\eta_n$ choice and reciprocal-square asymptotic summation; those
literal steps are not separately certified. The local moment/squared-$L^1$
equivalence is proved by a Scheffé argument using almost-everywhere subsequences
and dominated convergence, supplying the source's stated but unproved equivalence.

The height theorem follows the paper’s invocation of companion Theorem 3(3),
with all its hypotheses discharged. Its dependency proof uses direct forward
moment-generating functions and higher-moment bounds instead of the companion
paper’s reverse Bernoulli representation. This proves M01 without validating
N01 or N02. The exact 16-module dependency closure was copied from a stable
sibling-project snapshot, with only imports relocated; it compiled locally
without warnings. [Companion provenance](docs/companion-provenance.md) records
original and destination hashes, proof content, and the retained Apache license
and notice. The canonical zero-row extension is transported back to the original
array’s tree laws, so the source theorem has no extra horizon-zero premise.

For N06(v), the proof keeps the paper’s crossing-balance and local-square
strategy, supplying the finite endpoint terms, shifted denominator estimates,
and uniform final-cell error explicitly. The statement includes every positive
$\varepsilon$, with singleton intervals retained and empty maxima set to zero.
The assembled [PopulationLemma](Freezing2/Analysis/PopulationLemma.lean) exports
all five conclusions in the source’s $f$ notation.

The new reverse development follows Algorithm 2's actual transition kernels.
Its joint law supplies the conditional history, graph-step support, phase
membership, coarsening components, and terminal connectivity. Constant
conditional Bernoulli probabilities imply independence for each vertex's
successive increments; no independence between different vertices is used.
Frozen phases have zero increment, including the extinction endpoint where
the paper's unmasked Bernoulli parameter $1/S_n$ would be undefined (S04).
For N04 the exact survival recursion gives the printed product over
$c+2,\ldots,\min(b_u,b_v)$ after the missing distinctness premise is supplied.

The N07 proof retains the source's height-at-first-merger strategy. Acyclic
graph growth preserves existing distances; disjoint old root paths and the
new joining edge give the exact distance at coalescence. Birth endpoints are
included in the height maximum, which repairs the diagonal omission in the
printed finite maximum. The conservative family bound is $2(n+1)^2$, rather
than a certification of the printed $2n^2$. Only the global reciprocal $L^1$
profile is needed for this approximation.

The subcritical analytic estimate clips boundary-reaching intervals to a
fixed compact interior region before applying N06(v); local square-profile
convergence does not justify applying it directly at endpoint one. The
stochastic assembly also uses a shorter window to avoid a one-step discrepancy
between a weak gap inequality and an integer survival product. These are
repairs of the source proof, not checks of its literal endpoint inequalities.

For N10 the actual product sample law retains collisions with their exact
probability $1/|\mathcal V_n|$. The late common-birth event is bounded by the
first vertex's late-birth event, whose probability tends to $\delta$, instead
of using the paper's sharper $\delta^2$. Sending $\delta$ to zero proves the
same conclusion and repairs the omitted repeated-sample case. The separately stated uniform compact-hazard big-O rate and exact closed
common-birth $\delta^2$ limit are now explicit checked exports. The latter follows
from the actual iid product law and the null boundary of the uniform limit;
the earlier sufficient $\delta$-bound proof of N10 remains unchanged.

The subcritical distortion argument checks the exact inclusive harmonic
decomposition. Its common interval is controlled by N08 and uniform continuity
of the limiting primitive; the reciprocal endpoint is separately bounded by
$n^{\alpha-1}$. This also handles coincident labels without falsely treating
the harmonic surrogate as a metric. The subsequent GH proof uses the actual
finite graph metric and Mathlib's approximate-map bound. Macroscopic freezing
counts and a finite compact cover establish uniform density, retaining the
one-step shift and both endpoints; continuity and monotonicity identify the
primitive image with the exact source segment. This replaces the paper's
explicit nearest-birth correspondence by an equivalent dense-map argument.
The measured GHP conclusion is proved directly in one common ambient space. The canonical measure-preserving scaled isometry and N01 transport it to the actual forward tree. The exact ambient infimum descends to whole-space measured-isometry classes and has a proved triangle inequality, giving its topology and Borel structure. Bounded continuous test functions turn the vanishing distance tails into the original weak-limit statement without a global separability premise. This bypasses the paper's separate GP-plus-GH implication; N15 and N16 are proved separately and are not used here. Separate arguments now prove GHP completeness and separability, rather than using the paper’s cited background as assumptions. A separate compactness argument now proves zero-distance separation: near-optimal ambient embeddings give approximate carrier isometries, a compactness limit is a genuine surjective isometry, and Prokhorov bounds identify its pushed measure. The construction needs no measurable selection or full-support assumption.

The N01 counting proof is carried out on the actual support of each
fixed schedule. An aggregate terminal-tree class from the companion paper's
counting argument does not by itself enforce that schedule's attachment and
freezing times. The new forward terminal-mass theorem therefore proves the
formula precisely for reachable legal histories and zero mass elsewhere.
This support correction is essential to the proved law comparison; no
overbroad uniformity claim is assumed.

For example, at schedule $(+1,-1,+1)$ the final counts are three vertices and
two active vertices. The companion paper's aggregate class also contains a
two-leaf star with attachment labels $1,2$ and root frozen at time $3$, which
instead requires schedule $(+1,+1,-1)$. Its mass under the first schedule is
zero, rather than that schedule's positive history product $1/2$. This
counterexample has been checked informally; the complete counterexample object
has not separately been encoded in Lean. The formal support-corrected mass
theorems do not depend on it.

The supercritical proof display `eq2 thm sur-critique` shares the Introduction's
diagonal defect: coalescence of a sample with itself equals its birth time,
so its normalized coalescence need not vanish. The authorized zero-diagonal
correction is also applied to this affected proof display. Pair-marginal
arguments use distinct coordinate indices and retain repeated vertex labels
as collision events.

The N14 proof now checks the substantive oldest-vertex comparison through a
coupling of actual transition kernels: current singleton components can be
swapped by a root correspondence despite different untracked tree shapes.
At the younger marked birth both surviving singleton components are comparable;
a previously lost singleton cannot reappear. Integrating this comparison and
counting singleton roots yields the source expectation bound. Exact signed-step
counting gives the stronger denominator $\delta-M_n$, and the numerical
coefficient follows uniformly once $M\sqrt{k}\geq12$. The exported source
statement uses $i\geq1$, so every forest phase is defined. It does not certify
the printed $i=0$ case.

The N13 proof repairs S12 as follows. Occupancy blocks have length
$16\lceil Mn/\sqrt k\rceil$; the named N14 keeps its factor four, and the
conditional block bound accepts any all-born interval at least that long.
Bennett's inequality is applied with $g(1/4)$ to the actually available mean,
and the one-vertex birth-index endpoint loss is retained. Fourfold collisions
are bounded only among frozen births: every active vertex has birth time $n$,
so the printed uniform-vertex collision bound cannot hold as stated. For the
alternating blocks, the formal proof does not assert conditional independence.
It derives the true conditional endpoint law given the complete reverse history
from the actual kernel trajectory, bounds each block's isolation probability by
$3/4$ conditionally on the past, and iterates by the tower property. The query
vertex's block is chosen deterministically from its birth time, so the estimate
is uniform over fixed query vertices and fixed sample sets satisfying the
occupancy event, before integrating over the actual iid sample law. The source
hypothesis $\max_{1\leq k\leq n}S^n_k=O(\sqrt n)$ is converted to one bound $M$
for all positive rows in
[CriticalPopulationBound.lean](Freezing2/Analysis/CriticalPopulationBound.lean).

The GHP background proof keeps the literal summed ambient-isometry infimum.
Countable codes record both finite-net distances and exact pushed atomic masses.
Successive near-optimal measured couplings glue into one complete ambient
space; their carrier images lie in a compact hull. Probability compactness on
that hull and the proved Hausdorff/weak support lemma supply a measured limit.
This proves a Polish topology without identifying zero-mass points. The same
compact-hull method shows that compact GH carrier families have compact GHP
preimages, even for arbitrary probabilities on those carriers.

The fresh source reconciliation also retains the unqualified recursive-tree no-GHP-limit sentence (S19) and the bounded-population nonuniversality assertion in U20. The former needs a nontrivial-limit qualification, since sufficiently strong shrinking permits a one-point limit; both negative claims are now proved in qualified forms: the recursive-tree clause (U04b, `urt_weak_limit_eq_onePoint`, `urt_tendsto_iff`) and the nonuniversality assertion (U20).

The zero-diagonal correction is explicitly authorized. The false interval
pairing is replaced in the finite development by a correct endpoint-potential
identity, recorded as a substantive proof departure. The main theorem statements
have otherwise not been silently changed. The false original coalescence law,
negative-time block case, and CRT auxiliary claims remain visible obligations;
they cannot be certified literally. The valid positive-index block correction
is now proved explicitly.

In particular, the uniform CRT bound `eq:borne`,
$P(X_n(\delta)\geq\varepsilon)\leq C\delta^2/\varepsilon$, is false as printed.
For $n\geq2$, take $\delta=1/\sqrt n$ and $\varepsilon=1/(2\sqrt n)$.
The positive excursion returns to 1 at time 2 with probability
$C_{n-1}/C_n=(n+1)/(4n-2)>1/4$, where $C_n$ is Catalan. On that event
$X_n(\delta)\geq1/\sqrt n$, but the asserted upper bound is $2C/\sqrt n\to0$.
This argument is now machine-checked
([ExcursionCounterexamples.lean](Freezing2/Audit/ExcursionCounterexamples.lean):
`not_uniform_smallValue_bound`, with the conditioned walk identified with the
conditioned simple random walk by `excursionLaw_eq_cond` and the Catalan counting
by `excursionEquivDyckWord`), as is the refutation of the local formula
`eq:probalocale` (S15, `not_kempermanDisplay`) and of the summation step
(`not_bounded_sqrt_mul_sum_inv_rpow`). The counterexample lets $\varepsilon\to0$ with
$n$, so it does not refute a version with $C=C(\varepsilon)$, which is all the next
step uses. It refutes this auxiliary bound, not the CRT corollary. A valid
replacement estimate is needed; independent review: PASS with notes.

## Verification and review

Work resumed on 29 October 2026 from [HANDOFF_CLAUDE.md](HANDOFF_CLAUDE.md).
The two remaining N13 elaboration errors were repaired, the literal $O(\sqrt n)$
population bridge was added, and the failing continuous-kernel draft and its
survival consumer were repaired. All 232 maintained modules were then imported by
`Freezing2.lean`, with no draft module outside the integrated closure; every
later checkpoint, including the latest (283 modules), again covers every
maintained module.

The N13 statement (`critical_sampled_cover_probability_of_isBigO`) was compared
with the source lines 1506–1510, the standing survival convention at line 695 and
the hypothesis of `thm:critique` by Claude, who did not author the declaration
(it was written by the previous Codex agent); its semantic dependencies
(`sampledCriticalCoverLaw`, `sampledCriticalCoverEvent`,
`sourceCoalescenceDistance`, `uniformVertex`, `uniformVertexVectorLaw`) were
inspected. Verdict: faithful, with the uniform threshold depending only on the
population bound. This is an agent review, not human peer review.

An independent agent reviewed both implementation milestones and their source-facing definitions and results in
[docs/milestone-audit.md](docs/milestone-audit.md), including extinction,
quantifier scope, correction terms, and the finite/asymptotic distinction.
This is an independent source review, not human peer review or independent
kernel replay. The report identifies the exact reviewed source hashes.

The M04b–c statements (`IsBinaryTree`, `criticalTreeLaw_ae_binary_iff`,
`criticalTreeLaw_ae_rootDegree`, `critical_tree_properties`) were compared with
`thm:properties` (2) and its proof by an independent Claude agent: **PASS with
notes** (metric degree three for binary branch points; the infinite-degree point
represents the root only up to the unpointed encoding; the source's "root of degree
1" remark needs a pointed limit and is not claimed); see
[docs/milestone-audit.md](docs/milestone-audit.md).

The M03 statement `critical_scaling_limit` and its dependencies
(`criticalTreeLaw`, `criticalDistanceLaw`, `IsGenealogyLimit`, `upperLimit`,
`coalescenceLimit`, `propagator`, `kingGen`) were compared with `thm:critique`,
`sec:deflim`, the continuous coalescent and `eq:GP` by an independent Claude agent
that did not author them: **PASS with notes**, the only missing source clause being
the real-tree property U26; see [docs/milestone-audit.md](docs/milestone-audit.md).

The publication candidate (30 October 2026) adds the Mathlib-only statement
interface ([Challenge.lean](Challenge.lean), [Solution.lean](Solution.lean),
[comparator.json](comparator.json), `Freezing2/Interface`) for M01, M02, M03 with
M04, corrected M06 and N09. Its check: `lake build` (4,177 jobs; the only warnings
are the five deliberate `sorry` holes of `Challenge.lean`), the default
all-source axiom check for **3,724 explicit definitions and theorems in all 289
maintained modules** (only `propext`, `Classical.choice`, `Quot.sound`), the
Challenge copy check, and a preliminary **unsandboxed** local Comparator run that
accepted the solution. See [publication-candidate-axioms.log](evidence/publication-candidate-axioms.log),
[context and hashes](evidence/publication-candidate-context.txt) and
[comparator output](evidence/comparator-local-unsandboxed.txt). No sandboxed
Comparator run, Palomar preflight, submission or registration has taken place.

The previous checkpoint, after U01's second clause (uniform plane tree) and the
model facts U06, U29 (normalization) and U20 ($L^p$ height), ran the default
all-source checker: `lake build` (4,168 jobs, no warnings) and the transitive-axiom
check for **3,645 explicit definitions and theorems in all 285 maintained
modules**; only `propext`, `Classical.choice`, and `Quot.sound` occur. See
[plane-tree-axioms.log](evidence/plane-tree-axioms.log) and
[exact scope and hashes](evidence/plane-tree-context.txt) (a later docstring-only
edit is recorded there).

The previous checkpoint, after N15 (`GPSpace.equivGP`, with Gromov's reconstruction
theorem for Polish spaces) and N16 (`tendsto_ghp_of_gp_of_gh`), checked 3,524
explicit definitions and theorems in all 283 maintained modules (4,166 build jobs,
no warnings). See
[gp-lemmas-axioms.log](evidence/gp-lemmas-axioms.log) and
[exact scope and hashes](evidence/gp-lemmas-context.txt).

The previous checkpoint, after the GP space (U49/E09 GP part, S18) and the
restriction of the S15 refutation to the source domain, checked 3,416 explicit
definitions and theorems in all 281 maintained modules (4,164 build jobs, no
warnings). See
[gromov-prokhorov-axioms.log](evidence/gromov-prokhorov-axioms.log) and
[exact scope and hashes](evidence/gromov-prokhorov-context.txt).

The previous checkpoint, after the recursive-tree clause of U04b and the Lean
refutations of S15/S16, checked 3,354 explicit definitions and theorems in all 280
maintained modules (4,162 build jobs, no warnings). See
[excursion-counterexamples-axioms.log](evidence/excursion-counterexamples-axioms.log)
and [exact scope and hashes](evidence/excursion-counterexamples-context.txt) (the
S15 refutation's domain was afterwards restricted to $n\ge1$, $k\ge1$, recorded
there; recheck at the next checkpoint). The recursive-tree clause alone was checked
at 3,290 declarations in 279 modules
([recursive-no-limit-axioms.log](evidence/recursive-no-limit-axioms.log)).

An earlier checkpoint, after proving N12a (corrected local limit, plane form) and
U20 (bounded-population GHP nonuniversality with a general GHP limit theorem),
checked 3,243 explicit definitions and theorems in all 278 maintained modules (4,156
build jobs, no warnings); see [local-limit-axioms.log](evidence/local-limit-axioms.log)
and [exact scope and hashes](evidence/local-limit-context.txt).

The previous checkpoint, after proving N11 in source form (labelled plane forests),
U01's first clause and the supercritical no-weak-limit corollary, checked 2,984
explicit definitions and theorems in all 275 maintained modules (4,153 build jobs,
no warnings). See
[coalescent-forests-axioms.log](evidence/coalescent-forests-axioms.log) and
[exact scope and hashes](evidence/coalescent-forests-context.txt) (later
docstring-only edits recorded there). Independent statement review: N11 source
form PASS with notes; U01 and `supercritical_no_weak_limit` PASS.

The previous checkpoint, after proving N11 (history form), the U23 claims and the
supercritical non-tightness U04b, checked 2,795 explicit definitions and theorems
in all 273 maintained modules (4,151 build jobs, no warnings). See
[coalescent-density-axioms.log](evidence/coalescent-density-axioms.log) and
[exact scope and hashes](evidence/coalescent-density-context.txt) (one later
docstring-only edit is recorded there). The N11, U23 and U04b statements were
reviewed by an independent Claude agent: **PASS with notes** each (N11 proved in
history form; labelled-forest encoding in prose only; U04b with the S08 radius
correction).

The previous checkpoint, after proving N09 (`bounded_population_GH_limit`), checked
2,574 explicit definitions and theorems in all 270 maintained modules (4,148 build
jobs, no warnings); see [bounded-population-axioms.log](evidence/bounded-population-axioms.log)
and [exact scope and hashes](evidence/bounded-population-context.txt). The N09
statement was compared with `thm:alpha0` by an independent Claude agent: **PASS
with notes** (n = 0 falls back to a one-point space, irrelevant asymptotically;
the GHP nonuniversality remark is separate, U20).

The previous checkpoint, after proving M04b–c and hence all of `thm:properties`
(`critical_tree_properties`, with U39–U41), checked 2,549 explicit definitions and
theorems in all 269 maintained modules (4,147 build jobs, no warnings); see
[critical-branching-axioms.log](evidence/critical-branching-axioms.log) and
[exact scope and hashes](evidence/critical-branching-context.txt).

An earlier checkpoint, after proving M04a (`criticalTreeLaw_ae_leaves`) with
the merge-atom lemma U38, checked 2,459 explicit definitions and theorems in all
265 maintained modules (4,143 build jobs, no warnings); see
[critical-leaves-axioms.log](evidence/critical-leaves-axioms.log) and
[exact scope and hashes](evidence/critical-leaves-context.txt).

An earlier checkpoint, after proving the real-tree clause U26 and hence M03 in
full (`critical_scaling_limit_realTree`), ran the default all-source checker:
`lake build` (4,140 jobs, no warnings) and the transitive-axiom check for
2,430 explicit definitions and theorems in all 262 maintained modules; see
[critical-real-tree-axioms.log](evidence/critical-real-tree-axioms.log) and
[exact scope and hashes](evidence/critical-real-tree-context.txt).

An earlier checkpoint, after proving the critical `eq:GP` and M03 up to its
real-tree clause, ran the default all-source checker: `lake build` (4,137 jobs,
no warnings) and the transitive-axiom check for **2,376 explicit definitions and
theorems in all 259 maintained modules**. Only `propext`, `Classical.choice`, and
`Quot.sound` occur, or no axioms. See
[critical-scaling-limit-axioms.log](evidence/critical-scaling-limit-axioms.log)
and [exact scope and hashes](evidence/critical-scaling-limit-context.txt).
Intermediate all-source runs after the tracked-chain limit (2,258 declarations,
252 modules) and after the sampled genealogy law (2,354 declarations, 257
modules) are retained in
[tracked-chain-limit-axioms.log](evidence/tracked-chain-limit-axioms.log) and
[critical-genealogy-axioms.log](evidence/critical-genealogy-axioms.log), with
their context files. `C.1` was generalized from a law on infinite matrices to a
family of block laws (`leafTightFamily`); the reviewed `LeafTightCriterion`
statement is unchanged and still proved.

The previous checkpoint, after proving `C.1` (N17) and forward leaf-tightness,
ran the default all-source checker: `lake build` (4,120 jobs) and the
transitive-axiom check for **2,159 explicit definitions and theorems in all 246
maintained modules**. Only `propext`, `Classical.choice`, and `Quot.sound`
occur, or no axioms. See
[leaf-tight-criterion-axioms.log](evidence/leaf-tight-criterion-axioms.log) and
[exact scope and hashes](evidence/leaf-tight-criterion-context.txt). Intermediate
all-source runs for forward leaf-tightness (2,085 declarations, 237 modules) and
for the conditional `C.1` reduction (2,135 declarations, 242 modules) are
retained in [forward-leaf-tightness-axioms.log](evidence/forward-leaf-tightness-axioms.log)
and [leaf-tight-reduction-axioms.log](evidence/leaf-tight-reduction-axioms.log),
with their context files.

The preceding leaf-tightness checkpoint ran the **default all-source** checker
`python3 scripts/check_axioms.py`: `lake build` (4,103 jobs) and the
transitive-axiom check for **2,077 explicit definitions and theorems in all 236
maintained modules**, every one imported by `Freezing2.lean`. It adds the
iid-sequence marginals, fixed-query N13, the dyadic chaining bounds,
`eq:stepone` and leaf-tightness `eq:GH`. Only `propext`, `Classical.choice`,
and `Quot.sound` occur, or no axioms. See
[critical-leaf-tightness-axioms.log](evidence/critical-leaf-tightness-axioms.log)
and [exact scope and hashes](evidence/critical-leaf-tightness-context.txt).
An intermediate all-source run for `eq:stepone` (2,074 declarations, 235
modules) is retained in
[critical-stepone-axioms.log](evidence/critical-stepone-axioms.log) and
[its context](evidence/critical-stepone-context.txt).

The preceding N13 integration passed `lake build` (4,098 jobs) and the
transitive-axiom check for **2,044 explicit definitions and theorems in 232
modules**, which at that run were all maintained sources. It adds N13, repaired
U36 occupancy, the actual-history conditional block chain U37, the literal
discrete attachment-rate samplers, GHP tightness transfer, sampled-distance and
covering-radius laws with their GHP continuity, the full-support criterion, and
the normalized continuous coalescent clocks with measurable next-event kernels.
Only `propext`, `Classical.choice`, and `Quot.sound` occur, or no axioms. See
[critical-cover-axioms.log](evidence/critical-cover-axioms.log) and
[exact scope and hashes](evidence/critical-cover-context.txt).

The preceding critical-topology integration passed `lake build` (4,045 jobs)
and the transitive-axiom check for **1,806 explicit definitions and theorems in
199 modules**. It includes all prior integrated results, the exact GHP Polish
space and compact-preimage theorem, the corrected positive-index N14 with its
source quantifiers, actual oldest-isolation coupling, deterministic chaining,
finite-family and varying-domination convergence, mesh jitter and measurable
profile-mark analysis, and finite occupancy ingredients. Only `propext`,
`Classical.choice`, and `Quot.sound` occur, or no axioms. See
[critical-topology-axioms.log](evidence/critical-topology-axioms.log)
and [exact scope and hashes](evidence/critical-topology-context.txt).
It is retained as historical evidence.

The preceding critical-foundations checkpoint verified **1,683 declarations
in 171 modules**, with 4,004 build jobs. Its
[proof output](evidence/critical-foundations-axioms.log) and
[exact scope and hashes](evidence/critical-foundations-context.txt) are retained
as historical evidence.

The preceding noncritical-main-results checkpoint verified **1,517 declarations
in 153 modules**, with 3,986 build jobs. Its
[proof output](evidence/noncritical-main-results-axioms.log) and
[exact scope and hashes](evidence/noncritical-main-results-context.txt) are retained
as historical evidence. The current checkpoint includes the subsequent genuine
metric instance and the affected M02 import closure.

The preceding forward-supercritical checkpoint verified **1,451 declarations
in 143 modules**, with 3,976 build jobs. Its
[proof output](evidence/forward-supercritical-axioms.log) and
[exact scope and hashes](evidence/forward-supercritical-context.txt) are retained.

The preceding noncritical-limits checkpoint verified **1,357 declarations in
132 modules**, with 3,965 build jobs. Its
[proof output](evidence/noncritical-limits-axioms.log) and
[exact scope and hashes](evidence/noncritical-limits-context.txt) are retained.

The earlier geometry/history checkpoint verified **1,272 explicit declarations
in 122 modules**, with 3,955 build jobs. Its
[proof output](evidence/geometry-history-axioms.log) and
[exact scope and hashes](evidence/geometry-history-context.txt) are retained as
historical evidence. A subsequent 127-module law-comparison check also passed;
its log is historical because the ambient-topology definition was strengthened
afterward. The current 132-module checkpoint covers that strengthening.

The earlier noncritical-dependency integration passed `lake build` (3,937 jobs)
and the transitive-axiom check for **1,115 explicit definitions and theorems in
104 modules**. It includes N10, the actual fixed-$k$ iid branch limits, the
varying-space weak perturbation theorem, the subcritical uniform distortion
subclaim, graph-metric foundations, and the completed N01 history/support/order
dependencies, in addition to the earlier reverse-process results. Only
`propext`, `Classical.choice`, and `Quot.sound` occur, or no axioms. See
[noncritical-dependencies-axioms.log](evidence/noncritical-dependencies-axioms.log)
and [exact scope and hashes](evidence/noncritical-dependencies-context.txt).
Unintegrated drafts and subsequent additions remain outside this evidence.
The generic finite induced-graph distance helper was generalized to an explicit
`DecidableEq` parameter during the subsequent GH work. The 122-module checkpoint
above covers that change and the integrated canonical-replay/permutation modules;
the 104-module hash record remains historical evidence.

The earlier reverse-process integration passed `lake build` (3,912 jobs) and the
transitive-axiom check for **963 explicit definitions and theorems in 87
modules**. This covers the actual N02–N04 reverse laws, N07 approximation,
N08 maximum estimate, uniform birth limit, prior M01/N06 results, and the
24-module companion closure. Only `propext`, `Classical.choice`, and
`Quot.sound` occur, or no axioms. The complete output is
[reverse-milestone-axioms.log](evidence/reverse-milestone-axioms.log), with exact
proof, entry-point, configuration, source-paper, and checker hashes in
[reverse-milestone-context.txt](evidence/reverse-milestone-context.txt).
This explicitly scoped development checkpoint excludes unfinished modules;
their names are recorded. It is not an all-source completion check.

The checker now handles nested namespaces, named sections, wrapped axiom lists,
and nested Lean comments; a documentation sentence had initially been misread
as a declaration. The corrected checker reran the complete checkpoint and
verified that no selected proof or configuration file changed during it.
Later additions require fresh integration evidence. In particular, the entry
point and the shared finite distance-error helper have changed since that
snapshot; its exact hashes describe a historical checkpoint, not the entire
current tree. The 104-module checkpoint above supersedes it for integrated
noncritical dependencies.

The earlier M01/N06 checkpoint checked 535 declarations in 54 modules:
[build.log](evidence/build.log), [axioms.log](evidence/axioms.log), and
[check-context.txt](evidence/check-context.txt). It remains historical evidence.

The earlier 257-declaration/28-module population checkpoint remains in
[profile-milestone-axioms.log](evidence/profile-milestone-axioms.log) and
[profile-milestone-context.txt](evidence/profile-milestone-context.txt).
Declaration counts include definitions, helpers, and obstruction results;
they are not counts of formalized paper results.

The source paper is unchanged and its hash still matches. The full inventory was freshly reconciled, retaining all 23 named environments and substantive obligations, including the newly explicit S19 qualification and U20 nonuniversality claim. Independent
reviews now cover the population-profile interfaces and their affected dependencies;
[the milestone audit](docs/milestone-audit.md) records both source correspondence
and substantive departures. No whole-paper completion claim is made.

These are local checks using the pinned installed dependencies. A fresh public
checkout, Linux Comparator, independent kernel replay, and full Palomar preflight
have **not** been verified.

The reproducible local check is:

```sh
python3 scripts/check_axioms.py
```

It runs `lake build`, then queries transitive axioms of all explicit definitions
and theorems in the maintained modules. Only `propext`, `Classical.choice`, and
`Quot.sound` are permitted. This does not replace Comparator or Palomar's full
mechanical verification. There are no deliberate Challenge holes in this project.

During active development, `python3 scripts/check_axioms.py --integrated`
checks only the entry point's local import closure and explicitly lists excluded
draft files. The default command remains the stricter all-source check required
for a publication candidate.

## Remaining mathematical work and publication status

M01–M04, corrected M06 and all numbered results N01–N17 are proved with the
current integrated evidence, in the forms and with the qualifications recorded
above. No whole-paper completion is claimed. The remaining source obligations
are:

1. **M05 (`cor:CRT`)**, with U42–U48 and E02, E05, E07, E08. Blocked by
   external mathematics absent from the pinned Mathlib and from the companion
   project: a constructed Brownian excursion and Brownian CRT, Kaigh's and
   Aldous's invariance principles, Skorokhod representation, and local limit
   theorems for simple random walk. It also uses the uniform-plane-tree law E02
   (item 5), now proved here in plane-tree form (open in the companion project
   as its row A03); the source cites it as companion "Theorem 2", which in the local
   companion is the Examples paragraph (S20). M05 also needs measurability of
   $f\mapsto$ `criticalTreeLaw (1/f)` for the mixture identity (this is where
   the remark at line 254, that the results apply to random sequences, is
   exercised) and a terminal-horizon
   version of M03 (S14); U48 needs a pointed limit. The printed estimates S15
   and S16 are refuted in Lean, so valid replacement estimates, and the scaling
   correction S17, are needed before the source's route can be checked. See
   [docs/coverage-gaps.md](docs/coverage-gaps.md).
2. **U04a, dimensions**: the almost-sure lower bound $2$ for the Minkowski,
   packing and Hausdorff dimensions of $\mathcal T(f)$. The source gives no
   proof; the pinned Mathlib has `dimH` only, with no Minkowski or packing
   dimension and no Frostman-type lemma. The finite-dimensional clause of U04a
   is covered.
3. **U04b, remaining clause**: convergence of the supercritical trees to the
   long dendron in the ET21/Jan21 topology, which is absent from Mathlib. The
   comparisons with stable trees, non-generic and Cauchy–Bienaymé trees, and
   superexponential simply generated trees concern other models: they are
   external background (E11, classification (d) in
   [docs/coverage-gaps.md](docs/coverage-gaps.md)) and need no proof here.
4. **U24, Aldous time change** (`rem:timechange`, E04): the stochastic time
   change to Aldous's inhomogeneous coalescent, and Aldous's Theorem 2 (an
   alternative route to M05). The deterministic time change, the genealogy and
   its density are proved.
5. **U01, second clause** (E02): proved in plane-tree and rooted-isometry form
   ([UniformPlaneTree.lean](Freezing2/MainResults/UniformPlaneTree.lean)); only the
   pushforward to a law on `MeasuredGHSpace` (needed by M05) is not stated. The
   $\alpha=1$ descriptions are companion background.
6. **E05**: the Skorokhod representation theorem, absent from Mathlib. It is
   needed only in the CRT section (item 1); its other uses are bypassed.
7. **Residual qualifications** recorded in the rows above: U34's count
   including unborn marked vertices (bypassed for N14); the finite decoding of
   N12a's discrete event to $\mathcal F^n_r$; an explicit Markov path process
   for U23; the "root of degree one" remark in the proof of M04 (needs a pointed
   limit); and the printed false or undefined statements (S01, S02, S06, N14 at
   $i=0$, S15, S16), which cannot be certified literally.
8. **Bypassed or unexported intermediate claims.** Under the inventory's rule,
   a different proof of a later theorem does not check the paper's
   intermediate steps. The following remain uncertified, although the results
   they serve are proved:
   - U28: the source route `eq:cv locale bis`, Fatou with conservation of
     mass, and Scheffé (lines 1390–1458), bypassed by the tracked-chain proof
     of N12b;
   - U32: the intermediate displays `16/01/11h` (line 1539) and `eq:delta`
     (lines 1542–1549) and the uniform-integrability argument; only `eq:GH`
     and the transfer are proved;
   - U24: the statement that $g_{0,k}$ determines the law in the divergent
     case (line 1302), which follows from N11 with $r=0$ and
     `coalescentLaw_allMerge` but is not stated separately;
   - U03: the explanatory prose at line 325, which is heuristic;
   - U27: the full local genealogy density and the discrete ordered and
     squared attachment-rate exports;
   - U20: an admissible array with no GHP limit, and the exclusion of a random
     universal limit (both immediate from the two examples, not exported).
   - Proved since the omission scan, in
     [ModelFacts.lean](Freezing2/MainResults/ModelFacts.lean): U06's monotone
     coupling (`forward_treeLaw_ae_evolve_extends`), stationarity exactly from
     extinction (`forward_treeLaw_succ_eq_self_iff`) and dependence on the
     first $n$ signs only (`forward_treeLaw_eq_of_eqOn`,
     `freezingTreeLaw_eq_of_eqOn`); U29's normalization $\sum_r\sum_{F_0}\int
     1_{[0,1]^k}g_{r,k}=1$ (`sum_lintegral_indicator_sourceDensity_eq_one`); and
     U20's $L^p$ height form under bounded population
     (`bounded_population_height_tendsto_Lp`).
9. **Omission scan.** The whole-source omission scan of 30 October 2026
   ([docs/omission-scan-2026-10-30.md](docs/omission-scan-2026-10-30.md)) is
   an agent scan, not a human review. It found no uncovered theorem, lemma or
   proof step on which a stated result depends. Its six uncovered claims are
   inventory rows U53–U58: companion background, heuristics, source slips,
   and U55, which can be derived from N01 and the first clause of U01 but is
   not stated as a theorem. Its source findings are S20–S23, together with
   minor slips listed in [MANUSCRIPT_RECOMMENDATIONS.md](MANUSCRIPT_RECOMMENDATIONS.md).
   Repeat the scan if the source or the claimed coverage changes, and before
   any coverage claim.

[Publication readiness](docs/publication-readiness.md) records the destination
requirements and current blockers. There is no public repository commit,
selected repository license, source-reviewed final Challenge/Solution pair,
Comparator pass, full Palomar mechanical report, submission, or registration.
A buildable partial library and complete-looking inventory must not be described
as the requested verified publication candidate.
