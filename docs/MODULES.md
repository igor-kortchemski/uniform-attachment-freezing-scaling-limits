# Module map

The library `Freezing2` has 289 modules, all imported by
[Freezing2.lean](../Freezing2.lean). The main statements are in
[Challenge.lean](../Challenge.lean) and are proved from the library in
[Freezing2/Interface/Statements.lean](../Freezing2/Interface/Statements.lean).
The [formalization report](../FORMALIZATION_REPORT.md) maps every result of the
paper to its Lean declarations.

## Directories

| Directory | Content |
| --- | --- |
| [Discrete](../Freezing2/Discrete) | Signed walks, vertex labels and finite estimates |
| [Analysis](../Freezing2/Analysis) | Population profiles, harmonic sums, Bennett's function and other real analysis |
| [Probability](../Freezing2/Probability) | Tree laws, couplings, coalescence and the probabilistic limit theorems |
| [Geometry](../Freezing2/Geometry) | Graph metrics, real trees, and the GH, GHP and GP spaces |
| [MainResults](../Freezing2/MainResults) | The main theorems for the actual forward trees |
| [Interface](../Freezing2/Interface) | Definitions shared with `Challenge.lean`, bridges, and the proofs of the Challenge statements |
| [Audit](../Freezing2/Audit) | Obstructions and Lean refutations for printed statements of the paper |
| [Companion](../Freezing2/Companion) | Modules adapted from the companion formalization ([provenance](companion-provenance.md)) |

## Selected modules

| Module | Content |
| --- | --- |
| [Walk](../Freezing2/Discrete/Walk.lean) | Signed paths, counts, survival, and faithful natural-number representation |
| [Labels](../Freezing2/Discrete/Labels.lean) | Disjoint vertex labels, birth times, actual uniform measure, `uniformVertex_birth_lt_before_extinction` |
| [WeightedWalk](../Freezing2/Discrete/WeightedWalk.lean) | Exact harmonic and coalescence weighted balances |
| [Estimates](../Freezing2/Discrete/Estimates.lean) | Specialization to the paper's surviving signed paths and uniform logarithmic boundary bound |
| [Bennett](../Freezing2/Probability/Bennett.lean) | Both strict concentration tails and absolute deviation, derived from exact Bernoulli MGFs |
| [BennettFunction](../Freezing2/Analysis/BennettFunction.lean) | Positivity and monotonicity of Bennett's rate function |
| [ExponentialDecay](../Freezing2/Analysis/ExponentialDecay.lean) | Polynomial versus stretched-exponential and geometric decay |
| [SourceHypotheses](../Freezing2/Analysis/SourceHypotheses.lean) | Source profile conventions and sublinear population, N06(i) |
| [SignMeasures](../Freezing2/Analysis/SignMeasures.lean) | Weak convergence of both empirical sign measures, N06(ii) |
| [HarmonicConclusions](../Freezing2/Analysis/HarmonicConclusions.lean) | Harmonic asymptotic equivalences and the uniform interval maximum, N06(iii–iv) |
| [LocalSquareProfiles](../Freezing2/Analysis/LocalSquareProfiles.lean) | Equivalence of the source's local square-moment and squared-$L^1$ hypotheses |
| [InteriorMinimumLimit](../Freezing2/Analysis/InteriorMinimumLimit.lean) | Interior minimum growth needed by N06(v) |
| [PopulationLemma](../Freezing2/Analysis/PopulationLemma.lean) | All five parts of the population-profile lemma in source notation |
| [Height](../Freezing2/MainResults/Height.lean) | Introduction height theorem for the actual forward tree law |
| [SubcriticalDistribution](../Freezing2/MainResults/SubcriticalDistribution.lean) | Actual forward subcritical measured-tree convergence in the GHP topology |
| [Supercritical](../Freezing2/MainResults/Supercritical.lean) | Corrected root-inclusive forward supercritical matrix limit |
| [CriticalRealTree](../Freezing2/Probability/CriticalRealTree.lean) | Critical GHP limit to a random compact measured real tree, M03 |
| [CriticalLeaves](../Freezing2/Probability/CriticalLeaves.lean) | The limit's mass measure charges only leaves, M04a |
| [CriticalBranching](../Freezing2/Probability/CriticalBranching.lean) | Binary criterion and infinite-degree point (unpointed), M04b–c |
| [BoundedPopulation](../Freezing2/MainResults/BoundedPopulation.lean) | Bounded-population GH limit to a segment, N09 |
| [BoundedPopulationMeasure](../Freezing2/MainResults/BoundedPopulationMeasure.lean) | GHP nonuniversality for bounded populations, U20 (new formulation) |
| [RecursiveNoLimit](../Freezing2/MainResults/RecursiveNoLimit.lean) | Recursive trees have no nondegenerate GHP limit, U04b (S19-qualified) |
| [SupercriticalNonTight](../Freezing2/MainResults/SupercriticalNonTight.lean) | Supercritical GHP non-tightness, U04b (S08-corrected) |
| [ReversePaper](../Freezing2/Probability/ReversePaper.lean) | Actual conditional increments in original labels, including extinction |
| [CoalescenceHistory](../Freezing2/Probability/CoalescenceHistory.lean) | Corrected exact coalescence distribution for distinct vertices |
| [DistanceApproximation](../Freezing2/Probability/DistanceApproximation.lean) | Uniform approximation of actual reverse-tree distances |
| [SubcriticalCoalescenceLaw](../Freezing2/Probability/SubcriticalCoalescenceLaw.lean) | Uniform maximum coalescence delay is sublinear |
| [BirthTimeLimit](../Freezing2/Probability/BirthTimeLimit.lean) | Actual normalized birth measures converge weakly to uniform measure |
| [BranchLengthLimit](../Freezing2/Probability/BranchLengthLimit.lean) | Actual scalar and fixed-$k$ iid harmonic branch limits |
| [SupercriticalCoalescenceLaw](../Freezing2/Probability/SupercriticalCoalescenceLaw.lean) | Actual iid sampled coalescence time is sublinear |
| [SubcriticalDistanceApproximation](../Freezing2/Probability/SubcriticalDistanceApproximation.lean) | Uniform graph-distance approximation under harmonic coordinates |
| [SubcriticalGHLimit](../Freezing2/Probability/SubcriticalGHLimit.lean) | Actual reverse-tree GH convergence to the source segment |
| [ForwardTerminalLaw](../Freezing2/Probability/ForwardTerminalLaw.lean) | Exact masses on the fixed schedule's reachable terminal support |
| [CoalescentForests](../Freezing2/Probability/CoalescentForests.lean) | Continuous coalescent forest density in source form, N11 |
| [CriticalLocalLimitPlane](../Freezing2/Probability/CriticalLocalLimitPlane.lean) | Corrected local limit in tracked-chain form, N12a |
| [CriticalGenealogyLaw](../Freezing2/Probability/CriticalGenealogyLaw.lean) | Convergence of sampled birth and coalescence times, N12b |
| [CriticalSampledCover](../Freezing2/Probability/CriticalSampledCover.lean) | Tightness time estimate with repaired constants, N13 |
| [OneStepTightnessAsymptotic](../Freezing2/Probability/OneStepTightnessAsymptotic.lean) | One-block tightness estimate for positive block indices, N14 |
| [GPMatrixCharacterization](../Freezing2/Probability/GPMatrixCharacterization.lean) | GP convergence iff convergence of sampled distance matrices, N15 |
| [GPGHtoGHP](../Freezing2/Probability/GPGHtoGHP.lean) | GP plus GH weak convergence gives GHP weak convergence, N16 |
| [SampledReconstruction](../Freezing2/Probability/SampledReconstruction.lean) | Leaf-tightness criterion `C.1`, N17 |
| [GromovProkhorov](../Freezing2/Geometry/GromovProkhorov.lean) | Polish Gromov–Prokhorov space and the GHP-to-GP projection |
| [Obstructions](../Freezing2/Audit/Obstructions.lean) | Zero-diagonal correction, distributional obstruction, and other precise source issues |
| [ExcursionCounterexamples](../Freezing2/Audit/ExcursionCounterexamples.lean) | Lean refutations of the printed CRT estimates S15 and S16 |
