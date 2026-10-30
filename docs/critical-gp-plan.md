# Plan for the critical finite-dimensional limit `eq:GP` (N11, N12, U25)

Status: **completed for `eq:GP` and M03 up to the real-tree clause U26.** This
document records the formal route; the implemented route is the "revised route"
below, steps 1–5, all proved (see the progress list).

## Target

`eq:GP`: for every $k$, the sampled distance matrix
$(d^n(V_j,V_\ell)/\sqrt n)_{j,\ell\le k}$ of the actual tree with iid uniform
vertices converges in law to
$(\int_{C_{j\ell}}^{B_j}(2f)^{-1}+\int_{C_{j\ell}}^{B_\ell}(2f)^{-1})_{j,\ell}$,
where $(B,C)$ are births and pairwise coalescence times of the continuous
coalescent (with $C_{j\ell}=0$ if never merged and $C_{jj}=B_j$).

By N07 and the harmonic approximations, it suffices to prove N12b: joint
convergence of $(B^n_j/n, \mathrm{coal}_n(V_j,V_\ell)/n)$.

## Encoding

Use partition paths instead of plane forests (S09 is then irrelevant for
`eq:GP`; the literal plane-forest statement N11 is a later bridge):

- state: partition of the born sample indices into current clusters;
- events, in decreasing time: birth of sample $j$, or merger of two current
  blocks (unordered);
- discrete merge probability of a specific pair at an up-step: $1/\binom{S}{2}$
  (`ClusterTransition.transitionLaw_fixedPair`); no tracked merge:
  $1-\binom{a}{2}/\binom{S}{2}$ (`transitionLaw_noMerger`);
- continuous density of a path: births density one each, merges
  $\prod 1/f(c)^2$, survival $\exp(-\int\binom{a(t)}{2}/f^2)$.

## Progress

- Done: `Probability/ReverseMarkovPath.lean` (`jointLaw_path_eq_prod`: exact path
  probabilities of the reverse history from the actual kernel and conditional
  expectations) and `Probability/TrackedGenealogy.lean`
  (`jointLaw_trackedGenealogy`: a prescribed tracked connectivity/count path of
  distinct labels born before the horizon has probability
  $\prod$ `stepFactor`, with factor 1 at freezing steps, $1-\binom a2/\binom S2$ at
  attachment steps without tracked merger, $1/\binom S2$ at a prescribed merger).
- Done: `Probability/CriticalTreeBridge.lean` (component 6 below).
- Done (revised route, all steps): `TrackedChain` (exact one-step law, Markov
  step, Chapman–Kolmogorov), `MatrixProductLimit` (telescoping bound and
  `tendsto_orderedProd_exp`), `TrackedChainLimit` (one-step matrix is
  $1+h\,G$; birth-free windows; continuous `propagator` and
  `tendsto_chainPower_propagator`), `TrackedChainPath` (observation recursions
  and their convergence), `VertexQuantileCoupling` (iid uniform vertices from
  Lebesgue measure with a.s. convergent scaled births, replacing Skorokhod),
  `CriticalGenealogyLimit` and `CriticalSampledGenealogy` (coalescence-threshold
  events and upper-set limits), `CriticalGenealogyLaw` (co-countable π-system,
  identification, convergence), `CriticalDistanceLimit` (U25, `eq:GP` for the
  reverse tree) and `CriticalScalingLimit` (forward transfer, family `C.1`, M03
  as `critical_scaling_limit`). The local limit N12a and the density N11 were
  not needed.
- Revised route for N12b (replaces components 2–4 for M03; N11's density
  formula stays a separate source obligation):
  1. *Lumped tracked chain.* State = connectivity relation of the tracked labels
     (`Fin k → Fin k → Bool`, unborn labels as singletons). From the step lemmas,
     the state process is a Markov chain: at an attachment step the matrix is
     $I+h_pG_\beta$ with $h_p=1/\binom{S_{p+1}}2$ and $G_\beta$ the Kingman
     generator on the born labels; freezing steps insert a singleton. Prove the
     distribution recursion for events constraining the state at finitely many
     steps.
  2. *Matrix products.* Factors commute within a birth-free interval; a telescoping
     bound gives $\|\prod(I+h_pG)-\exp((\sum h_p)G)\|\le C\sum h_p^2\to0$, and
     $\sum h_p\to\int 1/f^2$ by `tendsto_critical_coalescence_hazard_sum`.
  3. *Births.* Average over iid uniform frozen labels; empirical down-step law to
     Lebesgue (N06(ii)); continuous convergence plus Portmanteau.
  4. *Identification.* Laws of $(B^n/n, C^n/n)$ live on a compact cube; any two
     subsequential limits agree on the π-system of events {births in boxes,
     connectivity at finitely many times outside both limits' atoms}; hence
     convergence, with a limit depending only on $f$.
  5. `C.1` only uses block laws: add a variant taking a consistent family of block
     laws instead of a law $M$ on infinite matrices (avoids Kolmogorov extension).

## Components

1. **Markov path product (discrete, exact).** For `Kernel.traj`, if transition
   events have deterministic one-step probability on the event that the past
   path is as prescribed, the path probability is the product. Then the tracked
   partition path law of fixed distinct frozen labels is the explicit product.
2. **Continuous normalization.** Above a cutoff $\varepsilon$, the merge process
   given births is a finite-rate jump process; prove the total density mass is
   one by induction on the number of blocks, using the clock normalization in
   `ContinuousCoalescentHazard`/`Endpoint` (density plus atom has mass one).
3. **Local limit (N12a analogue).** Under uniform reference laws on down-steps
   (births) and up-steps (merges), the rescaled discrete path probabilities
   converge in probability to the continuous density, using
   `CriticalSurvivalProduct`, `AuxiliaryAttachmentSquare` (joint convergence of
   time and $n/S^2$), `MarkedProfileSampling`, and sign-measure limits N06(ii).
4. **Weak convergence (N12b).** Fatou plus equal total mass gives convergence of
   expectations (`FiniteFamilyScheffe`), Scheffé gives $L^1$, and
   `VariableDominatedConvergence` gives bounded test functions; then remove the
   cutoff $\varepsilon$.
5. **Distances (U25) and `eq:GP`.** Continuous mapping with the profile time
   change $H$ (`ProfileTimeChange`), N07, frozen-distinct sampling corrections.
6. **Bridge into `C.1`** for `forwardMeasuredTreeLaw x (1/2) n`: annealed
   matrix laws equal the sampled matrices; annealed cover radius equals the
   `eq:GH` event (with $k+1$ samples); then M03 modulo U26 (real trees).

Existing ingredients are listed in `FORMALIZATION_REPORT.md` rows U27–U29.
