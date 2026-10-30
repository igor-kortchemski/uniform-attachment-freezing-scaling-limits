# Statement interface (Challenge / Solution / Comparator)

This note explains the Comparator statement interface of the formalization of
*Uniform attachment with freezing: Scaling limits*
([attachement-uniforme-2-final.tex](../attachement-uniforme-2-final.tex)). It is
the reference for reviewers of [Challenge.lean](../Challenge.lean).

## Files

| File | Role |
| --- | --- |
| [Freezing2/Interface/Defs.lean](../Freezing2/Interface/Defs.lean) | Single source of truth for the interface definitions. Imports only Mathlib. |
| [Challenge.lean](../Challenge.lean) | Same imports, a verbatim copy of the block of `Defs.lean` between the markers `BEGIN SHARED DEFINITIONS` and `END SHARED DEFINITIONS`, then the five statements with deliberate `sorry` proofs. |
| [Freezing2/Interface/BridgeModel.lean](../Freezing2/Interface/BridgeModel.lean) | Bridge for the discrete model, the hypotheses, heights and sampled distances. |
| [Freezing2/Interface/BridgeGHP.lean](../Freezing2/Interface/BridgeGHP.lean) | Bridge for compact measured spaces, the GHP topology and weak convergence. |
| [Freezing2/Interface/Statements.lean](../Freezing2/Interface/Statements.lean) | Proofs of the five statements, with the Challenge names, from the library results. |
| [Solution.lean](../Solution.lean) | Imports the whole library (`Freezing2`), hence `Statements`. Does not import `Challenge`. |
| [comparator.json](../comparator.json) | The five theorem names, `definition_names: []`, permitted axioms `propext`, `Classical.choice`, `Quot.sound`. |
| [scripts/check_challenge.py](../scripts/check_challenge.py) | Checks the verbatim copy and the Palomar size and import constraints. |

All interface constants are in the namespace `FreezingStatements`, which no
library module uses, so a Challenge constant never shares a name with a library
constant. Comparator requires every constant reachable from the five
statements (including definition bodies and proofs nested in definitions) to be
identical in the Challenge and Solution environments. Since `Challenge.lean`
and `Defs.lean` have the same imports and the same text for these
declarations, under `@[expose] public section`, their elaborations coincide.
Proofs nested in definitions are short term-mode or `rw` proofs, which create
no module-private auxiliary declaration.

The only proof holes are the five `sorry` proofs of the Challenge statements;
each produces the expected warning `declaration uses sorry` when
`Challenge.lean` is built. All definitions are complete. The library,
`Statements.lean` and `Solution.lean` contain no `sorry`, and the five Solution
theorems depend only on `propext`, `Classical.choice` and `Quot.sound`.

## Notation shared by the statements

* The driving array is `x : ℕ → ℕ → ℤ`; its row `x n` is the source's sequence
  $X^n$, read at indices $1, \dots, n$ (index $0$ is unused). The hypothesis
  `∀ n, 0 < n → IsSigned (x n) ∧ SurvivesThrough (x n) n` states
  $X^n_i \in \{-1, 1\}$ and $\tau(X^n) > n$ for every $n \ge 1$, where
  $S_k(X) = 1 + \sum_{i \le k} X_i$ is `activeCount`.
* `profileMeasure` is Lebesgue measure on $[0, 1]$. The source's function
  $f : [0,1] \to \mathbb{R}_+$ enters through $g = 1/f$. The hypothesis
  `∀ᵐ t ∂profileMeasure, 0 < f t` makes $1/f$ meaningful with Lean's convention
  $1/0 = 0$; it follows from $1/f \in L^1$ in the source.
* `HasL1ReciprocalProfile x α (1/f)` is $(\mathsf{Lim}^\alpha_{1/f})$: $1/f$ is
  integrable on $[0,1]$ and $t \mapsto n^\alpha / S^n_{\lfloor nt \rfloor}$
  converges to $1/f$ in $L^1([0,1])$.
* `HasLocalSquareMomentProfile x α (1/f)` is $(\mathsf{Lim}^\alpha_{1/f^2})$
  together with the standing assumption $1/f \in L^2_{\mathrm{loc}}((0,1))$: for
  all $0 < a < b < 1$, $f^{-2}$ is integrable on $[a,b]$ and
  $\int_a^b (n^\alpha/S^n_{nt})^2\,dt \to \int_a^b f^{-2}$.
* `branchLength f u` is $\int_0^u \frac{dt}{2f(t)}$.

### The random trees

`TreeState` records the vertices (natural numbers; the root is $0$ and the
vertex born at time $t$ is $t$), the active vertices and the edges.
`step s t ε v` is one step of Algorithm 1 at the chosen active vertex $v$: for
$\varepsilon = 1$ a new active vertex $t$ is attached to $v$; otherwise $v$ is
frozen. `transitionLaw` chooses $v$ uniformly among the active vertices (a
state with no active vertex is frozen forever), and `treeLaw x n` is the law of
$\mathcal T_n(X)$, obtained by iterating these transitions with `Measure.bind`.
The statements use `treeLaw (x n) n`, the law of $\mathcal T_n = \mathcal T_n(X^n)$.

`height s` is the largest graph distance to the root, and
`sampledDistanceLaw x α n k` is the law of the matrix
$(d^n(V_i,V_j)/n^{1-\alpha})_{0 \le i,j \le k}$, where $V_0$ is the root and,
given the tree, $V_1, \dots, V_k$ are independent uniform vertices.

### Compact measured spaces and the GHP topology

`CompactMeasuredSpace` bundles a type with a metric, nonemptiness, compactness,
the Borel σ-algebra and a probability measure, exactly as the library's
`Freezing2.CompactMeasuredSpace`. The GHP distance `ghpDist` is the source's
infimum, over isometric embeddings $i, j$ of the two spaces into a common metric
space, of the Lévy–Prokhorov distance of the image measures plus the Hausdorff
distance of the images (`ghpCosts`, `ghpDistance`, copies of the library
definitions).

The GHP topology is `TopologicalSpace.generateFrom` of the open GHP balls, and
the measurable structure is its Borel σ-algebra. This needs no proof
obligation in the Challenge: the topology is defined on the spaces themselves,
not on their isometry classes. Since `ghpDist` is a pseudometric (proved in the
bridge), this is a pseudometric topology whose Kolmogorov quotient is the usual
GHP space of measure-preserving isometry classes.

`ConvergesInDistribution μ ν` means that $\int F\,d\mu_n \to \int F\,d\nu$ for
every bounded continuous $F$, the defining condition of weak convergence.

`treeSpace c s` is the tree of `s` with $c$ times its graph distance and the
uniform probability on its vertices; `scaledTreeLaw x n c` is the law of
$c \cdot \mathcal T_n(X)$ as a random compact measured space. A one-point
fallback is used only for a disconnected graph or $c \le 0$, which never
occurs for the random trees with positive scaling.

`measuredSegment L φ` is the segment $[0, L]$ with the image of the uniform
measure on $[0, 1]$ under $\varphi$. Values of $\varphi$ are clamped into
$[0, L]$; this changes nothing for the segment of `thm:sous-critique`, where
$\varphi$ maps $[0, 1]$ onto $[0, L]$. For $L < 0$ it is the one-point space.

### Real trees and degrees

`IsRealTree X` is the standard definition: any two points are joined by a unique
geodesic segment, and every injective path between them has the image of that
segment. `degree x` is the number, in $\mathbb N \cup \{\infty\}$, of connected
components of $X \setminus \{x\}$. Leaves are points of degree $1$, branch
points those of degree at least $3$, and a binary branch point has degree $3$
(two children).

## The statements

### `height_scaling_limit` — Theorem `thm:heightalpha` (M01)

Let $0 < \alpha < 1$ and assume $(\mathsf{Lim}^\alpha_{1/f})$. Then for every real
$p \ge 1$,

$$
\frac{\mathrm{Height}(\mathcal T_n)}{n^{1-\alpha}} \longrightarrow \int_0^1 \frac{dt}{2f(t)}
\quad \text{in } L^p,
$$

stated as `eLpNorm (Height/n^(1-α) - ∫_0^1 dt/(2f)) p → 0` under `treeLaw (x n) n`.
The source also assumes $(\mathsf{Lim}^\alpha_{1/f^2})$, which is not needed;
the statement is therefore stronger than the source's.

### `subcritical_scaling_limit` — Theorem `thm:sous-critique` (M02)

Let $0 < \alpha < 1/2$ and assume $(\mathsf{Lim}^\alpha_{1/f})$ and
$(\mathsf{Lim}^\alpha_{1/f^2})$. Then $n^{-(1-\alpha)} \mathcal T_n$, with the
uniform probability on its vertices, converges in distribution for the GHP
topology to the deterministic segment $[0, \int_0^1 \frac{dt}{2f}]$ equipped with
the image of the uniform measure on $[0,1]$ under
$u \mapsto \int_0^u \frac{dt}{2f}$. The limit is a Dirac mass at
`measuredSegment (branchLength f 1) (branchLength f)`.

### `critical_scaling_limit` — Theorems `thm:critique` and `thm:properties` (M03, M04)

The source states that $\mathcal T_n/\sqrt n$ converges to "a random measured
compact real tree $\mathcal T(f)$" and then lists its properties. The
interface states both theorems at once:

there is a map `T` from functions $f$ to laws of random compact measured
spaces such that, for every array $X$ and every $f$ with $\alpha = 1/2$,
$(\mathsf{Lim}^{1/2}_{1/f})$, $(\mathsf{Lim}^{1/2}_{1/f^2})$ and
$\max_{1 \le k \le n} S^n_k = O(\sqrt n)$:

1. $\mathcal T_n/\sqrt n$, with the uniform probability on its vertices,
   converges in distribution for the GHP topology to `T f`;
2. `T f`-almost surely, the space $\mathcal T(f)$ satisfies:
   * its mass measure has full support (`IsOpenPosMeasure`);
   * it is a real tree;
   * its mass measure gives full measure to the leaves (`thm:properties` (1));
   * it is binary, that is, all degrees are at most $3$, if and only if
     $\int_0^{1/2} f^{-2} = \infty$ (written as a lower Lebesgue integral over
     $(0, 1/2]$, which is $\infty$ exactly when the integral diverges);
   * if $\int_0^{1/2} f^{-2} < \infty$, some point $\rho$ has infinite degree and
     every other point of degree at least $3$ has degree exactly $3$
     (`thm:properties` (2)).

Encoding choices:

* **Existential limit law.** `T` is quantified before the array and the
  profile, so the limit law depends only on $f$, as in the source. Because the
  GHP topology on spaces (not on classes) is not Hausdorff, weak limits are not
  unique as points of the topology; but Borel sets are unions of isometry
  classes, so a law is fully determined by its image on classes, and that image
  is unique. All the listed properties are invariant under measure-preserving
  isometry, so the statement has the same content as the corresponding
  statement on classes.
* **Unpointed root.** The GHP limit is unpointed, so the root of the source is
  represented by the point $\rho$ of infinite degree, which is automatically
  unique. The source's remark that the root has degree $1$ when the integral is
  infinite needs a pointed limit and is not stated.

### `supercritical_distance_matrix_limit` — Theorem `thm:sur-critique` (M06), corrected

Let $1/2 < \alpha < 1$ and assume $(\mathsf{Lim}^\alpha_{1/f})$ and
$(\mathsf{Lim}^\alpha_{1/f^2})$. For every $k$, let $V_0$ be the root and
$V_1, \dots, V_k$ conditionally independent uniform vertices of $\mathcal T_n$.
Then

$$
\left(\frac{d^n(V_i, V_j)}{n^{1-\alpha}}\right)_{0 \le i, j \le k}
\longrightarrow
\left(\mathbf 1_{i \ne j}\left(\int_0^{U_i}\frac{dt}{2f(t)} + \int_0^{U_j}\frac{dt}{2f(t)}\right)\right)_{0 \le i, j \le k}
$$

in distribution, where $U_0 = 0$ and $U_1, \dots, U_k$ are independent and
uniform on $[0, 1]$ (`starLimitLaw f k`). The indicator is the zero-diagonal
correction approved by the user: the printed formula gives a positive diagonal,
whereas $d^n(V_i, V_i) = 0$. The source assumes $k \ge 2$; the statement holds
for every $k$.

### `bounded_population_GH_limit` — Theorem `thm:alpha0` (N09)

If $\tau(X^n) > n$ for all $n \ge 1$ and $S^n_k \le M$ for all $k \le n$, then
$\mathcal T_n / h_n^+$ converges in probability to $[0, 1]$ for the
Gromov–Hausdorff distance, where $h_n^+ = \sum_{i=1}^n \mathbf 1_{\{X^n_i = 1\}}/S^n_i$
(`upHarmonicSum`): for every $\varepsilon > 0$,
$\mathbb P\left(d_{\mathrm{GH}}(\mathcal T_n/h_n^+, [0,1]) > \varepsilon\right) \to 0$,
with Mathlib's `GromovHausdorff.ghDist`.

### Not stated

The CRT corollary `cor:CRT` (M05) is excluded; its status is documented in
[FORMALIZATION_REPORT.md](../FORMALIZATION_REPORT.md) and
[coverage-gaps.md](coverage-gaps.md).

## Design choice: fresh interface constants and bridges

Two designs were considered: (a) restate the model as fresh constants and prove
bridge lemmas, or (b) copy the library definitions verbatim under their library
names, as in the companion project's Challenge.

Option (b) is not viable here. Comparator compares every reachable constant,
including the values of theorems nested in definitions, so the copies would have
to elaborate identically in the Challenge, whose imports are Mathlib modules,
and in the library modules, whose imports differ. The library model modules also
import project modules and contain instance proofs (for example the probability
instance of `freezingTreeLaw`), auxiliary structural-recursion declarations and
`open scoped Classical` decision procedures that would all need to coincide. The
library GHP space is a quotient whose metric instance embeds long proofs, and
`IsRealTree`, `degree` and the leaf property are stated there on representatives
of isometry classes through `underlyingGH`. Option (b) would therefore make the
Challenge long and fragile.

Option (a) is used. The interface definitions are small, readable and close to
the source, and they live in one Mathlib-only module that is copied verbatim.
Several of them have the same bodies as the library definitions in another
namespace (the hypotheses, `ghpDistance`, `IsRealTree`, `degree`, the metric
of a scaled graph), so their bridges are definitional (`Iff.rfl`, `rfl`).

## The bridge

* **Model** (`BridgeModel`). `forget` drops the parent, height and freezing-label
  fields of the library state `Freezing1.Forward.State`. It commutes with every
  legal step (a step chooses an active vertex), so the interface tree law is the
  image of the library law: `treeLaw (x n) n = (freezingTreeLaw x n).map forget`.
  On valid states the interface height (maximal graph distance to the root) is
  the library `treeHeight`, using `height_eq_tree_dist` and
  `forward_tree_dist_eq`. The sampled-distance law is the library
  `forwardSampledDistanceLaw`, and `starLimitLaw f k` is the library
  `(iidSourceBranchLimit f k).map sourceStarMatrixMap`, because the branch length
  agrees on $[0,1]$ with the continuous primitive `profilePrimitive (1/f)`.
  `upHarmonicSum` is the companion height scale.
* **GHP** (`BridgeGHP`). `toLib`/`ofLib` copy the fields between interface and
  library spaces, and `ghpClass X` is the library measured-isometry class of
  `X`. The interface GHP distance is literally the library distance of the
  classes (`ghpDist_eq`, by `rfl`). The interface topology equals the topology
  induced by `ghpClass` (`topology_eq`): balls are open for the induced
  pseudometric, and every open set of that pseudometric is a union of balls.
  Hence `ghpClass` is inducing and surjective, thus a quotient map, and every
  bounded continuous function on interface spaces factors through it
  (`exists_factor`); so weak convergence of the library laws gives
  `ConvergesInDistribution` for any interface laws with these images
  (`convergesInDistribution_of_tendsto`). The interface scaled trees and segment
  have the classes of the library `forwardMeasuredSpace` and
  `profileMeasuredSegment` (measure-preserving isometries
  `ghpClass_treeSpace`, `ghpClass_measuredSegment`).
* **Critical limit law.** In the Solution, `T f` is the image of the library
  law `criticalTreeLaw (1/f)` under a measurable section `ghpRep` of
  `ghpClass` (measurable because the interface Borel σ-algebra is the pullback
  of the library one). Its image under `ghpClass` is `criticalTreeLaw (1/f)`,
  which gives the convergence. The almost-sure properties hold for every
  representative of almost every class (`criticalTreeLaw_ae_structure`,
  `critical_tree_properties`, transported along an isometry between a
  representative and the library `underlyingGH` representative), and
  `ae_map_ghpRep` turns this into a `T f`-almost-sure statement.
* **Library results used.** `height_scaling_limit_positive_horizons`,
  `subcritical_scaling_limit`, `critical_scaling_limit_realTree`,
  `critical_tree_properties`, `criticalTreeLaw_ae_structure`,
  `supercritical_distance_matrix_limit` and `bounded_population_GH_limit`; see
  the rows M01–M06 and N09 of [FORMALIZATION_REPORT.md](../FORMALIZATION_REPORT.md).

## Checks

From the project directory:

```sh
python3 scripts/check_challenge.py
lake build Challenge Solution
lake comparator --inadvisably-no-sandbox   # local, unsandboxed (macOS has no bwrap)
```

The unsandboxed local comparison is a preliminary check only. A trustworthy
comparison runs `lake comparator` with its `bwrap` sandbox on Linux, and the
Palomar verification runs its own pipeline on a public commit.

An independent agent that did not write the interface reviewed `Challenge.lean`
against the source (30 October 2026): **PASS with notes**, no required fixes. Its
optional notes are applied: the topology and M03 docstrings now state the
representative-level topology and the unpointed root. The review also checked
that every `Measure.map` in the interface is applied to a measurable or
a.e.-measurable map under the hypotheses (in this Mathlib, `Measure.map` of a
non-measurable map is an arbitrary Dirac mass, so this matters), and that the
point-space fallbacks and the segment clamp are inert under the hypotheses.
