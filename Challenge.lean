module

public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Combinatorics.SimpleGraph.Metric
public import Mathlib.Data.Set.Card
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Constructions.UnitInterval
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.GiryMonad
public import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.Order.Interval.Set.ProjIcc
public import Mathlib.Probability.Distributions.Uniform
public import Mathlib.Probability.UniformOn
public import Mathlib.Topology.ContinuousMap.Bounded.Basic
public import Mathlib.Topology.MetricSpace.GromovHausdorff
public import Mathlib.Topology.MetricSpace.HausdorffDistance
public import Mathlib.Topology.Order.Compact

/-!
# Uniform attachment with freezing: scaling limits — Challenge

Statement interface for Comparator and Palomar. The source is
`attachement-uniforme-2-final.tex` (*Uniform attachment with freezing: Scaling
limits*). This file states its main results:

* `height_scaling_limit`: Theorem `thm:heightalpha` (M01);
* `subcritical_scaling_limit`: Theorem `thm:sous-critique` (M02);
* `critical_scaling_limit`: Theorems `thm:critique` and `thm:properties`
  (M03, M04), in one statement with an existential limit law `T f`;
* `supercritical_distance_matrix_limit`: Theorem `thm:sur-critique` (M06), with
  the zero diagonal of the corrected statement;
* `bounded_population_GH_limit`: Theorem `thm:alpha0` (N09).

The CRT corollary `cor:CRT` (M05) is not stated. The definitions below, up to
the marker `END SHARED DEFINITIONS`, are a verbatim copy of the library module
`Freezing2.Interface.Defs` (checked by `scripts/check_challenge.py`). This file
imports only Mathlib and is imported neither by the library nor by
`Solution.lean`. The theorem proofs are deliberate Challenge holes (`sorry`);
the definitions are complete. See `docs/statement-interface.md` for the
encoding choices.
-/

-- BEGIN SHARED DEFINITIONS (identical in Freezing2/Interface/Defs.lean and Challenge.lean)
@[expose] public section

open MeasureTheory Filter Set
open scoped Topology ENNReal BoundedContinuousFunction

universe u

namespace FreezingStatements

/-! ## The driving array and the source hypotheses -/

/-- A driving sequence `x = (x_i)_{i ≥ 1}` takes values in `{-1, +1}`
(index `0` is unused). -/
def IsSigned (x : ℕ → ℤ) : Prop := ∀ i, 0 < i → x i = 1 ∨ x i = -1

/-- The walk `S_k(x) = 1 + x_1 + ⋯ + x_k`: the number of active vertices after
`k` steps of Algorithm 1. -/
def activeCount (x : ℕ → ℤ) (k : ℕ) : ℤ := 1 + ∑ i ∈ Finset.Ioc 0 k, x i

/-- `τ(x) > n`: the walk `S(x)` is positive at every time `k ≤ n`. -/
def SurvivesThrough (x : ℕ → ℤ) (n : ℕ) : Prop := ∀ k, k ≤ n → 0 < activeCount x k

/-- Lebesgue measure on `[0, 1]`. -/
noncomputable abbrev profileMeasure : Measure ℝ := volume.restrict (Icc 0 1)

/-- The rescaled reciprocal population `t ↦ n^α / S^n_{⌊nt⌋}` of the row `x n`. -/
noncomputable def reciprocalProfile (x : ℕ → ℕ → ℤ) (α : ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  (n : ℝ) ^ α / (activeCount (x n) ⌊(n : ℝ) * t⌋₊ : ℝ)

/-- Hypothesis `(Lim^α_{1/f})` for `g = 1/f`: `g ∈ L¹([0,1])` and the rescaled
reciprocal populations converge to `g` in `L¹([0,1])`. -/
def HasL1ReciprocalProfile (x : ℕ → ℕ → ℤ) (α : ℝ) (g : ℝ → ℝ) : Prop :=
  Integrable g profileMeasure ∧
    Tendsto (fun n ↦ ∫ t, |reciprocalProfile x α n t - g t| ∂profileMeasure)
      atTop (𝓝 0)

/-- Hypothesis `(Lim^α_{1/f²})` for `g = 1/f`, together with the standing
assumption `g ∈ L²_loc((0,1))`: for all `0 < a < b < 1`,
`∫_a^b (n^α / S^n_{nt})² dt → ∫_a^b g²`. -/
def HasLocalSquareMomentProfile (x : ℕ → ℕ → ℤ) (α : ℝ) (g : ℝ → ℝ) : Prop :=
  ∀ a b : ℝ, 0 < a → a < b → b < 1 →
    IntegrableOn (fun t ↦ (g t) ^ 2) (Icc a b) volume ∧
      Tendsto (fun n : ℕ ↦ ∫ t in Icc a b, (reciprocalProfile x α n t) ^ 2)
        atTop (𝓝 (∫ t in Icc a b, (g t) ^ 2))

/-- `max_{1 ≤ k ≤ n} S_k(x)` (negative values are clipped to `0`). -/
def rowMaxPopulation (x : ℕ → ℤ) (n : ℕ) : ℕ :=
  (Finset.Icc 1 n).sup (fun k ↦ (activeCount x k).toNat)

/-- The height scale `h_n^+ = ∑_{i=1}^n 1{x_i = 1} / S_i(x)`. -/
noncomputable def upHarmonicSum (x : ℕ → ℤ) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.Icc 1 n, if x i = 1 then 1 / (activeCount x i : ℝ) else 0

/-- The source's branch length `∫_0^u dt / (2 f(t))`. -/
noncomputable def branchLength (f : ℝ → ℝ) (u : ℝ) : ℝ :=
  ∫ t in Icc 0 u, 1 / (2 * f t)

/-! ## Algorithm 1: uniform attachment with freezing -/

/-- A state of Algorithm 1. Vertices are natural numbers: `0` is the initial
root and the vertex created at time `t` is `t`. `active` is the set of
non-frozen vertices, and `graph` has the edges of the tree (all other natural
numbers are isolated). -/
structure TreeState where
  vertices : Finset ℕ
  active : Finset ℕ
  graph : SimpleGraph ℕ

/-- A single active root and no edge. -/
def initialState : TreeState := ⟨{0}, {0}, ⊥⟩

/-- Step `t` of Algorithm 1 with sign `ε`, applied to the chosen active vertex
`v`: if `ε = 1`, a new active vertex `t` is attached to `v`; otherwise `v` is
frozen. -/
def step (s : TreeState) (t : ℕ) (ε : ℤ) (v : ℕ) : TreeState :=
  if ε = 1 then ⟨insert t s.vertices, insert t s.active, s.graph ⊔ SimpleGraph.edge v t⟩
  else ⟨s.vertices, s.active.erase v, s.graph⟩

instance : MeasurableSpace TreeState := ⊤

/-- The law of step `t`: the vertex `v` is chosen uniformly among the active
vertices. A state without active vertex no longer evolves. -/
noncomputable def transitionLaw (s : TreeState) (t : ℕ) (ε : ℤ) : Measure TreeState :=
  if s.active.Nonempty then (Measure.uniformOfFinset s.active).map (step s t ε)
  else Measure.dirac s

/-- The law of the random tree `T_n(x)` obtained by reading `x_1, …, x_n`. -/
noncomputable def treeLaw (x : ℕ → ℤ) : ℕ → Measure TreeState
  | 0 => Measure.dirac initialState
  | n + 1 => (treeLaw x n).bind fun s ↦ transitionLaw s (n + 1) (x (n + 1))

/-- The tree: the graph restricted to the vertices created so far. -/
def TreeState.tree (s : TreeState) : SimpleGraph {v // v ∈ s.vertices} :=
  s.graph.induce (s.vertices : Set ℕ)

/-- The height: the largest graph distance to the root `0`. The graph has no
edge outside the created vertices, so `s.graph.dist` is the distance in the
tree. -/
noncomputable def height (s : TreeState) : ℕ := s.vertices.sup fun v ↦ s.graph.dist 0 v

/-- The root `V_0 = 0` followed by the vertices `V_1, …, V_k`. -/
def rootedSample {k : ℕ} (v : Fin k → ℕ) : Fin (k + 1) → ℕ := Fin.cases 0 v

/-- The law of the matrix `(d(V_i, V_j) / n^(1-α))_{0 ≤ i, j ≤ k}`, where `d` is
the graph distance of `T_n(x)`, `V_0` is its root and, conditionally on
`T_n(x)`, the vertices `V_1, …, V_k` are independent and uniform. -/
noncomputable def sampledDistanceLaw (x : ℕ → ℤ) (α : ℝ) (n k : ℕ) :
    Measure (Fin (k + 1) → Fin (k + 1) → ℝ) :=
  (treeLaw x n).bind fun s ↦
    (Measure.pi fun _ : Fin k ↦ Measure.uniformOfFinset s.vertices).map fun v i j ↦
      (s.graph.dist (rootedSample v i) (rootedSample v j) : ℝ) / (n : ℝ) ^ (1 - α)

/-- The star limit of the supercritical theorem, with zero diagonal: the law of
`(1{i ≠ j} (∫_0^{U_i} dt/(2f) + ∫_0^{U_j} dt/(2f)))_{0 ≤ i, j ≤ k}`, where
`U_0 = 0` and `U_1, …, U_k` are independent and uniform on `[0, 1]`. -/
noncomputable def starLimitLaw (f : ℝ → ℝ) (k : ℕ) :
    Measure (Fin (k + 1) → Fin (k + 1) → ℝ) :=
  (Measure.pi fun _ : Fin k ↦ profileMeasure).map fun U i j ↦
    if i = j then 0
    else branchLength f ((Fin.cases 0 U : Fin (k + 1) → ℝ) i) +
      branchLength f ((Fin.cases 0 U : Fin (k + 1) → ℝ) j)

/-! ## Compact measured spaces and the Gromov–Hausdorff–Prokhorov topology -/

/-- A nonempty compact metric space equipped with a Borel probability measure. -/
structure CompactMeasuredSpace where
  carrier : Type u
  metric : MetricSpace carrier
  nonempty : Nonempty carrier
  compact : @CompactSpace carrier metric.toUniformSpace.toTopologicalSpace
  measurable : MeasurableSpace carrier
  borel : @BorelSpace carrier metric.toUniformSpace.toTopologicalSpace measurable
  law : @ProbabilityMeasure carrier measurable

namespace CompactMeasuredSpace

instance : CoeSort CompactMeasuredSpace.{u} (Type u) := ⟨carrier⟩
instance (X : CompactMeasuredSpace) : MetricSpace X := X.metric
instance (X : CompactMeasuredSpace) : Nonempty X := X.nonempty
instance (X : CompactMeasuredSpace) : CompactSpace X := X.compact
instance (X : CompactMeasuredSpace) : MeasurableSpace X := X.measurable
instance (X : CompactMeasuredSpace) : BorelSpace X := X.borel

/-- Bundle a space with its probability measure. -/
def of (X : Type u) [MetricSpace X] [Nonempty X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] (μ : ProbabilityMeasure X) :
    CompactMeasuredSpace.{u} where
  carrier := X
  metric := inferInstance
  nonempty := inferInstance
  compact := inferInstance
  measurable := inferInstance
  borel := inferInstance
  law := μ

end CompactMeasuredSpace

section GHP

variable {X Y : Type u} [MetricSpace X] [MeasurableSpace X]
  [MetricSpace Y] [MeasurableSpace Y]

/-- The costs `d_P(i_* μ, j_* ν) + d_H(i(X), j(Y))` of all pairs of isometric
embeddings `i : X → Z`, `j : Y → Z` into a common metric space `Z` (with its
Borel σ-algebra); `d_P` is the Lévy–Prokhorov distance and `d_H` the Hausdorff
distance. -/
def ghpCosts [CompactSpace X] [BorelSpace X] [CompactSpace Y] [BorelSpace Y]
    (μ : Measure X) (ν : Measure Y) : Set ℝ :=
  {r | ∃ Z : Type u, ∃ m : MetricSpace Z,
    letI := m
    letI : TopologicalSpace Z := m.toUniformSpace.toTopologicalSpace
    letI : MeasurableSpace Z := borel Z
    ∃ i : X → Z, ∃ j : Y → Z, Isometry i ∧ Isometry j ∧
      r = levyProkhorovDist (μ.map i) (ν.map j) + Metric.hausdorffDist (range i) (range j)}

/-- The Gromov–Hausdorff–Prokhorov distance: the infimum of these costs. -/
noncomputable def ghpDistance [CompactSpace X] [BorelSpace X] [CompactSpace Y] [BorelSpace Y]
    (μ : Measure X) (ν : Measure Y) : ℝ := sInf (ghpCosts μ ν)

end GHP

/-- The GHP distance between two compact measured spaces. -/
noncomputable def CompactMeasuredSpace.ghpDist (X Y : CompactMeasuredSpace.{u}) : ℝ :=
  ghpDistance (X.law : Measure X) (Y.law : Measure Y)

/-- The GHP topology: the topology generated by the open GHP balls. It lives on
representatives, not on isometry classes: it is the topology of the GHP
pseudometric, it is not Hausdorff, and its Kolmogorov quotient is the space of
measure-preserving isometry classes. Open (hence Borel) sets are unions of
isometry classes, so laws and weak convergence here are those of the classes. -/
instance : TopologicalSpace CompactMeasuredSpace.{u} :=
  TopologicalSpace.generateFrom
    {U | ∃ X r, U = {Y | CompactMeasuredSpace.ghpDist X Y < r}}

/-- The Borel σ-algebra of the GHP topology. -/
noncomputable instance : MeasurableSpace CompactMeasuredSpace.{u} := borel _

/-- Convergence in distribution: the integrals of every bounded continuous real
function converge. -/
def ConvergesInDistribution {Ω : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω]
    (μ : ℕ → Measure Ω) (ν : Measure Ω) : Prop :=
  ∀ F : Ω →ᵇ ℝ, Tendsto (fun n ↦ ∫ ω, F ω ∂μ n) atTop (𝓝 (∫ ω, F ω ∂ν))

/-! ## The trees and the segment as compact measured spaces -/

/-- The vertices of a connected graph, with `c > 0` times the graph distance. -/
@[instance_reducible] noncomputable def scaledGraphMetric {V : Type*} (G : SimpleGraph V) (hG : G.Connected)
    (c : ℝ) (hc : 0 < c) : MetricSpace V where
  dist u v := c * (G.dist u v : ℝ)
  dist_self u := by rw [SimpleGraph.dist_self, Nat.cast_zero, mul_zero]
  dist_comm u v := by rw [SimpleGraph.dist_comm]
  dist_triangle u v w := by
    rw [← mul_add, ← Nat.cast_add]
    exact mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hG.dist_triangle) hc.le
  eq_of_dist_eq_zero h :=
    hG.dist_eq_zero_iff.mp (Nat.cast_eq_zero.mp ((mul_eq_zero.mp h).resolve_left hc.ne'))

/-- The one-point space. -/
noncomputable def pointSpace : CompactMeasuredSpace.{0} :=
  CompactMeasuredSpace.of Unit ⟨Measure.dirac (), inferInstance⟩

open scoped Classical in
/-- The tree of `s` with graph distance multiplied by `c > 0`, equipped with the
uniform probability measure on its vertices. The one-point fallback is used only
if the tree is disconnected or `c ≤ 0`; it never occurs below for the random
trees with positive scaling. -/
noncomputable def treeSpace (c : ℝ) (s : TreeState) : CompactMeasuredSpace.{0} :=
  if h : s.tree.Connected ∧ 0 < c then
    letI := scaledGraphMetric s.tree h.1 c h.2
    letI := h.1.nonempty
    letI : MeasurableSpace {v // v ∈ s.vertices} := borel _
    haveI : BorelSpace {v // v ∈ s.vertices} := ⟨rfl⟩
    CompactMeasuredSpace.of {v // v ∈ s.vertices}
      ⟨ProbabilityTheory.uniformOn Set.univ, inferInstance⟩
  else pointSpace

/-- The law of `c · T_n(x)` as a random compact measured space. -/
noncomputable def scaledTreeLaw (x : ℕ → ℤ) (n : ℕ) (c : ℝ) :
    Measure CompactMeasuredSpace.{0} :=
  (treeLaw x n).map (treeSpace c)

open scoped Classical in
/-- The segment `[0, L]` equipped with the image of the uniform measure on
`[0, 1]` under `φ` (values are clamped into `[0, L]`, which changes nothing when
`φ` maps `[0, 1]` into `[0, L]`). For `L < 0` it is the one-point space. -/
noncomputable def measuredSegment (L : ℝ) (φ : ℝ → ℝ) : CompactMeasuredSpace.{0} :=
  if h : 0 ≤ L then
    haveI : Nonempty (Icc 0 L) := ⟨⟨0, left_mem_Icc.mpr h⟩⟩
    CompactMeasuredSpace.of (Icc 0 L)
      (ProbabilityMeasure.map (⟨volume, inferInstance⟩ : ProbabilityMeasure unitInterval)
        fun t ↦ projIcc 0 L h (φ t))
  else pointSpace

/-! ## Real trees and degrees -/

/-- `γ` parametrizes a geodesic segment from `s` to `t` on `[0, d(s, t)]`. -/
def IsSegment {X : Type*} [MetricSpace X] (s t : X) (γ : ℝ → X) : Prop :=
  γ 0 = s ∧ γ (dist s t) = t ∧
    ∀ a ∈ Icc 0 (dist s t), ∀ b ∈ Icc 0 (dist s t), dist (γ a) (γ b) = |a - b|

/-- A real tree: any two points are joined by a unique geodesic segment, and
every injective path between them has the image of that segment. -/
def IsRealTree (X : Type*) [MetricSpace X] : Prop :=
  ∀ s t : X, (∃ γ, IsSegment s t γ) ∧
    (∀ γ γ', IsSegment s t γ → IsSegment s t γ' → EqOn γ γ' (Icc 0 (dist s t))) ∧
    ∀ γ q : ℝ → X, IsSegment s t γ → ContinuousOn q (Icc 0 1) → InjOn q (Icc 0 1) →
      q 0 = s → q 1 = t → q '' Icc 0 1 = γ '' Icc 0 (dist s t)

/-- The degree of `x`: the number (in `ℕ∞`) of connected components of `X \ {x}`.
Leaves are the points of degree `1`, branch points those of degree at least `3`. -/
noncomputable def degree {X : Type*} [MetricSpace X] (x : X) : ℕ∞ :=
  {C : Set X | ∃ y, y ≠ x ∧ C = connectedComponentIn {x}ᶜ y}.encard

end FreezingStatements
-- END SHARED DEFINITIONS

/-! # Statements

Each statement below is proved in `Solution.lean` (through the library module
`Freezing2.Interface.Statements`). Here the proofs are deliberate Challenge
holes. Throughout, `x n` is the `n`-th row `x^n` of the driving array, `T_n` is
the random tree `T_n(x^n)` with law `treeLaw (x n) n`, and the source function
`f : [0, 1] → ℝ₊` enters only through `1 / f`.
-/

namespace FreezingStatements

open MeasureTheory Filter Set Asymptotics
open scoped Topology ENNReal

/-- **Theorem `thm:heightalpha` (M01).** If `0 < α < 1` and `(Lim^α_{1/f})`
holds, then for every real `p ≥ 1`,
`Height(T_n) / n^(1-α) → ∫_0^1 dt / (2 f(t))` in `L^p`.
The hypothesis `(Lim^α_{1/f²})` of the source is not needed. -/
theorem height_scaling_limit {x : ℕ → ℕ → ℤ} {α : ℝ} {f : ℝ → ℝ}
    (hx : ∀ n : ℕ, 0 < n → IsSigned (x n) ∧ SurvivesThrough (x n) n)
    (hα0 : 0 < α) (hα1 : α < 1)
    (hf : ∀ᵐ t ∂profileMeasure, 0 < f t)
    (hL1 : HasL1ReciprocalProfile x α fun t ↦ 1 / f t)
    {p : ℝ} (hp : 1 ≤ p) :
    Tendsto (fun n : ℕ ↦ eLpNorm
      (fun s : TreeState ↦ (height s : ℝ) / (n : ℝ) ^ (1 - α) - ∫ t in Icc 0 1, 1 / (2 * f t))
      (ENNReal.ofReal p) (treeLaw (x n) n)) atTop (𝓝 0) := by
  sorry

/-- **Theorem `thm:sous-critique` (M02).** If `0 < α < 1/2` and `f` satisfies
`(Lim^α_{1/f})` and `(Lim^α_{1/f²})`, then `T_n / n^(1-α)`, with the uniform
probability on its vertices, converges in distribution for the GHP topology to
the segment `[0, ∫_0^1 dt/(2f)]` equipped with the image of the uniform measure
on `[0, 1]` under `u ↦ ∫_0^u dt/(2f)`. -/
theorem subcritical_scaling_limit {x : ℕ → ℕ → ℤ} {α : ℝ} {f : ℝ → ℝ}
    (hx : ∀ n : ℕ, 0 < n → IsSigned (x n) ∧ SurvivesThrough (x n) n)
    (hα0 : 0 < α) (hα : α < 1 / 2)
    (hf : ∀ᵐ t ∂profileMeasure, 0 < f t)
    (hL1 : HasL1ReciprocalProfile x α fun t ↦ 1 / f t)
    (h2 : HasLocalSquareMomentProfile x α fun t ↦ 1 / f t) :
    ConvergesInDistribution (fun n ↦ scaledTreeLaw (x n) n (1 / (n : ℝ) ^ (1 - α)))
      (Measure.dirac (measuredSegment (branchLength f 1) (branchLength f))) := by
  sorry

/-- **Theorems `thm:critique` and `thm:properties` (M03, M04).** There is a
random compact measured space `𝒯(f)`, whose law `T f` depends only on `f`, such
that, whenever `α = 1/2`, `f` satisfies `(Lim^{1/2}_{1/f})` and
`(Lim^{1/2}_{1/f²})`, and `max_{1 ≤ k ≤ n} S^n_k = O(√n)`:
* `T_n / √n`, with the uniform probability on its vertices, converges in
  distribution to `𝒯(f)` for the GHP topology;
* almost surely, `𝒯(f)` is a real tree whose mass measure has full support and
  gives full measure to the leaves (`thm:properties` (1));
* almost surely, `𝒯(f)` is binary (all degrees at most `3`) if and only if
  `∫_0^{1/2} f⁻² = ∞`; and if `∫_0^{1/2} f⁻² < ∞`, some point has infinite
  degree and every other branch point has degree `3` (`thm:properties` (2)).
The point of infinite degree stands in for the source's root, which is not part
of the unpointed GHP structure; for the same reason the source's remark that
the root has degree `1` when `∫_0^{1/2} f⁻² = ∞` is not stated. -/
theorem critical_scaling_limit :
    ∃ T : (ℝ → ℝ) → ProbabilityMeasure CompactMeasuredSpace.{0},
      ∀ (x : ℕ → ℕ → ℤ) (f : ℝ → ℝ),
        (∀ n : ℕ, 0 < n → IsSigned (x n) ∧ SurvivesThrough (x n) n) →
        (∀ᵐ t ∂profileMeasure, 0 < f t) →
        HasL1ReciprocalProfile x (1 / 2) (fun t ↦ 1 / f t) →
        HasLocalSquareMomentProfile x (1 / 2) (fun t ↦ 1 / f t) →
        (fun n ↦ (rowMaxPopulation (x n) n : ℝ)) =O[atTop] (fun n : ℕ ↦ √(n : ℝ)) →
        ConvergesInDistribution (fun n ↦ scaledTreeLaw (x n) n (1 / √(n : ℝ))) (T f) ∧
          ∀ᵐ (X : CompactMeasuredSpace.{0}) ∂(T f : Measure CompactMeasuredSpace.{0}),
            Measure.IsOpenPosMeasure (X.law : Measure X) ∧ IsRealTree X ∧
              (∀ᵐ y ∂(X.law : Measure X), degree y = 1) ∧
              ((∀ y : X, degree y ≤ 3) ↔
                ∫⁻ t in Ioc 0 (1 / 2), ENNReal.ofReal ((1 / f t) ^ 2) = ⊤) ∧
              (∫⁻ t in Ioc 0 (1 / 2), ENNReal.ofReal ((1 / f t) ^ 2) < ⊤ →
                ∃ ρ : X, degree ρ = ⊤ ∧ ∀ y : X, y ≠ ρ → 3 ≤ degree y → degree y = 3) := by
  sorry

/-- **Theorem `thm:sur-critique` (M06), with the zero diagonal.** If
`1/2 < α < 1` and `f` satisfies `(Lim^α_{1/f})` and `(Lim^α_{1/f²})`, then for
every `k`, the matrix `(d(V_i, V_j) / n^(1-α))_{0 ≤ i, j ≤ k}` of the root
`V_0` and of `k` conditionally independent uniform vertices of `T_n` converges
in distribution to
`(1{i ≠ j} (∫_0^{U_i} dt/(2f) + ∫_0^{U_j} dt/(2f)))_{0 ≤ i, j ≤ k}`, where
`U_0 = 0` and `U_1, …, U_k` are independent uniform variables on `[0, 1]`.
The source prints the same formula without the indicator, which is false on
the diagonal. -/
theorem supercritical_distance_matrix_limit {x : ℕ → ℕ → ℤ} {α : ℝ} {f : ℝ → ℝ}
    (hx : ∀ n : ℕ, 0 < n → IsSigned (x n) ∧ SurvivesThrough (x n) n)
    (hα : 1 / 2 < α) (hα1 : α < 1)
    (hf : ∀ᵐ t ∂profileMeasure, 0 < f t)
    (hL1 : HasL1ReciprocalProfile x α fun t ↦ 1 / f t)
    (h2 : HasLocalSquareMomentProfile x α fun t ↦ 1 / f t) (k : ℕ) :
    ConvergesInDistribution (fun n ↦ sampledDistanceLaw (x n) α n k) (starLimitLaw f k) := by
  sorry

/-- **Theorem `thm:alpha0` (N09).** If `S^n_k ≤ M` for all `k ≤ n`, then
`T_n / h_n^+` converges in probability to `[0, 1]` for the Gromov–Hausdorff
distance. -/
theorem bounded_population_GH_limit {x : ℕ → ℕ → ℤ}
    (hx : ∀ n : ℕ, 0 < n → IsSigned (x n) ∧ SurvivesThrough (x n) n)
    (hM : ∃ M : ℕ, ∀ n k : ℕ, k ≤ n → activeCount (x n) k ≤ M) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n ↦ (treeLaw (x n) n).real
      {s | ε < GromovHausdorff.ghDist (treeSpace (1 / upHarmonicSum (x n) n) s) unitInterval})
      atTop (𝓝 0) := by
  sorry

end FreezingStatements
