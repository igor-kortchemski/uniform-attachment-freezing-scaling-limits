module

public import Freezing2.Interface.BridgeGHP
public import Freezing2.MainResults.Height
public import Freezing2.MainResults.Supercritical
public import Freezing2.MainResults.BoundedPopulation
public import Freezing2.Probability.CriticalBranching

/-!
# Statement interface: proofs

This module proves the theorems stated in `Challenge.lean`, with the same
fully qualified names and the same statements, from the library results
through the bridges `Freezing2.Interface.BridgeModel` and
`Freezing2.Interface.BridgeGHP`. The definitions they mention are those of
`Freezing2.Interface.Defs`, of which `Challenge.lean` contains a verbatim copy.
This module is imported by `Solution.lean` and never imports `Challenge`.

| Statement | Source | Library result |
| --- | --- | --- |
| `height_scaling_limit` | `thm:heightalpha` (M01) | `height_scaling_limit_positive_horizons` |
| `subcritical_scaling_limit` | `thm:sous-critique` (M02) | `subcritical_scaling_limit` |
| `critical_scaling_limit` | `thm:critique`, `thm:properties` (M03, M04) | `critical_scaling_limit_realTree`, `critical_tree_properties`, `criticalTreeLaw_ae_structure` |
| `supercritical_distance_matrix_limit` | `thm:sur-critique` (M06, zero diagonal) | `supercritical_distance_matrix_limit` |
| `bounded_population_GH_limit` | `thm:alpha0` (N09) | `bounded_population_GH_limit` |
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped Topology ENNReal BoundedContinuousFunction

open Freezing2 (toMeasuredGHSpace)

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
  refine (Freezing2.height_scaling_limit_positive_horizons hx hα0 hα1 hf hL1 hp).congr' ?_
  refine Eventually.of_forall fun n ↦ ?_
  dsimp only
  rw [Bridge.treeLaw_eq_map_freezingTreeLaw, eLpNorm_map_measure
    measurable_from_top.aestronglyMeasurable Bridge.measurable_forget.aemeasurable]
  apply eLpNorm_congr_ae
  filter_upwards [Freezing2.freezingTreeLaw_valid x n] with s hs
  simp only [Function.comp_apply, Bridge.height_forget hs]

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
  refine Bridge.convergesInDistribution_of_tendsto
    (Eventually.of_forall fun n ↦ Bridge.map_scaledTreeLaw x α n) ?_
    (Freezing2.subcritical_scaling_limit hx hα0 hα hf hL1 h2)
  rw [Measure.map_dirac' Bridge.measurable_ghpClass, Bridge.ghpClass_measuredSegment hf hL1.1]
  rfl

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
  refine ⟨fun f ↦ (Freezing2.criticalTreeLaw (fun t ↦ 1 / f t)).map Bridge.ghpRep, ?_⟩
  intro x f hx hf hL1 h2 hpop
  refine ⟨?_, ?_⟩
  · refine Bridge.convergesInDistribution_of_tendsto
      (P := Freezing2.forwardMeasuredTreeLaw x (1 / 2)) (Eventually.of_forall fun n ↦ ?_) ?_
      (Freezing2.critical_scaling_limit_realTree hx hf hL1 h2 hpop).1
    · rw [show (1 : ℝ) / √(n : ℝ) = 1 / (n : ℝ) ^ (1 - 1 / 2 : ℝ) by
        rw [Real.sqrt_eq_rpow]; norm_num]
      exact Bridge.map_scaledTreeLaw x (1 / 2) n
    · rw [ProbabilityMeasure.toMeasure_map,
        Measure.map_map Bridge.measurable_ghpClass Bridge.measurable_ghpRep,
        Bridge.ghpClass_comp_ghpRep, Measure.map_id]
  · rw [ProbabilityMeasure.toMeasure_map]
    apply Bridge.ae_map_ghpRep
    filter_upwards [Freezing2.critical_tree_properties hx hf hL1 h2 hpop,
      Freezing2.criticalTreeLaw_ae_structure hx hf hL1 h2 hpop] with Z hZ hS
    rintro X rfl
    obtain ⟨-, -, hleaves, hbin, hroot⟩ := hZ
    obtain ⟨hfull, -, hreal, -⟩ := hS (Bridge.toLib X) rfl
    obtain ⟨e⟩ : Nonempty
        ((Freezing2.MeasuredGHSpace.underlyingGH (Bridge.ghpClass X)).Rep ≃ᵢ Bridge.toLib X) := by
      change Nonempty ((Freezing2.MeasuredGHSpace.underlyingGH
        (toMeasuredGHSpace (Bridge.toLib X))).Rep ≃ᵢ Bridge.toLib X)
      rw [Freezing2.MeasuredGHSpace.underlyingGH_toMeasuredGHSpace]
      exact GromovHausdorff.toGHSpace_eq_toGHSpace_iff_isometryEquiv.mp
        (GromovHausdorff.GHSpace.toGHSpace_rep _)
    have hdeg (r : (Freezing2.MeasuredGHSpace.underlyingGH (Bridge.ghpClass X)).Rep) :
        degree (X := X) (e r) = Freezing2.RealTree.degree r :=
      Freezing2.RealTree.degree_isometryEquiv e r
    refine ⟨hfull, hreal, hleaves (Bridge.toLib X) rfl, ?_, fun hfin ↦ ?_⟩
    · rw [← hbin]
      constructor
      · intro h r
        rw [← hdeg r]
        exact h (e r)
      · intro h y
        obtain ⟨r, rfl⟩ := e.surjective y
        rw [hdeg]
        exact h r
    · obtain ⟨ρ, hρ, hother⟩ := hroot hfin
      refine ⟨e ρ, by rw [hdeg, hρ], fun y hy h3 ↦ ?_⟩
      obtain ⟨r, rfl⟩ := e.surjective y
      rw [hdeg] at h3 ⊢
      exact hother r (fun h ↦ hy (by rw [h])) h3

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
  have hlib := Freezing2.supercritical_distance_matrix_limit hx hα hα1 hf hL1 h2 k
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto] at hlib
  intro F
  simp only [Bridge.sampledDistanceLaw_eq, Bridge.starLimitLaw_eq hL1.1]
  exact hlib F

/-- **Theorem `thm:alpha0` (N09).** If `S^n_k ≤ M` for all `k ≤ n`, then
`T_n / h_n^+` converges in probability to `[0, 1]` for the Gromov–Hausdorff
distance. -/
theorem bounded_population_GH_limit {x : ℕ → ℕ → ℤ}
    (hx : ∀ n : ℕ, 0 < n → IsSigned (x n) ∧ SurvivesThrough (x n) n)
    (hM : ∃ M : ℕ, ∀ n k : ℕ, k ≤ n → activeCount (x n) k ≤ M) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n ↦ (treeLaw (x n) n).real
      {s | ε < GromovHausdorff.ghDist (treeSpace (1 / upHarmonicSum (x n) n) s) unitInterval})
      atTop (𝓝 0) := by
  refine (Freezing2.bounded_population_GH_limit hx hM hε).congr' ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  rw [Bridge.treeLaw_eq_map_freezingTreeLaw,
    map_measureReal_apply Bridge.measurable_forget MeasurableSpace.measurableSet_top,
    Bridge.upHarmonicSum_eq (x n) (hx n hn).1 n]
  congr 1
  ext s
  change _ ↔ ε < dist (GromovHausdorff.toGHSpace (Bridge.toLib (treeSpace _ (Bridge.forget s))))
    (GromovHausdorff.toGHSpace unitInterval)
  rw [← Freezing2.MeasuredGHSpace.underlyingGH_toMeasuredGHSpace, ← Bridge.ghpClass,
    Bridge.ghpClass_treeSpace]
  exact Iff.rfl

end FreezingStatements
