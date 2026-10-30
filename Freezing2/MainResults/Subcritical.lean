module

public import Freezing2.Probability.ForwardGHPTransport
public import Freezing2.Probability.CompanionModel

/-!
# Subcritical convergence for the actual forward measured trees

This proves convergence in probability of the exact ambient-infimum GHP
 distance to the deterministic segment with its specified image measure.
The forward tree is the genuine uniform attachment/freezing law, with the
uniform measure on all vertices. The remaining quotient/topology interface
for the source's distributional formulation is recorded separately.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped Topology

namespace Freezing2

open ReverseHistory

/-- The reverse history and actual forward tree give exactly the same law
for the measured GHP distance to the source segment. -/
theorem map_jointLaw_reverseGHPDistance_eq_forward
    {x : ℕ → ℤ} (hx : IsSigned x) {n : ℕ} (hs : SurvivesThrough x n)
    (hn : 0 < n) {g : ℝ → ℝ} (hg : Integrable g profileMeasure)
    (hpos : PositiveProfile g) (α : ℝ) :
    (jointLaw (companionSchedule x) n).map (reverseGHPDistance g hg hpos α n) =
      (Freezing1.Forward.treeLaw (companionSchedule x) n).map
        (forwardGHPDistance g hg hpos ((n : ℝ) ^ (α - 1))) := by
  have hm : Measurable (forestGHPDistance g hg hpos ((n : ℝ) ^ (α - 1))) :=
    measurable_from_top
  change (jointLaw (companionSchedule x) n).map
    ((forestGHPDistance g hg hpos ((n : ℝ) ^ (α - 1))) ∘ (fun ω : History ↦ ω n)) = _
  rw [← Measure.map_map hm (measurable_pi_apply n), jointLaw_map_eval]
  exact ReverseStamped.map_reverse_treeLaw_forestGHPDistance_eq_forward
    (companionSchedule x) n (companion_before_extinction x hx hs).le hg hpos
    (Real.rpow_pos_of_pos (by exact_mod_cast hn) _)

/-- The actual forward uniformly measured tree approaches the source segment
in the manuscript's summed GHP distance, in probability. -/
theorem subcritical_GHP_distance_limit
    {x : ℕ → ℕ → ℤ} {α : ℝ} {g : ℝ → ℝ}
    (hx : AdmissibleArray x) (hα0 : 0 < α) (hαhalf : α < 1 / 2)
    (hL1 : HasL1ReciprocalProfile x α g) (hpos : PositiveProfile g)
    (h2 : HasLocalSquareMomentProfile x α g) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n ↦ (freezingTreeLaw x n).real
      {s | ε < forwardGHPDistance g hL1.1 hpos ((n : ℝ) ^ (α - 1)) s})
      atTop (𝓝 0) := by
  apply (tendsto_reverseGHPDistance_probability hx hα0 hαhalf hL1 hpos h2 hε).congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hlaw := map_jointLaw_reverseGHPDistance_eq_forward (hx n).1 (hx n).2 hn hL1.1 hpos α
  have he := congrArg (fun μ : Measure ℝ ↦ μ (Ioi ε)) hlaw
  rw [Measure.map_apply (measurable_reverseGHPDistance g hL1.1 hpos α n) measurableSet_Ioi,
    Measure.map_apply (measurable_forwardGHPDistance g hL1.1 hpos _) measurableSet_Ioi] at he
  exact congrArg ENNReal.toReal he

/-- Positive-horizon source assumptions and the exact scale `1/n^(1-α)`.
The target measure is the image of uniform `[0,1]` under
`t ↦ ∫ s in [0,t], 1/(2*f s)`, as proved in `ProfileCoordinateLaw`. -/
theorem subcritical_GHP_distance_limit_positive_horizons
    {x : ℕ → ℕ → ℤ} {α : ℝ} {f : ℝ → ℝ}
    (hx : ∀ n, 0 < n → IsSigned (x n) ∧ SurvivesThrough (x n) n)
    (hα0 : 0 < α) (hαhalf : α < 1 / 2)
    (hf : ∀ᵐ t ∂profileMeasure, 0 < f t)
    (hL1 : HasL1ReciprocalProfile x α (fun t ↦ 1 / f t))
    (h2 : HasLocalSquareMomentProfile x α (fun t ↦ 1 / f t)) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n ↦ (freezingTreeLaw x n).real
      {s | ε < forwardGHPDistance (fun t ↦ 1 / f t) hL1.1 (positiveProfile_reciprocal hf)
        (1 / (n : ℝ) ^ (1 - α)) s}) atTop (𝓝 0) := by
  apply (subcritical_GHP_distance_limit (admissible_initialRowExtension hx)
    hα0 hαhalf (hasL1ReciprocalProfile_initialRowExtension hL1)
    (positiveProfile_reciprocal hf) (hasLocalSquareMomentProfile_initialRowExtension h2) hε).congr'
  filter_upwards [initialRowExtension_eventually_eq x] with n hn
  have hscale : (n : ℝ) ^ (α - 1) = 1 / (n : ℝ) ^ (1 - α) := by
    rw [show α - 1 = -(1 - α) by ring, Real.rpow_neg (Nat.cast_nonneg n), one_div]
  simp only [freezingTreeLaw, hn, hscale]

end Freezing2
