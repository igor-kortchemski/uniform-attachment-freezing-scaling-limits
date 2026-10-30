module

public import Freezing2.Probability.ReverseLegalSteps
public import Freezing2.Probability.ReverseLabelBridge
public import Mathlib.Order.SuccPred.ENat

/-!
# Paper-facing conditional height increments

The original integer schedule and one-based vertex labels are used here.
The finite no-zero-before-horizon condition is proved equivalent to `n ≤ τ`,
so the extinction endpoint is retained. The conditioned observation is the
edge-labelled rooted-forest history, under the explicit canonical relabelling
from `ReverseLabelBridge`.
-/

@[expose] public section

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Freezing2

/-- Exactly the source's `n≤τ`: no zero occurs strictly before the horizon.
The population is allowed to vanish at the horizon itself. -/
theorem companion_le_extinctionTime_iff_no_zero_before (x : ℕ → ℤ) (hx : IsSigned x)
    (n : ℕ) :
    (n : ℕ∞) ≤ Freezing1.extinctionTime (companionSchedule x) ↔
      ∀ k < n, activeCount x k ≠ 0 := by
  cases n with
  | zero => simp
  | succ n =>
    rw [Nat.cast_add, Nat.cast_one, ENat.natCast_add_one_le_iff,
      Freezing1.lt_extinctionTime_iff, Freezing1.positiveThrough_iff_no_zero]
    simp only [companion_activeCount x hx, Nat.lt_succ_iff]

namespace ReverseHistory

/-- The height of the paper's original vertex label in source forest `F_i`. -/
def sourceHeight (n i : ℕ) (v : VertexLabel) (ω : History) : ℕ :=
  (forestAt n i ω).depth (toCompanionLabel v)

/-- The source event uses integer subtraction, with no truncated-subtraction
convention hidden in the statement. -/
def sourceHeightIncrementEvent (n i : ℕ) (v : VertexLabel) : Set History :=
  {ω | (sourceHeight n (i - 1) v ω : ℤ) - (sourceHeight n i v ω : ℤ) = 1}

theorem sourceHeightIncrementEvent_eq {n i : ℕ} (hi : 1 ≤ i) (hin : i ≤ n)
    (v : VertexLabel) :
    sourceHeightIncrementEvent n i v =
      transitionEvent (heightIncrementPair (toCompanionLabel v)) (n - i) := by
  have ht : n - (i - 1) = n - i + 1 := by omega
  ext ω
  simp only [sourceHeightIncrementEvent, sourceHeight, forestAt, transitionEvent,
    heightIncrementPair, Set.mem_ofPred_eq, ht]
  omega

/-- Stored heights are actual graph distances to the component root for every
source vertex which has already appeared in the reverse construction. -/
theorem sourceHeight_eq_graphDistance {x : ℕ → ℤ} (hx : IsSigned x) {n i : ℕ}
    (hzero : ∀ k < n, activeCount x k ≠ 0) {v : VertexLabel}
    (hv : v ∈ vertexLabels x n) (hib : i ≤ birthTime n v) :
    ∀ᵐ ω ∂jointLaw (companionSchedule x) n,
      sourceHeight n i v ω = (forestAt n i ω).graph.dist
        ((forestAt n i ω).root (toCompanionLabel v)) (toCompanionLabel v) := by
  have hn := (companion_le_extinctionTime_iff_no_zero_before x hx n).mpr hzero
  have hvc := toCompanionLabel_mem x hx hv
  have hin : i ≤ n := by
    have hbirth := birthTime_le_horizon hvc
    rw [companion_birthTime] at hbirth
    exact hib.trans hbirth
  filter_upwards [jointLaw_forestAt_valid (companionSchedule x) n hn] with ω hω
  have hF := hω i hin
  have hvF : toCompanionLabel v ∈ (forestAt n i ω).vertices := by
    rw [hF.vertices_eq]
    exact (companion_mem_phaseLabels_iff_birthTime x hx hin hv).mpr hib
  exact (forestAt n i ω).depth_eq_dist hvF

/-- N02 (`lem:accroissementH`) for the paper's signed schedule and original
vertex labels, conditioned on the full edge-labelled forest history. -/
theorem conditional_source_height_increment {x : ℕ → ℤ} (hx : IsSigned x) {n i : ℕ}
    (hzero : ∀ k < n, activeCount x k ≠ 0) (hi : 1 ≤ i) {v : VertexLabel}
    (hv : v ∈ vertexLabels x n) (hib : i ≤ birthTime n v) :
    (jointLaw (companionSchedule x) n)[
      (sourceHeightIncrementEvent n i v).indicator (fun _ ↦ (1 : ℝ)) |
      labelledHistorySigma n (n - i)] =ᵐ[jointLaw (companionSchedule x) n]
      fun _ ↦ if x i = 1 then 1 / (activeCount x i : ℝ) else 0 := by
  have hn := (companion_le_extinctionTime_iff_no_zero_before x hx n).mpr hzero
  have hvc := toCompanionLabel_mem x hx hv
  have hibc : i ≤ Freezing1.birthTime n (toCompanionLabel v) := by
    simpa only [companion_birthTime] using hib
  have hin := hibc.trans (birthTime_le_horizon hvc)
  rw [sourceHeightIncrementEvent_eq hi hin]
  simpa only [incrementIndicator, transitionIndicator, companionSchedule,
    decide_eq_true_eq, companion_activeCount x hx] using
    conditional_height_increment_labelled hn hi hvc hibc

end ReverseHistory
end Freezing2
