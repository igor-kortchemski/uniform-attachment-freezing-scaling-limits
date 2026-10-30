module

public import Freezing2.Probability.SampledMatrixTransport

/-!
# The corrected supercritical sampled-distance limit

This is Introduction Theorem `thm:sur-critique`, with the user-approved zero
diagonal correction S01. The finite matrix uses indices `0, …, k`, the actual
forward tree root at index zero, and conditionally iid uniform vertices at the
other indices. Distances are divided by `n ^ (1 - α)`.

The limit has independent branches with the laws of `∫_[0,U] 1/(2*f)` for
uniform `U` in `[0,1]`; the root branch is zero. Off-diagonal entries are the
sum of the two branch lengths and diagonal entries are zero. Exact transport
through the proved forward/reverse law and finite graph isomorphism identifies
the actual forward sampled law. No equality-of-law assumption is added.
-/

@[expose] public section

open Filter MeasureTheory
open scoped Topology

namespace Freezing2

/-- **M06**, corrected as authorized: the root-inclusive distance matrix of
the actual forward uniform-attachment tree with freezing converges weakly to
the zero-diagonal star matrix. The source only requires admissibility at
positive horizons. The theorem also retains the valid cases `k = 0, 1`. -/
theorem supercritical_distance_matrix_limit
    {x : ℕ → ℕ → ℤ} {α : ℝ} {f : ℝ → ℝ}
    (hx : ∀ n, 0 < n → IsSigned (x n) ∧ SurvivesThrough (x n) n)
    (hαhalf : 1 / 2 < α) (hα1 : α < 1)
    (hf : ∀ᵐ t ∂profileMeasure, 0 < f t)
    (hL1 : HasL1ReciprocalProfile x α (fun t ↦ 1 / f t))
    (h2 : HasLocalSquareMomentProfile x α (fun t ↦ 1 / f t)) (k : ℕ) :
    Tendsto (fun n ↦ TreeSampling.forwardSampledDistanceLaw
      (companionSchedule (x n)) α n k) atTop
      (𝓝 ((iidSourceBranchLimit f k).map sourceStarMatrixMap)) := by
  apply (tendsto_add_atTop_iff_nat 1).mp
  apply (tendsto_sourceSampledDistanceLaw_positive_horizons hx hαhalf hα1 hf hL1 h2 k).congr'
  exact Eventually.of_forall fun n ↦ sourceSampledDistanceLaw_eq_forwardSampledDistanceLaw
    x α (n + 1) k (hx (n + 1) (Nat.zero_lt_succ n)).1
      (hx (n + 1) (Nat.zero_lt_succ n)).2

end Freezing2
