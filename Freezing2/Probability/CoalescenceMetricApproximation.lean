module

public import Freezing2.Probability.CoalescenceMetric
public import Freezing2.Probability.DistanceApproximation
public import Freezing2.Analysis.SmallHarmonicIntervals

/-!
# From coalescence-time covering to actual graph covering

Global reciprocal L¹ convergence gives a uniform modulus for inclusive
harmonic intervals, including their endpoint corrections. Small coalescence
metric distance therefore forces small normalized harmonic distance; N07's
actual all-pairs error then transfers this to graph distance. This replaces
the source's false endpoint-free inequality in critical tightness Step 2.
-/

@[expose] public section

open Filter MeasureTheory
open scoped Topology

namespace Freezing2

open ReverseHistory ReverseCoalescence

/-- A uniform coalescence-time modulus controls the literal inclusive harmonic
comparison, retaining its nonzero diagonal and both interval endpoints. -/
theorem eventually_harmonicDistance_small_of_coalescenceDistance
    {x : ℕ → ℕ → ℤ} {α : ℝ} {g : ℝ → ℝ}
    (hx : AdmissibleArray x) (hα : α < 1) (hL1 : HasL1ReciprocalProfile x α g)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ n : ℕ in atTop, ∀ ω : History,
      ∀ u ∈ vertexLabels (x n) n, ∀ v ∈ vertexLabels (x n) n,
        sourceCoalescenceDistance n u v ω ≤ δ * n →
          (n : ℝ) ^ (α - 1) * coalescenceHarmonicDistance (x n) n u v ω < ε := by
  obtain ⟨δ, hδ, hn⟩ := eventually_uniform_short_harmonic_bound hx hα hL1 hε
  refine ⟨δ / 2, half_pos hδ, ?_⟩
  filter_upwards [hn] with n hshort
  intro ω u hu v hv hsmall
  have hcu := sourceCoalescenceTime_le_birth_left n u v ω
  have hcv := sourceCoalescenceTime_le_birth_right n u v ω
  have hcu' : (sourceCoalescenceTime n u v ω : ℝ) ≤ birthTime n u := by exact_mod_cast hcu
  have hcv' : (sourceCoalescenceTime n u v ω : ℝ) ≤ birthTime n v := by exact_mod_cast hcv
  rw [sourceCoalescenceDistance_eq_formula] at hsmall
  have hlu : (birthTime n u : ℝ) - sourceCoalescenceTime n u v ω ≤ δ * n := by linarith
  have hlv : (birthTime n v : ℝ) - sourceCoalescenceTime n u v ω ≤ δ * n := by linarith
  have hU := hshort _ _ hcu (birthTime_le (x n) hu) hlu
  have hV := hshort _ _ hcv (birthTime_le (x n) hv) hlv
  calc
    _ = ((n : ℝ) ^ (α - 1) * inclusiveHarmonic (x n)
        (sourceCoalescenceTime n u v ω) (birthTime n u) +
      (n : ℝ) ^ (α - 1) * inclusiveHarmonic (x n)
        (sourceCoalescenceTime n u v ω) (birthTime n v)) / 2 := by
          unfold coalescenceHarmonicDistance
          ring
    _ < ε := by linarith

/-- Outside the genuine N07 error event, the same modulus controls every
actual graph distance simultaneously. No concentration estimate is assumed. -/
theorem eventually_reverseDistance_small_of_coalescenceDistance
    {x : ℕ → ℕ → ℤ} {α : ℝ} {g : ℝ → ℝ}
    (hx : AdmissibleArray x) (hα : α < 1) (hL1 : HasL1ReciprocalProfile x α g)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ n : ℕ in atTop, ∀ ω : History,
      (n : ℝ) ^ (α - 1) * reverseDistanceErrorMax x n ω ≤ ε / 2 →
      ∀ u ∈ vertexLabels (x n) n, ∀ v ∈ vertexLabels (x n) n,
        sourceCoalescenceDistance n u v ω ≤ δ * n →
          (n : ℝ) ^ (α - 1) * reverseDistance n u v ω < ε := by
  obtain ⟨δ, hδ, hn⟩ := eventually_harmonicDistance_small_of_coalescenceDistance
    hx hα hL1 (half_pos hε)
  refine ⟨δ, hδ, ?_⟩
  filter_upwards [hn] with n hmod
  intro ω herr u hu v hv hsmall
  have hH := hmod ω u hu v hv hsmall
  have he := (abs_le.mp (distance_error_le_reverseDistanceErrorMax x n hu hv ω)).2
  have hc : 0 ≤ (n : ℝ) ^ (α - 1) := Real.rpow_nonneg (Nat.cast_nonneg n) _
  have he' := mul_le_mul_of_nonneg_left he hc
  rw [mul_sub] at he'
  linarith

/-- The deterministic covering implication used by critical tightness. The
sample set is the actual nonempty finite set and every sampled label is legal. -/
theorem eventually_graph_cover_of_coalescence_cover
    {x : ℕ → ℕ → ℤ} {α : ℝ} {g : ℝ → ℝ}
    (hx : AdmissibleArray x) (hα : α < 1) (hL1 : HasL1ReciprocalProfile x α g)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ n : ℕ in atTop, ∀ ω : History,
      (n : ℝ) ^ (α - 1) * reverseDistanceErrorMax x n ω ≤ ε / 2 →
      ∀ B : Finset VertexLabel, ∀ hB : B.Nonempty, B ⊆ vertexLabels (x n) n →
      (∀ u ∈ vertexLabels (x n) n, sourceCoalescenceSetDistance n u B hB ω ≤ δ * n) →
      ∀ u ∈ vertexLabels (x n) n,
        ∃ v ∈ B, (n : ℝ) ^ (α - 1) * reverseDistance n u v ω < ε := by
  obtain ⟨δ, hδ, hn⟩ := eventually_reverseDistance_small_of_coalescenceDistance hx hα hL1 hε
  refine ⟨δ, hδ, ?_⟩
  filter_upwards [hn] with n hmod
  intro ω herr B hB hsub hcover u hu
  obtain ⟨v, hv, he⟩ := sourceCoalescenceSetDistance_attained n u B hB ω
  refine ⟨v, hv, hmod ω herr u hu v (hsub hv) ?_⟩
  rw [← he]
  exact hcover u hu

end Freezing2
