module

public import Freezing2.Probability.CoalescenceMetric
public import Freezing2.Probability.TrackedRootCorrespondence

/-!
# Birth blocks and the coalescence distance

These deterministic implications are the geometry of the small-birth and
large-birth cases of U37. All source phases are explicitly nonnegative.
They retain the exact factor one half in the coalescence distance.
-/

@[expose] public section

open scoped Classical

namespace Freezing2.ReverseCoalescence

open Freezing1 ReverseHistory TrackedClusters

theorem coalescenceDistance_le_half_birth_sum (n : ℕ) (u v : Label) (ω : History) :
    coalescenceDistance n u v ω ≤
      ((Freezing1.birthTime n u : ℝ) + Freezing1.birthTime n v) / 2 := by
  have h : (0 : ℝ) ≤ coalescenceTime n u v ω := Nat.cast_nonneg _
  unfold coalescenceDistance
  linarith

theorem coalescenceDistance_le_of_connected {n t : ℕ} {u v : Label} {ω : History}
    (hu : t ≤ Freezing1.birthTime n u) (hv : t ≤ Freezing1.birthTime n v)
    (hc : connectedAt n u v t ω) :
    coalescenceDistance n u v ω ≤
      ((Freezing1.birthTime n u : ℝ) + Freezing1.birthTime n v - 2 * t) / 2 := by
  have h := le_coalescenceTime_of_connected (show t ≤ commonBirth n u v from le_min hu hv) hc
  have hr : (t : ℝ) ≤ coalescenceTime n u v ω := by exact_mod_cast h
  unfold coalescenceDistance
  linarith

/-- Small birth times need no stochastic estimate. -/
theorem coalescenceDistance_le_of_small_births {n p d : ℕ} {u v : Label} (ω : History)
    (hp : 1 ≤ p) (hu : Freezing1.birthTime n u ≤ 2 * p * d)
    (hv : Freezing1.birthTime n v ≤ 2 * d) :
    coalescenceDistance n u v ω ≤ 2 * (p : ℝ) * d := by
  have h := coalescenceDistance_le_half_birth_sum n u v ω
  have hur : (Freezing1.birthTime n u : ℝ) ≤ 2 * (p : ℝ) * d := by exact_mod_cast hu
  have hvr : (Freezing1.birthTime n v : ℝ) ≤ 2 * (d : ℝ) := by exact_mod_cast hv
  have hpr : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hdr : (0 : ℝ) ≤ d := Nat.cast_nonneg _
  nlinarith

/-- Meeting one of the recent birth blocks forces a small time distance.
The window condition is written without truncated subtraction. -/
theorem coalescenceDistance_le_of_birth_block_connection
    {n p d i i₀ : ℕ} {u v : Label} {ω : History}
    (hp : 2 ≤ p) (hi : 1 ≤ i) (hwindow : i₀ ≤ i + p + 1)
    (hu : Freezing1.birthTime n u ≤ (i₀ + 1) * d)
    (hv : Freezing1.birthTime n v ≤ (i + 1) * d)
    (htu : (i - 1) * d ≤ Freezing1.birthTime n u)
    (htv : (i - 1) * d ≤ Freezing1.birthTime n v)
    (hc : connectedAt n u v ((i - 1) * d) ω) :
    coalescenceDistance n u v ω ≤ 2 * (p : ℝ) * d := by
  have h := coalescenceDistance_le_of_connected htu htv hc
  have hur : (Freezing1.birthTime n u : ℝ) ≤ ((i₀ : ℝ) + 1) * d := by exact_mod_cast hu
  have hvr : (Freezing1.birthTime n v : ℝ) ≤ ((i : ℝ) + 1) * d := by exact_mod_cast hv
  have hpr : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hwr : (i₀ : ℝ) ≤ (i : ℝ) + p + 1 := by exact_mod_cast hwindow
  have hie : ((i - 1 : ℕ) : ℝ) = (i : ℝ) - 1 := by
    rw [Nat.cast_sub hi, Nat.cast_one]
  have hdr : (0 : ℝ) ≤ d := Nat.cast_nonneg _
  simp only [Nat.cast_mul, hie] at h
  nlinarith [mul_le_mul_of_nonneg_right hwr hdr]

/-- A vertex far from every marked sample must remain isolated from every
eligible recent block. This is an event inclusion, not an independence claim. -/
theorem alone_of_far_from_birth_block {n p d i i₀ : ℕ} {u : Label}
    {A : Finset Label} {ω : History}
    (hp : 2 ≤ p) (hi : 1 ≤ i) (hwindow : i₀ ≤ i + p + 1)
    (hu : Freezing1.birthTime n u ≤ (i₀ + 1) * d)
    (htu : (i - 1) * d ≤ Freezing1.birthTime n u)
    (hA : ∀ v ∈ A, (i - 1) * d ≤ Freezing1.birthTime n v ∧
      Freezing1.birthTime n v ≤ (i + 1) * d)
    (hfar : ∀ v ∈ A, 2 * (p : ℝ) * d < coalescenceDistance n u v ω) :
    Alone (forestAt n ((i - 1) * d) ω) (insert u A) u := by
  intro v hv _ _ hc
  rcases Finset.mem_insert.mp hv with rfl | hv
  · rfl
  · exact False.elim ((not_lt_of_ge (coalescenceDistance_le_of_birth_block_connection
      hp hi hwindow hu (hA v hv).2 htu (hA v hv).1 hc)) (hfar v hv))

end Freezing2.ReverseCoalescence
