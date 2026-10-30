module

public import Freezing2.Probability.OneStepTightness
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Uniform source quantifiers for the corrected one-step tightness lemma

N14 with positive block index. One threshold depends only on the fixed
population constant M, uniformly over horizons, marked counts and vertices.
The original undefined negative-time case i=0 remains a documented defect.
-/

@[expose] public section

open scoped Classical

namespace Freezing2.TrackedClusters

open Freezing1

/-- Exact equivalence of the source cube-root range and natural cube bound. -/
theorem nat_le_cube_root_iff (k n : ℕ) :
    (k : ℝ) ≤ (n : ℝ) ^ (1 / (3 : ℝ)) ↔ k ^ 3 ≤ n := by
  have h := Real.le_rpow_inv_iff_of_pos (Nat.cast_nonneg k) (Nat.cast_nonneg n)
    (by norm_num : (0 : ℝ) < 3)
  simpa only [← one_div, Real.rpow_ofNat, ← Nat.cast_pow, Nat.cast_le] using h

/-- The source one-step estimate for every sufficiently large `k`, uniformly
over `k³ ≤ n`, all positive block indices and all distinct marked samples.
Only survival and the stated square-root population bound are needed. -/
theorem one_step_tightness_uniform_positive_blocks
    {x : ℕ → SignSequence} {M : ℝ} (hM : 0 < M)
    (hx : ∀ n : ℕ, 0 < n → (n : ℕ∞) ≤ extinctionTime (x n))
    (hpop : ∀ n : ℕ, 0 < n → ∀ s ≤ n,
      (Freezing1.activeCount (x n) s : ℝ) ≤ M * Real.sqrt n) :
    ∃ k₀ : ℕ, 1 ≤ k₀ ∧ ∀ k : ℕ, k₀ ≤ k → ∀ n : ℕ,
      (k : ℝ) ≤ (n : ℝ) ^ (1 / (3 : ℝ)) →
      ∀ K : ℕ, 0 < K → ∀ i : ℕ, 1 ≤ i → i * tightnessBlockLength M n k ≤ n →
      ∀ v : Fin (K + 1) → ℕ ⊕ ℕ, Function.Injective v →
      (∀ j, v j ∈ Freezing1.vertexLabels (x n) n) →
      (i + 1) * tightnessBlockLength M n k < Freezing1.birthTime n (v 0) →
      (∀ j : Fin (K + 1), j ≠ 0 →
        i * tightnessBlockLength M n k < Freezing1.birthTime n (v j) ∧
        Freezing1.birthTime n (v j) ≤ (i + 1) * tightnessBlockLength M n k) →
      (Reverse.lawAfter (x n) n (n - (i - 1) * tightnessBlockLength M n k)).real
        {F | Alone F (Finset.univ.image v) (v 0)} ≤
          3 * M * Real.sqrt k / (4 * K) := by
  obtain ⟨k₀, hk₀, hlarge⟩ := exists_tightness_sample_threshold hM
  refine ⟨k₀, hk₀, ?_⟩
  intro k hk n hkn K hK i hi hin v hvinj hv hborn0 hborn
  have hkn := (nat_le_cube_root_iff k n).mp hkn
  have hk1 : 1 ≤ k := hk₀.trans hk
  have hkn' : k ≤ n := (le_self_pow hk1 (by norm_num : (3 : ℕ) ≠ 0)).trans hkn
  have hkn0 := (hlarge k hk).1
  have hn0 := hkn0.trans_le hkn'
  exact one_step_tightness_positive_block (hx n hn0) hkn0 hkn' hK hM
    (hlarge k hk).2 (hpop n hn0) hi hin hvinj hv hborn0 hborn

end Freezing2.TrackedClusters
