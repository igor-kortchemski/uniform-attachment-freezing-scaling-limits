module

public import Freezing2.Probability.FrozenBlockOccupancy
public import Freezing2.Analysis.CriticalOccupancyRate

/-!
# Uniform occupancy of repaired critical birth blocks

For U36 we use block length `16 ceil(M n / sqrt k)`, repairing the printed
factor-four concentration mismatch. The underlying samples remain iid uniform
vertices of the full tree. Only frozen labels enter the occupancy and collision
events. The error is uniform over horizons `k³ ≤ n` and is o(k⁻⁴).
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped Topology Classical

namespace Freezing2

noncomputable def criticalSamplingBlockLength (M : ℝ) (n k : ℕ) : ℕ :=
  16 * ⌈M * n / Real.sqrt k⌉₊

noncomputable def criticalFrozenOccupancyFailure (x : ℕ → ℤ) (M : ℝ)
    (n k : ℕ) : Set (Fin k → VertexLabel) :=
  {v | ∃ i < n / criticalSamplingBlockLength M n k,
    ((sampledFrozenBirthBlock x n (i * criticalSamplingBlockLength M n k)
      ((i + 1) * criticalSamplingBlockLength M n k) v).card : ℝ) ≤ M * Real.sqrt k}

/-- The source set of distinct sampled birth times, with repetitions removed. -/
noncomputable def sampledBirthBlock (n a b : ℕ) {k : ℕ}
    (v : Fin k → VertexLabel) : Finset ℕ :=
  (Finset.univ.filter (fun i ↦ a < birthTime n (v i) ∧ birthTime n (v i) ≤ b)).image
    (fun i ↦ birthTime n (v i))

theorem sampledFrozenBirthBlock_card_le_birthBlock_card (x : ℕ → ℤ)
    (n a b : ℕ) {k : ℕ} (v : Fin k → VertexLabel) :
    (sampledFrozenBirthBlock x n a b v).card ≤ (sampledBirthBlock n a b v).card := by
  have hsub : sampledFrozenBirthBlock x n a b v ⊆ frozenVertexLabels x n := by
    intro w hw
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hw
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hi).2).1
  have hinj : Set.InjOn (birthTime n) (sampledFrozenBirthBlock x n a b v : Set VertexLabel) :=
    (birthTime_injOn_frozenVertexLabels x n).mono hsub
  rw [← Finset.card_image_of_injOn hinj]
  apply Finset.card_le_card
  intro t ht
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp ht
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hw
  apply Finset.mem_image.mpr
  exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
    (Finset.mem_filter.mp (Finset.mem_filter.mp hi).2).2⟩, rfl⟩

/-- The manuscript's occupancy failure event, for the repaired block length. -/
noncomputable def criticalBirthOccupancyFailure (M : ℝ) (n k : ℕ) : Set (Fin k → VertexLabel) :=
  {v | ∃ i < n / criticalSamplingBlockLength M n k,
    ((sampledBirthBlock n (i * criticalSamplingBlockLength M n k)
      ((i + 1) * criticalSamplingBlockLength M n k) v).card : ℝ) ≤ M * Real.sqrt k}

theorem criticalBirthOccupancyFailure_subset (x : ℕ → ℤ) (M : ℝ) (n k : ℕ) :
    criticalBirthOccupancyFailure M n k ⊆ criticalFrozenOccupancyFailure x M n k := by
  rintro v ⟨i, hi, hv⟩
  refine ⟨i, hi, ?_⟩
  exact (Nat.cast_le.mpr (sampledFrozenBirthBlock_card_le_birthBlock_card x n _ _ v)).trans hv

theorem criticalSamplingBlockLength_lower_bound (M : ℝ) (n k : ℕ) :
    16 * M * n / Real.sqrt k ≤ (criticalSamplingBlockLength M n k : ℝ) := by
  have h := mul_le_mul_of_nonneg_left (Nat.le_ceil (M * n / Real.sqrt k))
    (by norm_num : (0 : ℝ) ≤ 16)
  simpa only [criticalSamplingBlockLength, Nat.cast_mul, Nat.cast_ofNat, mul_div_assoc,
    mul_assoc] using h

theorem criticalFrozenOccupancyFailure_probability_le (x : ℕ → ℤ) (hx : IsSigned x)
    {n k : ℕ} (hk : 6 ≤ k) (hkn : k ^ 3 ≤ n)
    (hS : ∀ i ≤ n, 0 ≤ activeCount x i) {M : ℝ} (hM : 1 ≤ M)
    (hpop : ∀ i ≤ n, (activeCount x i : ℝ) ≤ M * Real.sqrt n) :
    (uniformVertexVectorLaw x n k).real (criticalFrozenOccupancyFailure x M n k) ≤
      criticalOccupancyError M k := by
  have hk0 : 0 < k := by omega
  have hkn' : k ≤ n := (le_self_pow (show 1 ≤ k by omega) (by norm_num : (3 : ℕ) ≠ 0)).trans hkn
  have hn0 : 0 < n := hk0.trans_le hkn'
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk0
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  have hM0 : 0 < M := by linarith
  have hsqrt : 0 < Real.sqrt (k : ℝ) := Real.sqrt_pos.mpr hkR
  let d := criticalSamplingBlockLength M n k
  have hd : 16 * M * n / Real.sqrt k ≤ (d : ℝ) := criticalSamplingBlockLength_lower_bound M n k
  have hdpos : 0 < d := by
    have : (0 : ℝ) < d := (by positivity : 0 < 16 * M * n / Real.sqrt k).trans_le hd
    exact_mod_cast this
  have hblock (i : ℕ) (hi : i < n / d) : (i + 1) * d ≤ n :=
    (Nat.mul_le_mul_right d (Nat.succ_le_of_lt hi)).trans (Nat.div_mul_le_self n d)
  have hmean (i : ℕ) (hi : i < n / d) : 6 * (M * Real.sqrt k) ≤
      k * ((frozenBirthBlock x n (i * d) ((i + 1) * d)).card : ℝ) / (vertexLabels x n).card := by
    apply frozenBirthBlock_mean_lower_bound x hx hk hkn'
      (Nat.mul_le_mul_right d (Nat.le_succ i)) (hblock i hi) hS hM hpop
    push_cast
    nlinarith [hd]
  have hfinite := frozenBirthBlock_distinct_occupancy_union_bound x hx (hS n le_rfl)
    k (n / d) d (mul_pos hM0 hsqrt) hmean
  have hJ : ((n / d : ℕ) : ℝ) ≤ Real.sqrt k / (16 * M) := by
    have hJd : (((n / d : ℕ) : ℝ)) * d ≤ n := by
      exact_mod_cast Nat.div_mul_le_self n d
    have hJ0 : (0 : ℝ) ≤ (n / d : ℕ) := Nat.cast_nonneg _
    have hj := (mul_le_mul_of_nonneg_left hd hJ0).trans hJd
    have hj' := mul_le_mul_of_nonneg_right hj hsqrt.le
    have he : (((n / d : ℕ) : ℝ) * (16 * M * n / Real.sqrt k)) * Real.sqrt k =
        (((n / d : ℕ) : ℝ) * (16 * M)) * n := by field_simp [hsqrt.ne']
    rw [he] at hj'
    apply (le_div_iff₀ (by positivity : 0 < 16 * M)).mpr
    nlinarith
  have hcard : (n : ℝ) / 2 ≤ (vertexLabels x n).card := by
    have he := twice_vertexLabels_card x hx (hS n le_rfl)
    have hsR : (0 : ℝ) ≤ activeCount x n := by exact_mod_cast hS n le_rfl
    linarith
  have hcollision : (k : ℝ) ^ 4 / (vertexLabels x n).card ^ 3 ≤ 8 / (k : ℝ) ^ 5 := by
    have hk3 : (k : ℝ) ^ 3 ≤ n := by exact_mod_cast hkn
    calc
      _ ≤ (k : ℝ) ^ 4 / ((n : ℝ) / 2) ^ 3 := by gcongr
      _ = 8 * (k : ℝ) ^ 4 / (n : ℝ) ^ 3 := by field_simp [hnR.ne']; ring
      _ ≤ 8 * (k : ℝ) ^ 4 / ((k : ℝ) ^ 3) ^ 3 := by gcongr
      _ = _ := by field_simp [hkR.ne']
  apply hfinite.trans
  unfold criticalOccupancyError
  apply add_le_add ?_ hcollision
  have h := mul_le_mul_of_nonneg_right hJ
    (Real.exp_pos (-6 * (M * Real.sqrt k) * bennettFunction (1 / 4))).le
  simpa only [mul_assoc] using h

/-- Explicit uniform form of the repaired U36 little-o estimate. The sample
cutoff is chosen before both the horizon and the admissible signed row. -/
theorem eventually_uniform_criticalFrozenOccupancyFailure_scaled_lt
    {M : ℝ} (hM : 1 ≤ M) {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℕ, ∀ k ≥ K, ∀ n, k ^ 3 ≤ n → ∀ x : ℕ → ℤ,
      IsSigned x → (∀ i ≤ n, 0 ≤ activeCount x i) →
      (∀ i ≤ n, (activeCount x i : ℝ) ≤ M * Real.sqrt n) →
      (k : ℝ) ^ 4 * (uniformVertexVectorLaw x n k).real
        (criticalFrozenOccupancyFailure x M n k) < ε := by
  have hlim := tendsto_scaled_criticalOccupancyError (show 0 < M by linarith)
  obtain ⟨K, hK⟩ := Filter.eventually_atTop.mp (hlim.eventually_lt_const hε)
  refine ⟨max 6 K, ?_⟩
  intro k hk n hn x hx hS hpop
  have hbound := criticalFrozenOccupancyFailure_probability_le x hx
    ((le_max_left 6 K).trans hk) hn hS hM hpop
  exact (mul_le_mul_of_nonneg_left hbound (by positivity)).trans_lt
    (hK k ((le_max_right 6 K).trans hk))

/-- The same uniform o(k⁻⁴) statement for the exact source birth-set event.
Active labels are retained; using only frozen births gives a stronger good event. -/
theorem eventually_uniform_criticalBirthOccupancyFailure_scaled_lt
    {M : ℝ} (hM : 1 ≤ M) {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℕ, ∀ k ≥ K, ∀ n, k ^ 3 ≤ n → ∀ x : ℕ → ℤ,
      IsSigned x → (∀ i ≤ n, 0 ≤ activeCount x i) →
      (∀ i ≤ n, (activeCount x i : ℝ) ≤ M * Real.sqrt n) →
      (k : ℝ) ^ 4 * (uniformVertexVectorLaw x n k).real
        (criticalBirthOccupancyFailure M n k) < ε := by
  obtain ⟨K, hK⟩ := eventually_uniform_criticalFrozenOccupancyFailure_scaled_lt hM hε
  refine ⟨K, ?_⟩
  intro k hk n hn x hx hS hpop
  have := uniformVertexVectorLaw_probability x hx (k := k) (hS n le_rfl)
  exact (mul_le_mul_of_nonneg_left
    (measureReal_mono (criticalBirthOccupancyFailure_subset x M n k)) (by positivity)).trans_lt
      (hK k hk n hn x hx hS hpop)

end Freezing2
