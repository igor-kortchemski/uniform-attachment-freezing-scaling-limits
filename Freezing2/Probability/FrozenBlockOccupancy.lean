module

public import Freezing2.Probability.FiniteOccupancy
public import Freezing2.Probability.FrozenBirthSampling

/-!
# Frozen birth blocks under actual iid vertex sampling

Only frozen vertices enter these blocks, including when the right endpoint
is the terminal horizon. Active vertices remain in the sampling measure.
The source birth convention shifts a freezing step by one; the finite
cardinality bound retains the resulting possible loss of one vertex.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped Classical ENNReal BigOperators

namespace Freezing2

def frozenBirthBlock (x : ℕ → ℤ) (n a b : ℕ) : Finset VertexLabel :=
  (frozenVertexLabels x n).filter (fun v ↦ a < birthTime n v ∧ birthTime n v ≤ b)

theorem frozenBirthBlock_subset (x : ℕ → ℤ) (n a b : ℕ) :
    frozenBirthBlock x n a b ⊆ vertexLabels x n :=
  (Finset.filter_subset _ _).trans (frozenVertexLabels_subset x n)

theorem downSteps_card_le_frozenBirthBlock_card_add_one (x : ℕ → ℤ)
    {n a b : ℕ} (hbn : b ≤ n) :
    (downSteps x a b).card ≤ (frozenBirthBlock x n a b).card + 1 := by
  have hsub : ((downSteps x a b).erase (a + 1)).map Function.Embedding.inl ⊆
      frozenBirthBlock x n a b := by
    intro v hv
    obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hv
    rcases Finset.mem_erase.mp hj with ⟨hne, hj⟩
    rcases Finset.mem_filter.mp hj with ⟨hji, hxj⟩
    rcases Finset.mem_Ioc.mp hji with ⟨haj, hjb⟩
    apply Finset.mem_filter.mpr
    refine ⟨?_, ?_⟩
    · rw [frozenVertexLabels_eq]
      apply Finset.mem_map.mpr
      exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨by omega, hjb.trans hbn⟩, hxj⟩, rfl⟩
    · change a < j - 1 ∧ j - 1 ≤ b
      omega
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_map] at hcard
  by_cases ha : a + 1 ∈ downSteps x a b
  · have he := Finset.card_erase_add_one ha
    omega
  · rw [Finset.erase_eq_of_notMem ha] at hcard
    omega

/-- Exact signed-walk arithmetic, including the birth-index shift. -/
theorem frozenBirthBlock_card_lower_bound (x : ℕ → ℤ) (hx : IsSigned x)
    {n a b : ℕ} (hab : a ≤ b) (hbn : b ≤ n)
    {P : ℝ} (ha0 : 0 ≤ activeCount x a) (hbP : (activeCount x b : ℝ) ≤ P) :
    ((b : ℝ) - a - P) / 2 - 1 ≤ (frozenBirthBlock x n a b).card := by
  have hc : (2 : ℝ) * (downSteps x a b).card =
      (b : ℝ) - a - activeCount x b + activeCount x a := by
    exact_mod_cast twice_downSteps_card x hx hab
  have hd : ((downSteps x a b).card : ℝ) ≤ (frozenBirthBlock x n a b).card + 1 := by
    exact_mod_cast downSteps_card_le_frozenBirthBlock_card_add_one x hbn
  have ha0' : (0 : ℝ) ≤ activeCount x a := by exact_mod_cast ha0
  linarith

/-- Exact total vertex count, retaining the active population. -/
theorem twice_vertexLabels_card (x : ℕ → ℤ) (hx : IsSigned x) {n : ℕ}
    (hs : 0 ≤ activeCount x n) :
    (2 : ℝ) * (vertexLabels x n).card = n + 1 + activeCount x n := by
  rw [vertexLabels_card x hx hs]
  have he : (2 : ℝ) * (upSteps x 0 n).card = n + activeCount x n - 1 := by
    have h := twice_upSteps_card x hx (Nat.zero_le n)
    simp only [Nat.cast_zero, sub_zero, activeCount_zero] at h
    exact_mod_cast h
  push_cast
  linarith

/-- A block sixteen times the scale Mn/√k has sufficient actual sampling
mass. The constants and the one-vertex endpoint loss are explicit. -/
theorem frozenBirthBlock_mean_lower_bound (x : ℕ → ℤ) (hx : IsSigned x)
    {n k a b : ℕ} (hk : 6 ≤ k) (hkn : k ≤ n) (hab : a ≤ b) (hbn : b ≤ n)
    (hS : ∀ i ≤ n, 0 ≤ activeCount x i) {M : ℝ} (hM : 1 ≤ M)
    (hpop : ∀ i ≤ n, (activeCount x i : ℝ) ≤ M * Real.sqrt n)
    (hlength : 16 * M * n / Real.sqrt k ≤ (b : ℝ) - a) :
    6 * (M * Real.sqrt k) ≤
      k * ((frozenBirthBlock x n a b).card : ℝ) / (vertexLabels x n).card := by
  have hkR : (6 : ℝ) ≤ k := by exact_mod_cast hk
  have hknR : (k : ℝ) ≤ n := by exact_mod_cast hkn
  have hk0 : (0 : ℝ) < k := by linarith
  have hs0 : 0 < Real.sqrt (k : ℝ) := Real.sqrt_pos.mpr hk0
  have hsk := Real.sq_sqrt (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
  have hsn := Real.sq_sqrt (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  have hsqrt : Real.sqrt (k : ℝ) ≤ Real.sqrt n := Real.sqrt_le_sqrt hknR
  have hprod : Real.sqrt (n : ℝ) * Real.sqrt k ≤ n := by
    nlinarith [Real.sqrt_nonneg (n : ℝ), Real.sqrt_nonneg (k : ℝ)]
  have hscale : M * Real.sqrt n ≤ M * n / Real.sqrt k := by
    apply (le_div_iff₀ hs0).mpr
    nlinarith
  have htwo : (2 : ℝ) ≤ M * n / Real.sqrt k := by
    apply (le_div_iff₀ hs0).mpr
    have hs2 : (2 : ℝ) ≤ Real.sqrt k := by nlinarith [Real.sqrt_nonneg (k : ℝ)]
    have hmn : (n : ℝ) ≤ M * n := by nlinarith
    nlinarith
  have hc := frozenBirthBlock_card_lower_bound x hx hab hbn (hS a (hab.trans hbn)) (hpop b hbn)
  have hc' : 7 * M * n / Real.sqrt k ≤ (frozenBirthBlock x n a b).card := by
    have he : 16 * M * n / Real.sqrt k = 16 * (M * n / Real.sqrt k) := by ring
    have he7 : 7 * M * n / Real.sqrt k = 7 * (M * n / Real.sqrt k) := by ring
    rw [he] at hlength
    rw [he7]
    linarith
  have hN : (0 : ℝ) < (vertexLabels x n).card := by
    exact_mod_cast (vertexLabels_nonempty x hx (hS n le_rfl)).card_pos
  have hNupper : ((vertexLabels x n).card : ℝ) ≤ n + 1 := by
    have hup : (upSteps x 0 n).card ≤ n := by
      simpa only [upSteps, Nat.card_Ioc, Nat.sub_zero] using
        Finset.card_filter_le (Finset.Ioc 0 n) (fun i ↦ x i = 1)
    rw [vertexLabels_card x hx (hS n le_rfl)]
    exact_mod_cast Nat.add_le_add_right hup 1
  have hN7 : 6 * ((vertexLabels x n).card : ℝ) ≤ 7 * n := by linarith
  have hmul := mul_le_mul_of_nonneg_left hc' hk0.le
  have he : (k : ℝ) * (7 * M * n / Real.sqrt k) = 7 * M * n * Real.sqrt k := by
    calc
      _ = ((k : ℝ) * (7 * M * n)) / Real.sqrt k := by ring
      _ = _ := by
        apply (div_eq_iff hs0.ne').mpr
        calc
          _ = (7 * M * n) * (Real.sqrt k ^ 2) := by rw [hsk]; ring
          _ = _ := by ring
  rw [he] at hmul
  apply (le_div_iff₀ hN).mpr
  have hbase := mul_le_mul_of_nonneg_left hN7 (mul_nonneg (by linarith : 0 ≤ M) hs0.le)
  nlinarith

theorem uniformVertex_frozenBirthBlock_mass (x : ℕ → ℤ) (n a b : ℕ) :
    (uniformVertex x n).real (frozenBirthBlock x n a b : Set VertexLabel) =
      ((frozenBirthBlock x n a b).card : ℝ) / (vertexLabels x n).card := by
  rw [Measure.real, uniformVertex, uniformOfFinset_apply_subfinset _ _
    (frozenBirthBlock_subset x n a b)]
  simp

/-- The actual iid block occupancy has the finite Bernoulli lower-tail bound. -/
theorem frozenBirthBlock_occupancy_lower_tail (x : ℕ → ℤ) (hx : IsSigned x)
    {n : ℕ} (hs : 0 ≤ activeCount x n) (a b k : ℕ)
    {L : ℝ} (hL : 0 < L)
    (hmean : 6 * L ≤ k * ((frozenBirthBlock x n a b).card : ℝ) / (vertexLabels x n).card) :
    (uniformVertexVectorLaw x n k).real
      {v | (sampleOccupancy (frozenBirthBlock x n a b : Set VertexLabel) v : ℝ) ≤ 4 * L} ≤
        Real.exp (-6 * L * bennettFunction (1 / 4)) := by
  have := uniformVertex_isProbabilityMeasure x hx hs
  have hm : 0 < (k : ℝ) * (uniformVertex x n).real
      (frozenBirthBlock x n a b : Set VertexLabel) := by
    rw [uniformVertex_frozenBirthBlock_mass]
    have hpos : 0 < 6 * L := by positivity
    simpa only [mul_div_assoc] using hpos.trans_le hmean
  have hbound := iid_sampleOccupancy_lower_tail (uniformVertex x n)
    (frozenBirthBlock x n a b).measurableSet k hm
  rw [uniformVertex_frozenBirthBlock_mass, ← mul_div_assoc] at hbound
  have hsub : {v : Fin k → VertexLabel | (sampleOccupancy
      (frozenBirthBlock x n a b : Set VertexLabel) v : ℝ) ≤ 4 * L} ⊆
      {v | (sampleOccupancy (frozenBirthBlock x n a b : Set VertexLabel) v : ℝ) ≤
        (2 / 3 : ℝ) * (k * ((frozenBirthBlock x n a b).card : ℝ) / (vertexLabels x n).card)} := by
    intro v hv
    change (sampleOccupancy (frozenBirthBlock x n a b : Set VertexLabel) v : ℝ) ≤
      (2 / 3 : ℝ) * (k * ((frozenBirthBlock x n a b).card : ℝ) / (vertexLabels x n).card)
    change (sampleOccupancy (frozenBirthBlock x n a b : Set VertexLabel) v : ℝ) ≤ 4 * L at hv
    linarith
  apply (measureReal_mono hsub).trans (hbound.trans ?_)
  apply Real.exp_le_exp.mpr
  have hb := bennettFunction_nonneg (show (0 : ℝ) ≤ 1 / 4 by norm_num)
  nlinarith

/-- Fourfold collisions are restricted to frozen labels; the active birth atom
is retained in the underlying iid measure and never assigned a false bound. -/
theorem uniformVertexVectorLaw_frozen_fourfold_collision_le (x : ℕ → ℤ)
    (hx : IsSigned x) {n : ℕ} (hs : 0 ≤ activeCount x n) (k : ℕ) :
    (uniformVertexVectorLaw x n k).real
      (repeatedSampleValue (frozenVertexLabels x n) k 4) ≤
        (k : ℝ) ^ 4 / (vertexLabels x n).card ^ 3 := by
  have h := pi_uniformOfFinset_repeated_value_le (vertexLabels x n)
    (frozenVertexLabels x n) (vertexLabels_nonempty x hx hs)
      (frozenVertexLabels_subset x n) k 4
  apply h.trans
  have hN : (0 : ℝ) < (vertexLabels x n).card := by
    exact_mod_cast (vertexLabels_nonempty x hx hs).card_pos
  have hF : ((frozenVertexLabels x n).card : ℝ) ≤ (vertexLabels x n).card := by
    exact_mod_cast Finset.card_le_card (frozenVertexLabels_subset x n)
  calc
    (k : ℝ) ^ 4 * (frozenVertexLabels x n).card / (vertexLabels x n).card ^ 4 ≤
        (k : ℝ) ^ 4 * (vertexLabels x n).card / (vertexLabels x n).card ^ 4 := by gcongr
    _ = _ := by field_simp [hN.ne']

/-- The distinct sampled frozen labels in one block. -/
noncomputable def sampledFrozenBirthBlock (x : ℕ → ℤ) (n a b : ℕ)
    {k : ℕ} (v : Fin k → VertexLabel) : Finset VertexLabel :=
  (Finset.univ.filter (fun i ↦ v i ∈ frozenBirthBlock x n a b)).image v

/-- Exact finite uniform bound for all prescribed complete blocks. Both the
occupancy and frozen fourfold-collision errors remain visible. -/
theorem frozenBirthBlock_distinct_occupancy_union_bound (x : ℕ → ℤ) (hx : IsSigned x)
    {n : ℕ} (hs : 0 ≤ activeCount x n) (k J d : ℕ)
    {L : ℝ} (hL : 0 < L)
    (hmean : ∀ i < J, 6 * L ≤
      k * ((frozenBirthBlock x n (i * d) ((i + 1) * d)).card : ℝ) / (vertexLabels x n).card) :
    (uniformVertexVectorLaw x n k).real
      {v | ∃ i < J, ((sampledFrozenBirthBlock x n (i * d) ((i + 1) * d) v).card : ℝ) ≤ L} ≤
        J * Real.exp (-6 * L * bennettFunction (1 / 4)) +
          (k : ℝ) ^ 4 / (vertexLabels x n).card ^ 3 := by
  have := uniformVertexVectorLaw_probability x hx (k := k) hs
  have hsub : {v : Fin k → VertexLabel | ∃ i < J,
      ((sampledFrozenBirthBlock x n (i * d) ((i + 1) * d) v).card : ℝ) ≤ L} ⊆
      (⋃ i ∈ Finset.range J, {v | (sampleOccupancy
        (frozenBirthBlock x n (i * d) ((i + 1) * d) : Set VertexLabel) v : ℝ) ≤ 4 * L}) ∪
          repeatedSampleValue (frozenVertexLabels x n) k 4 := by
    intro v hv
    by_cases hrepeat : v ∈ repeatedSampleValue (frozenVertexLabels x n) k 4
    · exact Or.inr hrepeat
    · obtain ⟨i, hi, hvi⟩ := hv
      apply Or.inl
      apply Set.mem_iUnion₂.mpr ⟨i, Finset.mem_range.mpr hi, ?_⟩
      have hlocal : v ∉ repeatedSampleValue (frozenBirthBlock x n (i * d) ((i + 1) * d)) k 4 := by
        rintro ⟨j, a, ha, hj⟩
        exact hrepeat ⟨j, a, (Finset.mem_filter.mp ha).1, hj⟩
      have hcount : (sampleOccupancy
          (frozenBirthBlock x n (i * d) ((i + 1) * d) : Set VertexLabel) v : ℝ) ≤
          3 * (sampledFrozenBirthBlock x n (i * d) ((i + 1) * d) v).card := by
        exact_mod_cast sampleOccupancy_le_three_mul_image_card _ v hlocal
      change (sampleOccupancy
        (frozenBirthBlock x n (i * d) ((i + 1) * d) : Set VertexLabel) v : ℝ) ≤ 4 * L
      linarith
  apply (measureReal_mono hsub).trans
  apply (measureReal_union_le _ _).trans
  apply add_le_add ?_ (uniformVertexVectorLaw_frozen_fourfold_collision_le x hx hs k)
  apply (measureReal_biUnion_finset_le (Finset.range J) _).trans
  calc
    _ ≤ ∑ _i ∈ Finset.range J, Real.exp (-6 * L * bennettFunction (1 / 4)) := by
      apply Finset.sum_le_sum
      intro i hi
      exact frozenBirthBlock_occupancy_lower_tail x hx hs _ _ k hL
        (hmean i (Finset.mem_range.mp hi))
    _ = _ := by simp

end Freezing2
