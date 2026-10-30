module

public import Freezing2.Probability.ConditionalIsolationChain
public import Freezing2.Probability.CriticalBlockGeometry
public import Freezing2.Analysis.CriticalBlockSchedule

/-!
# Covering a fixed vertex using occupied birth blocks

This is the fixed-sample estimate in U37. The forest remains random under its
actual joint law. The occupied blocks are deterministic here; their actual iid
sampling probabilities and the final logarithmic radius comparison are separate.
-/

@[expose] public section

open Filter MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

namespace Freezing2.ReverseCoalescence

open Freezing1 ReverseHistory TrackedClusters

theorem probability_far_le_geometric_of_birth_occupancy {x : SignSequence}
    {n k d p : ℕ} (hn : (n : ℕ∞) ≤ extinctionTime x)
    (hk : 0 < k) (hkn : k ≤ n) {M : ℝ} (hM : 0 < M)
    (hlarge : 12 ≤ M * Real.sqrt k)
    (hpop : ∀ i ≤ n, (Freezing1.activeCount x i : ℝ) ≤ M * Real.sqrt n)
    (hd : 0 < d) (hlength : tightnessBlockLength M n k ≤ d) (hp : 2 ≤ p)
    {u : Label} (hu : u ∈ Freezing1.vertexLabels x n)
    {B : Finset Label} (hB0 : B.Nonempty) (hB : B ⊆ Freezing1.vertexLabels x n)
    (hocc : ∀ i < n / d, M * Real.sqrt k <
      ((B.filter (fun v ↦ i * d < Freezing1.birthTime n v ∧
        Freezing1.birthTime n v ≤ (i + 1) * d)).card : ℝ)) :
    (jointLaw x n).real {ω | ∀ v ∈ B,
      2 * (p : ℝ) * d < coalescenceDistance n u v ω} ≤ (3 / 4 : ℝ) ^ ((p - 1) / 2) := by
  have hbu : Freezing1.birthTime n u ≤ n := birthTime_le_horizon hu
  have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hdR : (0 : ℝ) ≤ d := Nat.cast_nonneg _
  by_cases hsmall : Freezing1.birthTime n u ≤ 2 * p * d
  · have hclose (ω : History) : ∃ v ∈ B, coalescenceDistance n u v ω ≤ 2 * (p : ℝ) * d := by
      by_cases hdn : d ≤ n
      · have ho := hocc 0 (Nat.div_pos hdn hd)
        have hpos : 0 < (B.filter (fun v ↦ 0 * d < Freezing1.birthTime n v ∧
            Freezing1.birthTime n v ≤ (0 + 1) * d)).card := by
          exact_mod_cast (show (0 : ℝ) < _ from lt_trans (by linarith) ho)
        obtain ⟨v, hv⟩ := Finset.card_pos.mp hpos
        obtain ⟨hvB, hvborn⟩ := Finset.mem_filter.mp hv
        refine ⟨v, hvB, coalescenceDistance_le_of_small_births ω (by omega) hsmall ?_⟩
        simp only [zero_mul, zero_add, one_mul] at hvborn
        omega
      · obtain ⟨v, hv⟩ := hB0
        refine ⟨v, hv, ?_⟩
        have huR : (Freezing1.birthTime n u : ℝ) ≤ n := by exact_mod_cast hbu
        have hvR : (Freezing1.birthTime n v : ℝ) ≤ n := by
          exact_mod_cast birthTime_le_horizon (hB hv)
        have hnR : (n : ℝ) < d := by exact_mod_cast (show n < d by omega)
        have hh := coalescenceDistance_le_half_birth_sum n u v ω
        nlinarith
    have he : {ω | ∀ v ∈ B, 2 * (p : ℝ) * d < coalescenceDistance n u v ω} =
        (∅ : Set History) := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro ω hω
      obtain ⟨v, hv, hc⟩ := hclose ω
      exact (not_lt_of_ge hc) (hω v hv)
    rw [he, measureReal_empty]
    positivity
  · let i₀ := (Freezing1.birthTime n u - 1) / d
    let m := (p - 1) / 2
    have hbu0 : 0 < Freezing1.birthTime n u := by omega
    have hi₀lo : i₀ * d < Freezing1.birthTime n u :=
      (Nat.div_mul_le_self _ d).trans_lt (Nat.sub_lt hbu0 (by omega))
    have hi₀hi : Freezing1.birthTime n u ≤ (i₀ + 1) * d := by
      have hmod := Nat.mod_add_div (Freezing1.birthTime n u - 1) d
      have hrem := Nat.mod_lt (Freezing1.birthTime n u - 1) hd
      change _ + d * i₀ = _ at hmod
      rw [Nat.mul_comm d i₀] at hmod
      rw [Nat.add_mul, one_mul]
      omega
    have hi₀p : 2 * p ≤ i₀ := by
      apply (Nat.le_div_iff_mul_le hd).mpr
      omega
    have hm : 2 * m ≤ i₀ := by
      have hdiv := Nat.div_mul_le_self (p - 1) 2
      dsimp [m]
      omega
    let s := criticalTrialPhase i₀ d
    let i := criticalTrialBlock i₀
    let C : ℕ → Finset Label := fun j ↦ B.filter (fun v ↦
      i j * d < Freezing1.birthTime n v ∧ Freezing1.birthTime n v ≤ (i j + 1) * d)
    let A : ℕ → Finset Label := fun j ↦ insert u (C j)
    have hs (j : ℕ) : s j ≤ n := (criticalTrialPhase_le i₀ d j).trans (hi₀lo.le.trans hbu)
    have hsEq (j : ℕ) (hj : j < m) : s j = (i j + 1) * d :=
      criticalTrialPhase_eq_block_succ hm hj
    have htEq (j : ℕ) : s (j + 1) = (i j - 1) * d :=
      criticalTrialPhase_succ_eq_block_pred i₀ j d
    have hi (j : ℕ) (hj : j < m) : 1 ≤ i j := criticalTrialBlock_pos hm hj
    have hiN (j : ℕ) (hj : j < m) : i j < n / d := by
      apply Nat.lt_of_succ_le
      apply (Nat.le_div_iff_mul_le hd).mpr
      rw [← hsEq j hj]
      exact hs j
    have huC (j : ℕ) : u ∉ C j := by
      intro huC
      have hb := (Finset.mem_filter.mp huC).2.2
      have hj : i j + 1 ≤ i₀ := by
        by_cases h : j < m
        · have ht := hi j h
          dsimp [i, criticalTrialBlock] at ht ⊢
          omega
        · dsimp [i, criticalTrialBlock]
          have hi₀pos : 0 < i₀ := by omega
          omega
      exact (not_lt_of_ge (hb.trans (Nat.mul_le_mul_right d hj))) hi₀lo
    have hsub (j : ℕ) : A j ⊆ Freezing1.vertexLabels x n := by
      intro v hv
      rcases Finset.mem_insert.mp hv with rfl | hv
      · exact hu
      · exact hB (Finset.mem_filter.mp hv).1
    have hcard (j : ℕ) : (A j).card = (C j).card + 1 := Finset.card_insert_of_notMem (huC j)
    have hr (j : ℕ) (hj : j < m) : i j * d ≤ s j := by
      rw [hsEq j hj]
      exact Nat.mul_le_mul_right d (Nat.le_succ _)
    have ht (j : ℕ) : s (j + 1) ≤ i j * d := by
      rw [htEq j]
      exact Nat.mul_le_mul_right d (Nat.sub_le _ _)
    have huborn (j : ℕ) : s j ≤ Freezing1.birthTime n u :=
      (criticalTrialPhase_le i₀ d j).trans hi₀lo.le
    have hborn (j : ℕ) (hj : j < m) (v : Label) (hv : v ∈ A j) :
        i j * d ≤ Freezing1.birthTime n v := by
      rcases Finset.mem_insert.mp hv with rfl | hv
      · exact (hr j hj).trans (huborn j)
      · exact (Finset.mem_filter.mp hv).2.1.le
    have hyoung (j : ℕ) (hj : j < m) (v : Label) (hv : v ∈ A j) (hvu : v ≠ u) :
        Freezing1.birthTime n v ≤ s j := by
      have hvC := (Finset.mem_insert.mp hv).resolve_left hvu
      rw [hsEq j hj]
      exact (Finset.mem_filter.mp hvC).2.2
    have hchain := oldest_isolation_chain_probability_le hn hk hkn
      (criticalTrialPhase_antitone i₀ d) (fun j _ ↦ hs j) hr (fun j _ ↦ ht j)
      hM hlarge hpop
      (fun j hj ↦ by
        change tightnessBlockLength M n k ≤
          criticalTrialBlock i₀ j * d - criticalTrialPhase i₀ d (j + 1)
        rw [criticalTrialBlock_middle_gap hm hj]
        exact hlength)
      (fun j _ ↦ hsub j) (fun j _ ↦ hcard j)
      (fun j hj ↦ (hocc (i j) (hiN j hj)).le)
      (fun j _ ↦ Finset.mem_insert_self u (C j)) (fun j _ ↦ huborn j) hyoung hborn
    refine (measureReal_mono ?_).trans hchain
    intro ω hfar
    simp only [Set.mem_iInter, Finset.mem_range, Set.mem_ofPred_eq]
    intro j hj
    have hphase := htEq j
    change Alone (forestAt n (s (j + 1)) ω) (A j) u
    rw [hphase]
    apply alone_of_far_from_birth_block hp (hi j hj)
      (criticalTrialBlock_in_window hj) hi₀hi ((ht j).trans (hr j hj) |>.trans (huborn j))
    · intro v hv
      have hb := (Finset.mem_filter.mp hv).2
      exact ⟨(Nat.mul_le_mul_right d (Nat.sub_le _ _)).trans hb.1.le, hb.2⟩
    · intro v hv
      exact hfar v (Finset.mem_filter.mp hv).1

end Freezing2.ReverseCoalescence
