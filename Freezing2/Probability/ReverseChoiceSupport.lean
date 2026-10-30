module

public import Freezing2.Probability.ReverseChoiceHistory
public import Mathlib.Algebra.BigOperators.Intervals

/-!
# Full support and source masses of reverse root-choice histories

The exact recorded reverse process is supported on legal choices. Its history
atoms equal the source product of inverse ordered-pair counts, including the
case of extinction at the horizon.
-/

@[expose] public section

open Filter MeasureTheory
open scoped ENNReal Classical BigOperators

namespace Freezing2.ReverseChoiceHistory

theorem choiceLaw_supported (F : Forest) (sign : Bool)
    (htwo : sign = true → 2 ≤ F.forest.roots.card) :
    ∀ᵐ p ∂choiceLaw F sign,
      if sign then p ∈ F.forest.roots.offDiag else p = noChoice := by
  cases sign with
  | false => simp [choiceLaw]
  | true =>
    apply (ae_iff_prob_eq_one (measurable_of_countable _)).mpr
    rw [choiceLaw, ite_eq_left ⟨rfl, htwo rfl⟩,
      Freezing1.uniformRootPair, Measure.uniformOfFinset_apply]
    simp only [ite_true, Set.mem_ofPred_eq]
    have hf : F.forest.roots.offDiag.filter (fun p ↦ p ∈ F.forest.roots.offDiag) =
        F.forest.roots.offDiag := Finset.filter_eq_self.mpr fun _ hp ↦ hp
    rw [hf]
    exact ENNReal.div_self
      (by exact_mod_cast (Freezing1.offDiag_nonempty_of_two_le_card (htwo rfl)).card_pos.ne')
      (ENNReal.natCast_ne_top _)

theorem law_legal (x : Freezing1.SignSequence) (n k : ℕ)
    (hn : (n : ℕ∞) ≤ Freezing1.extinctionTime x) (hk : k ≤ n) :
    ∀ᵐ h ∂law x n k, Legal x n h := by
  induction k with
  | zero => simp [law, Legal]
  | succ k ih =>
    have hklt : k < n := by omega
    have hv : ∀ᵐ h ∂law x n k,
        Freezing1.Reverse.ValidAt x n (n - k) (state x n h).forest := by
      have hv0 := Freezing1.ReverseStamped.lawAfter_forest_valid x n k hn (by omega)
      rw [← map_law_state x n k (by omega)] at hv0
      exact ae_of_ae_map (f := state x n) measurable_from_top.aemeasurable hv0
    apply (ae_iff_prob_eq_one measurable_from_top).mpr
    rw [law, Measure.bind_apply (by trivial) measurable_from_top.aemeasurable]
    calc
      _ = ∫⁻ _h, (1 : ℝ≥0∞) ∂law x n k := by
        apply lintegral_congr_ae
        filter_upwards [law_length x n k, ih (by omega), hv] with h hlen hh hvalid
        apply (ae_iff_prob_eq_one measurable_from_top).mp
        rw [stepLaw, ae_map_iff (measurable_of_countable _).aemeasurable (by trivial)]
        have hphase : n - (h.length + 1) + 1 = n - k := by omega
        have htwo : x (n - (h.length + 1) + 1) = true →
            2 ≤ (state x n h).forest.roots.card := by
          intro hx
          rw [hvalid.roots_card, ← hphase]
          apply Freezing1.two_le_activeCount_toNat_succ_of_attachment _ hx
          exact le_trans (by exact_mod_cast (show n - (h.length + 1) + 1 ≤ n by omega)) hn
        filter_upwards [choiceLaw_supported (state x n h) _ htwo] with p hp
        exact ⟨hh, by omega, hp⟩
      _ = 1 := by simp

/-- The reverse product in chronological order of the reverse algorithm. -/
noncomputable def sourceWeight (x : Freezing1.SignSequence) (n k : ℕ) : ℝ :=
  ∏ j ∈ Finset.range k,
    if x (n - j) then
      ((Freezing1.activeCount x (n - j) : ℝ) *
        ((Freezing1.activeCount x (n - j) : ℝ) - 1))⁻¹ else 1

/-- At the terminal phase, reversing the finite product gives exactly the
source's forward-indexed formula. -/
theorem sourceWeight_top (x : Freezing1.SignSequence) (n : ℕ) :
    sourceWeight x n n = Freezing1.reverseHistoryWeight x n := by
  unfold sourceWeight Freezing1.reverseHistoryWeight
  rw [← Finset.prod_range_reflect (fun j ↦
    if x (j + 1) then
      ((Freezing1.activeCount x (j + 1) : ℝ) *
        ((Freezing1.activeCount x (j + 1) : ℝ) - 1))⁻¹ else 1) n]
  apply Finset.prod_congr rfl
  intro j hj
  have he : n - 1 - j + 1 = n - j := by have := Finset.mem_range.mp hj; omega
  rw [he]

theorem weight_toReal_of_legal (x : Freezing1.SignSequence) (n : ℕ) {h : History}
    (hh : Legal x n h) (hn : (n : ℕ∞) ≤ Freezing1.extinctionTime x) :
    (weight x n h).toReal = sourceWeight x n h.length := by
  induction h with
  | nil => simp [weight, sourceWeight]
  | cons p h ih =>
    have hphase : n - (h.length + 1) + 1 = n - h.length := by have := hh.2.1; omega
    have hv := (state_valid_of_legal x n hh.1 hn).1
    have hnphase : ((n - h.length : ℕ) : ℕ∞) ≤ Freezing1.extinctionTime x :=
      le_trans (by exact_mod_cast Nat.sub_le n h.length) hn
    have hcast : ((Freezing1.activeCount x (n - h.length)).toNat : ℝ) =
        (Freezing1.activeCount x (n - h.length) : ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg (Freezing1.activeCount_nonneg_of_le_extinctionTime hnphase)
    change (_ * weight x n h).toReal = _
    rw [ENNReal.toReal_mul, ih hh.1]
    simp only [sourceWeight, List.length_cons, Finset.prod_range_succ]
    cases hx : x (n - h.length) with
    | false => simp [hphase, hx]
    | true =>
      have hp : p ∈ (state x n h).forest.roots.offDiag := by
        simpa [hphase, hx] using hh.2.2
      have hcard : 1 ≤ (state x n h).forest.roots.card :=
        Nat.succ_le_of_lt (Finset.card_pos.mpr ⟨p.1, (Finset.mem_offDiag.mp hp).1⟩)
      simp only [hphase, hx, ite_true, ENNReal.toReal_inv, ENNReal.toReal_natCast]
      rw [Freezing1.card_offDiag_real _ hcard, hv.roots_card, hcast]
      ring

/-- Actual terminal reverse history atoms have the paper's reverse product,
not merely a formally analogous weight. -/
theorem law_real_singleton_of_legal (x : Freezing1.SignSequence) (n : ℕ) {h : History}
    (hh : Legal x n h) (hn : (n : ℕ∞) ≤ Freezing1.extinctionTime x) :
    (law x n h.length).real {h} = sourceWeight x n h.length := by
  change (law x n h.length {h}).toReal = _
  rw [law_singleton_of_legal x n hh]
  exact weight_toReal_of_legal x n hh hn

theorem law_terminal_real_singleton_of_legal (x : Freezing1.SignSequence) (n : ℕ)
    {h : History} (hh : Legal x n h) (hlen : h.length = n)
    (hn : (n : ℕ∞) ≤ Freezing1.extinctionTime x) :
    (law x n n).real {h} = Freezing1.reverseHistoryWeight x n := by
  have he := law_real_singleton_of_legal x n hh hn
  simpa only [hlen, sourceWeight_top] using he

end Freezing2.ReverseChoiceHistory
