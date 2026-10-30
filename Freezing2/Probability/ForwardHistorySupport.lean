module

public import Freezing2.Probability.ForwardHistoryLaw

/-!
# Support of actual forward choice histories

Up to and including extinction, every sampled history consists entirely of
legal active-vertex choices. Together with the exact history mass theorem,
this identifies the full support needed for the forward side of N01.
-/

@[expose] public section

open Filter MeasureTheory
open scoped ENNReal

namespace Freezing2.ForwardHistory

theorem choiceLaw_active {s : Freezing1.Forward.State} (hs : s.active.Nonempty) :
    ∀ᵐ v ∂choiceLaw s, v ∈ s.active := by
  apply (ae_iff_prob_eq_one measurable_from_top).mpr
  rw [choiceLaw, ite_eq_left hs, Measure.uniformOfFinset_apply]
  have hf : s.active.filter (fun v ↦ v ∈ {w | w ∈ s.active}) = s.active :=
    Finset.filter_eq_self.mpr fun _ hv ↦ hv
  simp only [Set.mem_ofPred_eq] at hf ⊢
  rw [hf]
  exact ENNReal.div_self (by exact_mod_cast hs.card_pos.ne') (ENNReal.natCast_ne_top _)

theorem stepLaw_legal (x : Freezing1.SignSequence) {h : History}
    (hh : Legal x h) (hs : (state x h).active.Nonempty) :
    ∀ᵐ h' ∂stepLaw x h, Legal x h' := by
  rw [stepLaw, ae_map_iff (measurable_from_top.aemeasurable) (by trivial)]
  filter_upwards [choiceLaw_active hs] with v hv
  exact ⟨hh, hv⟩

/-- Legal histories have full measure at every source-permitted horizon;
the terminal freezing step at extinction is included. -/
theorem law_legal (x : Freezing1.SignSequence) (n : ℕ)
    (hn : (n : ℕ∞) ≤ Freezing1.extinctionTime x) :
    ∀ᵐ h ∂law x n, Legal x h := by
  induction n with
  | zero => simp [law, Legal]
  | succ n ih =>
    have hnlt : (n : ℕ∞) < Freezing1.extinctionTime x :=
      lt_of_lt_of_le (by exact_mod_cast Nat.lt_succ_self n) hn
    have ha : ∀ᵐ h ∂law x n, (state x h).active.Nonempty := by
      have ha0 := Freezing1.Forward.treeLaw_active_nonempty x n hnlt
      rw [← map_law_state] at ha0
      exact ae_of_ae_map (f := state x) measurable_from_top.aemeasurable ha0
    apply (ae_iff_prob_eq_one measurable_from_top).mpr
    rw [law, Measure.bind_apply (by trivial) measurable_from_top.aemeasurable]
    calc
      _ = ∫⁻ _h, (1 : ℝ≥0∞) ∂law x n := by
        apply lintegral_congr_ae
        filter_upwards [ih hnlt.le, ha] with h hh hactive
        exact (ae_iff_prob_eq_one measurable_from_top).mp (stepLaw_legal x hh hactive)
      _ = 1 := by simp

/-- The exact scalar product is attached to almost every complete history,
not just to an abstract family of admissible choices. -/
theorem law_ae_length_legal_and_mass (x : Freezing1.SignSequence) (n : ℕ)
    (hn : (n : ℕ∞) ≤ Freezing1.extinctionTime x) :
    ∀ᵐ h ∂law x n, h.length = n ∧ Legal x h ∧
      (law x n).real {h} = Freezing1.forwardHistoryWeight x n := by
  filter_upwards [law_length x n, law_legal x n hn] with h hlen hlegal
  refine ⟨hlen, hlegal, ?_⟩
  simpa only [hlen] using law_real_singleton_of_legal x hlegal (by simpa only [hlen] using hn)

end Freezing2.ForwardHistory
