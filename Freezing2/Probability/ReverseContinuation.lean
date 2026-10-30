module

public import Freezing2.Probability.TrackedIsolation

/-!
# Actual reverse kernels from an arbitrary initial forest

This continuation law is needed for the conditional block argument U37.
It uses precisely the established reverse transition kernels; the arbitrary
initial forest must satisfy the same actual phase invariants. Past conditioning
is not replaced by an unconditional law or by independence of different blocks.
-/

@[expose] public section

open Filter MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

namespace Freezing2.ReverseContinuation

open Freezing1 Freezing2.TrackedClusters

/-- Start at source phase `s` from a specified forest and apply `j` actual
reverse kernels. After phase zero the state is held fixed. -/
noncomputable def law (x : SignSequence) (s : ℕ) (F : Reverse.Forest) :
    ℕ → Measure Reverse.Forest
  | 0 => Measure.dirac F
  | j + 1 => if j < s then (law x s F j).bind (Reverse.transitionLaw x (s - (j + 1)))
      else law x s F j

instance law_probability (x : SignSequence) (s : ℕ) (F : Reverse.Forest) (j : ℕ) :
    IsProbabilityMeasure (law x s F j) := by
  induction j with
  | zero => change IsProbabilityMeasure (Measure.dirac F); infer_instance
  | succ j ih =>
      simp only [law]
      split_ifs
      · exact isProbabilityMeasure_bind measurable_from_top.aemeasurable
          (Eventually.of_forall fun G ↦ Reverse.transitionLaw_probability x _ G)
      · exact ih

/-- Legal phase invariants propagate from any valid starting forest. -/
theorem law_valid {x : SignSequence} {n s j : ℕ} {F : Reverse.Forest}
    (hn : (n : ℕ∞) ≤ extinctionTime x) (hs : s ≤ n) (hj : j ≤ s)
    (hF : Reverse.ValidAt x n s F) :
    ∀ᵐ G ∂law x s F j, Reverse.ValidAt x n (s - j) G := by
  induction j with
  | zero =>
      simpa only [law, Nat.sub_zero] using
        (ae_dirac_iff (by trivial)).mpr hF
  | succ j ih =>
      have hjs : j < s := by omega
      have hprev := ih (by omega)
      have hphase : s - j = s - (j + 1) + 1 := by omega
      apply (ae_iff_prob_eq_one measurable_from_top).mpr
      rw [law, ite_eq_left hjs, Measure.bind_apply (by trivial)
        measurable_from_top.aemeasurable]
      calc
        _ = ∫⁻ _G, (1 : ℝ≥0∞) ∂law x s F j := by
          apply lintegral_congr_ae
          filter_upwards [hprev] with G hG
          rw [hphase] at hG
          exact (ae_iff_prob_eq_one measurable_from_top).mp
            (Reverse.transitionLaw_valid hn (by omega) hG)
        _ = 1 := by simp

/-- The original marginal law is the special case starting at its actual
initial forest. -/
theorem law_initial (x : SignSequence) (n j : ℕ) :
    law x n (Reverse.initial x n) j = Reverse.lawAfter x n j := by
  induction j with
  | zero => rfl
  | succ j ih => simp only [law, Reverse.lawAfter, ih]

/-- All marked vertices born by the current phase are present under the
actual continuation law. -/
theorem law_tracked_present {x : SignSequence} {n s j : ℕ} {F : Reverse.Forest}
    (hn : (n : ℕ∞) ≤ extinctionTime x) (hs : s ≤ n) (hj : j ≤ s)
    (hF : Reverse.ValidAt x n s F) {A : Finset (ℕ ⊕ ℕ)}
    (hA : A ⊆ Freezing1.vertexLabels x n)
    (hborn : ∀ v ∈ A, s - j ≤ Freezing1.birthTime n v) :
    ∀ᵐ G ∂law x s F j, A ⊆ G.vertices := by
  filter_upwards [law_valid hn hs hj hF] with G hG
  intro v hv
  rw [hG.vertices_eq]
  exact (Reverse.mem_phaseLabels_iff_birthTime ((Nat.sub_le _ _).trans hs) (hA hv)).mpr
    (hborn v hv)

/-- The continuation law evaluates exactly the previously proved backward
isolation value, for arbitrary starting forest and valid time length. -/
theorem integral_isolationValue (x : SignSequence) {s t j : ℕ}
    (hphase : t + j ≤ s) (F : Reverse.Forest) (A : Finset (ℕ ⊕ ℕ)) (v : ℕ ⊕ ℕ) :
    (∫ G, isolationValue x A t (s - (t + j)) G v ∂law x s F j) =
      isolationValue x A t (s - t) F v := by
  induction j with
  | zero =>
      simp only [Nat.add_zero, law]
      exact integral_dirac' _ F measurable_from_top.stronglyMeasurable
  | succ j ih =>
      have hjs : j < s := by omega
      have hj : t + j ≤ s := by omega
      have ht : t + (s - (t + (j + 1))) = s - (j + 1) := by omega
      have he : s - (t + j) = s - (t + (j + 1)) + 1 := by omega
      rw [law, ite_eq_left hjs, integral_bind_bounded x (s - (j + 1))]
      · have hfun : (fun G ↦ ∫ H, isolationValue x A t (s - (t + (j + 1))) H v
            ∂Reverse.transitionLaw x (s - (j + 1)) G) =
            fun G ↦ isolationValue x A t (s - (t + j)) G v := by
          funext G
          rw [he, isolationValue, ht]
        rw [hfun]
        exact ih hj
      · intro G
        rw [abs_of_nonneg (isolationValue_bounds x A t _ G v).1]
        exact (isolationValue_bounds x A t _ G v).2

/-- Terminal isolation probability of the actual continuation, expressed by
the backward kernel value. -/
theorem isolation_probability_eq_value (x : SignSequence) {s t : ℕ} (ht : t ≤ s)
    (F : Reverse.Forest) (A : Finset (ℕ ⊕ ℕ)) (v : ℕ ⊕ ℕ) :
    (law x s F (s - t)).real {G | Alone G A v} = isolationValue x A t (s - t) F v := by
  have h := integral_isolationValue x (s := s) (t := t) (j := s - t)
    (by omega) F A v
  have he : s - (t + (s - t)) = 0 := by omega
  rw [he] at h
  rw [← h]
  change (law x s F (s - t)).real {G | Alone G A v} =
    ∫ G, if Alone G A v then (1 : ℝ) else 0 ∂law x s F (s - t)
  exact (integral_indicator_one (by trivial)).symm

end Freezing2.ReverseContinuation
