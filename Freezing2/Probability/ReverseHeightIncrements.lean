module

public import Freezing2.Probability.ReverseConditional

/-!
# Height-increment conditional probabilities in the joint reverse construction

The conditional expectation is taken with respect to the entire exposed forest
history, using its concrete trajectory law. The source index `i` corresponds to
construction time `n-i`. Edge-time labels remain a separate observable bridge.
-/

@[expose] public section

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Freezing2.ReverseHistory

/-- The forest-pair event that a fixed vertex gains one unit of height. -/
def heightIncrementPair (v : ℕ ⊕ ℕ) : Set (Forest × Forest) :=
  {p | p.2.depth v = p.1.depth v + 1}

theorem measurableSet_heightIncrementPair (v : ℕ ⊕ ℕ) :
    MeasurableSet (heightIncrementPair v) := by
  have hd : Measurable (fun F : Forest ↦ F.depth v) := measurable_from_top
  exact measurableSet_eq_fun (hd.comp measurable_snd) ((hd.comp measurable_fst).add_const 1)

/-- The source height-increment indicator at increasing construction time `k`. -/
noncomputable abbrev incrementIndicator (k : ℕ) (v : ℕ ⊕ ℕ) : History → ℝ :=
  transitionIndicator (heightIncrementPair v) k

/-- A deterministic source label is born no later than the terminal horizon. -/
theorem birthTime_le_horizon {x : Freezing1.SignSequence} {n : ℕ} {v : ℕ ⊕ ℕ}
    (hv : v ∈ Freezing1.vertexLabels x n) : Freezing1.birthTime n v ≤ n := by
  cases v with
  | inl j => exact le_rfl
  | inr j =>
    have hj : j < n := (Finset.mem_filter.mp (Finset.inr_mem_disjSum.mp hv)).1
      |> Finset.mem_range.mp
    exact hj.le


/-- The height-increment conditional probability given all exposed rooted
forest states, with exactly the source range `1≤i≤birthTime(v)` and `n≤τ`.
Trajectory prefix time `n-i` contains source forests `F_n,…,F_i`. -/
theorem conditional_height_increment {x : Freezing1.SignSequence} {n i : ℕ}
    (hn : (n : ℕ∞) ≤ Freezing1.extinctionTime x) (hi : 1 ≤ i)
    {v : ℕ ⊕ ℕ} (hv : v ∈ Freezing1.vertexLabels x n)
    (hib : i ≤ Freezing1.birthTime n v) :
    (jointLaw x n)[incrementIndicator (n - i) v |
      Filtration.piLE (X := fun _ ↦ Forest) (n - i)] =ᵐ[jointLaw x n]
      fun _ ↦ if x i then 1 / (Freezing1.activeCount x i : ℝ) else 0 := by
  have hin : i ≤ n := hib.trans (birthTime_le_horizon hv)
  have hk : n - i < n := by omega
  have ht : n - ((n - i) + 1) + 1 = i := by omega
  have ht' : n - ((n - i) + 1) < n := by omega
  filter_upwards [conditional_transition_indicator x n (n - i)
    (measurableSet_heightIncrementPair v), jointLaw_forestAt_valid x n hn] with ω hc hvalid
  rw [hc]
  have hF : Freezing1.Reverse.ValidAt x n
      (n - ((n - i) + 1) + 1) (ω (n - i)) := by
    simpa only [ht, forestAt] using hvalid i hin
  have hvF : v ∈ (ω (n - i)).vertices := by
    rw [hF.vertices_eq, ht]
    exact (Freezing1.Reverse.mem_phaseLabels_iff_birthTime hin hv).mpr hib
  have hprob := Freezing1.Reverse.transitionLaw_height_increment hn ht' hF hvF
  simpa only [stepKernel, Kernel.coe_mk, hk, ite_true, ht, heightIncrementPair,
    Set.mem_ofPred_eq] using hprob

end Freezing2.ReverseHistory
