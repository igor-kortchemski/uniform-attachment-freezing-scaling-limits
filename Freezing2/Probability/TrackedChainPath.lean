module

public import Freezing2.Probability.TrackedChainLimit

/-!
# Finitely many observation times of the tracked chain

The probability that the tracked connectivity state lies in prescribed sets at
finitely many observation phases is an explicit vector recursion: starting from
the law of the state at a top phase, multiply by the transition matrix down to
the next observation phase and restrict to the prescribed set. Observation times
are real numbers `τ` placed at phases `φ τ`, and are processed in decreasing
order.

In the critical regime, these discrete recursions converge to the same recursion
with the continuous propagators, for actual tracked labels whose scaled births
converge to distinct limits avoiding the observation times.
-/

@[expose] public section

open MeasureTheory Set Filter Topology

namespace Freezing2.TrackedGenealogy

open Freezing1

variable {k : ℕ}

/-- Restriction of a vector to a set of states. -/
noncomputable def restrictVec (S : Set (Fin k → Fin k → Bool))
    (v : (Fin k → Fin k → Bool) → ℝ) : (Fin k → Fin k → Bool) → ℝ :=
  open Classical in fun s ↦ if s ∈ S then v s else 0

/-- The discrete observation recursion: from the vector `v` at phase `a`, process the
observation times of `T` in decreasing order. -/
noncomputable def discVec (x : SignSequence) (n : ℕ) (u : Fin k → ℕ ⊕ ℕ)
    (S : ℝ → Set (Fin k → Fin k → Bool)) (φ : ℝ → ℕ) :
    ℕ → Finset ℝ → ℕ → ((Fin k → Fin k → Bool) → ℝ) → ((Fin k → Fin k → Bool) → ℝ)
  | 0, _, _, v => v
  | m + 1, T, a, v =>
    if h : T.Nonempty then
      discVec x n u S φ m (T.erase (T.max' h)) (φ (T.max' h))
        (restrictVec (S (T.max' h))
          (Matrix.vecMul v (chainPower x n a u (a - φ (T.max' h)))))
    else v

/-- The continuous observation recursion with the propagators. -/
noncomputable def contVec (g : ℝ → ℝ) (b : Fin k → ℝ) (S : ℝ → Set (Fin k → Fin k → Bool)) :
    ℕ → Finset ℝ → ℝ → ((Fin k → Fin k → Bool) → ℝ) → ((Fin k → Fin k → Bool) → ℝ)
  | 0, _, _, v => v
  | m + 1, T, t, v =>
    if h : T.Nonempty then
      contVec g b S m (T.erase (T.max' h)) (T.max' h)
        (restrictVec (S (T.max' h)) (Matrix.vecMul v (propagator g b (T.max' h) t)))
    else v

variable {x : SignSequence} {n : ℕ} {u : Fin k → ℕ ⊕ ℕ}

/-- **Exact observation law.** Jointly with any event of the past up to phase `a`,
the probability that the tracked state lies in `S τ` at phase `φ τ` for every
`τ ∈ T` is the sum of the discrete observation recursion. -/
theorem jointLaw_observe_eq_discVec (hn : (n : ℕ∞) ≤ extinctionTime x)
    (hu : ∀ j, u j ∈ Freezing1.vertexLabels x n) (hinj : Function.Injective u)
    (S : ℝ → Set (Fin k → Fin k → Bool)) (φ : ℝ → ℕ) :
    ∀ m : ℕ, ∀ T : Finset ℝ, T.card ≤ m → ∀ a : ℕ, a ≤ n → (∀ τ ∈ T, φ τ < a) →
      StrictMonoOn φ T →
      ∀ A : Set ReverseHistory.History,
        MeasurableSet[Filtration.piLE (X := fun _ ↦ Reverse.Forest) (n - a)] A →
        (ReverseHistory.jointLaw x n).real
            (A ∩ {ω | ∀ τ ∈ T, chainState n u (n - φ τ) ω ∈ S τ}) =
          ∑ s, discVec x n u S φ m T a
            (fun s ↦ (ReverseHistory.jointLaw x n).real
              (A ∩ {ω | chainState n u (n - a) ω = s})) s := by
  classical
  intro m
  induction m with
  | zero =>
    intro T hT a ha _ _ A hA
    have hTe : T = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hT)
    subst hTe
    simp only [Finset.notMem_empty, IsEmpty.forall_iff, implies_true, ofPred_true, inter_univ,
      discVec]
    exact measureReal_eq_sum_fiber _ A (chainState n u (n - a)) fun c ↦
      (Filtration.piLE (X := fun _ ↦ Reverse.Forest)).le (n - a) _
        (measurableSet_chainState n u le_rfl c)
  | succ m ih =>
    intro T hT a ha hφa hmono A hA
    by_cases hne : T.Nonempty
    · set τ := T.max' hne with hτ
      have hτT : τ ∈ T := T.max'_mem hne
      have hqa : φ τ < a := hφa τ hτT
      set q := φ τ
      set A' : Set ReverseHistory.History := A ∩ {ω | chainState n u (n - q) ω ∈ S τ}
      have hA' : MeasurableSet[Filtration.piLE (X := fun _ ↦ Reverse.Forest) (n - q)] A' := by
        refine (Filtration.mono _ (by omega) _ hA).inter ?_
        exact ReverseHistory.measurable_eval_piLE le_rfl
          (show MeasurableSet {G : Reverse.Forest | trackedState n (n - (n - q)) u G ∈ S τ}
            from trivial)
      have hφq : ∀ τ' ∈ T.erase τ, φ τ' < q := by
        intro τ' hτ'
        obtain ⟨hne', hτ'T⟩ := Finset.mem_erase.mp hτ'
        exact hmono hτ'T hτT (lt_of_le_of_ne (T.le_max' τ' hτ'T) hne')
      have hev : A ∩ {ω | ∀ τ' ∈ T, chainState n u (n - φ τ') ω ∈ S τ'} =
          A' ∩ {ω | ∀ τ' ∈ T.erase τ, chainState n u (n - φ τ') ω ∈ S τ'} := by
        ext ω
        simp only [A', mem_inter_iff, mem_ofPred_eq, Finset.mem_erase]
        constructor
        · rintro ⟨hA, h⟩
          exact ⟨⟨hA, h τ hτT⟩, fun τ' hτ' ↦ h τ' hτ'.2⟩
        · rintro ⟨⟨hA, hτω⟩, h⟩
          refine ⟨hA, fun τ' hτ' ↦ ?_⟩
          by_cases he : τ' = τ
          · subst he
            exact hτω
          · exact h τ' ⟨he, hτ'⟩
      rw [hev, ih (T.erase τ) (by rw [Finset.card_erase_of_mem hτT]; omega) q (by omega) hφq
        (hmono.mono (Finset.erase_subset τ T)) A' hA']
      have hw : (fun s ↦ (ReverseHistory.jointLaw x n).real
          (A' ∩ {ω | chainState n u (n - q) ω = s})) =
          restrictVec (S τ) (Matrix.vecMul (fun s ↦ (ReverseHistory.jointLaw x n).real
            (A ∩ {ω | chainState n u (n - a) ω = s})) (chainPower x n a u (a - q))) := by
        funext s
        by_cases hs : s ∈ S τ
        · simp only [restrictVec, hs, ↓reduceIte, Matrix.vecMul, dotProduct]
          have hpow := jointLaw_chainState_power hn hu hinj ha hA (a - q) (by omega) s
          rw [show a - (a - q) = q by omega] at hpow
          rw [← hpow]
          congr 1
          ext ω
          simp only [A', mem_inter_iff, mem_ofPred_eq]
          constructor
          · rintro ⟨⟨hA, _⟩, h⟩
            exact ⟨hA, h⟩
          · rintro ⟨hA, h⟩
            exact ⟨⟨hA, h ▸ hs⟩, h⟩
        · simp only [restrictVec, hs, ↓reduceIte]
          have : A' ∩ {ω | chainState n u (n - q) ω = s} = ∅ := by
            ext ω
            simp only [A', mem_inter_iff, mem_ofPred_eq, mem_empty_iff_false, iff_false,
              not_and]
            intro h1 h2
            exact hs (h2 ▸ h1.2)
          rw [this, measureReal_empty]
      rw [hw, discVec, dite_eq_left_of_eq_true (eq_true hne)]
    · have hTe : T = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
      subst hTe
      simp only [Finset.notMem_empty, IsEmpty.forall_iff, implies_true, ofPred_true, inter_univ,
        discVec, Finset.not_nonempty_empty, ↓reduceDIte]
      exact measureReal_eq_sum_fiber _ A (chainState n u (n - a)) fun c ↦
        (Filtration.piLE (X := fun _ ↦ Reverse.Forest)).le (n - a) _
          (measurableSet_chainState n u le_rfl c)

theorem tendsto_restrictVec {ι : Type*} {l : Filter ι} (S : Set (Fin k → Fin k → Bool))
    {v : ι → (Fin k → Fin k → Bool) → ℝ} {w : (Fin k → Fin k → Bool) → ℝ}
    (hv : Tendsto v l (𝓝 w)) : Tendsto (fun i ↦ restrictVec S (v i)) l (𝓝 (restrictVec S w)) := by
  classical
  rw [tendsto_pi_nhds] at hv ⊢
  intro s
  by_cases hs : s ∈ S
  · simpa [restrictVec, hs] using hv s
  · simpa [restrictVec, hs] using tendsto_const_nhds

/-- **Convergence of the observation recursions.** -/
theorem tendsto_discVec_contVec {xa : ℕ → ℕ → ℤ} {g : ℝ → ℝ}
    (hx : AdmissibleArray xa) (hL1 : HasL1ReciprocalProfile xa (1 / 2) g)
    (hpos : PositiveProfile g) (h2 : HasLocalSquareMomentProfile xa (1 / 2) g)
    {u : ℕ → Fin k → ℕ ⊕ ℕ} {b : Fin k → ℝ} (hb : Function.Injective b)
    (hB : ∀ j, Tendsto (fun n ↦ (Freezing1.birthTime n (u n j) : ℝ) / n) atTop (𝓝 (b j)))
    (S : ℝ → Set (Fin k → Fin k → Bool)) {φ : ℕ → ℝ → ℕ} :
    ∀ m : ℕ, ∀ T : Finset ℝ, T.card ≤ m →
      (∀ τ ∈ T, 0 < τ ∧ (∀ j, b j ≠ τ) ∧ Tendsto (fun n ↦ (φ n τ : ℝ) / n) atTop (𝓝 τ)) →
      ∀ t : ℝ, t < 1 → (∀ τ ∈ T, τ < t) →
      ∀ a : ℕ → ℕ, Tendsto (fun n ↦ (a n : ℝ) / n) atTop (𝓝 t) →
      (∀ j, ∀ᶠ n in atTop, (a n ≤ Freezing1.birthTime n (u n j) ↔ t ≤ b j)) →
      ∀ v : ℕ → (Fin k → Fin k → Bool) → ℝ, ∀ w : (Fin k → Fin k → Bool) → ℝ,
        Tendsto v atTop (𝓝 w) →
        Tendsto (fun n ↦ discVec (companionSchedule (xa n)) n (u n) S (φ n) m T (a n) (v n))
          atTop (𝓝 (contVec g b S m T t w)) := by
  classical
  intro m
  induction m with
  | zero =>
    intro T _ _ t _ _ a _ _ v w hv
    simpa [discVec, contVec] using hv
  | succ m ih =>
    intro T hT hTpos t ht hTt a ha htop v w hv
    by_cases hne : T.Nonempty
    · set τ := T.max' hne with hτ
      have hτT : τ ∈ T := T.max'_mem hne
      have hτpos := hTpos τ hτT
      have hτt := hTt τ hτT
      simp only [discVec, contVec, dite_eq_left_of_eq_true (eq_true hne)]
      have hφτ := hτpos.2.2
      have hprop := tendsto_chainPower_propagator hx hL1 hpos h2 hτpos.1 hτt ht ha hφτ hb
        hτpos.2.1 hB htop
      have hvec := tendsto_restrictVec (S τ)
        (((continuous_fst.matrix_vecMul continuous_snd).tendsto (w, propagator g b τ t)).comp
          (hv.prodMk_nhds hprop))
      apply ih (T.erase τ) (by rw [Finset.card_erase_of_mem hτT]; omega)
        (fun τ' h ↦ hTpos τ' (Finset.mem_of_mem_erase h)) τ (hτt.trans ht)
        (fun τ' h ↦ lt_of_le_of_ne (T.le_max' τ' (Finset.mem_of_mem_erase h))
          (Finset.ne_of_mem_erase h)) (fun n ↦ φ n τ) hφτ _ _ _ hvec
      intro j
      rcases lt_or_gt_of_ne (hτpos.2.1 j) with hlt | hgt
      · filter_upwards [eventually_lt_of_tendsto_div (hB j) hφτ hlt] with n hn
        exact ⟨fun h ↦ absurd (lt_of_le_of_lt h hn) (lt_irrefl _), fun h ↦ absurd h (not_le.mpr hlt)⟩
      · filter_upwards [eventually_lt_of_tendsto_div hφτ (hB j) hgt] with n hn
        exact ⟨fun _ ↦ hgt.le, fun _ ↦ hn.le⟩
    · simp only [discVec, contVec, dite_eq_right_of_eq_false (eq_false hne)]
      exact hv

end Freezing2.TrackedGenealogy
