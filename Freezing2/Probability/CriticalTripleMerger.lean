module

public import Freezing2.Probability.CriticalMergeAtoms

/-!
# No triple mergers in the critical limit

In the limiting genealogy of `k` uniform vertices, three distinct samples almost surely
do not share a common positive pairwise coalescence time.

The discrete argument runs the tracked connectivity chain of three labels. Each step
changes the state with probability at most the coalescence hazard of that step, and a
single merger of a symmetric transitive state cannot connect three pairwise separated
labels. Hence, starting from separated labels, the probability that some pair is
connected after `d` steps is at most `card * H`, and the probability that all three are
connected is at most `(card * H)²`, where `H` is the hazard sum of these steps. On the
coalescence times this bounds the probability that the three coalescence phases lie in a
common window by the square of its hazard sum; repeated samples cost `O(1/n)`.

In the critical regime, hazard sums are uniformly close to integrals of `g²`. The
portmanteau theorem for open sets bounds the limit mass of each window of length `2/N`
by `card² (∫_{I_w} g²)²`, with `I_w` a slightly enlarged window. Summing over a cover of
`[η, 1 - η]` gives at most `card² · max_w ∫_{I_w} g² · 3 ∫ g²`, which is arbitrarily
small. Common values near `0` or `1` are excluded since the coalescence time of `i` and
`j` is at most the birth time of `i`, which is almost surely below one.
-/

@[expose] public section

open MeasureTheory Set Filter Topology

namespace Freezing2.CriticalGenealogy

open ReverseHistory ReverseCoalescence MeasuredGHSpace TrackedGenealogy

section Discrete

/-- Connectivity states of three tracked labels in which no two are connected. -/
def tripleSepStates : Set (Fin 3 → Fin 3 → Bool) :=
  {s | s 0 1 = false ∧ s 0 2 = false ∧ s 1 2 = false}

/-- Connectivity states of three tracked labels in which all three are connected. -/
def tripleAllStates : Set (Fin 3 → Fin 3 → Bool) :=
  {s | s 0 1 = true ∧ s 0 2 = true ∧ s 1 2 = true}

/-- The number of connectivity states of three tracked labels. -/
noncomputable def tripleCard : ℝ := Fintype.card (Fin 3 → Fin 3 → Bool)

theorem tripleCard_nonneg : 0 ≤ tripleCard := Nat.cast_nonneg _

theorem trackedState_symm {k n p : ℕ} (u : Fin k → ℕ ⊕ ℕ) (F : Freezing1.Reverse.Forest)
    (j l : Fin k) :
    trackedState n p u F j l = trackedState n p u F l j := by
  classical
  unfold trackedState
  by_cases hj : Born n p u j <;> by_cases hl : Born n p u l <;> simp [hj, hl, eq_comm]

theorem trackedState_trans {k n p : ℕ} (u : Fin k → ℕ ⊕ ℕ) (F : Freezing1.Reverse.Forest)
    {j l m : Fin k} (h1 : trackedState n p u F j l = true) (h2 : trackedState n p u F l m = true) :
    trackedState n p u F j m = true := by
  classical
  unfold trackedState at h1 h2 ⊢
  by_cases hj : Born n p u j <;> by_cases hl : Born n p u l <;> by_cases hm : Born n p u m <;>
    simp_all

/-- **Pigeonhole for one merger.** Merging two components of a symmetric transitive
state in which the three labels are pairwise disconnected cannot connect all three. -/
theorem mergeState_not_mem_tripleAllStates {s : Fin 3 → Fin 3 → Bool}
    (hsymm : ∀ a b, s a b = s b a) (htrans : ∀ a b c, s a b = true → s b c = true → s a c = true)
    (hs : s ∈ tripleSepStates) (j₀ l₀ : Fin 3) : mergeState s j₀ l₀ ∉ tripleAllStates := by
  obtain ⟨h01, h02, h12⟩ := hs
  have share : ∀ a b z, s a z = true → s b z = true → s a b = true := fun a b z h1 h2 ↦
    htrans a z b h1 (by rw [hsymm]; exact h2)
  have e01j : s 0 j₀ = true → s 1 j₀ = true → False := fun h h' ↦ by
    simpa [h01] using share 0 1 j₀ h h'
  have e01l : s 0 l₀ = true → s 1 l₀ = true → False := fun h h' ↦ by
    simpa [h01] using share 0 1 l₀ h h'
  have e02j : s 0 j₀ = true → s 2 j₀ = true → False := fun h h' ↦ by
    simpa [h02] using share 0 2 j₀ h h'
  have e02l : s 0 l₀ = true → s 2 l₀ = true → False := fun h h' ↦ by
    simpa [h02] using share 0 2 l₀ h h'
  have e12j : s 1 j₀ = true → s 2 j₀ = true → False := fun h h' ↦ by
    simpa [h12] using share 1 2 j₀ h h'
  have e12l : s 1 l₀ = true → s 2 l₀ = true → False := fun h h' ↦ by
    simpa [h12] using share 1 2 l₀ h h'
  rintro ⟨m01, m02, m12⟩
  simp only [mergeState, h01, h02, h12, Bool.false_or, Bool.or_eq_true, Bool.and_eq_true]
    at m01 m02 m12
  rcases m01 with ⟨a1, b1⟩ | ⟨a1, b1⟩ <;> rcases m02 with ⟨a2, c2⟩ | ⟨a2, c2⟩ <;>
    rcases m12 with ⟨b3, c3⟩ | ⟨b3, c3⟩ <;> tauto

variable {x : Freezing1.SignSequence} {n : ℕ}

theorem coalescenceHazard_nonneg_of_le (hn : (n : ℕ∞) ≤ Freezing1.extinctionTime x) {i : ℕ}
    (hi : i ≤ n) : 0 ≤ coalescenceHazard x i := by
  by_cases hx : x i = true
  · rw [coalescenceHazard_eq_inv_choose hn hi hx]
    positivity
  · simp [coalescenceHazard, hx]

/-- A change of tracked state in one step has probability at most the hazard. -/
theorem chainStep_le_coalescenceHazard {k : ℕ} (hn : (n : ℕ∞) ≤ Freezing1.extinctionTime x)
    {p : ℕ} (hp : p + 1 ≤ n) (u : Fin k → ℕ ⊕ ℕ) {s s' : Fin k → Fin k → Bool} (hss : s' ≠ s) :
    chainStep x n p u s s' ≤ coalescenceHazard x (p + 1) := by
  classical
  have h0 := coalescenceHazard_nonneg_of_le hn hp
  unfold chainStep
  by_cases hx : x (p + 1) = true
  · rw [coalescenceHazard_eq_inv_choose hn hp hx]
    simp only [hx, hss, ↓reduceIte]
    split_ifs
    · exact le_rfl
    · positivity
  · simp only [hx, hss, ↓reduceIte, Bool.false_eq_true]
    exact h0

/-- A change of tracked state which is not a merger has probability zero. -/
theorem chainStep_eq_zero_of_not_isMerge {k : ℕ} {p : ℕ} (u : Fin k → ℕ ⊕ ℕ)
    {s s' : Fin k → Fin k → Bool} (hss : s' ≠ s) (hm : ¬ IsMerge n (p + 1) u s s') :
    chainStep x n p u s s' = 0 := by
  classical
  unfold chainStep
  split_ifs <;> simp_all

theorem measurableSet_chainState_mem {k : ℕ} (u : Fin k → ℕ ⊕ ℕ) {m N : ℕ} (hm : m ≤ N)
    (T : Set (Fin k → Fin k → Bool)) :
    MeasurableSet[Filtration.piLE (X := fun _ ↦ Freezing1.Reverse.Forest) N]
      {ω | chainState n u m ω ∈ T} := by
  have e : {ω | chainState n u m ω ∈ T} = ⋃ s ∈ T, {ω | chainState n u m ω = s} := by
    ext ω
    simp
  rw [e]
  exact MeasurableSet.biUnion T.to_countable fun s _ ↦ measurableSet_chainState n u hm s

/-- **One step of the tracked chain.** If every transition into `T` from the current
state, weighted by the mass of `B`, is bounded by `h` times the mass of `B'`, then the
mass of `B` ending in `T` one step later is at most `card * h * P(B')`. -/
theorem chainState_step_mass_le {k : ℕ} {u : Fin k → ℕ ⊕ ℕ}
    (hn : (n : ℕ∞) ≤ Freezing1.extinctionTime x)
    (hu : ∀ j, u j ∈ Freezing1.vertexLabels x n) (hinj : Function.Injective u) {N : ℕ}
    (hN : N < n) {B B' : Set History}
    (hB : MeasurableSet[Filtration.piLE (X := fun _ ↦ Freezing1.Reverse.Forest) N] B)
    (T : Set (Fin k → Fin k → Bool)) {h : ℝ} (hh : 0 ≤ h)
    (hbound : ∀ s s', s' ∈ T →
      (jointLaw x n).real (B ∩ {ω | chainState n u N ω = s}) *
          chainStep x n (n - (N + 1)) u s s' ≤
        h * (jointLaw x n).real (B' ∩ {ω | chainState n u N ω = s})) :
    (jointLaw x n).real (B ∩ {ω | chainState n u (N + 1) ω ∈ T}) ≤
      Fintype.card (Fin k → Fin k → Bool) * h * (jointLaw x n).real B' := by
  classical
  set μ := jointLaw x n
  have hfib : ∀ m, m ≤ N + 1 → ∀ c : Fin k → Fin k → Bool,
      MeasurableSet (chainState n u m ⁻¹' {c}) :=
    fun m hm c ↦ (Filtration.piLE (X := fun _ ↦ Freezing1.Reverse.Forest)).le (N + 1) _
      (measurableSet_chainState n u hm c)
  have hB'sum : μ.real B' = ∑ s, μ.real (B' ∩ chainState n u N ⁻¹' {s}) :=
    measureReal_eq_sum_fiber μ B' (chainState n u N) (hfib N (Nat.le_succ N))
  rw [measureReal_eq_sum_fiber μ _ (chainState n u (N + 1)) (hfib (N + 1) le_rfl)]
  have hterm : ∀ s', μ.real (B ∩ {ω | chainState n u (N + 1) ω ∈ T} ∩
      chainState n u (N + 1) ⁻¹' {s'}) ≤ h * μ.real B' := by
    intro s'
    by_cases hs' : s' ∈ T
    · have e : B ∩ {ω | chainState n u (N + 1) ω ∈ T} ∩ chainState n u (N + 1) ⁻¹' {s'} =
          B ∩ {ω | chainState n u (N + 1) ω = s'} := by
        ext ω
        simp only [mem_inter_iff, mem_ofPred_eq, mem_preimage, mem_singleton_iff]
        constructor
        · rintro ⟨⟨hb, _⟩, he⟩
          exact ⟨hb, he⟩
        · rintro ⟨hb, he⟩
          exact ⟨⟨hb, he ▸ hs'⟩, he⟩
      rw [e, measureReal_eq_sum_fiber μ _ (chainState n u N) (hfib N (Nat.le_succ N)), hB'sum,
        Finset.mul_sum]
      refine Finset.sum_le_sum fun s _ ↦ ?_
      have hstep := jointLaw_chainState_step hn hu hinj hN hB s s'
      have e2 : B ∩ {ω | chainState n u (N + 1) ω = s'} ∩ chainState n u N ⁻¹' {s} =
          B ∩ {ω | chainState n u N ω = s} ∩ {ω | chainState n u (N + 1) ω = s'} := by
        ext ω
        simp only [mem_inter_iff, mem_ofPred_eq, mem_preimage, mem_singleton_iff]
        tauto
      rw [e2, hstep]
      exact hbound s s' hs'
    · have e : B ∩ {ω | chainState n u (N + 1) ω ∈ T} ∩ chainState n u (N + 1) ⁻¹' {s'} = ∅ := by
        ext ω
        simp only [mem_inter_iff, mem_ofPred_eq, mem_preimage, mem_singleton_iff,
          mem_empty_iff_false, iff_false]
        rintro ⟨⟨_, hT⟩, he⟩
        exact hs' (he ▸ hT)
      rw [e, measureReal_empty]
      exact mul_nonneg hh measureReal_nonneg
  calc _ ≤ ∑ _s' : Fin k → Fin k → Bool, h * μ.real B' :=
        Finset.sum_le_sum fun s' _ ↦ hterm s'
    _ = _ := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring

/-- **Two-merger bound for the tracked chain.** Starting from separated labels at step
`m₀`, the probability that some pair is connected after `d` steps is at most
`card * H`, and the probability that all three are connected is at most `(card * H)²`,
where `H` is the sum of the hazards of these steps. -/
theorem triple_chain_bound {u : Fin 3 → ℕ ⊕ ℕ} (hn : (n : ℕ∞) ≤ Freezing1.extinctionTime x)
    (hu : ∀ j, u j ∈ Freezing1.vertexLabels x n) (hinj : Function.Injective u) (m₀ : ℕ) :
    ∀ d, m₀ + d ≤ n →
      (jointLaw x n).real ({ω | chainState n u m₀ ω ∈ tripleSepStates} ∩
          {ω | chainState n u (m₀ + d) ω ∉ tripleSepStates}) ≤
        tripleCard * ∑ r ∈ Finset.range d, coalescenceHazard x (n - (m₀ + r)) ∧
      (jointLaw x n).real ({ω | chainState n u m₀ ω ∈ tripleSepStates} ∩
          {ω | chainState n u (m₀ + d) ω ∈ tripleAllStates}) ≤
        tripleCard ^ 2 * (∑ r ∈ Finset.range d, coalescenceHazard x (n - (m₀ + r))) ^ 2 := by
  classical
  set μ := jointLaw x n
  set A₀ := {ω | chainState n u m₀ ω ∈ tripleSepStates}
  intro d
  induction d with
  | zero =>
    intro _
    have e1 : A₀ ∩ {ω | chainState n u (m₀ + 0) ω ∉ tripleSepStates} = ∅ := by
      ext ω
      simp only [A₀, add_zero, mem_inter_iff, mem_ofPred_eq, mem_empty_iff_false, iff_false]
      exact fun h ↦ h.2 h.1
    have e2 : A₀ ∩ {ω | chainState n u (m₀ + 0) ω ∈ tripleAllStates} = ∅ := by
      ext ω
      simp only [A₀, add_zero, mem_inter_iff, mem_ofPred_eq, mem_empty_iff_false, iff_false,
        tripleSepStates, tripleAllStates]
      rintro ⟨⟨h, -, -⟩, h', -, -⟩
      rw [h] at h'
      exact Bool.false_ne_true h'
    rw [e1, e2]
    simp
  | succ d ih =>
    intro hd
    obtain ⟨ih1, ih2⟩ := ih (by omega)
    set N := m₀ + d with hNdef
    have hN : N < n := by omega
    have hNs : m₀ + (d + 1) = N + 1 := by omega
    rw [hNs, Finset.sum_range_succ]
    set H := ∑ r ∈ Finset.range d, coalescenceHazard x (n - (m₀ + r))
    set h := coalescenceHazard x (n - N)
    have hh : 0 ≤ h := coalescenceHazard_nonneg_of_le hn (Nat.sub_le _ _)
    have hH : 0 ≤ H := Finset.sum_nonneg fun r _ ↦ coalescenceHazard_nonneg_of_le hn
      (Nat.sub_le _ _)
    have hA₀ : MeasurableSet[Filtration.piLE (X := fun _ ↦ Freezing1.Reverse.Forest) N] A₀ :=
      measurableSet_chainState_mem u (by omega) _
    have hstep_le : ∀ s s', s' ≠ s → chainStep x n (n - (N + 1)) u s s' ≤ h := by
      intro s s' hss
      have := chainStep_le_coalescenceHazard hn (by omega : n - (N + 1) + 1 ≤ n) u hss
      rwa [show n - (N + 1) + 1 = n - N by omega] at this
    constructor
    · have hsub : A₀ ∩ {ω | chainState n u (N + 1) ω ∉ tripleSepStates} ⊆
          (A₀ ∩ {ω | chainState n u N ω ∉ tripleSepStates}) ∪
            ((A₀ ∩ {ω | chainState n u N ω ∈ tripleSepStates}) ∩
              {ω | chainState n u (N + 1) ω ∈ tripleSepStatesᶜ}) := by
        rintro ω ⟨hA, h1⟩
        by_cases hN' : chainState n u N ω ∈ tripleSepStates
        · exact Or.inr ⟨⟨hA, hN'⟩, h1⟩
        · exact Or.inl ⟨hA, hN'⟩
      have hB : MeasurableSet[Filtration.piLE (X := fun _ ↦ Freezing1.Reverse.Forest) N]
          (A₀ ∩ {ω | chainState n u N ω ∈ tripleSepStates}) :=
        hA₀.inter (measurableSet_chainState_mem u le_rfl _)
      have hstep := chainState_step_mass_le hn hu hinj hN hB tripleSepStatesᶜ hh
        (B' := A₀ ∩ {ω | chainState n u N ω ∈ tripleSepStates}) (fun s s' hs' ↦ by
          by_cases hs : s ∈ tripleSepStates
          · have hss : s' ≠ s := fun e ↦ hs' (e ▸ hs)
            rw [mul_comm h]
            exact mul_le_mul_of_nonneg_left (hstep_le s s' hss) measureReal_nonneg
          · have e : A₀ ∩ {ω | chainState n u N ω ∈ tripleSepStates} ∩
                {ω | chainState n u N ω = s} = ∅ := by
              ext ω
              simp only [mem_inter_iff, mem_ofPred_eq, mem_empty_iff_false, iff_false]
              rintro ⟨⟨_, h1⟩, h2⟩
              exact hs (h2 ▸ h1)
            rw [e, measureReal_empty]
            simp)
      calc _ ≤ _ := measureReal_mono hsub
        _ ≤ _ := measureReal_union_le _ _
        _ ≤ tripleCard * H + tripleCard * h * 1 :=
          add_le_add ih1 (hstep.trans (mul_le_mul_of_nonneg_left measureReal_le_one
            (mul_nonneg tripleCard_nonneg hh)))
        _ = _ := by ring
    · have hsub : A₀ ∩ {ω | chainState n u (N + 1) ω ∈ tripleAllStates} ⊆
          (A₀ ∩ {ω | chainState n u N ω ∈ tripleAllStates}) ∪
            ((A₀ ∩ {ω | chainState n u N ω ∈ tripleAllStatesᶜ}) ∩
              {ω | chainState n u (N + 1) ω ∈ tripleAllStates}) := by
        rintro ω ⟨hA, h1⟩
        by_cases hN' : chainState n u N ω ∈ tripleAllStates
        · exact Or.inl ⟨hA, hN'⟩
        · exact Or.inr ⟨⟨hA, hN'⟩, h1⟩
      have hB : MeasurableSet[Filtration.piLE (X := fun _ ↦ Freezing1.Reverse.Forest) N]
          (A₀ ∩ {ω | chainState n u N ω ∈ tripleAllStatesᶜ}) :=
        hA₀.inter (measurableSet_chainState_mem u le_rfl _)
      have hstep := chainState_step_mass_le hn hu hinj hN hB tripleAllStates hh
        (B' := A₀ ∩ {ω | chainState n u N ω ∉ tripleSepStates}) (fun s s' hs' ↦ by
          by_cases hne : (A₀ ∩ {ω | chainState n u N ω ∈ tripleAllStatesᶜ} ∩
              {ω | chainState n u N ω = s}).Nonempty
          · obtain ⟨ω, ⟨hA, hnall⟩, hω⟩ := hne
            have hω : chainState n u N ω = s := hω
            have hsall : s ∉ tripleAllStates := hω ▸ hnall
            have hss : s' ≠ s := fun e ↦ hsall (e ▸ hs')
            by_cases hs : s ∈ tripleSepStates
            · have hz : chainStep x n (n - (N + 1)) u s s' = 0 := by
                apply chainStep_eq_zero_of_not_isMerge u hss
                rintro ⟨j₀, l₀, -, -, -, rfl⟩
                subst hω
                exact mergeState_not_mem_tripleAllStates
                  (fun a b ↦ trackedState_symm _ _ a b)
                  (fun a b c h1 h2 ↦ trackedState_trans _ _ h1 h2) hs j₀ l₀ hs'
              rw [hz, mul_zero]
              exact mul_nonneg hh measureReal_nonneg
            · have hsub2 : A₀ ∩ {ω | chainState n u N ω ∈ tripleAllStatesᶜ} ∩
                  {ω | chainState n u N ω = s} ⊆
                  A₀ ∩ {ω | chainState n u N ω ∉ tripleSepStates} ∩
                    {ω | chainState n u N ω = s} := by
                rintro ω' ⟨⟨hA', -⟩, hω'⟩
                have hω' : chainState n u N ω' = s := hω'
                refine ⟨⟨hA', ?_⟩, hω'⟩
                show chainState n u N ω' ∉ tripleSepStates
                rw [hω']
                exact hs
              rw [mul_comm h]
              exact (mul_le_mul_of_nonneg_left (hstep_le s s' hss) measureReal_nonneg).trans
                (mul_le_mul_of_nonneg_right (measureReal_mono hsub2) hh)
          · rw [not_nonempty_iff_eq_empty.mp hne, measureReal_empty, zero_mul]
            exact mul_nonneg hh measureReal_nonneg)
      calc _ ≤ _ := measureReal_mono hsub
        _ ≤ _ := measureReal_union_le _ _
        _ ≤ tripleCard ^ 2 * H ^ 2 + tripleCard * h * (tripleCard * H) :=
          add_le_add ih2 (hstep.trans (mul_le_mul_of_nonneg_left ih1
            (mul_nonneg tripleCard_nonneg hh)))
        _ ≤ _ := by
          nlinarith [mul_nonneg (mul_nonneg (sq_nonneg tripleCard) hH) hh,
            mul_nonneg (sq_nonneg tripleCard) (sq_nonneg h)]

/-- **Triple coalescence in a window.** For three distinct tracked labels, the
probability that all three pairwise coalescence phases lie in `[φb, φt)` is at most
`card² (∑_{φb < i ≤ φt} hazard i)²`. -/
theorem triple_coalescence_window_le {u : Fin 3 → ℕ ⊕ ℕ}
    (hn : (n : ℕ∞) ≤ Freezing1.extinctionTime x)
    (hu : ∀ j, u j ∈ Freezing1.vertexLabels x n) (hinj : Function.Injective u) {φb φt : ℕ}
    (hbt : φb ≤ φt) (ht : φt ≤ n) :
    (jointLaw x n).real {ω |
        (φb ≤ coalescenceTime n (u 0) (u 1) ω ∧ coalescenceTime n (u 0) (u 1) ω < φt) ∧
        (φb ≤ coalescenceTime n (u 0) (u 2) ω ∧ coalescenceTime n (u 0) (u 2) ω < φt) ∧
        (φb ≤ coalescenceTime n (u 1) (u 2) ω ∧ coalescenceTime n (u 1) (u 2) ω < φt)} ≤
      tripleCard ^ 2 * (∑ i ∈ Finset.Ioc φb φt, coalescenceHazard x i) ^ 2 := by
  have hpairs : ∀ᵐ ω ∂jointLaw x n, ∀ p : Fin 3 × Fin 3,
      ∀ i ≤ commonBirth n (u p.1) (u p.2),
        connectedAt n (u p.1) (u p.2) i ω ↔ i ≤ coalescenceTime n (u p.1) (u p.2) ω :=
    ae_all_iff.mpr fun p ↦ jointLaw_connected_iff_le_coalescenceTime hn (hu p.1) (hu p.2)
  set m₀ := n - φt
  set d := φt - φb
  have hmd : m₀ + d = n - φb := by omega
  obtain ⟨-, hbound⟩ := triple_chain_bound hn hu hinj m₀ d (by omega)
  have hsum : ∑ r ∈ Finset.range d, coalescenceHazard x (n - (m₀ + r)) =
      ∑ i ∈ Finset.Ioc φb φt, coalescenceHazard x i := by
    rw [Finset.sum_congr rfl (g := fun r ↦ coalescenceHazard x (φt - r)) fun r hr ↦ by
      have := Finset.mem_range.mp hr
      congr 1
      omega]
    rw [sum_range_sub_eq_sum_Icc (fun q ↦ coalescenceHazard x q) (by omega : d ≤ φt)]
    congr 1
    ext q
    simp only [Finset.mem_Icc, Finset.mem_Ioc]
    omega
  rw [hsum, hmd] at hbound
  refine le_trans (ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae ?_)) hbound
  filter_upwards [hpairs] with ω hω hE
  obtain ⟨⟨b01, t01⟩, ⟨b02, t02⟩, ⟨b12, t12⟩⟩ := hE
  have c : ∀ (j l : Fin 3), j ≠ l → ∀ φ, φ ≤ n →
      (chainState n u (n - φ) ω j l = true ↔ φ ≤ coalescenceTime n (u j) (u l) ω) :=
    fun j l hjl φ hφ ↦ chainState_eq_true_iff hφ hjl (hω (j, l))
  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩
  · rw [← Bool.not_eq_true, c 0 1 (by decide) φt ht]
    omega
  · rw [← Bool.not_eq_true, c 0 2 (by decide) φt ht]
    omega
  · rw [← Bool.not_eq_true, c 1 2 (by decide) φt ht]
    omega
  · exact (c 0 1 (by decide) φb (by omega)).mpr b01
  · exact (c 0 2 (by decide) φb (by omega)).mpr b02
  · exact (c 1 2 (by decide) φb (by omega)).mpr b12

end Discrete

section Sampled

/-- Two distinct coordinates of iid uniform labels coincide with the collision
probability. -/
theorem pi_uniformVertex_real_eq (x : ℕ → ℤ) (hx : IsSigned x) {n : ℕ}
    (hs : SurvivesThrough x n) {k : ℕ} {a b : Fin k} (hab : a ≠ b) :
    (Measure.pi fun _ : Fin k ↦ uniformVertex x n).real {V | V a = V b} =
      ((uniformVertex x n).prod (uniformVertex x n)).real {p | p.1 = p.2} := by
  let := uniformVertex_isProbabilityMeasure x hx (hs n le_rfl).le
  have hm : Measurable (fun q : History × (Fin k → VertexLabel) ↦ (q.1, (q.2 a, q.2 b))) :=
    measurable_fst.prodMk (((measurable_pi_apply a).comp measurable_snd).prodMk
      ((measurable_pi_apply b).comp measurable_snd))
  have hS : MeasurableSet (univ ×ˢ {p : VertexLabel × VertexLabel | p.1 = p.2} :
      Set (History × (VertexLabel × VertexLabel))) :=
    MeasurableSet.univ.prod (Set.to_countable _).measurableSet
  have h1 : (sampledReverseVectorLaw x n k).real
        (univ ×ˢ {V : Fin k → VertexLabel | V a = V b}) =
      (sampledReverseLaw x n).real (univ ×ˢ {p : VertexLabel × VertexLabel | p.1 = p.2}) := by
    rw [← sampledReverseVectorLaw_map_pair x hx hs hab, measureReal_def, measureReal_def,
      Measure.map_apply hm hS]
    rfl
  rw [sampledReverseVectorLaw, sampledReverseLaw, measureReal_prod_prod,
    measureReal_prod_prod] at h1
  simpa using h1

/-- **Triple coalescence of sampled vertices in a window.** For three distinct sample
coordinates, the probability that their pairwise coalescence phases all lie in
`[φb, φt)` is at most three collision probabilities plus the squared hazard bound. -/
theorem sampled_triple_window_le (x : ℕ → ℤ) (hx : IsSigned x) {n : ℕ}
    (hs : SurvivesThrough x n) {k : ℕ} {i j l : Fin k} (hij : i ≠ j) (hil : i ≠ l)
    (hjl : j ≠ l) {φb φt : ℕ} (hbt : φb ≤ φt) (ht : φt ≤ n) :
    (sampledReverseVectorLaw x n k).real {q |
        (φb ≤ sourceCoalescenceTime n (q.2 i) (q.2 j) q.1 ∧
          sourceCoalescenceTime n (q.2 i) (q.2 j) q.1 < φt) ∧
        (φb ≤ sourceCoalescenceTime n (q.2 i) (q.2 l) q.1 ∧
          sourceCoalescenceTime n (q.2 i) (q.2 l) q.1 < φt) ∧
        (φb ≤ sourceCoalescenceTime n (q.2 j) (q.2 l) q.1 ∧
          sourceCoalescenceTime n (q.2 j) (q.2 l) q.1 < φt)} ≤
      3 * ((uniformVertex x n).prod (uniformVertex x n)).real {p | p.1 = p.2} +
        tripleCard ^ 2 *
          (∑ m ∈ Finset.Ioc φb φt, coalescenceHazard (companionSchedule x) m) ^ 2 := by
  let := uniformVertex_isProbabilityMeasure x hx (hs n le_rfl).le
  set ν := Measure.pi fun _ : Fin k ↦ uniformVertex x n
  set E : Set (History × (Fin k → VertexLabel)) := {q |
        (φb ≤ sourceCoalescenceTime n (q.2 i) (q.2 j) q.1 ∧
          sourceCoalescenceTime n (q.2 i) (q.2 j) q.1 < φt) ∧
        (φb ≤ sourceCoalescenceTime n (q.2 i) (q.2 l) q.1 ∧
          sourceCoalescenceTime n (q.2 i) (q.2 l) q.1 < φt) ∧
        (φb ≤ sourceCoalescenceTime n (q.2 j) (q.2 l) q.1 ∧
          sourceCoalescenceTime n (q.2 j) (q.2 l) q.1 < φt)} with hEdef
  have hE : MeasurableSet E := by
    have hm : Measurable fun q : History × (Fin k → VertexLabel) ↦
        (sourceCoalescenceTime n (q.2 i) (q.2 j) q.1, sourceCoalescenceTime n (q.2 i) (q.2 l) q.1,
          sourceCoalescenceTime n (q.2 j) (q.2 l) q.1) :=
      measurable_from_prod_countable_left fun V ↦
        (measurable_sourceCoalescenceTime n (V i) (V j)).prodMk
          ((measurable_sourceCoalescenceTime n (V i) (V l)).prodMk
            (measurable_sourceCoalescenceTime n (V j) (V l)))
    exact ((measurable_of_countable (fun c : ℕ × ℕ × ℕ ↦ (φb ≤ c.1 ∧ c.1 < φt) ∧
      (φb ≤ c.2.1 ∧ c.2.1 < φt) ∧ (φb ≤ c.2.2 ∧ c.2.2 < φt))).comp hm).setOf
  set Bad : Set (Fin k → VertexLabel) :=
    {V | V i = V j} ∪ {V | V i = V l} ∪ {V | V j = V l} with hBaddef
  have hBad : MeasurableSet Bad := (Set.to_countable _).measurableSet
  have hext : (n : ℕ∞) ≤ Freezing1.extinctionTime (companionSchedule x) :=
    (companion_before_extinction x hx hs).le
  have hlegalV : ∀ᵐ V ∂ν, ∀ a, V a ∈ vertexLabels x n :=
    ae_all_iff.mpr fun a ↦
      (measurePreserving_eval (fun _ : Fin k ↦ uniformVertex x n) a).quasiMeasurePreserving.ae
        (uniformVertex_mem x hx (hs n le_rfl).le)
  have hne : ∀ {v w : VertexLabel}, v ∈ vertexLabels x n → w ∈ vertexLabels x n → v ≠ w →
      toCompanionLabel v ≠ toCompanionLabel w := fun hv hw hvw he ↦
    hvw (by rw [← from_toCompanionLabel hv, he, from_toCompanionLabel hw])
  have hsec : ∀ᵐ V ∂ν, V ∉ Bad → (jointLaw (companionSchedule x) n).real {ω | (ω, V) ∈ E} ≤
      tripleCard ^ 2 *
        (∑ m ∈ Finset.Ioc φb φt, coalescenceHazard (companionSchedule x) m) ^ 2 := by
    filter_upwards [hlegalV] with V hV hnot
    simp only [Bad, mem_union, mem_ofPred_eq, not_or] at hnot
    obtain ⟨⟨h1, h2⟩, h3⟩ := hnot
    set u : Fin 3 → ℕ ⊕ ℕ :=
      ![toCompanionLabel (V i), toCompanionLabel (V j), toCompanionLabel (V l)] with hudef
    have hu : ∀ a, u a ∈ Freezing1.vertexLabels (companionSchedule x) n := by
      intro a
      fin_cases a <;> exact toCompanionLabel_mem x hx (hV _)
    have hinj : Function.Injective u := by
      intro a b hab
      fin_cases a <;> fin_cases b <;> simp [u] at hab ⊢
      · exact hne (hV i) (hV j) h1 hab
      · exact hne (hV i) (hV l) h2 hab
      · exact hne (hV i) (hV j) h1 hab.symm
      · exact hne (hV j) (hV l) h3 hab
      · exact hne (hV i) (hV l) h2 hab.symm
      · exact hne (hV j) (hV l) h3 hab.symm
    exact triple_coalescence_window_le (u := u) hext hu hinj hbt ht
  have hmain := measureReal_prod_event_le_bad_add (μ := jointLaw (companionSchedule x) n)
    (ν := ν) hE hBad (by positivity) hsec
  have hbad : ν.real Bad ≤ 3 * ((uniformVertex x n).prod (uniformVertex x n)).real
      {p | p.1 = p.2} := by
    have h12 := measureReal_union_le (μ := ν) {V : Fin k → VertexLabel | V i = V j}
      {V | V i = V l}
    have h123 := measureReal_union_le (μ := ν)
      ({V : Fin k → VertexLabel | V i = V j} ∪ {V | V i = V l}) {V | V j = V l}
    rw [pi_uniformVertex_real_eq x hx hs hij, pi_uniformVertex_real_eq x hx hs hil] at h12
    rw [pi_uniformVertex_real_eq x hx hs hjl] at h123
    linarith
  calc (sampledReverseVectorLaw x n k).real E
      = ((jointLaw (companionSchedule x) n).prod ν).real E := rfl
    _ ≤ _ := hmain
    _ ≤ _ := by linarith

end Sampled

section Analytic

/-- Overlapping windows of length `3h` starting at `b₀ + w h` cover each point at most
three times, so their integrals add up to at most three times the total integral. -/
theorem sum_window_integral_le {f : ℝ → ℝ} {A B b₀ h : ℝ} (hf : IntegrableOn f (Icc A B))
    (hf0 : ∀ t, 0 ≤ f t) (hA : A ≤ b₀) (hh : 0 < h) (W : ℕ)
    (hB : b₀ + ((W : ℝ) + 2) * h ≤ B) :
    ∑ w ∈ Finset.range W, ∫ t in Icc (b₀ + w * h) (b₀ + (w + 3) * h), f t ≤
      3 * ∫ t in Icc A B, f t := by
  set pt : ℕ → ℝ := fun v ↦ b₀ + v * h with hpt
  set Q : ℕ → ℝ := fun v ↦ ∫ t in pt v..pt (v + 1), f t with hQ
  have hpt_mono : Monotone pt := fun a b hab ↦ by
    have : (a : ℝ) ≤ b := by exact_mod_cast hab
    simp only [hpt]
    nlinarith
  have hptA : ∀ v, A ≤ pt v := fun v ↦ by
    simp only [hpt]
    nlinarith [(Nat.cast_nonneg v : (0 : ℝ) ≤ v)]
  have hptB : ∀ v, v ≤ W + 2 → pt v ≤ B := fun v hv ↦ by
    have : (v : ℝ) ≤ W + 2 := by exact_mod_cast hv
    simp only [hpt]
    nlinarith
  have hint : ∀ v, v ≤ W + 1 → IntervalIntegrable f volume (pt v) (pt (v + 1)) := by
    intro v hv
    apply IntegrableOn.intervalIntegrable
    apply hf.mono_set
    rw [uIcc_of_le (hpt_mono (Nat.le_succ v))]
    exact Icc_subset_Icc (hptA v) (hptB (v + 1) (by omega))
  have hQ0 : ∀ v, 0 ≤ Q v := fun v ↦
    intervalIntegral.integral_nonneg (hpt_mono (Nat.le_succ v)) fun t _ ↦ hf0 t
  have hwin : ∀ w, w < W → ∫ t in Icc (b₀ + w * h) (b₀ + (w + 3) * h), f t =
      ∑ r ∈ Finset.range 3, Q (w + r) := by
    intro w hw
    have hadj := intervalIntegral.sum_integral_adjacent_intervals (μ := volume) (f := f)
      (a := fun r ↦ pt (w + r)) (n := 3) (fun r hr ↦ hint (w + r) (by omega))
    have e1 : b₀ + (w : ℝ) * h = pt (w + 0) := by simp [hpt]
    have e2 : b₀ + ((w : ℝ) + 3) * h = pt (w + 3) := by simp [hpt]
    rw [e1, e2, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (hpt_mono (by omega)), ← hadj]
    rfl
  have hsum3 : ∑ w ∈ Finset.range W, ∑ r ∈ Finset.range 3, Q (w + r) ≤
      3 * ∑ v ∈ Finset.range (W + 2), Q v := by
    rw [Finset.sum_comm]
    have hr : ∀ r ∈ Finset.range 3, ∑ w ∈ Finset.range W, Q (w + r) ≤
        ∑ v ∈ Finset.range (W + 2), Q v := by
      intro r hr
      have hr3 := Finset.mem_range.mp hr
      rw [← Finset.sum_image (f := Q) (s := Finset.range W) (g := fun w ↦ w + r)
        (fun a _ b _ hab ↦ by simpa using hab)]
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro v hv
        simp only [Finset.mem_image, Finset.mem_range] at hv ⊢
        omega
      · exact fun v _ _ ↦ hQ0 v
    calc _ ≤ ∑ _r ∈ Finset.range 3, ∑ v ∈ Finset.range (W + 2), Q v := Finset.sum_le_sum hr
      _ = _ := by simp
  have htot : ∑ v ∈ Finset.range (W + 2), Q v = ∫ t in pt 0..pt (W + 2), f t :=
    intervalIntegral.sum_integral_adjacent_intervals fun v hv ↦ hint v (by omega)
  have hmono : ∫ t in pt 0..pt (W + 2), f t ≤ ∫ t in Icc A B, f t := by
    have hAB : A ≤ B := (hptA 0).trans (hptB 0 (by omega))
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hAB]
    apply intervalIntegral.integral_mono_interval (hptA 0) (hpt_mono (by omega))
      (hptB _ le_rfl) (ae_of_all _ fun t ↦ hf0 t)
    apply IntegrableOn.intervalIntegrable
    rw [uIcc_of_le hAB]
    exact hf
  calc _ = ∑ w ∈ Finset.range W, ∑ r ∈ Finset.range 3, Q (w + r) :=
        Finset.sum_congr rfl fun w hw ↦ hwin w (Finset.mem_range.mp hw)
    _ ≤ 3 * ∑ v ∈ Finset.range (W + 2), Q v := hsum3
    _ = 3 * ∫ t in pt 0..pt (W + 2), f t := by rw [htot]
    _ ≤ _ := by linarith

end Analytic

section Limit

variable {xa : ℕ → ℕ → ℤ} {g : ℝ → ℝ} {k : ℕ}

theorem coalescenceIntervalError_le_max {α ε : ℝ} {n a b : ℕ}
    (hab : CoalescenceInterval ε n a b) :
    coalescenceIntervalError xa α g n a b ≤ coalescenceIntervalErrorMax xa α g ε n := by
  unfold coalescenceIntervalErrorMax
  have hmem : ((⟨a, by have := hab.2.1; have := hab.2.2.1; omega⟩ : Fin (n + 1)),
      (⟨b, by have := hab.2.2.1; omega⟩ : Fin (n + 1))) ∈ Finset.univ := Finset.mem_univ _
  refine le_trans ?_ (Finset.le_sup' _ hmem)
  simp only [hab, ↓reduceIte, le_refl]

/-- **Triple mergers in a window.** The limit gives mass at most
`card² (∫_a^{b'} g²)²` to the event that all three coalescence times lie in `(a, b)`. -/
theorem criticalGenealogyLimit_tripleWindow_le (hx : AdmissibleArray xa)
    (hL1 : HasL1ReciprocalProfile xa (1 / 2) g) (hpos : PositiveProfile g)
    (h2 : HasLocalSquareMomentProfile xa (1 / 2) g) {i j l : Fin k} (hij : i ≠ j)
    (hil : i ≠ l) (hjl : j ≠ l) {ε a b b' : ℝ} (hε : 0 < ε) (ha : ε ≤ a)
    (hab : a < b) (hbb : b < b') (hb' : b' ≤ 1 - ε) :
    (criticalGenealogyLimit g k : Measure (GenealogySpace k))
        {z | (a < z.2 i j ∧ z.2 i j < b) ∧ (a < z.2 i l ∧ z.2 i l < b) ∧
          (a < z.2 j l ∧ z.2 j l < b)} ≤
      ENNReal.ofReal (tripleCard ^ 2 * (∫ t in Icc a b', g t ^ 2) ^ 2) := by
  set O : Set (GenealogySpace k) := {z | (a < z.2 i j ∧ z.2 i j < b) ∧
    (a < z.2 i l ∧ z.2 i l < b) ∧ (a < z.2 j l ∧ z.2 j l < b)} with hOdef
  have hc : ∀ p q : Fin k, Continuous fun z : GenealogySpace k ↦ z.2 p q := fun p q ↦
    (continuous_apply q).comp ((continuous_apply p).comp continuous_snd)
  have hband : ∀ p q : Fin k, IsOpen {z : GenealogySpace k | a < z.2 p q ∧ z.2 p q < b} :=
    fun p q ↦ (isOpen_lt continuous_const (hc p q)).inter (isOpen_lt (hc p q) continuous_const)
  have hO : IsOpen O := (hband i j).inter ((hband i l).inter (hband j l))
  have hlim := ProbabilityMeasure.le_liminf_measure_open_of_tendsto
    (tendsto_genealogyLaw_criticalGenealogyLimit hx hL1 hpos h2 k) hO
  refine hlim.trans ?_
  set J := ∫ t in Icc a b', g t ^ 2 with hJdef
  have hJint : IntegrableOn (fun t ↦ g t ^ 2) (Icc a b') volume :=
    (h2 a b' (by linarith) (by linarith) (by linarith)).1
  set coll : ℕ → ℝ := fun n ↦
    ((uniformVertex (xa n) n).prod (uniformVertex (xa n) n)).real {p | p.1 = p.2} with hcolldef
  set err : ℕ → ℝ := coalescenceIntervalErrorMax xa (1 / 2) g ε with herrdef
  have hcoll : Tendsto coll atTop (𝓝 0) :=
    tendsto_uniformVertex_collision hx (by norm_num : (1 / 2 : ℝ) < 1) hL1 hpos
  have herr : Tendsto err atTop (𝓝 0) := tendsto_coalescenceIntervalErrorMax hx
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1) hL1 hpos h2 hε
  have hreal : Tendsto (fun n ↦ 3 * coll n + tripleCard ^ 2 * (J + 2 * err n) ^ 2) atTop
      (𝓝 (tripleCard ^ 2 * J ^ 2)) := by
    have := (hcoll.const_mul 3).add ((((tendsto_const_nhds (x := J)).add
      (herr.const_mul 2)).pow 2).const_mul (tripleCard ^ 2))
    simpa using this
  have hbound := (ENNReal.continuous_ofReal.tendsto _).comp hreal
  refine (liminf_le_liminf ?_).trans_eq hbound.liminf_eq
  filter_upwards [eventually_gt_atTop 0, eventually_ge_atTop ⌈2 / (b - a)⌉₊,
    eventually_ge_atTop ⌈1 / (b' - b)⌉₊] with n hn0 hn1 hn2
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn0
  have hn1' : 2 ≤ (b - a) * n := by
    have := Nat.ceil_le.mp hn1
    rw [div_le_iff₀ (by linarith)] at this
    linarith
  have hn2' : 1 ≤ (b' - b) * n := by
    have := Nat.ceil_le.mp hn2
    rw [div_le_iff₀ (by linarith)] at this
    linarith
  have han : 0 ≤ a * n := mul_nonneg (by linarith) hnr.le
  obtain ⟨φb, hφb⟩ : ∃ m : ℕ, m = ⌊a * n⌋₊ + 1 := ⟨_, rfl⟩
  obtain ⟨φt, hφt⟩ : ∃ m : ℕ, m = ⌈b * n⌉₊ := ⟨_, rfl⟩
  have hφb1 : a * n < (φb : ℝ) := by
    rw [hφb]
    push_cast
    exact Nat.lt_floor_add_one _
  have hφb2 : (φb : ℝ) ≤ a * n + 1 := by
    rw [hφb]
    push_cast
    linarith [Nat.floor_le han]
  have hφt1 : b * n ≤ (φt : ℝ) := by
    rw [hφt]
    exact Nat.le_ceil _
  have hφt2 : (φt : ℝ) < b * n + 1 := by
    rw [hφt]
    exact Nat.ceil_lt_add_one (by nlinarith)
  have hbt : φb + 1 ≤ φt := by
    have : ((φb + 1 : ℕ) : ℝ) ≤ φt := by
      push_cast
      nlinarith
    exact_mod_cast this
  have hφtn' : (φt : ℝ) ≤ (1 - ε) * n := by nlinarith
  have htn : φt ≤ n := by
    have : (φt : ℝ) ≤ n := by nlinarith
    exact_mod_cast this
  let := sampledReverseVectorLaw_probability (xa n) (hx n).1 (k := k) (hx n).2
  have hsub : genealogyVector n ⁻¹' O ⊆ {q |
      (φb ≤ sourceCoalescenceTime n (q.2 i) (q.2 j) q.1 ∧
        sourceCoalescenceTime n (q.2 i) (q.2 j) q.1 < φt) ∧
      (φb ≤ sourceCoalescenceTime n (q.2 i) (q.2 l) q.1 ∧
        sourceCoalescenceTime n (q.2 i) (q.2 l) q.1 < φt) ∧
      (φb ≤ sourceCoalescenceTime n (q.2 j) (q.2 l) q.1 ∧
        sourceCoalescenceTime n (q.2 j) (q.2 l) q.1 < φt)} := by
    intro q hq
    simp only [mem_preimage, hOdef, mem_ofPred_eq, genealogyVector] at hq
    have key : ∀ c : ℕ, a < (c : ℝ) / n → (c : ℝ) / n < b → φb ≤ c ∧ c < φt := by
      intro c h1 h2
      rw [lt_div_iff₀ hnr] at h1
      rw [div_lt_iff₀ hnr] at h2
      refine ⟨?_, ?_⟩
      · rw [hφb]
        exact Nat.add_one_le_iff.mpr ((Nat.floor_lt han).mpr h1)
      · rw [hφt]
        exact Nat.lt_ceil.mpr h2
    exact ⟨key _ hq.1.1 hq.1.2, key _ hq.2.1.1 hq.2.1.2, key _ hq.2.2.1 hq.2.2.2⟩
  have hS := sampled_triple_window_le (xa n) (hx n).1 (hx n).2 hij hil hjl
    (by omega : φb ≤ φt) htn
  have hsumeq : ∑ m ∈ Finset.Ioc φb φt, coalescenceHazard (companionSchedule (xa n)) m =
      2 * coalescenceUpSum (xa n) φb (φt - φb) := by
    have := sum_companion_coalescenceHazard (xa n) (hx n).1 φb (φt - φb)
    rwa [show φb + (φt - φb) = φt by omega] at this
  have hsum0 : 0 ≤ ∑ m ∈ Finset.Ioc φb φt, coalescenceHazard (companionSchedule (xa n)) m :=
    Finset.sum_nonneg fun m hm ↦ companion_coalescenceHazard_nonneg (xa n) (hx n).1 (hx n).2
      ((Finset.mem_Ioc.mp hm).2.trans htn)
  have hinterval : CoalescenceInterval ε n (φb + 1) φt :=
    ⟨by omega, hbt, htn, by push_cast; nlinarith, hφtn'⟩
  have hle : coalescenceIntervalError xa (1 / 2) g n (φb + 1) φt ≤ err n :=
    coalescenceIntervalError_le_max hinterval
  have hint_le : ∫ t in Icc (((φb + 1 : ℕ) : ℝ) / n) ((φt : ℝ) / n), g t ^ 2 ≤ J := by
    apply setIntegral_mono_set hJint (ae_of_all _ fun t ↦ sq_nonneg (g t))
    refine LE.le.eventuallySubset (Icc_subset_Icc ?_ ?_)
    · rw [le_div_iff₀ hnr]
      push_cast
      linarith
    · rw [div_le_iff₀ hnr]
      nlinarith
  have hscale : ((n : ℝ) ^ (2 * (1 / 2 : ℝ)) / n) = 1 := by
    rw [show (2 : ℝ) * (1 / 2) = 1 by norm_num, Real.rpow_one, div_self hnr.ne']
  have hupper : ∑ m ∈ Finset.Ioc φb φt, coalescenceHazard (companionSchedule (xa n)) m ≤
      J + 2 * err n := by
    rw [hsumeq]
    have h' := hle
    unfold coalescenceIntervalError at h'
    rw [hscale, one_mul, abs_le] at h'
    simp only [Nat.add_sub_cancel, show φt + 1 - (φb + 1) = φt - φb by omega] at h'
    linarith [h'.2]
  rw [← ENNReal.ofReal_toReal (measure_ne_top _ O), ← measureReal_def]
  apply ENNReal.ofReal_le_ofReal
  have heq : (genealogyLaw hx k n : Measure (GenealogySpace k)).real O =
      (sampledReverseVectorLaw (xa n) n k).real (genealogyVector n ⁻¹' O) := by
    simp only [genealogyLaw, ProbabilityMeasure.coe_mk, measureReal_def]
    rw [Measure.map_apply (measurable_genealogyVector n) hO.measurableSet]
  rw [heq]
  refine (measureReal_mono hsub).trans (hS.trans ?_)
  have hsq := pow_le_pow_left₀ hsum0 hupper 2
  have := mul_le_mul_of_nonneg_left hsq (sq_nonneg tripleCard)
  simp only [hcolldef]
  linarith

/-- Triple mergers whose common value lies in `[η, 1 - η]` have probability zero. -/
theorem criticalGenealogyLimit_tripleMerger_band_null (hx : AdmissibleArray xa)
    (hL1 : HasL1ReciprocalProfile xa (1 / 2) g) (hpos : PositiveProfile g)
    (h2 : HasLocalSquareMomentProfile xa (1 / 2) g) {i j l : Fin k} (hij : i ≠ j)
    (hil : i ≠ l) (hjl : j ≠ l) {η : ℝ} (hη : 0 < η) (hη4 : η < 1 / 4) :
    (criticalGenealogyLimit g k : Measure (GenealogySpace k))
      {z | η ≤ z.2 i j ∧ z.2 i j ≤ 1 - η ∧ z.2 i l = z.2 i j ∧ z.2 j l = z.2 i j} = 0 := by
  set μ := (criticalGenealogyLimit g k : Measure (GenealogySpace k))
  apply le_antisymm _ bot_le
  apply ENNReal.le_of_forall_pos_le_add
  intro ε hε _
  have hεr : (0 : ℝ) < ε := by exact_mod_cast hε
  set A := η / 4 with hAdef
  set B := 1 - η / 4 with hBdef
  have hint : IntegrableOn (fun t ↦ g t ^ 2) (Icc A B) volume :=
    (h2 A B (by positivity) (by linarith) (by linarith)).1
  set G := ∫ t in Icc A B, g t ^ 2 with hGdef
  have hG : 0 ≤ G := setIntegral_nonneg measurableSet_Icc fun t _ ↦ sq_nonneg _
  set K := tripleCard ^ 2 with hKdef
  have hK : 0 ≤ K := sq_nonneg _
  have hD : 0 < 3 * K * G + 1 := by nlinarith [mul_nonneg hK hG]
  set ρ := (ε : ℝ) / (3 * K * G + 1) with hρdef
  have hρ : 0 < ρ := div_pos hεr hD
  obtain ⟨δ, hδ, hsmall⟩ := exists_uniform_small_interval_integral hint hρ
  obtain ⟨N, hN⟩ := exists_nat_gt (3 / δ + 4 / η)
  have h3δ : 0 ≤ 3 / δ := by positivity
  have h4η : 0 ≤ 4 / η := by positivity
  have hNpos : (0 : ℝ) < N := by linarith
  set h := (1 : ℝ) / N with hhdef
  have hh : 0 < h := by positivity
  have hh3 : 3 * h ≤ δ := by
    have h1 : 3 / δ < N := by linarith
    rw [div_lt_iff₀ hδ] at h1
    rw [hhdef, mul_one_div, div_le_iff₀ hNpos]
    linarith
  have hh4 : h ≤ η / 4 := by
    have h1 : 4 / η < N := by linarith
    rw [div_lt_iff₀ hη] at h1
    rw [hhdef, div_le_iff₀ hNpos]
    linarith
  set b₀ := η / 2 - h with hb₀def
  set W := ⌊(1 - 3 * η / 2) * N⌋₊ + 1 with hWdef
  have hWh : ((W : ℝ) - 1) * h ≤ 1 - 3 * η / 2 := by
    have h1 : (⌊(1 - 3 * η / 2) * N⌋₊ : ℝ) ≤ (1 - 3 * η / 2) * N :=
      Nat.floor_le (by nlinarith)
    have h2 : ((W : ℝ) - 1) = ⌊(1 - 3 * η / 2) * N⌋₊ := by
      rw [hWdef]
      push_cast
      ring
    rw [h2, hhdef, mul_one_div, div_le_iff₀ hNpos]
    exact h1
  set O : ℕ → Set (GenealogySpace k) := fun w ↦
    {z | (b₀ + w * h < z.2 i j ∧ z.2 i j < b₀ + (w + 2) * h) ∧
      (b₀ + w * h < z.2 i l ∧ z.2 i l < b₀ + (w + 2) * h) ∧
      (b₀ + w * h < z.2 j l ∧ z.2 j l < b₀ + (w + 2) * h)} with hOdef
  set Jw : ℕ → ℝ := fun w ↦ ∫ t in Icc (b₀ + w * h) (b₀ + (w + 3) * h), g t ^ 2 with hJwdef
  have hwinA : ∀ w : ℕ, A ≤ b₀ + w * h := fun w ↦ by
    have : 0 ≤ (w : ℝ) * h := mul_nonneg (Nat.cast_nonneg w) hh.le
    linarith
  have hwinB : ∀ w ∈ Finset.range W, b₀ + (w + 3) * h ≤ 1 - η / 2 := by
    intro w hw
    have hw' : (w : ℝ) ≤ W - 1 := by
      have := Finset.mem_range.mp hw
      have : ((w + 1 : ℕ) : ℝ) ≤ W := by exact_mod_cast this
      push_cast at this
      linarith
    have : (w : ℝ) * h ≤ ((W : ℝ) - 1) * h := mul_le_mul_of_nonneg_right hw' hh.le
    nlinarith
  have hO : ∀ w ∈ Finset.range W, μ (O w) ≤ ENNReal.ofReal (K * Jw w ^ 2) := fun w hw ↦
    criticalGenealogyLimit_tripleWindow_le hx hL1 hpos h2 hij hil hjl (ε := A) (by positivity)
      (hwinA w) (by nlinarith) (by nlinarith) (by linarith [hwinB w hw])
  have hJ0 : ∀ w, 0 ≤ Jw w := fun w ↦ setIntegral_nonneg measurableSet_Icc fun t _ ↦ sq_nonneg _
  have hJρ : ∀ w ∈ Finset.range W, Jw w ≤ ρ := fun w hw ↦
    hsmall _ _ (hwinA w) (by nlinarith) (by linarith [hwinB w hw]) (by nlinarith)
  have hsumJ : ∑ w ∈ Finset.range W, Jw w ≤ 3 * G := by
    refine sum_window_integral_le hint (fun t ↦ sq_nonneg _) (by simpa using hwinA 0) hh W ?_
    have : ((W : ℝ) - 1) * h + 3 * h ≤ 1 - 3 * η / 2 + η / 4 * 3 := by linarith
    nlinarith
  have hcover : {z : GenealogySpace k | η ≤ z.2 i j ∧ z.2 i j ≤ 1 - η ∧ z.2 i l = z.2 i j ∧
      z.2 j l = z.2 i j} ⊆ ⋃ w ∈ Finset.range W, O w := by
    rintro z ⟨hc1, hc2, hc3, hc4⟩
    have hc0 : 0 ≤ (z.2 i j - η / 2) * N := by nlinarith
    obtain ⟨w, hwdef⟩ : ∃ w : ℕ, w = ⌊(z.2 i j - η / 2) * N⌋₊ := ⟨_, rfl⟩
    have hw1 : (w : ℝ) ≤ (z.2 i j - η / 2) * N := by rw [hwdef]; exact Nat.floor_le hc0
    have hw2 : (z.2 i j - η / 2) * N < w + 1 := by rw [hwdef]; exact Nat.lt_floor_add_one _
    have hwW : w < W := by
      have : w ≤ ⌊(1 - 3 * η / 2) * N⌋₊ := by
        rw [hwdef]
        exact Nat.floor_le_floor (by nlinarith)
      omega
    have hlo : b₀ + w * h < z.2 i j := by
      have : (w : ℝ) * h ≤ z.2 i j - η / 2 := by
        rw [hhdef, mul_one_div, div_le_iff₀ hNpos]
        exact hw1
      linarith
    have hhi : z.2 i j < b₀ + (w + 2) * h := by
      have : z.2 i j - η / 2 < ((w : ℝ) + 1) * h := by
        rw [hhdef, mul_one_div, lt_div_iff₀ hNpos]
        exact hw2
      have e : b₀ + ((w : ℝ) + 2) * h = η / 2 + ((w : ℝ) + 1) * h := by
        rw [hb₀def]
        ring
      linarith
    refine mem_iUnion₂.mpr ⟨w, Finset.mem_range.mpr hwW, ?_⟩
    simp only [hOdef, mem_ofPred_eq, hc3, hc4]
    exact ⟨⟨hlo, hhi⟩, ⟨hlo, hhi⟩, ⟨hlo, hhi⟩⟩
  have hreal : ∑ w ∈ Finset.range W, K * Jw w ^ 2 ≤ ε := by
    calc ∑ w ∈ Finset.range W, K * Jw w ^ 2 ≤ ∑ w ∈ Finset.range W, K * ρ * Jw w :=
          Finset.sum_le_sum fun w hw ↦ by
            have := mul_le_mul_of_nonneg_right (hJρ w hw) (hJ0 w)
            have := mul_le_mul_of_nonneg_left this hK
            nlinarith
      _ = K * ρ * ∑ w ∈ Finset.range W, Jw w := by rw [Finset.mul_sum]
      _ ≤ K * ρ * (3 * G) := mul_le_mul_of_nonneg_left hsumJ (mul_nonneg hK hρ.le)
      _ = ε * (3 * K * G / (3 * K * G + 1)) := by
          rw [hρdef]
          field_simp
      _ ≤ ε * 1 := mul_le_mul_of_nonneg_left ((div_le_one hD).mpr (by linarith)) hεr.le
      _ = ε := mul_one _
  calc μ {z | η ≤ z.2 i j ∧ z.2 i j ≤ 1 - η ∧ z.2 i l = z.2 i j ∧ z.2 j l = z.2 i j}
      ≤ μ (⋃ w ∈ Finset.range W, O w) := measure_mono hcover
    _ ≤ ∑ w ∈ Finset.range W, μ (O w) := measure_biUnion_finset_le _ _
    _ ≤ ∑ w ∈ Finset.range W, ENNReal.ofReal (K * Jw w ^ 2) := Finset.sum_le_sum hO
    _ = ENNReal.ofReal (∑ w ∈ Finset.range W, K * Jw w ^ 2) :=
        (ENNReal.ofReal_sum_of_nonneg fun w _ ↦ mul_nonneg hK (sq_nonneg _)).symm
    _ ≤ ENNReal.ofReal ε := ENNReal.ofReal_le_ofReal hreal
    _ = ⊥ + (ε : ENNReal) := by rw [bot_eq_zero, zero_add, ENNReal.ofReal_coe_nnreal]

/-- Scaled birth times of the limit are almost surely below one. -/
theorem criticalGenealogyLimit_birth_ge_one_null (hx : AdmissibleArray xa)
    (hL1 : HasL1ReciprocalProfile xa (1 / 2) g) (hpos : PositiveProfile g)
    (h2 : HasLocalSquareMomentProfile xa (1 / 2) g) {i j : Fin k} (hij : i ≠ j) :
    (criticalGenealogyLimit g k : Measure (GenealogySpace k)) {z | 1 ≤ z.1 i} = 0 := by
  apply le_antisymm _ bot_le
  apply ENNReal.le_of_forall_pos_le_add
  intro η hη _
  have hθ : (0 : ℝ) < min (η : ℝ) (1 / 2) := lt_min (by exact_mod_cast hη) (by norm_num)
  have hr0 : (0 : ℝ) ≤ 1 - min (η : ℝ) (1 / 2) := by linarith [min_le_right (η : ℝ) (1 / 2)]
  have hsub : {z : GenealogySpace k | 1 ≤ z.1 i} ⊆ {z | 1 - min (η : ℝ) (1 / 2) < z.1 i} :=
    fun z (hz : 1 ≤ z.1 i) ↦ by show 1 - min (η : ℝ) (1 / 2) < z.1 i; linarith
  refine (measure_mono hsub).trans ((criticalGenealogyLimit_birth_gt_le hx hL1 hpos h2 hij hr0
      (by linarith)).trans ?_)
  rw [bot_eq_zero, zero_add, sub_sub_cancel]
  exact (ENNReal.ofReal_le_ofReal (min_le_left _ _)).trans_eq (ENNReal.ofReal_coe_nnreal)

/-- **No triple mergers.** In the critical limit, three distinct samples almost surely do
not share a common positive pairwise coalescence time. -/
theorem criticalGenealogyLimit_tripleMerger_null (hx : AdmissibleArray xa)
    (hL1 : HasL1ReciprocalProfile xa (1 / 2) g) (hpos : PositiveProfile g)
    (h2 : HasLocalSquareMomentProfile xa (1 / 2) g) {i j l : Fin k} (hij : i ≠ j)
    (hil : i ≠ l) (hjl : j ≠ l) :
    (criticalGenealogyLimit g k : Measure (GenealogySpace k))
      {z | 0 < z.2 i j ∧ z.2 i l = z.2 i j ∧ z.2 j l = z.2 i j} = 0 := by
  set μ := (criticalGenealogyLimit g k : Measure (GenealogySpace k))
  have hsupp : μ (genealogySupport k)ᶜ = 0 :=
    (prob_compl_eq_zero_iff (isClosed_genealogySupport k).measurableSet).mpr
      (criticalGenealogyLimit_support hx hL1 hpos h2 k)
  have hhigh : μ {z | 1 ≤ z.1 i} = 0 :=
    criticalGenealogyLimit_birth_ge_one_null hx hL1 hpos h2 hij
  have hmid : ∀ m : ℕ, μ {z | 1 / ((m : ℝ) + 5) ≤ z.2 i j ∧ z.2 i j ≤ 1 - 1 / ((m : ℝ) + 5) ∧
      z.2 i l = z.2 i j ∧ z.2 j l = z.2 i j} = 0 := fun m ↦
    criticalGenealogyLimit_tripleMerger_band_null hx hL1 hpos h2 hij hil hjl (by positivity)
      (by rw [div_lt_iff₀ (by positivity)]; linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)])
  apply measure_mono_null (t := (genealogySupport k)ᶜ ∪ {z | 1 ≤ z.1 i} ∪ ⋃ m : ℕ,
    {z | 1 / ((m : ℝ) + 5) ≤ z.2 i j ∧ z.2 i j ≤ 1 - 1 / ((m : ℝ) + 5) ∧
      z.2 i l = z.2 i j ∧ z.2 j l = z.2 i j})
  · rintro z ⟨hc0, hc3, hc4⟩
    by_cases hs : z ∈ genealogySupport k
    swap
    · exact Or.inl (Or.inl hs)
    by_cases h1 : 1 ≤ z.1 i
    · exact Or.inl (Or.inr h1)
    have h1' : z.1 i < 1 := not_le.mp h1
    have hci : z.2 i j ≤ z.1 i := by
      have h := hs.2.2 i i j
      rw [hs.2.1 j i, min_self, hs.1 i] at h
      exact h
    have hp : 0 < min (z.2 i j) (1 - z.2 i j) := lt_min hc0 (by linarith)
    obtain ⟨m, hm⟩ := exists_nat_one_div_lt hp
    have hle : 1 / ((m : ℝ) + 5) ≤ 1 / ((m : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by linarith)
    refine Or.inr (mem_iUnion.mpr ⟨m, ?_, ?_, hc3, hc4⟩)
    · linarith [min_le_left (z.2 i j) (1 - z.2 i j)]
    · linarith [min_le_right (z.2 i j) (1 - z.2 i j)]
  · exact measure_union_null (measure_union_null hsupp hhigh) (measure_iUnion_null hmid)

end Limit

end Freezing2.CriticalGenealogy
