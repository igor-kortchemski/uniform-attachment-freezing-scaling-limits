module

public import Freezing2.Probability.CoalescentDensity

/-!
# Decoding the coalescent genealogy, and side claims of the construction

This file completes Proposition `loi du coalescent généralisé` (inventory N11) in the source's
form, as the law of the genealogy forest, births and merge times `(F, B, C)`, and proves the
side claims U23 of the continuous coalescent.

## Decoding

`decodeHistory : GenealogySpace k → HistorySpace k` recovers the merge history from births
and pairwise coalescence times. The merge times are the distinct positive off-diagonal
values in decreasing order (`topVal`), and after the `i`-th merge two labels are related when
their coalescence time is at least the `i`-th merge time. The history space is the sigma
type `Σ m, (Fin m → ConnState k) × (Fin k → ℝ) × (Fin m → ℝ)` (number of merges, merge
history, births, merge times).

* `measurable_decodeHistory`: the decoding map is measurable.
* `decodeHistory_genealogyOf`: it inverts `genealogyOf` on admissible histories.
* `map_decodeHistory_criticalGenealogyLimit`: under the limiting genealogy law, `(F, B, C)`
  has the law `historyLaw g k`, which has density `historyDensity` against Lebesgue measure
  on each fibre `(m, xs)`. This is N11 in history form; the bijection with the source's
  labelled plane forests and its admissibility via increasing bijections is in
  `CoalescentForests` (`sourceForest_law`).
* `planeLaw_eq_uniformOrders`, `map_forgetOrders_planeLaw`: the plane version. Every child
  order receives the same weight `2^{-m}`, and forgetting the orders gives back the law of
  `(F, B, C)`.

## Measurable modifications of the profile

`isGenealogyLimit_congr` and `criticalGenealogyLimit_congr`: the limit characterization only
depends on the integrals of `g²` on windows inside `(0, 1)`, so it is unchanged when `g` is
modified on a null subset of `(0, 1)`.
`tendsto_genealogyLaw_coalescentLaw_of_profile` drops the measurability hypothesis: under the
source hypotheses alone, the limit is the coalescent law of a measurable modification of `g`.

## Side claims (U23)

* `ae_mergeTimes_strictAnti`: almost surely the genealogy is that of an admissible binary
  history with distinct (strictly decreasing) positive merge times.
* `coalescentLaw_noMerger_pos`: if `∫₀^{1/2} g² < ∞`, then with positive probability no two
  particles ever merge.
* `coalescentLaw_allMerge`: if `∫₀^{1/2} g² = ∞`, then almost surely all pairwise
  coalescence times are positive, so all particles end in one cluster.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace Freezing2.CoalescentDensity

open TrackedGenealogy CriticalGenealogy ContinuousCoalescent

/-! ### Measurability on sigma types -/

section SigmaMeasurable

variable {β : ℕ → Type*} [∀ m, MeasurableSpace (β m)]

theorem measurableSet_sigma_iff {S : Set (Σ m, β m)} :
    MeasurableSet S ↔ ∀ m, MeasurableSet (Sigma.mk m ⁻¹' S) := by
  change MeasurableSet[⨅ m, _] S ↔ _
  rw [MeasurableSpace.measurableSet_iInf]
  rfl

theorem measurable_sigmaMk (m : ℕ) : Measurable (Sigma.mk (β := β) m) :=
  fun _ hS ↦ measurableSet_sigma_iff.mp hS m

/-- A map into a sigma type over `ℕ` is measurable when its index is measurable and each
of its fibre components is measurable. -/
theorem measurable_sigma_of_fibres {X : Type*} [MeasurableSpace X] {M : X → ℕ}
    (hM : Measurable M) {G : ∀ m, X → β m} (hG : ∀ m, Measurable (G m)) :
    Measurable (fun x ↦ (⟨M x, G (M x) x⟩ : Σ m, β m)) := by
  intro S hS
  have hset : (fun x ↦ (⟨M x, G (M x) x⟩ : Σ m, β m)) ⁻¹' S =
      ⋃ m, (M ⁻¹' {m}) ∩ (G m ⁻¹' (Sigma.mk m ⁻¹' S)) := by
    ext x
    simp only [mem_preimage, mem_iUnion, mem_inter_iff, mem_singleton_iff]
    constructor
    · intro h
      exact ⟨M x, rfl, h⟩
    · rintro ⟨m, rfl, h⟩
      exact h
  rw [hset]
  exact MeasurableSet.iUnion fun m ↦
    (hM (measurableSet_singleton m)).inter (hG m (measurableSet_sigma_iff.mp hS m))

/-- A map out of a sigma type over `ℕ` is measurable when it is measurable on each fibre. -/
theorem measurable_sigma_elim {Y : Type*} [MeasurableSpace Y] {f : (Σ m, β m) → Y}
    (hf : ∀ m, Measurable (fun q : β m ↦ f ⟨m, q⟩)) : Measurable f :=
  fun _ hT ↦ measurableSet_sigma_iff.mpr fun m ↦ hf m hT

end SigmaMeasurable

variable {k : ℕ}

/-! ### Facts on admissible histories -/

section HistoryFacts

variable {b : Fin k → ℝ}

theorem IsAdmissible.state_mono {m : ℕ} : ∀ {t : ℝ} {x : ConnState k}
    {xs : Fin m → ConnState k} {cs : Fin m → ℝ}, IsAdmissible b m t x xs cs →
      ∀ {j l : Fin k}, x j l = true → ∀ i, xs i j l = true := by
  induction m with
  | zero => intro t x xs cs _ j l _ i; exact i.elim0
  | succ m ih =>
    intro t x xs cs h j l hx i
    obtain ⟨-, hm, ha⟩ := h
    refine Fin.cases (hm.ge hx) (fun i ↦ ?_) i
    exact ih ha (hm.ge hx) i

theorem IsAdmissible.strictAnti {m : ℕ} : ∀ {t : ℝ} {x : ConnState k}
    {xs : Fin m → ConnState k} {cs : Fin m → ℝ}, IsAdmissible b m t x xs cs → StrictAnti cs := by
  induction m with
  | zero => intro t x xs cs _ a; exact a.elim0
  | succ m ih =>
    intro t x xs cs h a c hac
    obtain ⟨-, -, ha⟩ := h
    induction a using Fin.cases with
    | zero =>
      obtain ⟨c', rfl⟩ := Fin.exists_succ_eq.mpr (ne_of_gt hac)
      exact (ha.time_mem c').2
    | succ a =>
      obtain ⟨c', rfl⟩ := Fin.exists_succ_eq.mpr (ne_of_gt (lt_trans (Fin.succ_pos a) hac))
      exact ih ha (Fin.succ_lt_succ_iff.mp hac)

theorem coalTime_eq_zero_or {m : ℕ} : ∀ {t : ℝ} {x : ConnState k} {xs : Fin m → ConnState k}
    {cs : Fin m → ℝ} {j l : Fin k}, x j l = false →
      coalTime m t x xs cs j l = 0 ∨ ∃ i, coalTime m t x xs cs j l = cs i := by
  induction m with
  | zero =>
    intro t x xs cs j l hx
    left
    simp [coalTime, hx]
  | succ m ih =>
    intro t x xs cs j l hx
    simp only [coalTime, hx, Bool.false_eq_true, ↓reduceIte]
    by_cases h0 : xs 0 j l = true
    · exact Or.inr ⟨0, coalTime_of_true h0⟩
    · rcases ih (Bool.eq_false_iff.mpr h0) with h | ⟨i, hi⟩
      · exact Or.inl h
      · exact Or.inr ⟨i.succ, hi⟩

theorem IsAdmissible.coalTime_attained {m : ℕ} : ∀ {t : ℝ} {x : ConnState k}
    {xs : Fin m → ConnState k} {cs : Fin m → ℝ}, IsAdmissible b m t x xs cs →
      (∀ j, x j j = true) → ∀ i, ∃ j l, j ≠ l ∧ x j l = false ∧
        coalTime m t x xs cs j l = cs i := by
  induction m with
  | zero => intro t x xs cs _ _ i; exact i.elim0
  | succ m ih =>
    intro t x xs cs h hrefl i
    obtain ⟨-, hm, ha⟩ := h
    induction i using Fin.cases with
    | zero =>
      obtain ⟨-, j₀, -, l₀, -, hs, hx0⟩ := hm
      refine ⟨j₀, l₀, fun he ↦ ?_, hs, ?_⟩
      · rw [he, hrefl] at hs
        exact Bool.noConfusion hs
      · have h0 : xs 0 j₀ l₀ = true := by
          rw [hx0, mergeState_iff]
          exact Or.inr (Or.inl ⟨hrefl j₀, hrefl l₀⟩)
        simp only [coalTime, hs, Bool.false_eq_true, ↓reduceIte]
        exact coalTime_of_true h0
    | succ i =>
      obtain ⟨j, l, hjl, hx0, hc⟩ := ih ha (fun j ↦ hm.ge (hrefl j)) i
      have hx : x j l = false := by
        by_contra hc'
        rw [Bool.not_eq_false] at hc'
        rw [hm.ge hc'] at hx0
        exact Bool.noConfusion hx0
      refine ⟨j, l, hjl, hx, ?_⟩
      simp only [coalTime, hx, Bool.false_eq_true, ↓reduceIte]
      exact hc

theorem IsAdmissible.coalTime_lt {m : ℕ} {t : ℝ} {x : ConnState k} {xs : Fin m → ConnState k}
    {cs : Fin m → ℝ} (h : IsAdmissible b m t x xs cs) (ht : 0 < t) {j l : Fin k}
    (hx : x j l = false) : coalTime m t x xs cs j l < t := by
  rcases coalTime_eq_zero_or (t := t) (xs := xs) (cs := cs) hx with h0 | ⟨i, hi⟩
  · rw [h0]
    exact ht
  · rw [hi]
    exact (h.time_mem i).2

theorem IsAdmissible.state_iff {m : ℕ} : ∀ {t : ℝ} {x : ConnState k}
    {xs : Fin m → ConnState k} {cs : Fin m → ℝ}, IsAdmissible b m t x xs cs →
      ∀ {j l : Fin k}, x j l = false → ∀ i,
        (xs i j l = true ↔ cs i ≤ coalTime m t x xs cs j l) := by
  induction m with
  | zero => intro t x xs cs _ j l _ i; exact i.elim0
  | succ m ih =>
    intro t x xs cs h j l hx i
    obtain ⟨hc, hm, ha⟩ := h
    have hct : coalTime (m + 1) t x xs cs j l =
        coalTime m (cs 0) (xs 0) (Fin.tail xs) (Fin.tail cs) j l := by
      simp [coalTime, hx]
    rw [hct]
    induction i using Fin.cases with
    | zero =>
      constructor
      · intro h0
        rw [coalTime_of_true h0]
      · intro hle
        by_contra h0
        have := ha.coalTime_lt hc.1 (Bool.eq_false_iff.mpr h0)
        linarith
    | succ i =>
      by_cases h0 : xs 0 j l = true
      · rw [coalTime_of_true h0]
        have hti : xs i.succ j l = true := ha.state_mono h0 i
        have hlt : cs i.succ < cs 0 := (ha.time_mem i).2
        exact ⟨fun _ ↦ hlt.le, fun _ ↦ hti⟩
      · exact ih ha (Bool.eq_false_iff.mpr h0) i

end HistoryFacts

/-! ### The decoding of a genealogy -/

/-- The distinct positive off-diagonal values of `C` in decreasing order, padded with `0`:
`topVal C 0` is the largest one, and `topVal C (i + 1)` the largest one below `topVal C i`. -/
noncomputable def topVal (C : Fin k → Fin k → ℝ) : ℕ → ℝ
  | 0 => (Finset.univ : Finset (Fin k × Fin k)).fold max 0 fun p ↦
      open Classical in if p.1 ≠ p.2 ∧ 0 < C p.1 p.2 then C p.1 p.2 else 0
  | i + 1 => (Finset.univ : Finset (Fin k × Fin k)).fold max 0 fun p ↦
      open Classical in if p.1 ≠ p.2 ∧ 0 < C p.1 p.2 ∧ C p.1 p.2 < topVal C i then C p.1 p.2 else 0

/-- Histories: number of merges, merge history, births and merge times. -/
abbrev HistorySpace (k : ℕ) := Σ m : ℕ, (Fin m → ConnState k) × (Fin k → ℝ) × (Fin m → ℝ)

/-- The decoded number of merges: the number of distinct positive off-diagonal values. -/
noncomputable def decCount (z : GenealogySpace k) : ℕ :=
  (Finset.univ.filter fun i : Fin (k * k) ↦ 0 < topVal z.2 i).card

/-- The decoded merge times. -/
noncomputable def decTimes (z : GenealogySpace k) (m : ℕ) : Fin m → ℝ := fun i ↦ topVal z.2 i

/-- The decoded states: after the `i`-th merge, two labels are related when their
coalescence time is at least the `i`-th merge time. -/
noncomputable def decStates (z : GenealogySpace k) (m : ℕ) : Fin m → ConnState k :=
  fun i j l ↦ open Classical in if j = l then true else decide (topVal z.2 i ≤ z.2 j l)

/-- **The decoding map** from births and pairwise coalescence times to the merge history. -/
noncomputable def decodeHistory (z : GenealogySpace k) : HistorySpace k :=
  ⟨decCount z, (decStates z (decCount z), z.1, decTimes z (decCount z))⟩

/-- The genealogy (births and pairwise coalescence times) of a history. -/
noncomputable def genealogyOfHistory (h : HistorySpace k) : GenealogySpace k :=
  genealogyOf h.1 h.2.1 h.2.2.1 h.2.2.2

/-- Admissibility of a history from singletons at time `1`. -/
def HistoryAdmissible (h : HistorySpace k) : Prop :=
  IsAdmissible h.2.2.1 h.1 1 diagState h.2.1 h.2.2.2

theorem fold_max_eq {ι : Type*} (s : Finset ι) (f : ι → ℝ) {v : ℝ} (hv : 0 ≤ v)
    (hle : ∀ p ∈ s, f p ≤ v) (hatt : v = 0 ∨ ∃ p ∈ s, f p = v) : s.fold max 0 f = v := by
  refine le_antisymm ((Finset.fold_max_le v).mpr ⟨hv, hle⟩) ((Finset.le_fold_max v).mpr ?_)
  rcases hatt with h | ⟨p, hp, hfp⟩
  · exact Or.inl h.le
  · exact Or.inr ⟨p, hp, hfp.ge⟩

theorem topVal_genealogyOf {b : Fin k → ℝ} {m : ℕ} {xs : Fin m → ConnState k} {cs : Fin m → ℝ}
    (h : IsAdmissible b m 1 diagState xs cs) :
    ∀ i : ℕ, (∀ hi : i < m, topVal (genealogyOf m xs b cs).2 i = cs ⟨i, hi⟩) ∧
      (m ≤ i → topVal (genealogyOf m xs b cs).2 i = 0) := by
  classical
  set C := (genealogyOf m xs b cs).2 with hC
  have hCjl : ∀ j l, j ≠ l → C j l = coalTime m 1 diagState xs cs j l := by
    intro j l hjl
    simp [hC, genealogyOf, hjl]
  have hdiag : ∀ {j l : Fin k}, j ≠ l → diagState j l = false := by
    intro j l hjl
    simp [diagState, hjl]
  have hpos : ∀ j l, j ≠ l → 0 < C j l → ∃ i, C j l = cs i := by
    intro j l hjl hp
    rw [hCjl j l hjl] at hp ⊢
    rcases coalTime_eq_zero_or (t := 1) (xs := xs) (cs := cs) (hdiag hjl) with h0 | hi
    · rw [h0] at hp
      exact absurd hp (lt_irrefl 0)
    · exact hi
  have hatt : ∀ i, ∃ j l, j ≠ l ∧ C j l = cs i := by
    intro i
    obtain ⟨j, l, hjl, -, hc⟩ := h.coalTime_attained (fun j ↦ by simp [diagState]) i
    exact ⟨j, l, hjl, (hCjl j l hjl).trans hc⟩
  have hanti := h.strictAnti
  have hcpos : ∀ i, 0 < cs i := fun i ↦ (h.time_mem i).1
  intro i
  induction i with
  | zero =>
    refine ⟨fun hi ↦ ?_, fun hi ↦ ?_⟩
    · refine fold_max_eq _ _ (hcpos _).le (fun p _ ↦ ?_) (Or.inr ?_)
      · split_ifs with hp
        · obtain ⟨i', hi'⟩ := hpos p.1 p.2 hp.1 hp.2
          rw [hi']
          exact hanti.antitone (show (⟨0, hi⟩ : Fin m) ≤ i' from Nat.zero_le _)
        · exact (hcpos _).le
      · obtain ⟨j, l, hjl, hc⟩ := hatt ⟨0, hi⟩
        refine ⟨(j, l), Finset.mem_univ _, ?_⟩
        simp only
        rw [ite_eq_left ⟨hjl, hc ▸ hcpos _⟩, hc]
    · refine fold_max_eq _ _ le_rfl (fun p _ ↦ ?_) (Or.inl rfl)
      split_ifs with hp
      · obtain ⟨i', -⟩ := hpos p.1 p.2 hp.1 hp.2
        exact absurd i'.2 (by omega)
      · exact le_rfl
  | succ i ih =>
    have htop : topVal C (i + 1) = (Finset.univ : Finset (Fin k × Fin k)).fold max 0 fun p ↦
        if p.1 ≠ p.2 ∧ 0 < C p.1 p.2 ∧ C p.1 p.2 < topVal C i then C p.1 p.2 else 0 := rfl
    by_cases hi : i < m
    · rw [ih.1 hi] at htop
      refine ⟨fun hi1 ↦ ?_, fun hi1 ↦ ?_⟩
      · rw [htop]
        refine fold_max_eq _ _ (hcpos _).le (fun p _ ↦ ?_) (Or.inr ?_)
        · split_ifs with hp
          · obtain ⟨i', hi'⟩ := hpos p.1 p.2 hp.1 hp.2.1
            rw [hi'] at hp ⊢
            have : i < i'.val := by
              by_contra hle
              exact absurd hp.2.2 (not_lt.mpr (hanti.antitone (Fin.mk_le_mk.mpr (by omega))))
            exact hanti.antitone (Fin.mk_le_mk.mpr (by omega))
          · exact (hcpos _).le
        · obtain ⟨j, l, hjl, hc⟩ := hatt ⟨i + 1, hi1⟩
          refine ⟨(j, l), Finset.mem_univ _, ?_⟩
          simp only
          rw [ite_eq_left ⟨hjl, hc ▸ hcpos _, hc ▸ hanti (Fin.mk_lt_mk.mpr (by omega))⟩, hc]
      · rw [htop]
        refine fold_max_eq _ _ le_rfl (fun p _ ↦ ?_) (Or.inl rfl)
        split_ifs with hp
        · obtain ⟨i', hi'⟩ := hpos p.1 p.2 hp.1 hp.2.1
          rw [hi'] at hp
          have : i < i'.val := by
            by_contra hle
            exact absurd hp.2.2 (not_lt.mpr (hanti.antitone (Fin.mk_le_mk.mpr (by omega))))
          exact absurd i'.2 (by omega)
        · exact le_rfl
    · rw [ih.2 (by omega)] at htop
      refine ⟨fun hi1 ↦ absurd hi1 (by omega), fun _ ↦ ?_⟩
      rw [htop]
      refine fold_max_eq _ _ le_rfl (fun p _ ↦ ?_) (Or.inl rfl)
      split_ifs with hp
      · exact absurd (hp.2.1.trans hp.2.2) (lt_irrefl 0)
      · exact le_rfl

theorem card_filter_fin_lt {n m : ℕ} (h : m ≤ n) :
    (Finset.univ.filter fun i : Fin n ↦ (i : ℕ) < m).card = m := by
  have : (Finset.univ.filter fun i : Fin n ↦ (i : ℕ) < m) =
      (Finset.univ : Finset (Fin m)).map (Fin.castLEEmb h) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map, Fin.castLEEmb_apply]
    constructor
    · intro hi
      exact ⟨⟨i, hi⟩, rfl⟩
    · rintro ⟨j, rfl⟩
      exact j.2
  rw [this, Finset.card_map, Finset.card_univ, Fintype.card_fin]

/-- **Decoding inverts the genealogy map on admissible histories.** -/
theorem decodeHistory_genealogyOf {b : Fin k → ℝ} {m : ℕ} {xs : Fin m → ConnState k}
    {cs : Fin m → ℝ} (h : IsAdmissible b m 1 diagState xs cs) :
    decodeHistory (genealogyOf m xs b cs) = ⟨m, (xs, b, cs)⟩ := by
  classical
  set z := genealogyOf m xs b cs with hz
  have htop := topVal_genealogyOf h
  have hmk : m ≤ k * k := h.le_card_sub_one.trans ((Nat.sub_le k 1).trans (Nat.le_mul_self k))
  have hcount : decCount z = m := by
    unfold decCount
    rw [← card_filter_fin_lt hmk]
    congr 1
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hp
      by_contra hle
      rw [(htop i).2 (not_lt.mp hle)] at hp
      exact lt_irrefl 0 hp
    · intro hi
      rw [(htop i).1 hi]
      exact (h.time_mem _).1
  have htimes : decTimes z m = cs := by
    funext i
    exact (htop i).1 i.2
  have hstates : decStates z m = xs := by
    funext i j l
    simp only [decStates]
    by_cases hjl : j = l
    · subst hjl
      rw [ite_eq_left rfl]
      exact (h.state_mono (by simp [diagState]) i).symm
    · rw [ite_eq_right hjl, (htop i).1 i.2]
      have hiff := h.state_iff (j := j) (l := l) (by simp [diagState, hjl]) i
      have hzjl : z.2 j l = coalTime m 1 diagState xs cs j l := by simp [hz, genealogyOf, hjl]
      rw [hzjl]
      exact Bool.eq_iff_iff.mpr (by rw [decide_eq_true_iff]; exact hiff.symm)
  have key : ∀ n, n = m → (⟨n, (decStates z n, z.1, decTimes z n)⟩ : HistorySpace k) =
      ⟨m, (xs, b, cs)⟩ := by
    intro n hn
    subst hn
    rw [hstates, htimes]
    rfl
  exact key _ hcount

/-! ### Measurability of the decoding -/

theorem measurable_fold_max {X ι : Type*} [MeasurableSpace X] (s : Finset ι)
    {f : ι → X → ℝ} (hf : ∀ i, Measurable (f i)) :
    Measurable (fun x ↦ s.fold max 0 fun i ↦ f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.fold_empty]
    exact measurable_const
  | @insert a s ha ih =>
    simp only [Finset.fold_insert ha]
    exact (hf a).max ih

theorem measurable_topVal (i : ℕ) : Measurable (fun C : Fin k → Fin k → ℝ ↦ topVal C i) := by
  classical
  have hC : ∀ p : Fin k × Fin k, Measurable (fun C : Fin k → Fin k → ℝ ↦ C p.1 p.2) := fun p ↦
    (measurable_pi_apply p.2).comp (measurable_pi_apply p.1)
  induction i with
  | zero =>
    simp only [topVal]
    refine measurable_fold_max _ fun p ↦ Measurable.ite ?_ (hC p) measurable_const
    exact (MeasurableSet.const _).inter (measurableSet_lt measurable_const (hC p))
  | succ i ih =>
    simp only [topVal]
    refine measurable_fold_max _ fun p ↦ Measurable.ite ?_ (hC p) measurable_const
    exact (MeasurableSet.const _).inter ((measurableSet_lt measurable_const (hC p)).inter
      (measurableSet_lt (hC p) ih))

theorem measurable_decCount : Measurable (decCount (k := k)) := by
  classical
  have hv : Measurable (fun z : GenealogySpace k ↦ fun i : Fin (k * k) ↦
      decide (0 < topVal z.2 i)) := by
    refine measurable_pi_iff.mpr fun i ↦ measurable_to_bool ?_
    have : (fun z : GenealogySpace k ↦ decide (0 < topVal z.2 i)) ⁻¹' {true} =
        {z | 0 < topVal z.2 i} := by
      ext z
      simp
    rw [this]
    exact measurableSet_lt measurable_const ((measurable_topVal i).comp measurable_snd)
  have heq : decCount (k := k) = (fun v : Fin (k * k) → Bool ↦
      (Finset.univ.filter fun i ↦ v i = true).card) ∘
        (fun z : GenealogySpace k ↦ fun i ↦ decide (0 < topVal z.2 i)) := by
    funext z
    simp [decCount]
  rw [heq]
  exact (measurable_of_countable _).comp hv

/-- **The decoding map is measurable.** -/
theorem measurable_decodeHistory : Measurable (decodeHistory (k := k)) := by
  classical
  have hG : ∀ m, Measurable (fun z : GenealogySpace k ↦ (decStates z m, z.1, decTimes z m)) := by
    intro m
    refine Measurable.prodMk ?_ (measurable_fst.prodMk ?_)
    · refine measurable_pi_iff.mpr fun i ↦ measurable_pi_iff.mpr fun j ↦
        measurable_pi_iff.mpr fun l ↦ ?_
      by_cases hjl : j = l
      · simp only [decStates, hjl, ↓reduceIte]
        exact measurable_const
      · simp only [decStates, hjl, ↓reduceIte]
        refine measurable_to_bool ?_
        have : (fun z : GenealogySpace k ↦ decide (topVal z.2 i ≤ z.2 j l)) ⁻¹' {true} =
            {z | topVal z.2 i ≤ z.2 j l} := by
          ext z
          simp
        rw [this]
        exact measurableSet_le ((measurable_topVal i).comp measurable_snd)
          ((measurable_pi_apply l).comp ((measurable_pi_apply j).comp measurable_snd))
    · exact measurable_pi_iff.mpr fun i ↦ (measurable_topVal i).comp measurable_snd
  exact measurable_sigma_of_fibres (β := fun m ↦ (Fin m → ConnState k) × (Fin k → ℝ) × (Fin m → ℝ))
    measurable_decCount (G := fun m z ↦ (decStates z m, z.1, decTimes z m)) hG

theorem measurable_genealogyOfHistory : Measurable (genealogyOfHistory (k := k)) :=
  measurable_sigma_elim fun m ↦ measurable_from_prod_countable_right fun xs ↦
    measurable_genealogyOf m xs

/-! ### The history law -/

/-- The history with `m` merges along `xs`, births `p.1` and merge times `p.2`. -/
def historyMk (m : ℕ) (xs : Fin m → ConnState k) (p : (Fin k → ℝ) × (Fin m → ℝ)) :
    HistorySpace k :=
  ⟨m, (xs, p.1, p.2)⟩

theorem measurable_historyMk (m : ℕ) (xs : Fin m → ConnState k) :
    Measurable (historyMk (k := k) m xs) := by
  have h := (measurable_sigmaMk (β := fun m ↦ (Fin m → ConnState k) × (Fin k → ℝ) × (Fin m → ℝ))
    m).comp (show Measurable (fun p : (Fin k → ℝ) × (Fin m → ℝ) ↦ (xs, p.1, p.2)) from
      measurable_const.prodMk (measurable_fst.prodMk measurable_snd))
  exact h

theorem measurableEmbedding_historyMk (m : ℕ) (xs : Fin m → ConnState k) :
    MeasurableEmbedding (historyMk (k := k) m xs) where
  injective p q h := by
    simp only [historyMk, Sigma.mk.inj_iff, heq_eq_eq, Prod.mk.injEq, true_and] at h
    exact Prod.ext h.1 h.2
  measurable := measurable_historyMk m xs
  measurableSet_image' A hA := by
    refine measurableSet_sigma_iff.mpr fun m' ↦ ?_
    by_cases hm : m' = m
    · subst hm
      have : Sigma.mk m' ⁻¹' (historyMk m' xs '' A) =
          {q : (Fin m' → ConnState k) × (Fin k → ℝ) × (Fin m' → ℝ) | q.1 = xs} ∩
            (fun q ↦ (q.2.1, q.2.2)) ⁻¹' A := by
        ext q
        simp only [mem_preimage, mem_image, historyMk, Sigma.mk.inj_iff, heq_eq_eq, true_and,
          mem_inter_iff, Set.mem_ofPred_eq]
        constructor
        · rintro ⟨p, hp, rfl⟩
          exact ⟨rfl, hp⟩
        · rintro ⟨h1, h2⟩
          exact ⟨(q.2.1, q.2.2), h2, by rw [← h1]⟩
      rw [this]
      exact (measurableSet_eq_fun measurable_fst measurable_const).inter
        ((measurable_snd.fst.prodMk measurable_snd.snd) hA)
    · have : Sigma.mk m' ⁻¹' (historyMk m xs '' A) = ∅ := by
        ext q
        simp only [mem_preimage, mem_image, historyMk, Sigma.mk.inj_iff, mem_empty_iff_false,
          iff_false, not_exists, not_and]
        intro p _ h
        exact absurd h.symm hm
      rw [this]
      exact MeasurableSet.empty

/-- **The law of `(F, B, C)`**: on each fibre `(m, xs)` of the history space, the measure
with density `historyDensity` against Lebesgue measure on births in `[0, 1]^k` and on the
merge times. -/
noncomputable def historyLaw (g : ℝ → ℝ) (k : ℕ) : Measure (HistorySpace k) :=
  Measure.sum fun m : ℕ ↦ ∑ xs : Fin m → ConnState k,
    (((cubeMeasure k).prod volume).withDensity fun p ↦ historyDensity g p.1 m xs p.2).map
      (historyMk m xs)

variable {g : ℝ → ℝ}

theorem measurable_historyDensity (hg : Measurable g) (m : ℕ) (xs : Fin m → ConnState k) :
    Measurable (fun p : (Fin k → ℝ) × (Fin m → ℝ) ↦ historyDensity g p.1 m xs p.2) := by
  have h := (measurable_pathDensity hg m diagState xs).comp
    (show Measurable (fun p : (Fin k → ℝ) × (Fin m → ℝ) ↦ (p.1, (1 : ℝ), p.2)) from
      measurable_fst.prodMk (measurable_const.prodMk measurable_snd))
  have heq : (fun p : (Fin k → ℝ) × (Fin m → ℝ) ↦ historyDensity g p.1 m xs p.2) =
      (fun q : (Fin k → ℝ) × ℝ × (Fin m → ℝ) ↦ pathDensity g q.1 m q.2.1 diagState xs q.2.2) ∘
        (fun p : (Fin k → ℝ) × (Fin m → ℝ) ↦ (p.1, (1 : ℝ), p.2)) := by
    funext p
    exact (pathDensity_eq_historyDensity m xs p.2).symm
  rw [heq]
  exact h

theorem isAdmissible_of_historyDensity_ne_zero {b : Fin k → ℝ} {m : ℕ}
    {xs : Fin m → ConnState k} {cs : Fin m → ℝ} (h : historyDensity g b m xs cs ≠ 0) :
    IsAdmissible b m 1 diagState xs cs := by
  classical
  by_contra ha
  apply h
  simp [historyDensity, ha]

theorem ae_historyLaw_admissible (hg : Measurable g) :
    ∀ᵐ h ∂historyLaw g k, HistoryAdmissible h := by
  rw [historyLaw, Measure.ae_sum_eq, Filter.eventually_iSup]
  intro m
  rw [← Measure.sum_fintype, Measure.ae_sum_eq, Filter.eventually_iSup]
  intro xs
  rw [(measurableEmbedding_historyMk m xs).ae_map_iff,
    ae_withDensity_iff (measurable_historyDensity hg m xs)]
  exact Eventually.of_forall fun p hp ↦ isAdmissible_of_historyDensity_ne_zero hp

/-- The coalescent law is the image of the history law under the genealogy map. -/
theorem coalescentLaw_eq_map_historyLaw :
    coalescentLaw g k = (historyLaw g k).map genealogyOfHistory := by
  ext S hS
  rw [Measure.map_apply measurable_genealogyOfHistory hS, coalescentLaw, historyLaw,
    Measure.sum_apply _ hS, Measure.sum_apply _ (measurable_genealogyOfHistory hS)]
  refine tsum_congr fun m ↦ ?_
  rw [Measure.coe_finsetSum, Measure.coe_finsetSum, Finset.sum_apply, Finset.sum_apply]
  refine Finset.sum_congr rfl fun xs _ ↦ ?_
  rw [Measure.map_apply (measurable_genealogyOf m xs) hS,
    Measure.map_apply (measurable_historyMk m xs) (measurable_genealogyOfHistory hS),
    historyMeasure]
  have hd : (fun p : (Fin k → ℝ) × (Fin m → ℝ) ↦ pathDensity g p.1 m 1 diagState xs p.2) =
      fun p ↦ historyDensity g p.1 m xs p.2 :=
    funext fun p ↦ pathDensity_eq_historyDensity m xs p.2
  rw [hd]
  rfl

/-- **Proposition `loi du coalescent généralisé` (N11), history form.** The law of the decoded
history `(F, B, C)` under the coalescent law is the history law with density
`historyDensity`. -/
theorem map_decodeHistory_coalescentLaw (hg : Measurable g) :
    (coalescentLaw g k).map decodeHistory = historyLaw g k := by
  rw [coalescentLaw_eq_map_historyLaw, Measure.map_map measurable_decodeHistory
    measurable_genealogyOfHistory]
  conv_rhs => rw [← Measure.map_id (μ := historyLaw g k)]
  refine Measure.map_congr ((ae_historyLaw_admissible hg).mono fun h hh ↦ ?_)
  obtain ⟨m, xs, b, cs⟩ := h
  exact decodeHistory_genealogyOf hh

/-- **Proposition `loi du coalescent généralisé` (N11).** Under the limiting genealogy law,
the decoded genealogy forest, births and merge times `(F, B, C)` have the law
`historyLaw g k`, with density `historyDensity` on each fibre. -/
theorem map_decodeHistory_criticalGenealogyLimit (hg : Measurable g) (hg2 : LocSqIntegrable g) :
    (criticalGenealogyLimit g k : Measure (GenealogySpace k)).map decodeHistory =
      historyLaw g k := by
  rw [criticalGenealogyLimit_eq_coalescentLaw hg hg2]
  exact map_decodeHistory_coalescentLaw hg

theorem historyLaw_univ (hg : Measurable g) (hg2 : LocSqIntegrable g) :
    historyLaw g k univ = 1 := by
  rw [← map_decodeHistory_coalescentLaw hg, Measure.map_apply measurable_decodeHistory
    MeasurableSet.univ, preimage_univ, coalescentLaw_univ hg hg2]

/-- Almost surely the decoded history is admissible and recovers the genealogy. -/
theorem ae_decodeHistory (hg : Measurable g) :
    ∀ᵐ z ∂coalescentLaw g k, HistoryAdmissible (decodeHistory z) ∧
      genealogyOfHistory (decodeHistory z) = z := by
  have h1 : ∀ᵐ z ∂coalescentLaw g k, HistoryAdmissible (decodeHistory z) := by
    refine ae_of_ae_map measurable_decodeHistory.aemeasurable ?_
    rw [map_decodeHistory_coalescentLaw hg]
    exact ae_historyLaw_admissible hg
  have hset : MeasurableSet {z : GenealogySpace k | genealogyOfHistory (decodeHistory z) = z} :=
    measurableSet_eq_fun (measurable_genealogyOfHistory.comp measurable_decodeHistory)
      measurable_id
  have h2 : ∀ᵐ z ∂coalescentLaw g k, genealogyOfHistory (decodeHistory z) = z := by
    rw [coalescentLaw_eq_map_historyLaw, ae_map_iff measurable_genealogyOfHistory.aemeasurable hset]
    refine (ae_historyLaw_admissible hg).mono fun h hh ↦ ?_
    obtain ⟨m, xs, b, cs⟩ := h
    show genealogyOfHistory (decodeHistory (genealogyOf m xs b cs)) = genealogyOf m xs b cs
    rw [decodeHistory_genealogyOf hh]
    rfl
  filter_upwards [h1, h2] with z hz1 hz2
  exact ⟨hz1, hz2⟩

/-! ### Plane histories -/

/-- Plane histories: a merge history together with the order of the two children of each
internal vertex. -/
abbrev PlaneHistorySpace (k : ℕ) :=
  Σ m : ℕ, (Fin m → ConnState k) × (Fin m → Bool) × (Fin k → ℝ) × (Fin m → ℝ)

/-- The plane history with `m` merges along `xs`, child orders `σ`, births `p.1` and merge
times `p.2`. -/
def planeMk (m : ℕ) (xs : Fin m → ConnState k) (σ : Fin m → Bool)
    (p : (Fin k → ℝ) × (Fin m → ℝ)) : PlaneHistorySpace k :=
  ⟨m, (xs, σ, p.1, p.2)⟩

/-- Forgetting the child orders. -/
def forgetOrders (h : PlaneHistorySpace k) : HistorySpace k :=
  ⟨h.1, (h.2.1, h.2.2.2)⟩

theorem measurable_planeMk (m : ℕ) (xs : Fin m → ConnState k) (σ : Fin m → Bool) :
    Measurable (planeMk (k := k) m xs σ) := by
  have h := (measurable_sigmaMk
    (β := fun m ↦ (Fin m → ConnState k) × (Fin m → Bool) × (Fin k → ℝ) × (Fin m → ℝ)) m).comp
    (show Measurable (fun p : (Fin k → ℝ) × (Fin m → ℝ) ↦ (xs, σ, p.1, p.2)) from
      measurable_const.prodMk (measurable_const.prodMk (measurable_fst.prodMk measurable_snd)))
  exact h

theorem measurable_forgetOrders : Measurable (forgetOrders (k := k)) :=
  measurable_sigma_elim fun m ↦ by
    have h := (measurable_sigmaMk
      (β := fun m ↦ (Fin m → ConnState k) × (Fin k → ℝ) × (Fin m → ℝ)) m).comp
      (show Measurable (fun q : (Fin m → ConnState k) × (Fin m → Bool) × (Fin k → ℝ) ×
        (Fin m → ℝ) ↦ (q.1, q.2.2)) from measurable_fst.prodMk measurable_snd.snd)
    exact h

/-- The law of plane histories, with density `planeDensity = 2^{-m} historyDensity` on each
fibre `(m, xs, σ)`. -/
noncomputable def planeLaw (g : ℝ → ℝ) (k : ℕ) : Measure (PlaneHistorySpace k) :=
  Measure.sum fun m : ℕ ↦ ∑ xs : Fin m → ConnState k, ∑ σ : Fin m → Bool,
    (((cubeMeasure k).prod volume).withDensity fun p ↦ planeDensity g p.1 m xs p.2).map
      (planeMk m xs σ)

/-- **Independent uniform child orders.** Given the history, each of the `2^m` child orders
has the same weight `2^{-m}`, independently of births and merge times. -/
theorem planeLaw_eq_uniformOrders (g : ℝ → ℝ) (k : ℕ) :
    planeLaw g k = Measure.sum fun m : ℕ ↦ ∑ xs : Fin m → ConnState k, ∑ σ : Fin m → Bool,
      ((2 : ℝ≥0∞) ^ m)⁻¹ • (((cubeMeasure k).prod volume).withDensity
        fun p ↦ historyDensity g p.1 m xs p.2).map (planeMk m xs σ) := by
  unfold planeLaw
  congr 1
  funext m
  refine Finset.sum_congr rfl fun xs _ ↦ Finset.sum_congr rfl fun σ _ ↦ ?_
  have hdens : (fun p : (Fin k → ℝ) × (Fin m → ℝ) ↦ planeDensity g p.1 m xs p.2) =
      ((2 : ℝ≥0∞) ^ m)⁻¹ • fun p ↦ historyDensity g p.1 m xs p.2 := by
    funext p
    simp [planeDensity, ENNReal.inv_pow]
  rw [hdens, withDensity_smul' _ _ (by simp), Measure.map_smul]
  exact (measurable_planeMk m xs σ).aemeasurable

/-- **Plane form of N11.** Forgetting the child orders of the plane law gives the law of the
decoded history under the limiting genealogy law. -/
theorem map_forgetOrders_planeLaw (hg : Measurable g) (hg2 : LocSqIntegrable g) :
    (planeLaw g k).map forgetOrders =
      (criticalGenealogyLimit g k : Measure (GenealogySpace k)).map decodeHistory := by
  rw [map_decodeHistory_criticalGenealogyLimit hg hg2]
  ext S hS
  rw [Measure.map_apply measurable_forgetOrders hS, planeLaw_eq_uniformOrders, historyLaw,
    Measure.sum_apply _ (measurable_forgetOrders hS), Measure.sum_apply _ hS]
  refine tsum_congr fun m ↦ ?_
  rw [Measure.coe_finsetSum, Measure.coe_finsetSum, Finset.sum_apply, Finset.sum_apply]
  refine Finset.sum_congr rfl fun xs _ ↦ ?_
  rw [Measure.coe_finsetSum, Finset.sum_apply, Measure.map_apply (measurable_historyMk m xs) hS]
  have hterm : ∀ σ : Fin m → Bool, (((2 : ℝ≥0∞) ^ m)⁻¹ • (((cubeMeasure k).prod volume).withDensity
      fun p ↦ historyDensity g p.1 m xs p.2).map (planeMk m xs σ)) (forgetOrders ⁻¹' S) =
      ((2 : ℝ≥0∞) ^ m)⁻¹ * (((cubeMeasure k).prod volume).withDensity
        fun p ↦ historyDensity g p.1 m xs p.2) (historyMk m xs ⁻¹' S) := by
    intro σ
    rw [Measure.smul_apply, smul_eq_mul, Measure.map_apply (measurable_planeMk m xs σ)
      (measurable_forgetOrders hS)]
    rfl
  rw [Finset.sum_congr rfl fun σ _ ↦ hterm σ, Finset.sum_const, Finset.card_univ,
    Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, nsmul_eq_mul, ← mul_assoc,
    Nat.cast_pow, Nat.cast_ofNat, ENNReal.mul_inv_cancel (by simp) (by simp), one_mul]

/-! ### Almost-everywhere modifications of the profile -/

/-- `g` and `g'` have the same integrals of squares on the windows used by the
propagators, those inside `(0, 1)`. -/
def SameSquareIntegrals (g g' : ℝ → ℝ) : Prop :=
  ∀ a t : ℝ, 0 < a → t < 1 → ∫ τ in Icc a t, g τ ^ 2 = ∫ τ in Icc a t, g' τ ^ 2

theorem sameSquareIntegrals_of_ae {g g' : ℝ → ℝ}
    (h : ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) 1), g t = g' t) : SameSquareIntegrals g g' := by
  intro a t ha ht
  rw [ae_restrict_iff' measurableSet_Ioo] at h
  refine setIntegral_congr_ae measurableSet_Icc ?_
  filter_upwards [h] with τ hτ hτI
  rw [hτ ⟨ha.trans_le hτI.1, hτI.2.trans_lt ht⟩]

theorem propagatorAux_congr {g g' : ℝ → ℝ} (h : SameSquareIntegrals g g') (b : Fin k → ℝ)
    {s : ℝ} (hs : 0 < s) : ∀ m t, t < 1 → propagatorAux g b s m t = propagatorAux g' b s m t := by
  classical
  intro m
  induction m with
  | zero =>
    intro t ht
    rw [propagatorAux, propagatorAux, h s t hs ht]
  | succ m ih =>
    intro t ht
    rw [propagatorAux, propagatorAux]
    by_cases hne : (birthsIn b s t).Nonempty
    · rw [dite_eq_left_of_eq_true (eq_true hne), dite_eq_left_of_eq_true (eq_true hne)]
      obtain ⟨jstar, hjmem, hjeq⟩ := Finset.exists_mem_eq_sup' hne b
      have hjb : s < b jstar ∧ b jstar < t := by simpa [birthsIn] using hjmem
      rw [h ((birthsIn b s t).sup' hne b) t (by rw [hjeq]; linarith [hjb.1]) ht,
        ih ((birthsIn b s t).sup' hne b) (by rw [hjeq]; linarith [hjb.2])]
    · rw [dite_eq_right_of_eq_false (eq_false hne), dite_eq_right_of_eq_false (eq_false hne),
        h s t hs ht]

theorem contVec_congr {g g' : ℝ → ℝ} (h : SameSquareIntegrals g g') (b : Fin k → ℝ)
    (S : ℝ → Set (ConnState k)) : ∀ m (T : Finset ℝ) (t : ℝ) (v : ConnState k → ℝ),
      (∀ τ ∈ T, 0 < τ ∧ τ < 1) → t < 1 → contVec g b S m T t v = contVec g' b S m T t v := by
  intro m
  induction m with
  | zero =>
    intro T t v _ _
    rfl
  | succ m ih =>
    intro T t v hT ht
    rw [contVec, contVec]
    by_cases hne : T.Nonempty
    · rw [dite_eq_left_of_eq_true (eq_true hne), dite_eq_left_of_eq_true (eq_true hne)]
      have hτ := hT _ (T.max'_mem hne)
      rw [propagator, propagator, propagatorAux_congr h b hτ.1 k t ht]
      exact ih _ _ _ (fun τ hτ' ↦ hT τ (Finset.mem_of_mem_erase hτ')) hτ.2
    · rw [dite_eq_right_of_eq_false (eq_false hne), dite_eq_right_of_eq_false (eq_false hne)]

theorem upperLimit_congr {g g' : ℝ → ℝ} (h : SameSquareIntegrals g g') (α : Fin k → ℝ)
    (γ : Fin k → Fin k → ℝ) : upperLimit g α γ = upperLimit g' α γ := by
  unfold upperLimit
  refine integral_congr_ae (ae_cube_lt_one.mono fun U hU ↦ ?_)
  simp only [upperIntegrand]
  split_ifs
  · unfold coalescenceLimit
    rw [contVec_congr h U (obsSet γ) _ _ _ _ (fun τ hτ ↦ obsTimes_pos hτ)
      (topTime_lt_one hU fun τ hτ ↦ (obsTimes_pos hτ).2)]
  · rfl

/-- The limit characterization only depends on `g` through the integrals of `g²` on
windows inside `(0, 1)`. -/
theorem isGenealogyLimit_congr {g g' : ℝ → ℝ} (h : SameSquareIntegrals g g')
    (μ : ProbabilityMeasure (GenealogySpace k)) :
    IsGenealogyLimit g μ ↔ IsGenealogyLimit g' μ := by
  unfold IsGenealogyLimit
  simp only [upperLimit_congr h]

theorem criticalGenealogyLimit_congr {g g' : ℝ → ℝ} (h : SameSquareIntegrals g g') :
    criticalGenealogyLimit g k = criticalGenealogyLimit g' k := by
  have hp : IsGenealogyLimit (k := k) g = IsGenealogyLimit g' :=
    funext fun μ ↦ propext (isGenealogyLimit_congr h μ)
  unfold criticalGenealogyLimit
  rw [hp]

/-- **The coalescent law does not depend on the modification of `g`.** -/
theorem coalescentLaw_congr_ae {g g' : ℝ → ℝ} (hg : Measurable g) (hg2 : LocSqIntegrable g)
    (hg' : Measurable g') (hg2' : LocSqIntegrable g')
    (h : ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) 1), g t = g' t) :
    coalescentLaw g k = coalescentLaw g' k := by
  have h1 := criticalGenealogyLimit_eq_coalescentLaw (k := k) hg hg2
  have h2 := criticalGenealogyLimit_eq_coalescentLaw (k := k) hg' hg2'
  rw [criticalGenealogyLimit_congr (sameSquareIntegrals_of_ae h), h2] at h1
  exact congrArg (fun μ : ProbabilityMeasure (GenealogySpace k) ↦
    (μ : Measure (GenealogySpace k))) h1.symm

/-- A measurable modification of a profile satisfying the source hypotheses. -/
theorem exists_measurable_modification {xa : ℕ → ℕ → ℤ}
    (hL1 : HasL1ReciprocalProfile xa (1 / 2) g) (h2 : HasLocalSquareMomentProfile xa (1 / 2) g) :
    ∃ g' : ℝ → ℝ, Measurable g' ∧ LocSqIntegrable g' ∧
      ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) 1), g t = g' t := by
  have hae := hL1.1.aestronglyMeasurable
  refine ⟨hae.mk g, hae.stronglyMeasurable_mk.measurable, fun a c ha hac hc ↦ ?_,
    ae_restrict_of_ae_restrict_of_subset Ioo_subset_Icc_self hae.ae_eq_mk⟩
  have h0 : g =ᵐ[volume.restrict (Icc a c)] hae.mk g :=
    ae_restrict_of_ae_restrict_of_subset (Icc_subset_Icc ha.le hc.le) hae.ae_eq_mk
  exact (h2 a c ha hac hc).1.congr (h0.mono fun t ht ↦ by simp only [ht])

/-- **Convergence of sampled genealogies without a measurability assumption.** Under the
source hypotheses alone, the limiting genealogy law is the coalescent law of a measurable
modification `g'` of `g`, and the sampled genealogies converge to it. -/
theorem tendsto_genealogyLaw_coalescentLaw_of_profile {xa : ℕ → ℕ → ℤ}
    (hx : AdmissibleArray xa) (hL1 : HasL1ReciprocalProfile xa (1 / 2) g)
    (hpos : PositiveProfile g) (h2 : HasLocalSquareMomentProfile xa (1 / 2) g) (k : ℕ) :
    ∃ (g' : ℝ → ℝ) (hg' : Measurable g') (hg2' : LocSqIntegrable g'),
      (∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) 1), g t = g' t) ∧
        criticalGenealogyLimit g k = coalescentLawPM g' k hg' hg2' ∧
        (criticalGenealogyLimit g k : Measure (GenealogySpace k)).map decodeHistory =
          historyLaw g' k ∧
        Tendsto (genealogyLaw hx k) atTop (𝓝 (coalescentLawPM g' k hg' hg2')) := by
  obtain ⟨g', hg', hg2', hae⟩ := exists_measurable_modification hL1 h2
  have hc : criticalGenealogyLimit g k = coalescentLawPM g' k hg' hg2' := by
    rw [criticalGenealogyLimit_congr (sameSquareIntegrals_of_ae hae),
      criticalGenealogyLimit_eq_coalescentLaw hg' hg2']
  refine ⟨g', hg', hg2', hae, hc, ?_, ?_⟩
  · rw [criticalGenealogyLimit_congr (sameSquareIntegrals_of_ae hae)]
    exact map_decodeHistory_criticalGenealogyLimit hg' hg2'
  · rw [← hc]
    exact tendsto_genealogyLaw_criticalGenealogyLimit hx hL1 hpos h2 k

/-! ### Side claims of the construction (U23) -/

/-- **Merge times are almost surely distinct.** Almost surely the genealogy is that of the
decoded admissible binary history, whose merge times are strictly decreasing in `(0, 1)`. -/
theorem ae_mergeTimes_strictAnti (hg : Measurable g) :
    ∀ᵐ z ∂coalescentLaw g k, genealogyOfHistory (decodeHistory z) = z ∧
      HistoryAdmissible (decodeHistory z) ∧ StrictAnti (decodeHistory z).2.2.2 ∧
        ∀ i, 0 < (decodeHistory z).2.2.2 i ∧ (decodeHistory z).2.2.2 i < 1 := by
  filter_upwards [ae_decodeHistory hg] with z hz
  have ha : IsAdmissible (decodeHistory z).2.2.1 (decodeHistory z).1 1 diagState
      (decodeHistory z).2.1 (decodeHistory z).2.2.2 := hz.1
  exact ⟨hz.2, hz.1, ha.strictAnti, fun i ↦ ha.time_mem i⟩

theorem topTime_ge_half (b : Fin k → ℝ) (T : Finset ℝ) : 1 / 2 ≤ topTime b T := by
  have : (0 : ℝ) ≤ (Finset.univ.image b ∪ T).fold max 0 id :=
    (Finset.le_fold_max 0).mpr (Or.inl le_rfl)
  unfold topTime
  linarith

theorem cumHazard_lt_top (hg2 : LocSqIntegrable g)
    (hfin : ∫⁻ t in Ioc 0 (1 / 2), ENNReal.ofReal (g t ^ 2) < ⊤) {b : Fin k → ℝ}
    (hb1 : ∀ j, b j < 1) (x : ConnState k) : cumHazard g b x 0 1 < ⊤ := by
  set t₀ := topTime b (∅ : Finset ℝ) with ht₀
  have ht₀1 : t₀ < 1 := topTime_lt_one hb1 (by simp)
  have ht₀h : 1 / 2 ≤ t₀ := topTime_ge_half b ∅
  rw [cumHazard_add g b x (by linarith : (0 : ℝ) ≤ t₀) ht₀1.le]
  have htop : cumHazard g b x t₀ 1 = 0 := by
    unfold cumHazard
    rw [setLIntegral_congr_fun measurableSet_Ioc (g := fun _ ↦ 0) ?_, lintegral_zero]
    intro u hu
    have hborn : bornAt b u = ∅ := by
      ext j
      simp only [bornAt, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
        iff_false, not_le]
      exact (birth_lt_topTime ∅ hb1 j).trans hu.1
    simp [hazard, pairCount, hborn, classesOn]
  rw [htop, add_zero]
  have hle : cumHazard g b x 0 t₀ ≤
      (k ^ 2 : ℝ≥0∞) * ∫⁻ u in Ioc 0 t₀, ENNReal.ofReal (g u ^ 2) := by
    unfold cumHazard
    rw [← lintegral_const_mul' _ _ (by simp)]
    refine lintegral_mono fun u ↦ ?_
    unfold hazard
    gcongr
    exact_mod_cast pairCount_le b x u
  refine lt_of_le_of_lt hle (ENNReal.mul_lt_top (by simp) ?_)
  rw [← Ioc_union_Ioc_eq_Ioc (by norm_num : (0 : ℝ) ≤ 1 / 2) ht₀h,
    lintegral_union measurableSet_Ioc (Ioc_disjoint_Ioc_of_le le_rfl)]
  refine ENNReal.add_lt_top.mpr ⟨hfin, ?_⟩
  rcases ht₀h.eq_or_lt with h | h
  · rw [← h, Ioc_self, Measure.restrict_empty, lintegral_zero_measure]
    exact ENNReal.zero_lt_top
  · exact Integrable.lintegral_lt_top ((hg2 (1 / 2) t₀ (by norm_num) h ht₀1).mono_set
      Ioc_subset_Icc_self)

/-- **Finite integrated hazard leaves a positive non-merger probability.** If
`∫₀^{1/2} g² < ∞`, then with positive probability no two of the `k` particles ever merge:
they end in `k` separate clusters. -/
theorem coalescentLaw_noMerger_pos (hg : Measurable g) (hg2 : LocSqIntegrable g)
    (hfin : ∫⁻ t in Ioc 0 (1 / 2), ENNReal.ofReal (g t ^ 2) < ⊤) :
    0 < coalescentLaw g k {z | ∀ j l, j ≠ l → z.2 j l = 0} := by
  classical
  have hE : MeasurableSet {z : GenealogySpace k | ∀ j l, j ≠ l → z.2 j l = 0} := by
    have : {z : GenealogySpace k | ∀ j l, j ≠ l → z.2 j l = 0} =
        ⋂ j, ⋂ l, {z : GenealogySpace k | j ≠ l → z.2 j l = 0} := by
      ext z
      simp
    rw [this]
    refine MeasurableSet.iInter fun j ↦ MeasurableSet.iInter fun l ↦ ?_
    by_cases hjl : j = l
    · simp [hjl]
    · simp only [ne_eq, hjl, not_false_eq_true, forall_const]
      exact measurableSet_eq_fun ((measurable_pi_apply l).comp
        ((measurable_pi_apply j).comp measurable_snd)) measurable_const
  rw [coalescentLaw_apply hg hE]
  have hmem : ∀ (b : Fin k → ℝ) (xs : Fin 0 → ConnState k) (cs : Fin 0 → ℝ),
      genealogyOf 0 xs b cs ∈ {z : GenealogySpace k | ∀ j l, j ≠ l → z.2 j l = 0} := by
    intro b xs cs j l hjl
    simp [genealogyOf, coalTime, diagState, hjl]
  have hlow : ∀ b : Fin k → ℝ, surv g b diagState 0 1 ≤ ∑' m, ∑ xs : Fin m → ConnState k,
      ∫⁻ cs : Fin m → ℝ, {z : GenealogySpace k | ∀ j l, j ≠ l → z.2 j l = 0}.indicator 1
        (genealogyOf m xs b cs) * pathDensity g b m 1 diagState xs cs := by
    intro b
    refine le_trans (le_of_eq ?_) (ENNReal.le_tsum 0)
    rw [Fintype.sum_unique, volume_pi, Measure.pi_of_empty, lintegral_dirac,
      Set.indicator_of_mem (hmem _ _ _)]
    simp [pathDensity]
  have hpos : ∀ᵐ b ∂cubeMeasure k, 0 < surv g b diagState 0 1 := by
    filter_upwards [ae_cube_lt_one (k := k)] with b hb
    unfold surv expNeg
    rw [ite_eq_right (cumHazard_lt_top hg2 hfin hb diagState).ne]
    exact ENNReal.ofReal_pos.mpr (Real.exp_pos _)
  have hmeas : Measurable fun b : Fin k → ℝ ↦ surv g b diagState 0 1 := by
    have h := (measurable_surv hg diagState).comp (show Measurable
      (fun b : Fin k → ℝ ↦ (b, (0 : ℝ), (1 : ℝ))) from measurable_id.prodMk measurable_const)
    exact h
  refine lt_of_lt_of_le ?_ (lintegral_mono hlow)
  rw [pos_iff_ne_zero]
  intro h0
  rw [lintegral_eq_zero_iff hmeas] at h0
  have hfalse : ∀ᵐ b ∂cubeMeasure k, False := by
    filter_upwards [h0, hpos] with b h1 h2
    rw [h1] at h2
    exact lt_irrefl 0 h2
  have hbot := Filter.eventually_false_iff_eq_bot.mp hfalse
  rw [ae_eq_bot] at hbot
  have := measure_univ (μ := cubeMeasure k)
  rw [hbot] at this
  simp at this

theorem classesOn_ge_two {β : Finset (Fin k)} {y : ConnState k} {j l : Fin k} (hj : j ∈ β)
    (hl : l ∈ β) (hll : y l l = true) (hjl : y j l = false) : 2 ≤ classesOn β y := by
  classical
  unfold classesOn
  have hne : (β.filter fun l' ↦ y j l' = true) ≠ β.filter fun l' ↦ y l l' = true := by
    intro h
    have : l ∈ β.filter fun l' ↦ y l l' = true := by simp [hl, hll]
    rw [← h] at this
    simp [hjl] at this
  have hsub : ({β.filter fun l' ↦ y j l' = true, β.filter fun l' ↦ y l l' = true} :
      Finset (Finset (Fin k))) ⊆ β.image fun i ↦ β.filter fun l' ↦ y i l' = true := by
    intro C hC
    simp only [Finset.mem_insert, Finset.mem_singleton] at hC
    rcases hC with rfl | rfl
    · exact Finset.mem_image_of_mem _ hj
    · exact Finset.mem_image_of_mem _ hl
  calc 2 = ({β.filter fun l' ↦ y j l' = true, β.filter fun l' ↦ y l l' = true} :
        Finset (Finset (Fin k))).card := (Finset.card_pair hne).symm
    _ ≤ _ := Finset.card_le_card hsub

theorem stateAt_related {m : ℕ} : ∀ {t : ℝ} {x : ConnState k} {xs : Fin m → ConnState k}
    {cs : Fin m → ℝ} {u : ℝ} {j l : Fin k}, stateAt m t x xs cs u j l = true →
      x j l = true ∨ u ≤ coalTime m t x xs cs j l := by
  induction m with
  | zero =>
    intro t x xs cs u j l h
    left
    simpa [stateAt] using h
  | succ m ih =>
    intro t x xs cs u j l h
    by_cases hc : cs 0 < u
    · left
      simpa [stateAt, hc] using h
    · have h' : stateAt m (cs 0) (xs 0) (Fin.tail xs) (Fin.tail cs) u j l = true := by
        simpa [stateAt, hc] using h
      by_cases hx : x j l = true
      · exact Or.inl hx
      · right
        simp only [coalTime, hx]
        rcases ih h' with h0 | h1
        · rw [coalTime_of_true h0]
          exact not_lt.mp hc
        · exact h1

theorem IsAdmissible.stateAt_refl {b : Fin k → ℝ} {m : ℕ} : ∀ {t : ℝ} {x : ConnState k}
    {xs : Fin m → ConnState k} {cs : Fin m → ℝ}, IsAdmissible b m t x xs cs →
      (∀ j, x j j = true) → ∀ u j, stateAt m t x xs cs u j j = true := by
  induction m with
  | zero =>
    intro t x xs cs _ hx u j
    simpa [stateAt] using hx j
  | succ m ih =>
    intro t x xs cs h hx u j
    obtain ⟨-, hm, ha⟩ := h
    by_cases hc : cs 0 < u
    · simpa [stateAt, hc] using hx j
    · have := ih ha (fun j ↦ hm.ge (hx j)) u j
      simpa [stateAt, hc] using this

/-- **Infinite integrated hazard forces a final merger.** If `∫₀^{1/2} g² = ∞`, then almost
surely all pairwise coalescence times are positive: the `k` particles end in one cluster. -/
theorem coalescentLaw_allMerge (hg : Measurable g) (hg2 : LocSqIntegrable g)
    (hdiv : ∫⁻ t in Ioc 0 (1 / 2), ENNReal.ofReal (g t ^ 2) = ⊤) :
    ∀ᵐ z ∂coalescentLaw g k, ∀ j l, j ≠ l → 0 < z.2 j l := by
  classical
  have hE : MeasurableSet {z : GenealogySpace k | ∀ j l, j ≠ l → 0 < z.2 j l} := by
    have : {z : GenealogySpace k | ∀ j l, j ≠ l → 0 < z.2 j l} =
        ⋂ j, ⋂ l, {z : GenealogySpace k | j ≠ l → 0 < z.2 j l} := by
      ext z
      simp
    rw [this]
    refine MeasurableSet.iInter fun j ↦ MeasurableSet.iInter fun l ↦ ?_
    by_cases hjl : j = l
    · simp [hjl]
    · simp only [ne_eq, hjl, not_false_eq_true, forall_const]
      exact measurableSet_lt measurable_const ((measurable_pi_apply l).comp
        ((measurable_pi_apply j).comp measurable_snd))
  have key : ∀ b : Fin k → ℝ, (∀ j, 0 < b j) → ∀ m (xs : Fin m → ConnState k) (cs : Fin m → ℝ),
      pathDensity g b m 1 diagState xs cs ≠ 0 →
        genealogyOf m xs b cs ∈ {z : GenealogySpace k | ∀ j l, j ≠ l → 0 < z.2 j l} := by
    intro b hb m xs cs hd j l hjl
    rw [pathDensity_eq_historyDensity] at hd
    have ha := isAdmissible_of_historyDensity_ne_zero hd
    show 0 < (if j = l then b j else coalTime m 1 diagState xs cs j l)
    rw [ite_eq_right hjl]
    by_contra hnpos
    apply hd
    set δ := min (min (b j) (b l)) (1 / 2) with hδ
    have hδ0 : 0 < δ := lt_min (lt_min (hb j) (hb l)) (by norm_num)
    have hδh : δ ≤ 1 / 2 := min_le_right _ _
    have hpt : ∀ u ∈ Ioc 0 δ, ENNReal.ofReal (g u ^ 2) ≤
        ((clusterCount b m xs cs u).choose 2 : ℝ≥0∞) * ENNReal.ofReal (g u ^ 2) := by
      intro u hu
      have hju : j ∈ bornAt b u := by
        simp only [bornAt, Finset.mem_filter, Finset.mem_univ, true_and]
        exact hu.2.trans ((min_le_left _ _).trans (min_le_left _ _))
      have hlu : l ∈ bornAt b u := by
        simp only [bornAt, Finset.mem_filter, Finset.mem_univ, true_and]
        exact hu.2.trans ((min_le_left _ _).trans (min_le_right _ _))
      have hrefl := ha.stateAt_refl (fun i ↦ by simp [diagState]) u
      have hsep : stateAt m 1 diagState xs cs u j l = false := by
        by_contra hc
        rw [Bool.not_eq_false] at hc
        rcases stateAt_related hc with h1 | h1
        · simp [diagState, hjl] at h1
        · exact hnpos (lt_of_lt_of_le hu.1 h1)
      have h2 := classesOn_ge_two hju hlu (hrefl l) hsep
      have h1 : 1 ≤ ((clusterCount b m xs cs u).choose 2 : ℝ≥0∞) := by
        exact_mod_cast Nat.choose_pos h2
      calc ENNReal.ofReal (g u ^ 2) = 1 * ENNReal.ofReal (g u ^ 2) := (one_mul _).symm
        _ ≤ _ := by gcongr
    have hI : ∫⁻ u in Ioc 0 1,
        ((clusterCount b m xs cs u).choose 2 : ℝ≥0∞) * ENNReal.ofReal (g u ^ 2) = ⊤ := by
      have hδtop : ∫⁻ u in Ioc 0 δ, ENNReal.ofReal (g u ^ 2) = ⊤ := by
        rw [← Ioc_union_Ioc_eq_Ioc hδ0.le hδh, lintegral_union measurableSet_Ioc
          (Ioc_disjoint_Ioc_of_le le_rfl)] at hdiv
        have hrest : ∫⁻ u in Ioc δ (1 / 2), ENNReal.ofReal (g u ^ 2) < ⊤ := by
          rcases hδh.eq_or_lt with h | h
          · rw [h, Ioc_self, Measure.restrict_empty, lintegral_zero_measure]
            exact ENNReal.zero_lt_top
          · exact Integrable.lintegral_lt_top ((hg2 δ (1 / 2) hδ0 h (by norm_num)).mono_set
              Ioc_subset_Icc_self)
        by_contra hne
        exact (ENNReal.add_lt_top.mpr ⟨lt_top_iff_ne_top.mpr hne, hrest⟩).ne hdiv
      refine top_le_iff.mp (hδtop ▸ ?_)
      calc ∫⁻ u in Ioc 0 δ, ENNReal.ofReal (g u ^ 2)
          ≤ ∫⁻ u in Ioc 0 δ,
            ((clusterCount b m xs cs u).choose 2 : ℝ≥0∞) * ENNReal.ofReal (g u ^ 2) :=
            lintegral_mono_ae ((ae_restrict_iff' measurableSet_Ioc).mpr
              (Eventually.of_forall hpt))
        _ ≤ _ := lintegral_mono_set (Ioc_subset_Ioc le_rfl (hδh.trans (by norm_num)))
    unfold historyDensity
    rw [hI]
    simp [expNeg]
  rw [ae_iff, show {z : GenealogySpace k | ¬ ∀ j l, j ≠ l → 0 < z.2 j l} =
    {z : GenealogySpace k | ∀ j l, j ≠ l → 0 < z.2 j l}ᶜ from rfl, coalescentLaw_apply hg hE.compl]
  have hzero : (fun b ↦ ∑' m, ∑ xs : Fin m → ConnState k, ∫⁻ cs : Fin m → ℝ,
      {z : GenealogySpace k | ∀ j l, j ≠ l → 0 < z.2 j l}ᶜ.indicator 1 (genealogyOf m xs b cs) *
        pathDensity g b m 1 diagState xs cs) =ᵐ[cubeMeasure k] 0 := by
    filter_upwards [ae_cube_good (k := k) ∅] with b hb
    have hb0 : ∀ j, 0 < b j := fun j ↦ (hb.1 j).1
    simp only [Pi.zero_apply]
    refine ENNReal.tsum_eq_zero.mpr fun m ↦ Finset.sum_eq_zero fun xs _ ↦ ?_
    rw [lintegral_congr (g := fun _ ↦ 0) fun cs ↦ ?_, lintegral_zero]
    by_cases hd : pathDensity g b m 1 diagState xs cs = 0
    · simp [hd]
    · have := key b hb0 m xs cs hd
      rw [Set.indicator_of_notMem (by simpa using this), zero_mul]
  rw [lintegral_congr_ae hzero]
  simp

end Freezing2.CoalescentDensity
