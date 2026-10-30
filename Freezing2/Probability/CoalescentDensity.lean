module

public import Freezing2.Probability.CriticalDistanceLimit
public import Freezing2.Probability.ContinuousCoalescentSurvival
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-!
# The density of the continuous coalescent genealogy

This file proves Proposition `loi du coalescent généralisé` (inventory N11): the joint law of
the genealogy forest, the birth times and the ordered coalescence times of the `k`-particle
continuous coalescent has the density

`g_{r,k} = 2^{-(k-1-r)} exp (-∫₀¹ C(a(t), 2) f(t)⁻² dt) ∏_{j=r+1}^{k-1} f(c_j)⁻²`

on admissible triplets, where `a(t)` is the number of clusters at time `t` and `r` is the
number of zero merger times.

## The coalescent and its genealogies

Particles `j : Fin k` are born at times `b j` (iid uniform on `[0, 1]`); time runs from `1`
down to `0` and every pair of clusters merges at rate `g(t)²`, where `g = 1/f`.

A *merge history* with `m` merges is a sequence `xs : Fin m → ConnState k` of connectivity
relations, `xs i` being the relation just after the `i`-th merge, with merge times
`cs : Fin m → ℝ` listed from the top (`cs 0` is the latest merge). This is the non-plane,
leaf-labelled, ranked forest: its `r + 1 = k - m` trees are the final clusters, and
`r = k - 1 - m` is the number of zero merger times `C_1 = ⋯ = C_r = 0`. The source's merge
times `c_{r+1} < ⋯ < c_{k-1}` are `cs (m - 1) < ⋯ < cs 0`. Admissibility (`IsAdmissible`)
says that the merge times decrease in `(0, 1)` and that each step merges two distinct
clusters of particles already born at the merge time, which is the compatibility of the
relative order of births and merges with the increasing labelling of the forest.

## The ordering convention (S09)

A plane forest is a merge history together with the orders `σ : Fin m → Bool` of the two
children of each internal vertex, chosen uniformly and independently. The `r + 1` trees are
ordered canonically, by increasing root label (chronologically), as for the forests of
`𝔉⁺_{r,k}` whose labels increase along branches; no randomness is attached to the root
order. Under this convention each plane history has density `2^{-m} = 2^{-(k-1-r)}` times
the non-plane density (`planeDensity`), and summing over the `2^m` child orders gives back
the non-plane law (`coalescentLaw_eq_planeDensity`). Allowing all `(r + 1)!` orders of the
trees as distinct forests would require an extra factor `1/(r + 1)!`.

## Main results

* `coalescentLaw g k`: the image on `GenealogySpace k` (births and pairwise coalescence
  times) of the history laws `historyMeasure`, which have the density `pathDensity` against
  Lebesgue measure on `[0, 1]^k × ℝ^m`; `coalescentLaw_univ` shows it is a probability
  measure, also when `∫₀ g² = ∞`.
* `pathDensity_eq_historyDensity` and `historyDensity_eq_source`: the density is
  `1_{admissible} ∏ g(cⱼ)² exp (-∫₀¹ C(a(u), 2) g(u)² du)`, with the source's formula
  `a(u) = #{j : b j > u} - #{i : cs i > u}` and `exp (-∞) = 0`.
* `IsAdmissible.le_card_sub_one`: admissible histories have at most `k - 1` merges, so
  `r ∈ [0, k - 1]`.
* `coalescentLaw_eq_historyDensity`, `coalescentLaw_eq_planeDensity`: the law as a sum over
  `m` and over (plane) merge histories of measures with density `g_{r,k}`.
* `isGenealogyLimit_coalescentLaw` and `criticalGenealogyLimit_eq_coalescentLaw`: the density
  law satisfies the semigroup characterization `IsGenealogyLimit g`, hence is the limiting
  genealogy law `criticalGenealogyLimit g k`; `tendsto_genealogyLaw_coalescentLaw` gives the
  convergence of the sampled genealogies of the reverse tree to it.

## Proof

The path masses `pathMass` (merge paths between two times, weighted by observation
constraints) satisfy the Chapman–Kolmogorov identity `transMass_split`. In a birth-free
window they are the entries of `exp ((∫ g²) • kingGen β)` (`transMass_window`): the
Duhamel formula for the matrix exponential, the change of variables along the cumulative
hazard (only absolutely continuous), and an induction on the number of related pairs of a
state. Gluing windows gives the propagator (`transMass_propagator`). The total mass from a
valid state is one (`sum_transMass_eq_one`) by the normalization of the existing
next-event law `positiveEventMeasure`, which retains a possibly divergent hazard at time `0`,
and by counting merges (`card_isMergeStep`). The observation recursion `contVec` then
computes constrained path masses (`contVec_eq_transMass`), identifying `coalescenceLimit`
(`coalescenceLimit_eq`); integrating over the births gives the upper-set values
`upperLimit`, and `IsGenealogyLimit.unique` concludes.

The only analytic hypotheses are that `g` is measurable and `LocSqIntegrable g`
(`∫_a^b g² < ∞` for `0 < a < b < 1`), consistent with `HasLocalSquareMomentProfile`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology NormedSpace
open scoped ENNReal

namespace Freezing2.CoalescentDensity

open TrackedGenealogy CriticalGenealogy ContinuousCoalescent

variable {k : ℕ}

/-! ### Extended survival exponentials -/

/-- `exp (-L)` for an extended nonnegative `L`, with `exp (-∞) = 0`. -/
noncomputable def expNeg (L : ℝ≥0∞) : ℝ≥0∞ :=
  if L = ∞ then 0 else ENNReal.ofReal (Real.exp (-L.toReal))

theorem expNeg_add (A B : ℝ≥0∞) : expNeg (A + B) = expNeg A * expNeg B := by
  unfold expNeg
  by_cases hA : A = ∞
  · simp [hA]
  by_cases hB : B = ∞
  · simp [hB]
  simp only [ENNReal.add_ne_top.mpr ⟨hA, hB⟩, hA, hB, ↓reduceIte]
  rw [ENNReal.toReal_add hA hB, neg_add, Real.exp_add, ENNReal.ofReal_mul (Real.exp_pos _).le]

@[simp] theorem expNeg_zero : expNeg 0 = 1 := by simp [expNeg]

theorem expNeg_le_one (L : ℝ≥0∞) : expNeg L ≤ 1 := by
  unfold expNeg
  split_ifs
  · exact zero_le_one
  · rw [ENNReal.ofReal_le_one, Real.exp_le_one_iff, neg_nonpos]
    exact ENNReal.toReal_nonneg

theorem expNeg_ne_top (L : ℝ≥0∞) : expNeg L ≠ ∞ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top (expNeg_le_one L)

theorem expNeg_ofReal {x : ℝ} (hx : 0 ≤ x) :
    expNeg (ENNReal.ofReal x) = ENNReal.ofReal (Real.exp (-x)) := by
  simp [expNeg, ENNReal.toReal_ofReal hx]

theorem measurable_expNeg : Measurable expNeg := by
  unfold expNeg
  exact Measurable.ite (measurableSet_singleton ∞) measurable_const
    (ENNReal.measurable_ofReal.comp
      (Real.continuous_exp.measurable.comp ENNReal.measurable_toReal.neg))

/-! ### Connectivity states and merges -/

/-- Connectivity states of `k` labels, as in the tracked chain. -/
abbrev ConnState (k : ℕ) := Fin k → Fin k → Bool

/-- A merge step: `x'` merges two distinct clusters of labels of `β` in `x`. -/
def IsMergeStep (β : Finset (Fin k)) (x x' : ConnState k) : Prop :=
  x' ≠ x ∧ MergeOn β x x'

/-- The number of related ordered pairs of a state. -/
def trueCount (x : ConnState k) : ℕ :=
  (Finset.univ.filter fun p : Fin k × Fin k ↦ x p.1 p.2 = true).card

theorem trueCount_le (x : ConnState k) : trueCount x ≤ k * k := by
  unfold trueCount
  calc _ ≤ (Finset.univ : Finset (Fin k × Fin k)).card := Finset.card_filter_le _ _
    _ = k * k := by simp

theorem mergeState_iff (x : ConnState k) (j₀ l₀ j l : Fin k) :
    mergeState x j₀ l₀ j l = true ↔ x j l = true ∨ (x j j₀ = true ∧ x l l₀ = true) ∨
      (x j l₀ = true ∧ x l j₀ = true) := by
  simp [mergeState, Bool.or_eq_true, Bool.and_eq_true, or_assoc]

theorem mergeState_ge {x : ConnState k} {j l : Fin k} (h : x j l = true) (j₀ l₀ : Fin k) :
    mergeState x j₀ l₀ j l = true := (mergeState_iff x j₀ l₀ j l).mpr (Or.inl h)

theorem IsMergeStep.ge {β : Finset (Fin k)} {x x' : ConnState k} (h : IsMergeStep β x x')
    {j l : Fin k} (hx : x j l = true) : x' j l = true := by
  obtain ⟨-, j₀, -, l₀, -, -, rfl⟩ := h
  exact mergeState_ge hx j₀ l₀

theorem trueCount_lt_of_isMergeStep {β : Finset (Fin k)} {x x' : ConnState k}
    (h : IsMergeStep β x x') : trueCount x < trueCount x' := by
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_subset_ne]
  refine ⟨fun p hp ↦ ?_, fun heq ↦ h.1 ?_⟩
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    exact h.ge hp
  · funext j l
    have := congrArg (fun s ↦ (j, l) ∈ s) heq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, eq_iff_iff] at this
    exact (Bool.eq_iff_iff.mpr this).symm

theorem IsMergeStep.mono {β β' : Finset (Fin k)} {x x' : ConnState k} (h : IsMergeStep β x x')
    (hβ : β ⊆ β') : IsMergeStep β' x x' := by
  obtain ⟨hne, j₀, hj₀, l₀, hl₀, hs, he⟩ := h
  exact ⟨hne, j₀, hβ hj₀, l₀, hβ hl₀, hs, he⟩

/-- Valid states: equivalence relations in which every label outside `β` (not yet born)
is a singleton. -/
structure IsValid (β : Finset (Fin k)) (x : ConnState k) : Prop where
  refl : ∀ j, x j j = true
  symm : ∀ j l, x j l = true → x l j = true
  trans : ∀ j l m, x j l = true → x l m = true → x j m = true
  born : ∀ j l, j ≠ l → x j l = true → j ∈ β

theorem isValid_diagState (β : Finset (Fin k)) : IsValid β diagState where
  refl j := by simp [diagState]
  symm j l h := by
    simp only [diagState, decide_eq_true_eq] at h ⊢
    exact h.symm
  trans j l m h1 h2 := by
    simp only [diagState, decide_eq_true_eq] at h1 h2 ⊢
    exact h1.trans h2
  born j l hjl h := by
    simp only [diagState, decide_eq_true_eq] at h
    exact absurd h hjl

theorem IsValid.mono {β β' : Finset (Fin k)} {x : ConnState k} (h : IsValid β x)
    (hβ : β ⊆ β') : IsValid β' x :=
  ⟨h.refl, h.symm, h.trans, fun j l hjl hx ↦ hβ (h.born j l hjl hx)⟩

theorem IsValid.mergeState {β : Finset (Fin k)} {x : ConnState k} (h : IsValid β x)
    {j₀ l₀ : Fin k} (hj₀ : j₀ ∈ β) (hl₀ : l₀ ∈ β) : IsValid β (mergeState x j₀ l₀) where
  refl j := mergeState_ge (h.refl j) j₀ l₀
  symm j l hjl := by
    rw [mergeState_iff] at hjl ⊢
    rcases hjl with h1 | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl (h.symm j l h1)
    · exact Or.inr (Or.inr ⟨h2, h1⟩)
    · exact Or.inr (Or.inl ⟨h2, h1⟩)
  trans j l m h1 h2 := by
    rw [mergeState_iff] at h1 h2 ⊢
    have S := h.symm
    have T := h.trans
    rcases h1 with h1 | ⟨h1a, h1b⟩ | ⟨h1a, h1b⟩ <;>
      rcases h2 with h2 | ⟨h2a, h2b⟩ | ⟨h2a, h2b⟩
    · exact Or.inl (T j l m h1 h2)
    · exact Or.inr (Or.inl ⟨T j l j₀ h1 h2a, h2b⟩)
    · exact Or.inr (Or.inr ⟨T j l l₀ h1 h2a, h2b⟩)
    · exact Or.inr (Or.inl ⟨h1a, T m l l₀ (S l m h2) h1b⟩)
    · exact Or.inr (Or.inl ⟨h1a, h2b⟩)
    · exact Or.inl (T j j₀ m h1a (S m j₀ h2b))
    · exact Or.inr (Or.inr ⟨h1a, T m l j₀ (S l m h2) h1b⟩)
    · exact Or.inl (T j l₀ m h1a (S m l₀ h2b))
    · exact Or.inr (Or.inr ⟨h1a, h2b⟩)
  born j l hjl hx := by
    rw [mergeState_iff] at hx
    rcases hx with h1 | ⟨h1, -⟩ | ⟨h1, -⟩
    · exact h.born j l hjl h1
    · by_cases hj : j = j₀
      · exact hj ▸ hj₀
      · exact h.born j j₀ hj h1
    · by_cases hj : j = l₀
      · exact hj ▸ hl₀
      · exact h.born j l₀ hj h1

theorem IsValid.isMergeStep {β β' : Finset (Fin k)} {x x' : ConnState k} (h : IsValid β x)
    (hβ : β ⊆ β') (hm : IsMergeStep β' x x') : IsValid β' x' := by
  obtain ⟨-, j₀, hj₀, l₀, hl₀, -, rfl⟩ := hm
  exact (h.mono hβ).mergeState hj₀ hl₀

open Classical in
/-- **Counting merges.** In a valid state, the merges of two distinct clusters of labels
of `β` are as many as the unordered pairs of clusters. -/
theorem card_isMergeStep {β : Finset (Fin k)} {x : ConnState k} (h : IsValid β x) :
    (Finset.univ.filter fun x' ↦ IsMergeStep β x x').card = (classesOn β x).choose 2 := by
  set cls : Fin k → Finset (Fin k) := fun j ↦ β.filter fun l ↦ x j l = true with hclsdef
  set Cl := β.image cls with hCl
  have hcl : classesOn β x = Cl.card := rfl
  let f : Finset (Fin k) × Finset (Fin k) → ConnState k := fun p j l ↦
    x j l || (decide (j ∈ p.1) && decide (l ∈ p.2)) || (decide (j ∈ p.2) && decide (l ∈ p.1))
  have hf : ∀ p j l, f p j l = true ↔ x j l = true ∨ (j ∈ p.1 ∧ l ∈ p.2) ∨ (j ∈ p.2 ∧ l ∈ p.1) := by
    intro p j l
    simp [f, Bool.or_eq_true, Bool.and_eq_true, or_assoc]
  have hmem : ∀ j₀ ∈ β, ∀ j, j ∈ cls j₀ ↔ x j j₀ = true := by
    intro j₀ hj₀ j
    simp only [hclsdef, Finset.mem_filter]
    constructor
    · rintro ⟨-, hx⟩
      exact h.symm _ _ hx
    · intro hx
      refine ⟨?_, h.symm _ _ hx⟩
      by_cases hj : j = j₀
      · exact hj ▸ hj₀
      · exact h.born j j₀ hj hx
  have hself : ∀ j ∈ β, j ∈ cls j := fun j hj ↦ (hmem j hj j).mpr (h.refl j)
  have hmerge : ∀ j₀ ∈ β, ∀ l₀ ∈ β, mergeState x j₀ l₀ = f (cls j₀, cls l₀) := by
    intro j₀ hj₀ l₀ hl₀
    funext j l
    apply Bool.eq_iff_iff.mpr
    rw [mergeState_iff, hf, hmem j₀ hj₀, hmem l₀ hl₀, hmem j₀ hj₀, hmem l₀ hl₀]
  have hcls_eq : ∀ j₀ ∈ β, ∀ a ∈ cls j₀, cls j₀ = cls a := by
    intro j₀ hj₀ a ha
    have ha' : x j₀ a = true := (Finset.mem_filter.mp ha).2
    ext l
    simp only [hclsdef, Finset.mem_filter]
    constructor
    · rintro ⟨hl, hx⟩
      exact ⟨hl, h.trans _ _ _ (h.symm _ _ ha') hx⟩
    · rintro ⟨hl, hx⟩
      exact ⟨hl, h.trans _ _ _ ha' hx⟩
  have hfswap : ∀ p, f p.swap = f p := by
    intro p
    funext j l
    apply Bool.eq_iff_iff.mpr
    rw [hf, hf, Prod.fst_swap, Prod.snd_swap]
    tauto
  have hE : Finset.univ.filter (fun x' ↦ IsMergeStep β x x') = Cl.offDiag.image f := by
    ext x'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image,
      Finset.mem_offDiag, hCl, Finset.mem_image]
    constructor
    · rintro ⟨-, j₀, hj₀, l₀, hl₀, hs, rfl⟩
      refine ⟨(cls j₀, cls l₀), ⟨⟨j₀, hj₀, rfl⟩, ⟨l₀, hl₀, rfl⟩, fun he ↦ ?_⟩,
        (hmerge j₀ hj₀ l₀ hl₀).symm⟩
      have he' : cls j₀ = cls l₀ := he
      have : l₀ ∈ cls j₀ := by rw [he']; exact hself l₀ hl₀
      rw [hmem j₀ hj₀] at this
      rw [h.symm _ _ this] at hs
      simp at hs
    · rintro ⟨⟨A, B⟩, ⟨⟨j₀, hj₀, rfl⟩, ⟨l₀, hl₀, rfl⟩, hAB⟩, rfl⟩
      have hs : x j₀ l₀ = false := by
        by_contra hc
        rw [Bool.not_eq_false] at hc
        exact hAB (hcls_eq j₀ hj₀ l₀ ((hmem j₀ hj₀ l₀).mpr (h.symm _ _ hc)))
      refine ⟨fun he ↦ ?_, j₀, hj₀, l₀, hl₀, hs, (hmerge j₀ hj₀ l₀ hl₀).symm⟩
      have : f (cls j₀, cls l₀) j₀ l₀ = true :=
        (hf _ _ _).mpr (Or.inr (Or.inl ⟨hself j₀ hj₀, hself l₀ hl₀⟩))
      rw [he, hs] at this
      exact Bool.false_ne_true this
  have hinj : ∀ p ∈ Cl.offDiag, ∀ q ∈ Cl.offDiag, f q = f p → q = p ∨ q = p.swap := by
    intro p hp q hq hqp
    simp only [Finset.mem_offDiag, hCl, Finset.mem_image] at hp hq
    obtain ⟨⟨a, ha, hqa⟩, ⟨c, hc, hqc⟩, hqne⟩ := hq
    have hfa : f q a c = true := by
      rw [hf, ← hqa, ← hqc]
      exact Or.inr (Or.inl ⟨hself a ha, hself c hc⟩)
    have hxac : x a c = false := by
      by_contra hcon
      rw [Bool.not_eq_false] at hcon
      apply hqne
      rw [← hqa, ← hqc]
      exact hcls_eq a ha c ((hmem a ha c).mpr (h.symm _ _ hcon))
    rw [hqp, hf, hxac] at hfa
    obtain ⟨⟨j₁, hj₁, hp1⟩, ⟨l₁, hl₁, hp2⟩, -⟩ := hp
    rcases hfa with hfa | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact absurd hfa Bool.false_ne_true
    · left
      rw [← hp1] at h1
      rw [← hp2] at h2
      ext1
      · rw [← hqa, ← hp1, hcls_eq j₁ hj₁ a h1]
      · rw [← hqc, ← hp2, hcls_eq l₁ hl₁ c h2]
    · right
      rw [← hp2] at h1
      rw [← hp1] at h2
      ext1
      · rw [← hqa, Prod.fst_swap, ← hp2, hcls_eq l₁ hl₁ a h1]
      · rw [← hqc, Prod.snd_swap, ← hp1, hcls_eq j₁ hj₁ c h2]
  have hfib : ∀ e ∈ Cl.offDiag.image f, (Cl.offDiag.filter fun q ↦ f q = e).card = 2 := by
    intro e he
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp he
    have hpne : p ≠ p.swap := by
      intro hps
      have := (Finset.mem_offDiag.mp hp).2.2
      exact this (congrArg Prod.fst hps)
    have hset : Cl.offDiag.filter (fun q ↦ f q = f p) = {p, p.swap} := by
      ext q
      simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨hq, hfq⟩
        exact hinj p hp q hq hfq
      · rintro (rfl | rfl)
        · exact ⟨hp, rfl⟩
        · refine ⟨?_, hfswap p⟩
          have := Finset.mem_offDiag.mp hp
          exact Finset.mem_offDiag.mpr ⟨this.2.1, this.1, fun he ↦ this.2.2 he.symm⟩
    rw [hset, Finset.card_pair hpne]
  have hcount : Cl.offDiag.card = 2 * (Cl.offDiag.image f).card := by
    rw [Finset.card_eq_sum_card_image f Cl.offDiag, Finset.sum_congr rfl hfib]
    simp [mul_comm]
  rw [hE, hcl, Nat.choose_two_right]
  rw [Finset.offDiag_card] at hcount
  have : Cl.card * Cl.card - Cl.card = Cl.card * (Cl.card - 1) := by
    rw [Nat.mul_sub_one]
  rw [this] at hcount
  omega

/-! ### Rates, survival and observation weights -/

/-- The merge rate from `x` to `x'` at time `c`: rate one for each pair of distinct
clusters of labels born at time `c`. -/
noncomputable def mergeRate (b : Fin k → ℝ) (c : ℝ) (x x' : ConnState k) : ℝ≥0∞ :=
  open Classical in if IsMergeStep (bornAt b c) x x' then 1 else 0

/-- The number `C(a(u), 2)` of pairs of clusters of labels born at time `u`. -/
noncomputable def pairCount (b : Fin k → ℝ) (x : ConnState k) (u : ℝ) : ℕ :=
  (classesOn (bornAt b u) x).choose 2

/-- The total merge hazard `C(a(u), 2) g(u)²` of the state `x` at time `u`. -/
noncomputable def hazard (g : ℝ → ℝ) (b : Fin k → ℝ) (x : ConnState k) (u : ℝ) : ℝ≥0∞ :=
  (pairCount b x u : ℝ≥0∞) * ENNReal.ofReal (g u ^ 2)

/-- The integrated hazard of the state `x` over `(a, t]`, possibly infinite. -/
noncomputable def cumHazard (g : ℝ → ℝ) (b : Fin k → ℝ) (x : ConnState k) (a t : ℝ) : ℝ≥0∞ :=
  ∫⁻ u in Ioc a t, hazard g b x u

/-- Probability that no two clusters of `x` merge during `(a, t]`. -/
noncomputable def surv (g : ℝ → ℝ) (b : Fin k → ℝ) (x : ConnState k) (a t : ℝ) : ℝ≥0∞ :=
  expNeg (cumHazard g b x a t)

/-- Indicator that `x` lies in `S τ` for the observation times `τ ∈ T` in `[a, t)`. -/
noncomputable def obsWeight (S : ℝ → Set (ConnState k)) (T : Finset ℝ) (x : ConnState k)
    (a t : ℝ) : ℝ≥0∞ :=
  open Classical in if ∀ τ ∈ T, a ≤ τ → τ < t → x ∈ S τ then 1 else 0

theorem bornAt_anti (b : Fin k → ℝ) {s t : ℝ} (hst : s ≤ t) : bornAt b t ⊆ bornAt b s := by
  intro j hj
  simp only [bornAt, Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
  exact hst.trans hj

theorem mergeRate_le_one (b : Fin k → ℝ) (c : ℝ) (x x' : ConnState k) :
    mergeRate b c x x' ≤ 1 := by
  unfold mergeRate
  split_ifs <;> simp

/-- Row sums of the merge rates are the pair counts, for valid states. -/
theorem sum_mergeRate {b : Fin k → ℝ} {c : ℝ} {x : ConnState k} (h : IsValid (bornAt b c) x) :
    ∑ x', mergeRate b c x x' = pairCount b x c := by
  classical
  simp only [mergeRate]
  rw [Finset.sum_boole]
  have := card_isMergeStep h
  simp only [pairCount]
  rw [← this]

theorem cumHazard_add (g : ℝ → ℝ) (b : Fin k → ℝ) (x : ConnState k) {s a t : ℝ}
    (hsa : s ≤ a) (hat : a ≤ t) :
    cumHazard g b x s t = cumHazard g b x s a + cumHazard g b x a t := by
  unfold cumHazard
  rw [← Ioc_union_Ioc_eq_Ioc hsa hat, lintegral_union measurableSet_Ioc
    (Ioc_disjoint_Ioc_of_le le_rfl)]

theorem surv_mul (g : ℝ → ℝ) (b : Fin k → ℝ) (x : ConnState k) {s a t : ℝ}
    (hsa : s ≤ a) (hat : a ≤ t) : surv g b x s t = surv g b x s a * surv g b x a t := by
  unfold surv
  rw [cumHazard_add g b x hsa hat, expNeg_add]

@[simp] theorem surv_self (g : ℝ → ℝ) (b : Fin k → ℝ) (x : ConnState k) (a : ℝ) :
    surv g b x a a = 1 := by
  simp [surv, cumHazard]

theorem surv_le_one (g : ℝ → ℝ) (b : Fin k → ℝ) (x : ConnState k) (a t : ℝ) :
    surv g b x a t ≤ 1 := expNeg_le_one _

theorem obsWeight_mul (S : ℝ → Set (ConnState k)) (T : Finset ℝ) (x : ConnState k) {s a t : ℝ}
    (hsa : s ≤ a) (hat : a ≤ t) :
    obsWeight S T x s t = obsWeight S T x s a * obsWeight S T x a t := by
  classical
  unfold obsWeight
  by_cases h1 : ∀ τ ∈ T, s ≤ τ → τ < a → x ∈ S τ
  · by_cases h2 : ∀ τ ∈ T, a ≤ τ → τ < t → x ∈ S τ
    · have h : ∀ τ ∈ T, s ≤ τ → τ < t → x ∈ S τ := by
        intro τ hτ hs ht
        by_cases hτa : τ < a
        · exact h1 τ hτ hs hτa
        · exact h2 τ hτ (not_lt.mp hτa) ht
      rw [ite_eq_left h, ite_eq_left h1, ite_eq_left h2, mul_one]
    · have h : ¬ ∀ τ ∈ T, s ≤ τ → τ < t → x ∈ S τ := fun h ↦
        h2 fun τ hτ ha ht ↦ h τ hτ (hsa.trans ha) ht
      rw [ite_eq_right h, ite_eq_right h2, mul_zero]
  · have h : ¬ ∀ τ ∈ T, s ≤ τ → τ < t → x ∈ S τ := fun h ↦
      h1 fun τ hτ hs ha ↦ h τ hτ hs (ha.trans_le hat)
    rw [ite_eq_right h, ite_eq_right h1, zero_mul]

@[simp] theorem obsWeight_self (S : ℝ → Set (ConnState k)) (T : Finset ℝ) (x : ConnState k)
    (a : ℝ) : obsWeight S T x a a = 1 := by
  have : ∀ τ ∈ T, a ≤ τ → τ < a → x ∈ S τ := fun τ _ h1 h2 ↦ absurd (h1.trans_lt h2) (lt_irrefl a)
  unfold obsWeight
  rw [ite_eq_left this]

@[simp] theorem obsWeight_empty (S : ℝ → Set (ConnState k)) (x : ConnState k) (a t : ℝ) :
    obsWeight S ∅ x a t = 1 := by
  simp [obsWeight]

theorem obsWeight_le_one (S : ℝ → Set (ConnState k)) (T : Finset ℝ) (x : ConnState k)
    (a t : ℝ) : obsWeight S T x a t ≤ 1 := by
  unfold obsWeight
  split_ifs <;> simp

theorem obsWeight_congr {S : ℝ → Set (ConnState k)} {T T' : Finset ℝ} (x : ConnState k)
    {a t : ℝ} (h : ∀ τ, a ≤ τ → τ < t → (τ ∈ T ↔ τ ∈ T')) :
    obsWeight S T x a t = obsWeight S T' x a t := by
  classical
  unfold obsWeight
  congr 1
  apply propext
  constructor
  · intro H τ hτ ha ht
    exact H τ ((h τ ha ht).mpr hτ) ha ht
  · intro H τ hτ ha ht
    exact H τ ((h τ ha ht).mp hτ) ha ht

/-! ### Measurability -/

/-- Any function of the set of born labels is jointly measurable in births and time. -/
theorem measurable_bornAt_comp {α : Type*} [MeasurableSpace α] (Φ : Finset (Fin k) → α) :
    Measurable (fun p : (Fin k → ℝ) × ℝ ↦ Φ (bornAt p.1 p.2)) := by
  classical
  have hvec : Measurable (fun p : (Fin k → ℝ) × ℝ ↦ fun j ↦ decide (p.2 ≤ p.1 j)) := by
    refine measurable_pi_iff.mpr fun j ↦ measurable_to_bool ?_
    have : (fun p : (Fin k → ℝ) × ℝ ↦ decide (p.2 ≤ p.1 j)) ⁻¹' {true} =
        {p | p.2 ≤ p.1 j} := by
      ext p
      simp
    rw [this]
    exact measurableSet_le measurable_snd ((measurable_pi_apply j).comp measurable_fst)
  have heq : (fun p : (Fin k → ℝ) × ℝ ↦ Φ (bornAt p.1 p.2)) =
      (fun v : Fin k → Bool ↦ Φ (Finset.univ.filter fun j ↦ v j = true)) ∘
        (fun p : (Fin k → ℝ) × ℝ ↦ fun j ↦ decide (p.2 ≤ p.1 j)) := by
    funext p
    simp only [Function.comp_apply, bornAt, decide_eq_true_eq]
  rw [heq]
  exact (measurable_of_countable _).comp hvec

theorem measurable_mergeRate (x x' : ConnState k) :
    Measurable (fun p : (Fin k → ℝ) × ℝ ↦ mergeRate p.1 p.2 x x') := by
  classical
  have := measurable_bornAt_comp (k := k) (α := ℝ≥0∞)
    (fun β ↦ if IsMergeStep β x x' then 1 else 0)
  exact this

theorem measurable_hazard {g : ℝ → ℝ} (hg : Measurable g) (x : ConnState k) :
    Measurable (fun p : (Fin k → ℝ) × ℝ ↦ hazard g p.1 x p.2) := by
  have h1 := measurable_bornAt_comp (k := k) (α := ℝ≥0∞)
    (fun β ↦ ((classesOn β x).choose 2 : ℝ≥0∞))
  exact h1.mul ((hg.comp measurable_snd).pow_const 2).ennreal_ofReal

theorem measurable_cumHazard {g : ℝ → ℝ} (hg : Measurable g) (x : ConnState k) :
    Measurable (fun p : (Fin k → ℝ) × ℝ × ℝ ↦ cumHazard g p.1 x p.2.1 p.2.2) := by
  have hset : MeasurableSet {q : ((Fin k → ℝ) × ℝ × ℝ) × ℝ | q.1.2.1 < q.2 ∧ q.2 ≤ q.1.2.2} :=
    (measurableSet_lt measurable_fst.snd.fst measurable_snd).inter
      (measurableSet_le measurable_snd measurable_fst.snd.snd)
  have hf : Measurable (fun q : ((Fin k → ℝ) × ℝ × ℝ) × ℝ ↦
      {q : ((Fin k → ℝ) × ℝ × ℝ) × ℝ | q.1.2.1 < q.2 ∧ q.2 ≤ q.1.2.2}.indicator
        (fun q ↦ hazard g q.1.1 x q.2) q) :=
    ((measurable_hazard hg x).comp (measurable_fst.fst.prodMk measurable_snd)).indicator hset
  have hm := hf.lintegral_prod_right' (ν := volume)
  convert hm using 1
  funext p
  simp only [cumHazard]
  rw [← lintegral_indicator measurableSet_Ioc]
  congr 1

theorem measurable_surv {g : ℝ → ℝ} (hg : Measurable g) (x : ConnState k) :
    Measurable (fun p : (Fin k → ℝ) × ℝ × ℝ ↦ surv g p.1 x p.2.1 p.2.2) :=
  measurable_expNeg.comp (measurable_cumHazard hg x)

theorem measurable_obsWeight (S : ℝ → Set (ConnState k)) (T : Finset ℝ) (x : ConnState k) :
    Measurable (fun p : ℝ × ℝ ↦ obsWeight S T x p.1 p.2) := by
  classical
  have hset : MeasurableSet {p : ℝ × ℝ | ∀ τ ∈ T, p.1 ≤ τ → τ < p.2 → x ∈ S τ} := by
    have : {p : ℝ × ℝ | ∀ τ ∈ T, p.1 ≤ τ → τ < p.2 → x ∈ S τ} =
        ⋂ τ ∈ T, ({p : ℝ × ℝ | τ < p.1} ∪ {p | p.2 ≤ τ} ∪ {_p | x ∈ S τ}) := by
      ext p
      simp only [Set.mem_ofPred_eq, mem_iInter, mem_union]
      constructor
      · intro h τ hτ
        by_cases h1 : p.1 ≤ τ
        · by_cases h2 : τ < p.2
          · exact Or.inr (h τ hτ h1 h2)
          · exact Or.inl (Or.inr (not_lt.mp h2))
        · exact Or.inl (Or.inl (not_le.mp h1))
      · intro h τ hτ h1 h2
        rcases h τ hτ with (h3 | h3) | h3
        · exact absurd h3 (not_lt.mpr h1)
        · exact absurd h2 (not_lt.mpr h3)
        · exact h3
    rw [this]
    exact Finset.measurableSet_biInter T fun τ _ ↦
      ((measurableSet_lt measurable_const measurable_fst).union
        (measurableSet_le measurable_snd measurable_const)).union (MeasurableSet.const _)
  exact Measurable.ite hset measurable_const measurable_const

/-! ### Path masses -/

/-- The weight of a first merge from `x` to `x'` at time `c`, seen from time `t`: hazard
density `g(c)²` for the merging pair, no merge in `(c, t]`, constraints in `[c, t)`. -/
noncomputable def stepWeight (g : ℝ → ℝ) (b : Fin k → ℝ) (S : ℝ → Set (ConnState k))
    (T : Finset ℝ) (x x' : ConnState k) (c t : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (g c ^ 2) * mergeRate b c x x' * surv g b x c t * obsWeight S T x c t

/-- The mass of the merge paths with `m` merges during `(s, t]`, from the state `x` at
time `t` to the state `y` at time `s`, restricted by the observation constraints. -/
noncomputable def pathMass (g : ℝ → ℝ) (b : Fin k → ℝ) (S : ℝ → Set (ConnState k))
    (T : Finset ℝ) : ℕ → ℝ → ℝ → ConnState k → ConnState k → ℝ≥0∞
  | 0, s, t, x, y => if x = y then surv g b x s t * obsWeight S T x s t else 0
  | m + 1, s, t, x, y => ∑ x', ∫⁻ c in Ioc s t,
      stepWeight g b S T x x' c t * pathMass g b S T m s c x' y

/-- The transition mass from `x` at time `t` to `y` at time `s`, over all numbers of merges. -/
noncomputable def transMass (g : ℝ → ℝ) (b : Fin k → ℝ) (S : ℝ → Set (ConnState k))
    (T : Finset ℝ) (s t : ℝ) (x y : ConnState k) : ℝ≥0∞ :=
  ∑' m, pathMass g b S T m s t x y

variable {g : ℝ → ℝ} {b : Fin k → ℝ} {S : ℝ → Set (ConnState k)} {T : Finset ℝ}

theorem measurable_stepWeight (hg : Measurable g) (b : Fin k → ℝ) (S : ℝ → Set (ConnState k))
    (T : Finset ℝ) (x x' : ConnState k) :
    Measurable (fun p : ℝ × ℝ ↦ stepWeight g b S T x x' p.1 p.2) := by
  have h1 : Measurable (fun p : ℝ × ℝ ↦ ENNReal.ofReal (g p.1 ^ 2)) :=
    ((hg.comp measurable_fst).pow_const 2).ennreal_ofReal
  have h2 := (measurable_mergeRate (k := k) x x').comp
    (show Measurable (fun p : ℝ × ℝ ↦ (b, p.1)) from measurable_const.prodMk measurable_fst)
  have h3 := (measurable_surv hg x).comp
    (show Measurable (fun p : ℝ × ℝ ↦ (b, p)) from measurable_const.prodMk measurable_id)
  have h4 := measurable_obsWeight S T x
  have h := ((h1.mul h2).mul h3).mul h4
  unfold stepWeight
  exact h

theorem measurable_stepWeight_left (hg : Measurable g) (b : Fin k → ℝ)
    (S : ℝ → Set (ConnState k)) (T : Finset ℝ) (x x' : ConnState k) (t : ℝ) :
    Measurable (fun c ↦ stepWeight g b S T x x' c t) := by
  have h := (measurable_stepWeight hg b S T x x').comp
    (show Measurable (fun c : ℝ ↦ (c, t)) from measurable_id.prodMk measurable_const)
  exact h

theorem measurable_pathMass (hg : Measurable g) (b : Fin k → ℝ) (S : ℝ → Set (ConnState k))
    (T : Finset ℝ) (m : ℕ) (s : ℝ) (x y : ConnState k) :
    Measurable (fun t ↦ pathMass g b S T m s t x y) := by
  induction m generalizing x with
  | zero =>
    have h3 := (measurable_surv hg x).comp (show Measurable (fun t : ℝ ↦ (b, s, t)) from
        measurable_const.prodMk (measurable_const.prodMk measurable_id))
    have h4 := (measurable_obsWeight S T x).comp (show Measurable (fun t : ℝ ↦ (s, t)) from
        measurable_const.prodMk measurable_id)
    by_cases hxy : x = y
    · simp only [pathMass, hxy, ↓reduceIte]
      exact (hxy ▸ h3).mul (hxy ▸ h4)
    · simp only [pathMass, hxy, ↓reduceIte]
      exact measurable_const
  | succ m ih =>
    simp only [pathMass]
    refine Finset.measurable_sum _ fun x' _ ↦ ?_
    have hset : MeasurableSet {p : ℝ × ℝ | s < p.2 ∧ p.2 ≤ p.1} :=
      (measurableSet_lt measurable_const measurable_snd).inter
        (measurableSet_le measurable_snd measurable_fst)
    have hF : Measurable (fun p : ℝ × ℝ ↦ {p : ℝ × ℝ | s < p.2 ∧ p.2 ≤ p.1}.indicator
        (fun p ↦ stepWeight g b S T x x' p.2 p.1 * pathMass g b S T m s p.2 x' y) p) :=
      (((measurable_stepWeight hg b S T x x').comp measurable_swap).mul
        ((ih x').comp measurable_snd)).indicator hset
    convert hF.lintegral_prod_right' (ν := volume) using 1
    funext t
    rw [← lintegral_indicator measurableSet_Ioc]
    congr 1

theorem measurable_transMass (hg : Measurable g) (b : Fin k → ℝ) (S : ℝ → Set (ConnState k))
    (T : Finset ℝ) (s : ℝ) (x y : ConnState k) :
    Measurable (fun t ↦ transMass g b S T s t x y) :=
  Measurable.tsum fun m ↦ measurable_pathMass hg b S T m s x y

theorem stepWeight_split (g : ℝ → ℝ) (b : Fin k → ℝ) (S : ℝ → Set (ConnState k))
    (T : Finset ℝ) (x x' : ConnState k) {c a t : ℝ} (hca : c ≤ a) (hat : a ≤ t) :
    stepWeight g b S T x x' c t =
      stepWeight g b S T x x' c a * (surv g b x a t * obsWeight S T x a t) := by
  unfold stepWeight
  rw [surv_mul g b x hca hat, obsWeight_mul S T x hca hat]
  ring

/-- **Chapman–Kolmogorov for path masses.** Splitting the paths at an intermediate time. -/
theorem pathMass_split (hg : Measurable g) {s a : ℝ} (hsa : s ≤ a) (m : ℕ) :
    ∀ t, a ≤ t → ∀ x y, pathMass g b S T m s t x y =
      ∑ p ∈ Finset.antidiagonal m, ∑ z, pathMass g b S T p.1 a t x z *
        pathMass g b S T p.2 s a z y := by
  induction m with
  | zero =>
    intro t hat x y
    simp only [Finset.Nat.antidiagonal_zero, Finset.sum_singleton, pathMass, ite_mul, zero_mul]
    rw [Finset.sum_ite_eq]
    simp only [Finset.mem_univ, ↓reduceIte]
    split_ifs with hxy
    · subst hxy
      rw [surv_mul g b x hsa hat, obsWeight_mul S T x hsa hat]
      ring
    · simp
  | succ m ih =>
    intro t hat x y
    rw [Finset.Nat.sum_antidiagonal_succ]
    have hsplit : ∀ x', ∫⁻ c in Ioc s t,
        stepWeight g b S T x x' c t * pathMass g b S T m s c x' y =
        (∫⁻ c in Ioc s a, stepWeight g b S T x x' c a * pathMass g b S T m s c x' y) *
            (surv g b x a t * obsWeight S T x a t) +
          ∑ p ∈ Finset.antidiagonal m, ∑ z,
            (∫⁻ c in Ioc a t, stepWeight g b S T x x' c t * pathMass g b S T p.1 a c x' z) *
              pathMass g b S T p.2 s a z y := by
      intro x'
      rw [← Ioc_union_Ioc_eq_Ioc hsa hat, lintegral_union measurableSet_Ioc
        (Ioc_disjoint_Ioc_of_le le_rfl)]
      congr 1
      · rw [← lintegral_mul_const _ (show Measurable (fun c ↦ stepWeight g b S T x x' c a *
          pathMass g b S T m s c x' y) from (measurable_stepWeight_left hg b S T x x' a).mul
          (measurable_pathMass hg b S T m s x' y))]
        apply setLIntegral_congr_fun measurableSet_Ioc
        intro c hc
        dsimp only
        rw [stepWeight_split g b S T x x' hc.2 hat]
        ring
      · have hrw : ∀ c ∈ Ioc a t, stepWeight g b S T x x' c t * pathMass g b S T m s c x' y =
            ∑ p ∈ Finset.antidiagonal m, ∑ z, stepWeight g b S T x x' c t *
              pathMass g b S T p.1 a c x' z * pathMass g b S T p.2 s a z y := by
          intro c hc
          rw [ih c hc.1.le x' y, Finset.mul_sum]
          refine Finset.sum_congr rfl fun p _ ↦ ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun z _ ↦ ?_
          ring
        rw [setLIntegral_congr_fun measurableSet_Ioc hrw]
        have hm : ∀ p : ℕ × ℕ, ∀ z, Measurable (fun c ↦ stepWeight g b S T x x' c t *
            pathMass g b S T p.1 a c x' z) := fun p z ↦
          (measurable_stepWeight_left hg b S T x x' t).mul (measurable_pathMass hg b S T p.1 a x' z)
        rw [lintegral_finsetSum _ fun p _ ↦ Finset.measurable_sum _ fun z _ ↦
          (hm p z).mul_const _]
        refine Finset.sum_congr rfl fun p _ ↦ ?_
        rw [lintegral_finsetSum _ fun z _ ↦ (hm p z).mul_const _]
        refine Finset.sum_congr rfl fun z _ ↦ ?_
        rw [lintegral_mul_const _ (hm p z)]
    have hlhs : pathMass g b S T (m + 1) s t x y = ∑ x', ∫⁻ c in Ioc s t,
        stepWeight g b S T x x' c t * pathMass g b S T m s c x' y := rfl
    rw [hlhs]
    simp_rw [hsplit]
    rw [Finset.sum_add_distrib]
    congr 1
    · rw [← Finset.sum_mul]
      have h0 : ∀ z, pathMass g b S T 0 a t x z =
          if x = z then surv g b x a t * obsWeight S T x a t else 0 := fun z ↦ rfl
      simp only [h0, ite_mul, zero_mul]
      rw [Finset.sum_ite_eq]
      simp only [Finset.mem_univ, ↓reduceIte]
      rw [mul_comm]
      rfl
    · rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun p _ ↦ ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun z _ ↦ ?_
      rw [← Finset.sum_mul]
      rfl

/-- The Cauchy product formula in `ℝ≥0∞`. -/
theorem ennreal_tsum_mul_tsum (f h : ℕ → ℝ≥0∞) :
    (∑' n, f n) * (∑' n, h n) = ∑' n, ∑ p ∈ Finset.antidiagonal n, f p.1 * h p.2 := by
  rw [← ENNReal.tsum_mul_right]
  simp_rw [← ENNReal.tsum_mul_left]
  rw [← ENNReal.tsum_prod (f := fun i j ↦ f i * h j),
    ← (Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd (A := ℕ)).tsum_eq, ENNReal.tsum_sigma']
  refine tsum_congr fun n ↦ ?_
  rw [← Finset.tsum_subtype]
  rfl

/-- **Chapman–Kolmogorov for transition masses.** -/
theorem transMass_split (hg : Measurable g) {s a t : ℝ} (hsa : s ≤ a) (hat : a ≤ t)
    (x y : ConnState k) :
    transMass g b S T s t x y = ∑ z, transMass g b S T a t x z * transMass g b S T s a z y := by
  unfold transMass
  simp_rw [pathMass_split hg hsa _ t hat x y]
  simp_rw [Finset.sum_comm (s := Finset.antidiagonal _)]
  rw [Summable.tsum_finsetSum fun _ _ ↦ ENNReal.summable]
  refine Finset.sum_congr rfl fun z _ ↦ ?_
  rw [ennreal_tsum_mul_tsum]

/-- **First-merge decomposition** of transition masses. -/
theorem transMass_eq (hg : Measurable g) (s t : ℝ) (x y : ConnState k) :
    transMass g b S T s t x y = pathMass g b S T 0 s t x y +
      ∑ x', ∫⁻ c in Ioc s t, stepWeight g b S T x x' c t * transMass g b S T s c x' y := by
  unfold transMass
  rw [tsum_eq_zero_add' ENNReal.summable]
  congr 1
  simp only [pathMass]
  rw [Summable.tsum_finsetSum fun _ _ ↦ ENNReal.summable]
  refine Finset.sum_congr rfl fun x' _ ↦ ?_
  rw [← lintegral_tsum fun m ↦ (show Measurable (fun c ↦ stepWeight g b S T x x' c t *
      pathMass g b S T m s c x' y) from (measurable_stepWeight_left hg b S T x x' t).mul
      (measurable_pathMass hg b S T m s x' y)).aemeasurable]
  congr 1
  funext c
  rw [ENNReal.tsum_mul_left]

/-! ### Supports and observation constraints -/

/-- Indicator that `y` lies in `S s`. -/
noncomputable def memWeight (S : ℝ → Set (ConnState k)) (s : ℝ) (y : ConnState k) : ℝ≥0∞ :=
  open Classical in if y ∈ S s then 1 else 0

/-- Path masses vanish unless the final state is valid. -/
theorem isValid_of_pathMass_ne_zero (m : ℕ) : ∀ {s t : ℝ} {x y : ConnState k}, s ≤ t →
    IsValid (bornAt b t) x → pathMass g b S T m s t x y ≠ 0 → IsValid (bornAt b s) y := by
  induction m with
  | zero =>
    intro s t x y hst hx h
    by_cases hxy : x = y
    · subst hxy
      exact hx.mono (bornAt_anti b hst)
    · simp [pathMass, hxy] at h
  | succ m ih =>
    intro s t x y hst hx h
    by_contra hy
    apply h
    simp only [pathMass]
    refine Finset.sum_eq_zero fun x' _ ↦ ?_
    rw [setLIntegral_congr_fun measurableSet_Ioc (g := fun _ ↦ 0) ?_, lintegral_zero]
    intro c hc
    dsimp only
    by_cases hm : IsMergeStep (bornAt b c) x x'
    · have hx' : IsValid (bornAt b c) x' := hx.isMergeStep (bornAt_anti b hc.2) hm
      have : pathMass g b S T m s c x' y = 0 := by
        by_contra hne
        exact hy (ih hc.1.le hx' hne)
      rw [this, mul_zero]
    · simp [stepWeight, mergeRate, hm]

theorem isValid_of_transMass_ne_zero {s t : ℝ} {x y : ConnState k} (hst : s ≤ t)
    (hx : IsValid (bornAt b t) x) (h : transMass g b S T s t x y ≠ 0) :
    IsValid (bornAt b s) y := by
  obtain ⟨m, hm⟩ : ∃ m, pathMass g b S T m s t x y ≠ 0 := by
    by_contra hc
    exact h (ENNReal.tsum_eq_zero.mpr fun m ↦ by
      by_contra hm
      exact hc ⟨m, hm⟩)
  exact isValid_of_pathMass_ne_zero m hst hx hm

theorem pathMass_congr_obs {T T' : Finset ℝ} (m : ℕ) : ∀ {s t : ℝ},
    (∀ τ, s ≤ τ → τ < t → (τ ∈ T ↔ τ ∈ T')) → ∀ x y,
    pathMass g b S T m s t x y = pathMass g b S T' m s t x y := by
  induction m with
  | zero =>
    intro s t h x y
    simp only [pathMass, obsWeight_congr x h]
  | succ m ih =>
    intro s t h x y
    simp only [pathMass]
    refine Finset.sum_congr rfl fun x' _ ↦ setLIntegral_congr_fun measurableSet_Ioc fun c hc ↦ ?_
    rw [stepWeight, stepWeight, obsWeight_congr x fun τ h1 h2 ↦ h τ (hc.1.le.trans h1) h2,
      ih (fun τ h1 h2 ↦ h τ h1 (h2.trans_le hc.2)) x' y]

/-- Observation constraints only matter inside the time window. -/
theorem transMass_congr_obs {T T' : Finset ℝ} {s t : ℝ}
    (h : ∀ τ, s ≤ τ → τ < t → (τ ∈ T ↔ τ ∈ T')) (x y : ConnState k) :
    transMass g b S T s t x y = transMass g b S T' s t x y :=
  tsum_congr fun m ↦ pathMass_congr_obs m h x y

theorem pathMass_obs_bottom (hg : Measurable g) {s : ℝ} (hsT : s ∈ T) (m : ℕ) :
    ∀ {t : ℝ}, s < t → (∀ τ ∈ T, s < τ → t ≤ τ) → ∀ x y,
      pathMass g b S T m s t x y = pathMass g b S ∅ m s t x y * memWeight S s y := by
  induction m with
  | zero =>
    intro t hst hT x y
    have hobs : obsWeight S T x s t = memWeight S s x := by
      unfold obsWeight memWeight
      congr 1
      apply propext
      constructor
      · intro H
        exact H s hsT le_rfl hst
      · intro H τ hτ h1 h2
        rcases h1.eq_or_lt with rfl | hlt
        · exact H
        · exact absurd (hT τ hτ hlt) (not_le.mpr h2)
    by_cases hxy : x = y
    · subst hxy
      simp only [pathMass, ↓reduceIte, hobs, obsWeight_empty, mul_one]
    · simp [pathMass, hxy]
  | succ m ih =>
    intro t hst hT x y
    simp only [pathMass]
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun x' _ ↦ ?_
    rw [← lintegral_mul_const _ (show Measurable (fun c ↦ stepWeight g b S ∅ x x' c t *
      pathMass g b S ∅ m s c x' y) from (measurable_stepWeight_left hg b S ∅ x x' t).mul
      (measurable_pathMass hg b S ∅ m s x' y))]
    refine setLIntegral_congr_fun measurableSet_Ioc fun c hc ↦ ?_
    have hobs : obsWeight S T x c t = 1 := by
      unfold obsWeight
      exact ite_eq_left fun τ hτ h1 h2 ↦
        absurd (hT τ hτ (hc.1.trans_le h1)) (not_le.mpr h2)
    rw [ih hc.1 (fun τ hτ h ↦ hc.2.trans (hT τ hτ h)) x' y, stepWeight, stepWeight, hobs,
      obsWeight_empty]
    ring

theorem transMass_obs_bottom (hg : Measurable g) {s t : ℝ} (hsT : s ∈ T) (hst : s < t)
    (hT : ∀ τ ∈ T, s < τ → t ≤ τ) (x y : ConnState k) :
    transMass g b S T s t x y = transMass g b S ∅ s t x y * memWeight S s y := by
  unfold transMass
  rw [← ENNReal.tsum_mul_right]
  exact tsum_congr fun m ↦ pathMass_obs_bottom hg hsT m hst hT x y

/-- Above all births and observation times nothing happens. -/
theorem transMass_top {a t : ℝ} (hb : ∀ j, b j ≤ a) (hT : ∀ τ ∈ T, ¬ (a ≤ τ ∧ τ < t))
    (x y : ConnState k) : transMass g b S T a t x y = if x = y then 1 else 0 := by
  have hborn : ∀ c, a < c → bornAt b c = ∅ := by
    intro c hc
    ext j
    simp only [bornAt, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
      iff_false, not_le]
    exact (hb j).trans_lt hc
  have hstep : ∀ m, pathMass g b S T (m + 1) a t x y = 0 := by
    intro m
    simp only [pathMass]
    refine Finset.sum_eq_zero fun x' _ ↦ ?_
    rw [setLIntegral_congr_fun measurableSet_Ioc (g := fun _ ↦ 0) ?_, lintegral_zero]
    intro c hc
    have hm : ¬ IsMergeStep (bornAt b c) x x' := by
      rw [hborn c hc.1]
      rintro ⟨-, j₀, hj₀, -⟩
      exact Finset.notMem_empty j₀ hj₀
    simp [stepWeight, mergeRate, hm]
  have hsurv : surv g b x a t = 1 := by
    have : cumHazard g b x a t = 0 := by
      unfold cumHazard
      rw [setLIntegral_congr_fun measurableSet_Ioc (g := fun _ ↦ 0) ?_, lintegral_zero]
      intro u hu
      simp [hazard, pairCount, hborn u hu.1, classesOn]
    simp [surv, this]
  have hobs : obsWeight S T x a t = 1 := by
    unfold obsWeight
    exact ite_eq_left fun τ hτ h1 h2 ↦ absurd ⟨h1, h2⟩ (hT τ hτ)
  unfold transMass
  rw [tsum_eq_single 0 fun m hm ↦ ?_]
  · simp only [pathMass, hsurv, hobs, mul_one]
  · obtain ⟨m', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm
    exact hstep m'

/-! ### Matrix exponentials: the Duhamel formula -/

section MatrixExp

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

theorem hasDerivAt_exp_entry_aux {ι : Type*} [Fintype ι] [DecidableEq ι] (G : Matrix ι ι ℝ)
    (x y : ι) (u : ℝ) :
    HasDerivAt (fun v : ℝ ↦ exp (v • G) x y) ((G * exp (u • G)) x y) u := by
  let L : Matrix ι ι ℝ →L[ℝ] ℝ := LinearMap.toContinuousLinearMap
    ((LinearMap.proj y).comp (LinearMap.proj x : (ι → ι → ℝ) →ₗ[ℝ] (ι → ℝ)))
  exact L.hasFDerivAt.comp_hasDerivAt u (hasDerivAt_exp_smul_const' (𝕂 := ℝ) G u)

end MatrixExp

/-- Entries of `exp (v • G)` are differentiable, with the derivative of the Kolmogorov
backward equation. -/
theorem hasDerivAt_exp_entry {ι : Type*} [Fintype ι] [DecidableEq ι] (G : Matrix ι ι ℝ)
    (x y : ι) (u : ℝ) :
    HasDerivAt (fun v : ℝ ↦ exp (v • G) x y) ((G * exp (u • G)) x y) u := by
  let := Matrix.linftyOpNormedRing (n := ι) (α := ℝ)
  let := Matrix.linftyOpNormedAlgebra (n := ι) (α := ℝ) (R := ℝ)
  exact hasDerivAt_exp_entry_aux G x y u

theorem continuous_exp_entry {ι : Type*} [Fintype ι] [DecidableEq ι] (G : Matrix ι ι ℝ)
    (x y : ι) : Continuous (fun v : ℝ ↦ exp (v • G) x y) :=
  continuous_iff_continuousAt.mpr fun u ↦ (hasDerivAt_exp_entry G x y u).continuousAt

/-- **Duhamel formula** for the entries of `exp (h • G)`: the diagonal part of `G` acts
as a killing rate and the off-diagonal part as jump rates. -/
theorem exp_entry_duhamel {ι : Type*} [Fintype ι] [DecidableEq ι] (G : Matrix ι ι ℝ)
    (x y : ι) (h : ℝ) :
    exp (h • G) x y = (if x = y then Real.exp (h * G x x) else 0) +
      ∫ u in (0 : ℝ)..h, Real.exp ((h - u) * G x x) *
        ∑ z, (if z = x then 0 else G x z) * exp (u • G) z y := by
  set F : ℝ → ℝ := fun u ↦ Real.exp (-(u * G x x)) *
    ∑ z, (if z = x then 0 else G x z) * exp (u • G) z y with hF
  have hsplit : ∀ u : ℝ, ∑ z, G x z * exp (u • G) z y =
      G x x * exp (u • G) x y + ∑ z, (if z = x then 0 else G x z) * exp (u • G) z y := by
    intro u
    have : ∀ z, G x z * exp (u • G) z y = (if z = x then G x x * exp (u • G) x y else 0) +
        (if z = x then 0 else G x z) * exp (u • G) z y := by
      intro z
      by_cases hz : z = x
      · subst hz
        simp
      · simp [hz]
    rw [Finset.sum_congr rfl fun z _ ↦ this z, Finset.sum_add_distrib, Finset.sum_ite_eq']
    simp
  have hderiv : ∀ u, HasDerivAt (fun v : ℝ ↦ Real.exp (-(v * G x x)) * exp (v • G) x y)
      (F u) u := by
    intro u
    have h1 : HasDerivAt (fun v : ℝ ↦ Real.exp (-(v * G x x)))
        (Real.exp (-(u * G x x)) * (-(1 * G x x))) u :=
      (((hasDerivAt_id u).mul_const (G x x)).neg).exp
    have h2 := hasDerivAt_exp_entry G x y u
    convert h1.mul h2 using 1
    rw [Matrix.mul_apply, hsplit u, hF]
    ring
  have hFc : Continuous F :=
    (Real.continuous_exp.comp (continuous_id.mul continuous_const).neg).mul
      (continuous_finsetSum _ fun z _ ↦ continuous_const.mul (continuous_exp_entry G z y))
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ ↦ hderiv u)
    (hFc.intervalIntegrable 0 h)
  simp only [zero_mul, neg_zero, Real.exp_zero, one_mul, zero_smul, NormedSpace.exp_zero,
    Matrix.one_apply] at hint
  have hI : ∫ u in (0 : ℝ)..h, Real.exp ((h - u) * G x x) *
      ∑ z, (if z = x then 0 else G x z) * exp (u • G) z y =
      Real.exp (h * G x x) * ∫ u in (0 : ℝ)..h, F u := by
    rw [← intervalIntegral.integral_const_mul]
    congr 1
    funext u
    rw [hF, ← mul_assoc, ← Real.exp_add]
    ring_nf
  have he : Real.exp (h * G x x) * Real.exp (-(h * G x x)) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  rw [hI, hint]
  split_ifs <;> linear_combination (-(exp (h • G) x y)) * he

open Classical in
theorem kingGen_offDiag (β : Finset (Fin k)) (x z : ConnState k) :
    (if z = x then 0 else kingGen β x z) = if IsMergeStep β x z then 1 else 0 := by
  by_cases hz : z = x
  · simp [hz, IsMergeStep]
  · simp [hz, kingGen, IsMergeStep]

theorem kingGen_self (β : Finset (Fin k)) (x : ConnState k) :
    kingGen β x x = -((classesOn β x).choose 2 : ℝ) := by
  simp [kingGen]

/-- Entries of `exp (h • kingGen β)` are nonnegative for `h ≥ 0`. -/
theorem exp_kingGen_nonneg (β : Finset (Fin k)) (x y : ConnState k) {h : ℝ} (hh : 0 ≤ h) :
    0 ≤ exp (h • kingGen β) x y := by
  classical
  suffices key : ∀ n, ∀ x, k * k - trueCount x = n → ∀ h : ℝ, 0 ≤ h →
      0 ≤ exp (h • kingGen β) x y from key _ x rfl h hh
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro x hxn h hh
  rw [exp_entry_duhamel]
  refine add_nonneg (by split_ifs <;> positivity) (intervalIntegral.integral_nonneg hh ?_)
  intro u hu
  refine mul_nonneg (Real.exp_pos _).le (Finset.sum_nonneg fun z _ ↦ ?_)
  rw [kingGen_offDiag]
  split_ifs with hz
  · have hlt := trueCount_lt_of_isMergeStep hz
    have hle := trueCount_le z
    exact mul_nonneg zero_le_one (ih _ (by omega) z rfl u hu.1)
  · simp

/-! ### Change of variables along the cumulative hazard -/

/-- Change of variables `v = ∫_s^c φ` for a nonnegative integrable density `φ`, which is
only assumed integrable (the cumulative function is absolutely continuous). -/
theorem integral_mul_comp_primitive {φ : ℝ → ℝ} {s t : ℝ} (hst : s ≤ t)
    (hφ : IntervalIntegrable φ volume s t) (hφ0 : ∀ u, 0 ≤ φ u) {F : ℝ → ℝ}
    (hF : Continuous F) :
    ∫ c in s..t, φ c * F (∫ u in s..c, φ u) = ∫ v in (0 : ℝ)..(∫ u in s..t, φ u), F v := by
  set H : ℝ → ℝ := fun c ↦ ∫ u in s..c, φ u with hH
  set Φ : ℝ → ℝ := fun v ↦ ∫ w in (0 : ℝ)..v, F w with hΦ
  have hHac : AbsolutelyContinuousOnInterval H s t :=
    hφ.absolutelyContinuousOnInterval_intervalIntegral Set.left_mem_uIcc
  have hrange : MapsTo H (uIcc s t) (Icc 0 (H t)) := by
    intro c hc
    rw [uIcc_of_le hst] at hc
    refine ⟨intervalIntegral.integral_nonneg hc.1 fun u _ ↦ hφ0 u, ?_⟩
    have h1 : IntervalIntegrable φ volume s c :=
      hφ.mono_set (by rw [uIcc_of_le hst, uIcc_of_le hc.1]; exact Icc_subset_Icc le_rfl hc.2)
    have h2 : IntervalIntegrable φ volume c t :=
      hφ.mono_set (by rw [uIcc_of_le hst, uIcc_of_le hc.2]; exact Icc_subset_Icc hc.1 le_rfl)
    have hadd := intervalIntegral.integral_add_adjacent_intervals h1 h2
    have hnn : 0 ≤ ∫ u in c..t, φ u := intervalIntegral.integral_nonneg hc.2 fun u _ ↦ hφ0 u
    simp only [hH]
    linarith
  obtain ⟨K, hK⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hF.continuousOn (s := Icc 0 (H t)))
  have hΦd : ∀ v, HasDerivAt Φ (F v) v := fun v ↦ (hF.integral_hasStrictDerivAt 0 v).hasDerivAt
  have hLip : LipschitzOnWith (Real.toNNReal K) Φ (Icc 0 (H t)) :=
    (convex_Icc 0 (H t)).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
      (fun v _ ↦ (hΦd v).hasDerivWithinAt) fun v hv ↦ by
        rw [← NNReal.coe_le_coe, coe_nnnorm]
        exact (hK v hv).trans (Real.le_coe_toNNReal K)
  have hΨ : AbsolutelyContinuousOnInterval (Φ ∘ H) s t :=
    hLip.comp_absolutelyContinuousOnInterval hrange hHac
  have hftc := hΨ.integral_deriv_eq_sub
  have hae : ∀ᵐ c, c ∈ uIoc s t → φ c * F (H c) = deriv (Φ ∘ H) c := by
    filter_upwards [hφ.ae_hasDerivAt_integral] with c hc hcI
    have hd : HasDerivAt H (φ c) c := hc (uIoc_subset_uIcc hcI) s Set.left_mem_uIcc
    rw [((hΦd (H c)).comp c hd).deriv]
    ring
  rw [intervalIntegral.integral_congr_ae hae, hftc]
  simp [Function.comp, hΦ, hH]

/-! ### Transition masses in a birth-free window -/

/-- Local square integrability of `g` on compact subintervals of `(0, 1)`: the source's
condition `∫_a^b f⁻² < ∞` for `0 < a < b < 1`, with `g = 1/f`. -/
def LocSqIntegrable (g : ℝ → ℝ) : Prop :=
  ∀ a c : ℝ, 0 < a → a < c → c < 1 → IntegrableOn (fun u ↦ g u ^ 2) (Icc a c)

theorem intervalIntegrable_sq (hg2 : LocSqIntegrable g) {s t : ℝ} (hs : 0 < s) (hst : s ≤ t)
    (ht : t < 1) : IntervalIntegrable (fun u ↦ g u ^ 2) volume s t := by
  rcases hst.eq_or_lt with rfl | hlt
  · exact IntervalIntegrable.refl
  · exact (intervalIntegrable_iff_integrableOn_Icc_of_le hst).mpr (hg2 s t hs hlt ht)

theorem bornAt_eq_of_birthsIn {s t c : ℝ} (hb : birthsIn b s t = ∅) (hc : c ∈ Ioc s t) :
    bornAt b c = bornAt b t := by
  ext j
  simp only [bornAt, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hcj
    rcases lt_or_ge (b j) t with hlt | hge
    · have : j ∈ birthsIn b s t := by simp [birthsIn, hc.1.trans_le hcj, hlt]
      rw [hb] at this
      exact absurd this (Finset.notMem_empty j)
    · exact hge
  · intro htj
    exact hc.2.trans htj

theorem surv_window (hg2 : LocSqIntegrable g) {s t : ℝ} (hs : 0 < s) (ht : t < 1)
    (hb : birthsIn b s t = ∅) {c t' : ℝ} (hsc : s ≤ c) (hct : c ≤ t') (htt : t' ≤ t)
    (x : ConnState k) :
    surv g b x c t' = ENNReal.ofReal (Real.exp (-(((classesOn (bornAt b t) x).choose 2 : ℝ) *
      ∫ u in c..t', g u ^ 2))) := by
  set q : ℝ := ((classesOn (bornAt b t) x).choose 2 : ℝ) with hq
  have hint : IntervalIntegrable (fun u ↦ g u ^ 2) volume c t' :=
    intervalIntegrable_sq hg2 (hs.trans_le hsc) hct (htt.trans_lt ht)
  have hcum : cumHazard g b x c t' = ENNReal.ofReal (q * ∫ u in c..t', g u ^ 2) := by
    unfold cumHazard
    rw [setLIntegral_congr_fun measurableSet_Ioc (g := fun u ↦ ENNReal.ofReal (q * g u ^ 2))]
    · rw [← ofReal_integral_eq_lintegral_ofReal
        ((intervalIntegrable_iff_integrableOn_Ioc_of_le hct).mp hint |>.const_mul q)
        (Eventually.of_forall fun u ↦ mul_nonneg (by positivity) (sq_nonneg _)),
        integral_const_mul, intervalIntegral.integral_of_le hct]
    · intro u hu
      have hborn : bornAt b u = bornAt b t :=
        bornAt_eq_of_birthsIn hb ⟨hsc.trans_lt hu.1, hu.2.trans htt⟩
      simp only [hazard, pairCount, hborn, hq]
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast]
  have hnn : 0 ≤ q * ∫ u in c..t', g u ^ 2 :=
    mul_nonneg (by positivity) (intervalIntegral.integral_nonneg hct fun u _ ↦ sq_nonneg _)
  unfold surv
  rw [hcum, expNeg_ofReal hnn]

/-- **Transition masses in a birth-free window are matrix exponentials.** Without births
in `(s, t)` and without observation constraints in `[s, t)`, the total mass of merge
paths from `x` at time `t` to `y` at time `s` is the `(x, y)` entry of
`exp ((∫_s^t g²) • kingGen β)`, where `β` is the set of labels born at time `t`. -/
theorem transMass_window (hg : Measurable g) (hg2 : LocSqIntegrable g) {s t : ℝ} (hs : 0 < s)
    (hst : s ≤ t) (ht : t < 1) (hb : birthsIn b s t = ∅) (hT : ∀ τ ∈ T, ¬ (s ≤ τ ∧ τ < t))
    (x y : ConnState k) :
    transMass g b S T s t x y =
      ENNReal.ofReal (exp ((∫ u in Icc s t, g u ^ 2) • kingGen (bornAt b t)) x y) := by
  classical
  set β := bornAt b t with hβ
  set G := kingGen β with hG
  set H : ℝ → ℝ := fun c ↦ ∫ u in s..c, g u ^ 2 with hH
  have hHt : (∫ u in Icc s t, g u ^ 2) = H t := by
    simp only [hH]
    rw [integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le hst]
  rw [hHt]
  have hint : ∀ t' ∈ Icc s t, IntervalIntegrable (fun u ↦ g u ^ 2) volume s t' :=
    fun t' ht' ↦ intervalIntegrable_sq hg2 hs ht'.1 (ht'.2.trans_lt ht)
  have hH0 : ∀ c, s ≤ c → 0 ≤ H c := fun c hc ↦
    intervalIntegral.integral_nonneg hc fun u _ ↦ sq_nonneg _
  have hHcont : ContinuousOn H (Icc s t) := by
    have := intervalIntegral.continuousOn_primitive_interval' (intervalIntegrable_sq hg2 hs hst ht)
      Set.left_mem_uIcc
    rwa [uIcc_of_le hst] at this
  suffices key : ∀ n, ∀ x, k * k - trueCount x = n → ∀ t' ∈ Icc s t, ∀ y,
      transMass g b S T s t' x y = ENNReal.ofReal (exp (H t' • G) x y) from
    key _ x rfl t ⟨hst, le_rfl⟩ y
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro x hxn t' ht' y
  set q : ℝ := ((classesOn β x).choose 2 : ℝ) with hq
  set h := H t' with hh
  have hGxx : G x x = -q := by rw [hG, kingGen_self]
  have hh0 : 0 ≤ h := hH0 t' ht'.1
  rw [transMass_eq hg]
  -- the no-merge term
  have hP0 : pathMass g b S T 0 s t' x y =
      ENNReal.ofReal (if x = y then Real.exp (h * G x x) else 0) := by
    have hobs : obsWeight S T x s t' = 1 := by
      unfold obsWeight
      exact ite_eq_left fun τ hτ h1 h2 ↦ absurd ⟨h1, h2.trans_le ht'.2⟩ (hT τ hτ)
    have hsv := surv_window hg2 hs ht hb le_rfl ht'.1 ht'.2 x
    rw [← hβ, ← hq] at hsv
    have hexp : Real.exp (-(q * ∫ u in s..t', g u ^ 2)) = Real.exp (h * G x x) := by
      rw [hGxx]
      simp only [hh, hH]
      ring_nf
    simp only [pathMass, hobs, mul_one, hsv, hexp]
    split_ifs <;> simp
  -- the first-merge terms
  have hI : ∀ x', ∫⁻ c in Ioc s t', stepWeight g b S T x x' c t' * transMass g b S T s c x' y =
      ENNReal.ofReal (∫ v in (0 : ℝ)..h, Real.exp ((h - v) * G x x) *
        ((if x' = x then 0 else G x x') * exp (v • G) x' y)) := by
    intro x'
    by_cases hm : IsMergeStep β x x'
    · have hlt := trueCount_lt_of_isMergeStep hm
      have hle := trueCount_le x'
      have hIH : ∀ c ∈ Icc s t, transMass g b S T s c x' y = ENNReal.ofReal (exp (H c • G) x' y) :=
        fun c hc ↦ ih _ (by omega) x' rfl c hc y
      set F : ℝ → ℝ := fun v ↦ Real.exp (-(q * (h - v))) * exp (v • G) x' y with hFdef
      have hFc : Continuous F :=
        (Real.continuous_exp.comp
          (continuous_const.mul (continuous_const.sub continuous_id)).neg).mul
          (continuous_exp_entry G x' y)
      have hrw : ∀ c ∈ Ioc s t', stepWeight g b S T x x' c t' * transMass g b S T s c x' y =
          ENNReal.ofReal (g c ^ 2 * F (H c)) := by
        intro c hc
        have hct : c ∈ Ioc s t := ⟨hc.1, hc.2.trans ht'.2⟩
        have hmr : mergeRate b c x x' = 1 := by
          unfold mergeRate
          rw [bornAt_eq_of_birthsIn hb hct]
          exact ite_eq_left hm
        have hobs : obsWeight S T x c t' = 1 := by
          unfold obsWeight
          exact ite_eq_left fun τ hτ h1 h2 ↦
            absurd ⟨hc.1.le.trans h1, h2.trans_le ht'.2⟩ (hT τ hτ)
        have hsv := surv_window hg2 hs ht hb hc.1.le hc.2 ht'.2 x
        rw [← hβ, ← hq] at hsv
        have hsub : (∫ u in c..t', g u ^ 2) = h - H c := by
          rw [hh, hH, intervalIntegral.integral_interval_sub_left (hint t' ht')
            (hint c ⟨hc.1.le, hct.2⟩)]
        rw [hsub] at hsv
        rw [stepWeight, hmr, hsv, hobs, hIH c ⟨hc.1.le, hct.2⟩, hFdef]
        dsimp only
        rw [mul_one, mul_one, ← ENNReal.ofReal_mul (sq_nonneg _), ← ENNReal.ofReal_mul
          (mul_nonneg (sq_nonneg _) (Real.exp_pos _).le), mul_assoc]
      rw [setLIntegral_congr_fun measurableSet_Ioc hrw]
      have hcomp : ContinuousOn (fun c ↦ F (H c)) (Icc s t') :=
        hFc.comp_continuousOn (hHcont.mono (Icc_subset_Icc le_rfl ht'.2))
      have hintF : IntegrableOn (fun c ↦ g c ^ 2 * F (H c)) (Icc s t') :=
        ((intervalIntegrable_iff_integrableOn_Icc_of_le ht'.1).mp (hint t' ht')).mul_continuousOn
          hcomp isCompact_Icc
      have hnonneg : ∀ c, s ≤ c → 0 ≤ g c ^ 2 * F (H c) := fun c hc ↦
        mul_nonneg (sq_nonneg _) (mul_nonneg (Real.exp_pos _).le
          (exp_kingGen_nonneg β x' y (hH0 c hc)))
      rw [← ofReal_integral_eq_lintegral_ofReal (hintF.mono_set Ioc_subset_Icc_self)
        ((ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun c hc ↦
          hnonneg c hc.1.le)), ← intervalIntegral.integral_of_le ht'.1]
      rw [integral_mul_comp_primitive ht'.1 (hint t' ht') (fun u ↦ sq_nonneg _) hFc]
      congr 1
      refine intervalIntegral.integral_congr fun v _ ↦ ?_
      have hoff : (if x' = x then 0 else G x x') = 1 := by
        rw [hG, kingGen_offDiag]
        exact ite_eq_left hm
      simp only [hFdef, hGxx, hoff]
      ring_nf
    · have hzero : ∀ c ∈ Ioc s t', stepWeight g b S T x x' c t' * transMass g b S T s c x' y =
          0 := by
        intro c hc
        have hmr : mergeRate b c x x' = 0 := by
          unfold mergeRate
          rw [bornAt_eq_of_birthsIn hb ⟨hc.1, hc.2.trans ht'.2⟩]
          exact ite_eq_right hm
        simp [stepWeight, hmr]
      rw [setLIntegral_congr_fun measurableSet_Ioc hzero, lintegral_zero]
      have hoff : (if x' = x then 0 else G x x') = 0 := by
        rw [hG, kingGen_offDiag]
        exact ite_eq_right hm
      simp [hoff]
  have hInn : ∀ x' ∈ Finset.univ, 0 ≤ ∫ v in (0 : ℝ)..h, Real.exp ((h - v) * G x x) *
      ((if x' = x then 0 else G x x') * exp (v • G) x' y) := by
    intro x' _
    refine intervalIntegral.integral_nonneg hh0 fun v hv ↦ ?_
    refine mul_nonneg (Real.exp_pos _).le (mul_nonneg ?_ (exp_kingGen_nonneg β x' y hv.1))
    rw [hG, kingGen_offDiag]
    split_ifs <;> norm_num
  rw [hP0, Finset.sum_congr rfl fun x' _ ↦ hI x', ← ENNReal.ofReal_sum_of_nonneg hInn,
    ← ENNReal.ofReal_add (by split_ifs <;> positivity) (Finset.sum_nonneg hInn),
    exp_entry_duhamel G x y h]
  congr 2
  have hcont : ∀ x' : ConnState k, Continuous (fun v : ℝ ↦ Real.exp ((h - v) * G x x) *
      ((if x' = x then 0 else G x x') * exp (v • G) x' y)) := fun x' ↦
    (Real.continuous_exp.comp ((continuous_const.sub continuous_id).mul continuous_const)).mul
      (continuous_const.mul (continuous_exp_entry G x' y))
  rw [← intervalIntegral.integral_finsetSum fun x' _ ↦ (hcont x').intervalIntegrable 0 h]
  refine intervalIntegral.integral_congr fun v _ ↦ ?_
  rw [Finset.mul_sum]

/-- **Transition masses are the continuous propagators** of the tracked chain. -/
theorem transMass_propagatorAux (hg : Measurable g) (hg2 : LocSqIntegrable g) {s : ℝ}
    (hs : 0 < s) : ∀ m : ℕ, ∀ t, s ≤ t → t < 1 → (birthsIn b s t).card ≤ m →
      (∀ τ ∈ T, ¬ (s ≤ τ ∧ τ < t)) → ∀ x y,
        transMass g b S T s t x y = ENNReal.ofReal (propagatorAux g b s m t x y) ∧
          0 ≤ propagatorAux g b s m t x y := by
  classical
  intro m
  induction m with
  | zero =>
    intro t hst ht hcard hT x y
    have hempty : birthsIn b s t = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hcard)
    exact ⟨transMass_window hg hg2 hs hst ht hempty hT x y,
      exp_kingGen_nonneg _ x y (integral_nonneg fun u ↦ sq_nonneg _)⟩
  | succ m ih =>
    intro t hst ht hcard hT x y
    by_cases hne : (birthsIn b s t).Nonempty
    · rw [propagatorAux, dite_eq_left_of_eq_true (eq_true hne)]
      obtain ⟨jstar, hjmem, hjeq⟩ := Finset.exists_mem_eq_sup' hne b
      set cstar := (birthsIn b s t).sup' hne b with hcstar
      have hjb : s < b jstar ∧ b jstar < t := by simpa [birthsIn] using hjmem
      have hsc : s < cstar := hjeq ▸ hjb.1
      have hct : cstar < t := hjeq ▸ hjb.2
      have htop : birthsIn b cstar t = ∅ := by
        ext j
        simp only [birthsIn, Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.notMem_empty, iff_false, not_and, not_lt]
        intro hj1
        by_contra hj2
        have hjmem' : j ∈ birthsIn b s t := by simp [birthsIn, hsc.trans hj1, not_le.mp hj2]
        exact absurd (Finset.le_sup' b hjmem') (not_le.mpr hj1)
      have hcard' : (birthsIn b s cstar).card ≤ m := by
        have hsub : birthsIn b s cstar ⊆ (birthsIn b s t).erase jstar := by
          intro j hj
          have hj' : s < b j ∧ b j < cstar := by simpa [birthsIn] using hj
          refine Finset.mem_erase.mpr ⟨fun h ↦ ?_, ?_⟩
          · subst h
            exact lt_irrefl _ (hjeq ▸ hj'.2)
          · simp [birthsIn, hj'.1, hj'.2.trans hct]
        have := Finset.card_le_card hsub
        rw [Finset.card_erase_of_mem hjmem] at this
        omega
      have hrest := ih cstar hsc.le (hct.trans ht) hcard' fun τ hτ h ↦
        hT τ hτ ⟨h.1, h.2.trans hct⟩
      have hwin := transMass_window (S := S) (T := T) hg hg2 (hs.trans hsc) hct.le ht htop
        fun τ hτ h ↦ hT τ hτ ⟨hsc.le.trans h.1, h.2⟩
      have hA : ∀ x z, 0 ≤ exp ((∫ u in Icc cstar t, g u ^ 2) • kingGen (bornAt b t)) x z :=
        fun x z ↦ exp_kingGen_nonneg _ x z (integral_nonneg fun u ↦ sq_nonneg _)
      refine ⟨?_, ?_⟩
      · rw [transMass_split hg hsc.le hct.le, Matrix.mul_apply,
          ENNReal.ofReal_sum_of_nonneg fun z _ ↦ mul_nonneg (hA x z) (hrest z y).2]
        refine Finset.sum_congr rfl fun z _ ↦ ?_
        rw [hwin x z, (hrest z y).1, ENNReal.ofReal_mul (hA x z)]
      · rw [Matrix.mul_apply]
        exact Finset.sum_nonneg fun z _ ↦ mul_nonneg (hA x z) (hrest z y).2
    · rw [propagatorAux, dite_eq_right_of_eq_false (eq_false hne)]
      exact ⟨transMass_window hg hg2 hs hst ht (Finset.not_nonempty_iff_eq_empty.mp hne) hT x y,
        exp_kingGen_nonneg _ x y (integral_nonneg fun u ↦ sq_nonneg _)⟩

theorem transMass_propagator (hg : Measurable g) (hg2 : LocSqIntegrable g) {s t : ℝ}
    (hs : 0 < s) (hst : s ≤ t) (ht : t < 1) (hT : ∀ τ ∈ T, ¬ (s ≤ τ ∧ τ < t))
    (x y : ConnState k) :
    transMass g b S T s t x y = ENNReal.ofReal (propagator g b s t x y) ∧
      0 ≤ propagator g b s t x y :=
  transMass_propagatorAux hg hg2 hs k t hst ht ((Finset.card_le_univ _).trans (by simp)) hT x y

/-! ### Normalization, including a divergent hazard at time zero -/

theorem pairCount_le (b : Fin k → ℝ) (x : ConnState k) (u : ℝ) : pairCount b x u ≤ k ^ 2 := by
  unfold pairCount classesOn
  calc _ ≤ _ ^ 2 := Nat.choose_le_pow _ 2
    _ ≤ k ^ 2 := by
      apply Nat.pow_le_pow_left
      exact Finset.card_image_le.trans ((Finset.card_le_univ _).trans (by simp))

/-- The real hazard `C(a(u), 2) g(u)²` of the state `x`. -/
noncomputable def hazardReal (g : ℝ → ℝ) (b : Fin k → ℝ) (x : ConnState k) (u : ℝ) : ℝ :=
  (pairCount b x u : ℝ) * g u ^ 2

theorem hazard_eq_ofReal (g : ℝ → ℝ) (b : Fin k → ℝ) (x : ConnState k) (u : ℝ) :
    hazard g b x u = ENNReal.ofReal (hazardReal g b x u) := by
  rw [hazard, hazardReal, ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]

theorem hazardReal_nonneg (g : ℝ → ℝ) (b : Fin k → ℝ) (x : ConnState k) (u : ℝ) :
    0 ≤ hazardReal g b x u :=
  mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)

theorem measurable_pairCount_real (b : Fin k → ℝ) (x : ConnState k) :
    Measurable (fun u ↦ (pairCount b x u : ℝ)) := by
  have h := (measurable_bornAt_comp (k := k) (α := ℝ)
    (fun β ↦ ((classesOn β x).choose 2 : ℝ))).comp
    (show Measurable (fun u : ℝ ↦ (b, u)) from measurable_const.prodMk measurable_id)
  exact h

theorem measurable_hazardReal (hg : Measurable g) (b : Fin k → ℝ) (x : ConnState k) :
    Measurable (hazardReal g b x) := by
  have h := (measurable_pairCount_real b x).mul (hg.pow_const 2)
  exact h

theorem intervalIntegrable_hazardReal (hg2 : LocSqIntegrable g) (b : Fin k → ℝ)
    (x : ConnState k) {a t : ℝ} (ha : 0 < a) (hat : a ≤ t) (ht : t < 1) :
    IntervalIntegrable (hazardReal g b x) volume a t := by
  have hsq := intervalIntegrable_sq hg2 ha hat ht
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hat] at hsq ⊢
  have h := hsq.bdd_mul (c := (k ^ 2 : ℝ))
    (measurable_pairCount_real b x).aestronglyMeasurable
    (Eventually.of_forall fun u ↦ by
      rw [Real.norm_natCast]
      exact_mod_cast pairCount_le b x u)
  exact h

/-- **One-step normalization.** Survival down to time `0` (zero if the hazard diverges at
`0`) plus the total first-merge density equals one. -/
theorem surv_add_lintegral_hazard (hg : Measurable g) (hg2 : LocSqIntegrable g)
    (x : ConnState k) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    surv g b x 0 t + ∫⁻ c in Ioc 0 t, hazard g b x c * surv g b x c t = 1 := by
  have h0 : ∀ u, 0 ≤ hazardReal g b x u := hazardReal_nonneg g b x
  have hInt : ∀ a, 0 < a → a ≤ t → IntervalIntegrable (hazardReal g b x) volume a t :=
    fun a ha hat ↦ intervalIntegrable_hazardReal hg2 b x ha hat ht1
  have hsurv : ∀ c, 0 < c → c ≤ t →
      surv g b x c t = ENNReal.ofReal (survival (hazardReal g b x) t c) := by
    intro c hc hct
    have hI := (intervalIntegrable_iff_integrableOn_Ioc_of_le hct).mp (hInt c hc hct)
    rw [surv, cumHazard, survival_eq_exp_neg]
    simp_rw [hazard_eq_ofReal]
    rw [← ofReal_integral_eq_lintegral_ofReal hI (Eventually.of_forall h0),
      ← intervalIntegral.integral_of_le hct,
      expNeg_ofReal (intervalIntegral.integral_nonneg hct fun u _ ↦ h0 u)]
  have hpos := positiveEventMeasure_univ h0 ht0 hInt
  rw [positiveEventMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at hpos
  have hcongr : ∫⁻ c in Ioc 0 t, hazard g b x c * surv g b x c t =
      ∫⁻ c in Ioc 0 t, ENNReal.ofReal (survival (hazardReal g b x) t c * hazardReal g b x c) := by
    refine setLIntegral_congr_fun measurableSet_Ioc fun c hc ↦ ?_
    rw [hsurv c hc.1 hc.2, hazard_eq_ofReal, ← ENNReal.ofReal_mul (h0 c), mul_comm]
  have hend : surv g b x 0 t = ENNReal.ofReal (endpointSurvival (hazardReal g b x) t) := by
    by_cases hdiv : ∫⁻ u in Ioc 0 t, ENNReal.ofReal (hazardReal g b x u) = ⊤
    · rw [endpointSurvival_eq_zero_of_lintegral_eq_top h0 ht0 hInt hdiv, ENNReal.ofReal_zero,
        surv, cumHazard]
      simp_rw [hazard_eq_ofReal]
      rw [hdiv]
      simp [expNeg]
    · have hIoc : IntegrableOn (hazardReal g b x) (Ioc 0 t) :=
        ⟨(measurable_hazardReal hg b x).aestronglyMeasurable,
          (hasFiniteIntegral_iff_ofReal (Eventually.of_forall h0)).mpr (lt_top_iff_ne_top.mpr hdiv)⟩
      have hII : IntervalIntegrable (hazardReal g b x) volume 0 t :=
        (intervalIntegrable_iff_integrableOn_Ioc_of_le ht0.le).mpr hIoc
      rw [endpointSurvival_eq_exp_neg_of_integrable h0 ht0 hII, surv, cumHazard]
      simp_rw [hazard_eq_ofReal]
      rw [← ofReal_integral_eq_lintegral_ofReal hIoc (Eventually.of_forall h0),
        ← intervalIntegral.integral_of_le ht0.le,
        expNeg_ofReal (intervalIntegral.integral_nonneg ht0.le fun u _ ↦ h0 u)]
  rw [hcongr, hpos, hend, ← ENNReal.ofReal_add (endpointSurvival_nonneg _ _)
    (sub_nonneg.mpr (endpointSurvival_le_one _ _))]
  simp

/-- **Mass one.** From a valid state at a time `t ∈ (0, 1)`, the merge paths down to time
`0` have total mass one: the coalescent is a genuine probability law, also when the
integrated hazard diverges at `0`. -/
theorem sum_transMass_eq_one (hg : Measurable g) (hg2 : LocSqIntegrable g) {t : ℝ}
    (ht0 : 0 < t) (ht1 : t < 1) {x : ConnState k} (hx : IsValid (bornAt b t) x) :
    ∑ y, transMass g b S ∅ 0 t x y = 1 := by
  suffices key : ∀ n, ∀ x, k * k - trueCount x = n → ∀ t, 0 < t → t < 1 →
      IsValid (bornAt b t) x → ∑ y, transMass g b S ∅ 0 t x y = 1 from
    key _ x rfl t ht0 ht1 hx
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro x hxn t ht0 ht1 hx
  have hstep : ∀ x', ∀ c ∈ Ioc 0 t, stepWeight g b S ∅ x x' c t *
      ∑ y, transMass g b S ∅ 0 c x' y = stepWeight g b S ∅ x x' c t := by
    intro x' c hc
    by_cases hm : IsMergeStep (bornAt b c) x x'
    · have hlt := trueCount_lt_of_isMergeStep hm
      have hle := trueCount_le x'
      rw [ih _ (by omega) x' rfl c hc.1 (hc.2.trans_lt ht1)
        (hx.isMergeStep (bornAt_anti b hc.2) hm), mul_one]
    · have : mergeRate b c x x' = 0 := by
        unfold mergeRate
        exact ite_eq_right hm
      simp [stepWeight, this]
  have hmeas : ∀ x' y, Measurable (fun c ↦ stepWeight g b S ∅ x x' c t *
      transMass g b S ∅ 0 c x' y) := fun x' y ↦
    (measurable_stepWeight_left hg b S ∅ x x' t).mul (measurable_transMass hg b S ∅ 0 x' y)
  calc ∑ y, transMass g b S ∅ 0 t x y
      = ∑ y, (pathMass g b S ∅ 0 0 t x y + ∑ x', ∫⁻ c in Ioc 0 t,
          stepWeight g b S ∅ x x' c t * transMass g b S ∅ 0 c x' y) :=
        Finset.sum_congr rfl fun y _ ↦ transMass_eq hg 0 t x y
    _ = surv g b x 0 t + ∑ x', ∫⁻ c in Ioc 0 t,
          stepWeight g b S ∅ x x' c t * ∑ y, transMass g b S ∅ 0 c x' y := by
        rw [Finset.sum_add_distrib]
        congr 1
        · simp [pathMass]
        · rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun x' _ ↦ ?_
          rw [← lintegral_finsetSum _ fun y _ ↦ hmeas x' y]
          congr 1
          funext c
          rw [Finset.mul_sum]
    _ = surv g b x 0 t + ∑ x', ∫⁻ c in Ioc 0 t, stepWeight g b S ∅ x x' c t := by
        congr 1
        exact Finset.sum_congr rfl fun x' _ ↦
          setLIntegral_congr_fun measurableSet_Ioc fun c hc ↦ hstep x' c hc
    _ = surv g b x 0 t + ∫⁻ c in Ioc 0 t, hazard g b x c * surv g b x c t := by
        congr 1
        rw [← lintegral_finsetSum _ fun x' _ ↦ measurable_stepWeight_left hg b S ∅ x x' t]
        refine setLIntegral_congr_fun measurableSet_Ioc fun c hc ↦ ?_
        simp only [stepWeight, obsWeight_empty, mul_one]
        rw [← Finset.sum_mul, ← Finset.mul_sum, sum_mergeRate (hx.mono (bornAt_anti b hc.2)),
          hazard]
        ring
    _ = 1 := surv_add_lintegral_hazard hg hg2 x ht0 ht1

/-! ### The observation recursion -/

/-- **The observation recursion is the density law.** Processing the observation times
from the top with the propagators computes the mass of the merge paths satisfying the
constraints. -/
theorem contVec_eq_transMass (hg : Measurable g) (hg2 : LocSqIntegrable g) :
    ∀ n (T : Finset ℝ), T.card ≤ n → ∀ t, 0 < t → t < 1 → (∀ τ ∈ T, 0 < τ ∧ τ < t) →
      ∀ v : ConnState k → ℝ, (∀ x, 0 ≤ v x) → (∀ x, v x ≠ 0 → IsValid (bornAt b t) x) →
        (∀ x, 0 ≤ contVec g b S n T t v x) ∧
          ENNReal.ofReal (∑ x, contVec g b S n T t v x) =
            ∑ x, ENNReal.ofReal (v x) * ∑ y, transMass g b S T 0 t x y := by
  classical
  intro n
  induction n with
  | zero =>
    intro T hT t ht0 ht1 hTt v hv hvs
    have hTe : T = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hT)
    subst hTe
    refine ⟨fun x ↦ hv x, ?_⟩
    simp only [contVec]
    rw [ENNReal.ofReal_sum_of_nonneg fun x _ ↦ hv x]
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    by_cases hx : v x = 0
    · simp [hx]
    · rw [sum_transMass_eq_one hg hg2 ht0 ht1 (hvs x hx), mul_one]
  | succ n ih =>
    intro T hT t ht0 ht1 hTt v hv hvs
    by_cases hne : T.Nonempty
    · set τ := T.max' hne with hτdef
      have hτT : τ ∈ T := T.max'_mem hne
      have hτ := hTt τ hτT
      set P := propagator g b τ t with hP
      have hPprop : ∀ x z, transMass g b S ∅ τ t x z = ENNReal.ofReal (P x z) ∧ 0 ≤ P x z :=
        fun x z ↦ transMass_propagator hg hg2 hτ.1 hτ.2.le ht1 (by simp) x z
      set w := restrictVec (S τ) (Matrix.vecMul v P) with hw
      have hvm : ∀ z, Matrix.vecMul v P z = ∑ x, v x * P x z := fun z ↦ rfl
      have hw0 : ∀ z, 0 ≤ w z := by
        intro z
        simp only [hw, restrictVec]
        split_ifs
        · rw [hvm]
          exact Finset.sum_nonneg fun x _ ↦ mul_nonneg (hv x) (hPprop x z).2
        · exact le_rfl
      have hws : ∀ z, w z ≠ 0 → IsValid (bornAt b τ) z := by
        intro z hz
        have hvz : ∑ x, v x * P x z ≠ 0 := by
          intro h0
          apply hz
          simp only [hw, restrictVec, hvm, h0, ite_self]
        obtain ⟨x, -, hx⟩ := Finset.exists_ne_zero_of_sum_ne_zero hvz
        have hvx : v x ≠ 0 := left_ne_zero_of_mul hx
        have hPx : P x z ≠ 0 := right_ne_zero_of_mul hx
        have htm : transMass g b S ∅ τ t x z ≠ 0 := by
          rw [(hPprop x z).1]
          exact (ENNReal.ofReal_pos.mpr (lt_of_le_of_ne (hPprop x z).2 (Ne.symm hPx))).ne'
        exact isValid_of_transMass_ne_zero hτ.2.le (hvs x hvx) htm
      have hT' : (T.erase τ).card ≤ n := by
        rw [Finset.card_erase_of_mem hτT]
        omega
      have hTt' : ∀ τ' ∈ T.erase τ, 0 < τ' ∧ τ' < τ := fun τ' h ↦
        ⟨(hTt τ' (Finset.mem_of_mem_erase h)).1,
          lt_of_le_of_ne (T.le_max' τ' (Finset.mem_of_mem_erase h)) (Finset.ne_of_mem_erase h)⟩
      obtain ⟨hpos, hid⟩ := ih (T.erase τ) hT' τ hτ.1 (hτ.2.trans ht1) hTt' w hw0 hws
      have hcv : contVec g b S (n + 1) T t v = contVec g b S n (T.erase τ) τ w := by
        rw [contVec, dite_eq_left_of_eq_true (eq_true hne)]
      refine ⟨fun x ↦ hcv ▸ hpos x, ?_⟩
      rw [hcv, hid]
      have hsplit : ∀ x, ∑ y, transMass g b S T 0 t x y = ∑ z, ENNReal.ofReal (P x z) *
          memWeight S τ z * ∑ y, transMass g b S (T.erase τ) 0 τ z y := by
        intro x
        simp_rw [transMass_split hg hτ.1.le hτ.2.le x]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun z _ ↦ ?_
        rw [← Finset.mul_sum, transMass_obs_bottom hg hτT hτ.2
          (fun τ' h1 h2 ↦ absurd (T.le_max' τ' h1) (not_le.mpr h2)) x z, (hPprop x z).1]
        congr 1
        refine Finset.sum_congr rfl fun y _ ↦ transMass_congr_obs (fun τ' _ h ↦ ?_) z y
        simp [Finset.mem_erase, h.ne]
      have hwz : ∀ z, ENNReal.ofReal (w z) =
          ∑ x, ENNReal.ofReal (v x) * (ENNReal.ofReal (P x z) * memWeight S τ z) := by
        intro z
        simp only [hw, restrictVec, memWeight, hvm]
        split_ifs
        · rw [ENNReal.ofReal_sum_of_nonneg fun x _ ↦ mul_nonneg (hv x) (hPprop x z).2]
          refine Finset.sum_congr rfl fun x _ ↦ ?_
          rw [ENNReal.ofReal_mul (hv x), mul_one]
        · simp
      have hR : ∑ x, ENNReal.ofReal (v x) * ∑ y, transMass g b S T 0 t x y =
          ∑ z, ∑ x, ENNReal.ofReal (v x) * (ENNReal.ofReal (P x z) * memWeight S τ z *
            ∑ y, transMass g b S (T.erase τ) 0 τ z y) := by
        conv_rhs => rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun x _ ↦ ?_
        rw [hsplit x, Finset.mul_sum]
      rw [hR]
      refine Finset.sum_congr rfl fun z _ ↦ ?_
      rw [hwz z, Finset.sum_mul]
      refine Finset.sum_congr rfl fun x _ ↦ ?_
      ring
    · have hcv : contVec g b S (n + 1) T t v = v := by
        rw [contVec, dite_eq_right_of_eq_false (eq_false hne)]
      have hTe : T = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
      subst hTe
      refine ⟨fun x ↦ hcv ▸ hv x, ?_⟩
      rw [hcv, ENNReal.ofReal_sum_of_nonneg fun x _ ↦ hv x]
      refine Finset.sum_congr rfl fun x _ ↦ ?_
      by_cases hx : v x = 0
      · simp [hx]
      · rw [sum_transMass_eq_one hg hg2 ht0 ht1 (hvs x hx), mul_one]

theorem topTime_pos (b : Fin k → ℝ) (T : Finset ℝ) : 0 < topTime b T := by
  have : (0 : ℝ) ≤ (Finset.univ.image b ∪ T).fold max 0 id :=
    (Finset.le_fold_max 0).mpr (Or.inl le_rfl)
  unfold topTime
  linarith

/-- **The observation limit is a density-law probability.** For births below one and
observation times in `(0, 1)`, the explicit observation limit of the tracked chain is the
mass of the merge paths of the coalescent from time `1` that satisfy the constraints. -/
theorem contVec_top_eq (hg : Measurable g) (hg2 : LocSqIntegrable g) (hb1 : ∀ j, b j < 1)
    (S : ℝ → Set (ConnState k)) (T : Finset ℝ) (hT : ∀ τ ∈ T, 0 < τ ∧ τ < 1) :
    0 ≤ ∑ s, contVec g b S T.card T (topTime b T) diagVec s ∧
      ENNReal.ofReal (∑ s, contVec g b S T.card T (topTime b T) diagVec s) =
        ∑ y, transMass g b S T 0 1 diagState y := by
  classical
  set t₀ := topTime b T with ht₀
  have ht₀1 : t₀ < 1 := topTime_lt_one hb1 fun τ h ↦ (hT τ h).2
  have ht₀0 : 0 < t₀ := topTime_pos b T
  have hobs : ∀ τ ∈ T, 0 < τ ∧ τ < t₀ := fun τ h ↦ ⟨(hT τ h).1, obs_lt_topTime b h (hT τ h).2⟩
  have hdiag0 : ∀ x : ConnState k, 0 ≤ (diagVec x : ℝ) := fun x ↦ by
    unfold diagVec
    split <;> norm_num
  have hdiags : ∀ x : ConnState k, (diagVec x : ℝ) ≠ 0 → IsValid (bornAt b t₀) x := by
    intro x hx
    have : x = diagState := by
      by_contra hne
      exact hx (by simp [diagVec, hne])
    exact this ▸ isValid_diagState _
  obtain ⟨hpos, hid⟩ := contVec_eq_transMass (S := S) hg hg2 T.card T le_rfl t₀ ht₀0 ht₀1 hobs
    diagVec hdiag0 hdiags
  refine ⟨Finset.sum_nonneg fun x _ ↦ hpos x, ?_⟩
  rw [hid, Finset.sum_eq_single diagState (fun x _ hx ↦ by simp [diagVec, hx]) (by simp)]
  simp only [diagVec, ↓reduceIte, ENNReal.ofReal_one, one_mul]
  refine Finset.sum_congr rfl fun y _ ↦ ?_
  rw [transMass_split hg ht₀0.le ht₀1.le]
  rw [Finset.sum_eq_single diagState (fun z _ hz ↦ ?_) (by simp)]
  · rw [transMass_top (fun j ↦ (birth_lt_topTime T hb1 j).le)
      (fun τ hτ h ↦ absurd h.1 (not_le.mpr (hobs τ hτ).2))]
    simp
  · rw [transMass_top (fun j ↦ (birth_lt_topTime T hb1 j).le)
      (fun τ hτ h ↦ absurd h.1 (not_le.mpr (hobs τ hτ).2)), ite_eq_right (Ne.symm hz), zero_mul]

/-- **Coalescence limits as path masses.** -/
theorem coalescenceLimit_eq (hg : Measurable g) (hg2 : LocSqIntegrable g) (hb1 : ∀ j, b j < 1)
    (γ : Fin k → Fin k → ℝ) :
    0 ≤ coalescenceLimit g b γ ∧ ENNReal.ofReal (coalescenceLimit g b γ) =
      ∑ y, transMass g b (obsSet γ) (obsTimes γ) 0 1 diagState y :=
  contVec_top_eq hg hg2 hb1 (obsSet γ) (obsTimes γ) fun _ h ↦ obsTimes_pos h

/-! ### Densities of merge histories -/

/-- Indicator of `c ∈ (0, t)`. -/
noncomputable def timeWeight (c t : ℝ) : ℝ≥0∞ :=
  open Classical in if 0 < c ∧ c < t then 1 else 0

/-- The density of a merge history with `m` merges, from the state `x` at time `t` down to
time `0`. The merge times `cs` are listed from the top: `cs 0` is the latest merge and the
following ones are in `(0, cs 0)`. The factors are the merge rate (one per pair of
clusters), the hazard density `g(c)²` at each merge, and the probability of no merge
between consecutive events, down to time `0`. -/
noncomputable def pathDensity (g : ℝ → ℝ) (b : Fin k → ℝ) : (m : ℕ) → ℝ → ConnState k →
    (Fin m → ConnState k) → (Fin m → ℝ) → ℝ≥0∞
  | 0, t, x, _, _ => surv g b x 0 t
  | m + 1, t, x, xs, cs => timeWeight (cs 0) t * ENNReal.ofReal (g (cs 0) ^ 2) *
      mergeRate b (cs 0) x (xs 0) * surv g b x (cs 0) t *
      pathDensity g b m (cs 0) (xs 0) (Fin.tail xs) (Fin.tail cs)

/-- The observation indicator of a merge history. -/
noncomputable def pathObs (S : ℝ → Set (ConnState k)) (T : Finset ℝ) : (m : ℕ) → ℝ →
    ConnState k → (Fin m → ConnState k) → (Fin m → ℝ) → ℝ≥0∞
  | 0, t, x, _, _ => obsWeight S T x 0 t
  | m + 1, t, x, xs, cs => obsWeight S T x (cs 0) t *
      pathObs S T m (cs 0) (xs 0) (Fin.tail xs) (Fin.tail cs)

theorem measurable_timeWeight : Measurable (fun p : ℝ × ℝ ↦ timeWeight p.1 p.2) := by
  unfold timeWeight
  exact Measurable.ite ((measurableSet_lt measurable_const measurable_fst).inter
    (measurableSet_lt measurable_fst measurable_snd)) measurable_const measurable_const

theorem measurable_fin_tail {m : ℕ} : Measurable (fun cs : Fin (m + 1) → ℝ ↦ Fin.tail cs) :=
  measurable_pi_iff.mpr fun i ↦ measurable_pi_apply i.succ

theorem measurable_pathDensity (hg : Measurable g) (m : ℕ) :
    ∀ (x : ConnState k) (xs : Fin m → ConnState k),
      Measurable (fun p : (Fin k → ℝ) × ℝ × (Fin m → ℝ) ↦
        pathDensity g p.1 m p.2.1 x xs p.2.2) := by
  induction m with
  | zero =>
    intro x xs
    have h := (measurable_surv hg x).comp (show Measurable
      (fun p : (Fin k → ℝ) × ℝ × (Fin 0 → ℝ) ↦ (p.1, (0 : ℝ), p.2.1)) from
        measurable_fst.prodMk (measurable_const.prodMk measurable_snd.fst))
    exact h
  | succ m ih =>
    intro x xs
    have hc0 : Measurable (fun p : (Fin k → ℝ) × ℝ × (Fin (m + 1) → ℝ) ↦ p.2.2 0) :=
      (measurable_pi_apply 0).comp measurable_snd.snd
    have h1 := measurable_timeWeight.comp (hc0.prodMk measurable_snd.fst)
    have h2 := ((hg.comp hc0).pow_const 2).ennreal_ofReal
    have h3 := (measurable_mergeRate x (xs 0)).comp (measurable_fst.prodMk hc0)
    have h4 := (measurable_surv hg x).comp (measurable_fst.prodMk (hc0.prodMk measurable_snd.fst))
    have h5 := (ih (xs 0) (Fin.tail xs)).comp
      (measurable_fst.prodMk (hc0.prodMk (measurable_fin_tail.comp measurable_snd.snd)))
    have h := (((h1.mul h2).mul h3).mul h4).mul h5
    simp only [pathDensity]
    exact h

theorem measurable_pathObs (S : ℝ → Set (ConnState k)) (T : Finset ℝ) (m : ℕ) :
    ∀ (x : ConnState k) (xs : Fin m → ConnState k),
      Measurable (fun p : ℝ × (Fin m → ℝ) ↦ pathObs S T m p.1 x xs p.2) := by
  induction m with
  | zero =>
    intro x xs
    have h := (measurable_obsWeight S T x).comp (show Measurable
      (fun p : ℝ × (Fin 0 → ℝ) ↦ ((0 : ℝ), p.1)) from measurable_const.prodMk measurable_fst)
    exact h
  | succ m ih =>
    intro x xs
    have hc0 : Measurable (fun p : ℝ × (Fin (m + 1) → ℝ) ↦ p.2 0) :=
      (measurable_pi_apply 0).comp measurable_snd
    have h1 := (measurable_obsWeight S T x).comp (hc0.prodMk measurable_fst)
    have h2 := (ih (xs 0) (Fin.tail xs)).comp (hc0.prodMk (measurable_fin_tail.comp measurable_snd))
    have h := h1.mul h2
    simp only [pathObs]
    exact h

/-- Integration over `ℝ^(m+1)` splits off the first coordinate. -/
theorem lintegral_fin_cons {m : ℕ} (F : (Fin (m + 1) → ℝ) → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ cs, F cs = ∫⁻ c, ∫⁻ cs', F (Fin.cons c cs') := by
  have hmp := measurePreserving_piFinSuccAbove (fun _ : Fin (m + 1) ↦ (volume : Measure ℝ)) 0
  have hFe : Measurable (fun p : ℝ × (Fin m → ℝ) ↦
      F ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) ↦ ℝ) 0).symm p)) :=
    hF.comp (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) ↦ ℝ) 0).symm.measurable
  rw [volume_pi, ← hmp.symm.lintegral_comp_emb
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) ↦ ℝ) 0).symm.measurableEmbedding F,
    lintegral_prod _ hFe.aemeasurable]
  refine lintegral_congr fun c ↦ ?_
  rw [volume_pi]
  refine lintegral_congr fun cs' ↦ ?_
  rw [MeasurableEquiv.piFinSuccAbove_symm_apply]
  simp [Fin.insertNthEquiv, Fin.insertNth_zero']

theorem lintegral_timeWeight_mul (f : ℝ → ℝ≥0∞) (t : ℝ) :
    ∫⁻ c, timeWeight c t * f c = ∫⁻ c in Ioc 0 t, f c := by
  rw [← setLIntegral_congr (Ioo_ae_eq_Ioc (μ := volume) (a := (0 : ℝ)) (b := t)),
    ← lintegral_indicator measurableSet_Ioo]
  refine lintegral_congr fun c ↦ ?_
  simp only [timeWeight, Set.indicator, mem_Ioo]
  split_ifs <;> simp

/-- **Fubini for merge histories.** Integrating the history density against the
observation indicator gives the path masses. -/
theorem sum_lintegral_pathDensity (hg : Measurable g) (S : ℝ → Set (ConnState k))
    (T : Finset ℝ) (m : ℕ) : ∀ (t : ℝ) (x : ConnState k),
      ∑ xs : Fin m → ConnState k, ∫⁻ cs, pathDensity g b m t x xs cs * pathObs S T m t x xs cs =
        ∑ y, pathMass g b S T m 0 t x y := by
  classical
  induction m with
  | zero =>
    intro t x
    rw [Fintype.sum_unique, volume_pi, Measure.pi_of_empty, lintegral_dirac]
    simp only [pathDensity, pathObs, pathMass]
    rw [Finset.sum_ite_eq]
    simp
  | succ m ih =>
    intro t x
    have hB : ∀ x0 (xs' : Fin m → ConnState k), Measurable (fun p : ℝ × (Fin m → ℝ) ↦
        pathDensity g b m p.1 x0 xs' p.2 * pathObs S T m p.1 x0 xs' p.2) := fun x0 xs' ↦
      ((measurable_pathDensity hg m x0 xs').comp (show Measurable
        (fun p : ℝ × (Fin m → ℝ) ↦ (b, p.1, p.2)) from measurable_const.prodMk measurable_id)).mul
        (measurable_pathObs S T m x0 xs')
    set A : ConnState k → ℝ → ℝ≥0∞ := fun x0 c ↦ timeWeight c t * stepWeight g b S T x x0 c t
      with hA
    have hAm : ∀ x0, Measurable (A x0) := fun x0 ↦
      (measurable_timeWeight.comp (show Measurable (fun c : ℝ ↦ (c, t)) from
        measurable_id.prodMk measurable_const)).mul (measurable_stepWeight_left hg b S T x x0 t)
    have hcons : ∀ x0 (xs' : Fin m → ConnState k) c (cs' : Fin m → ℝ),
        pathDensity g b (m + 1) t x (Fin.cons x0 xs') (Fin.cons c cs') *
          pathObs S T (m + 1) t x (Fin.cons x0 xs') (Fin.cons c cs') =
        A x0 c * (pathDensity g b m c x0 xs' cs' * pathObs S T m c x0 xs' cs') := by
      intro x0 xs' c cs'
      simp only [pathDensity, pathObs, Fin.cons_zero, Fin.tail_cons, hA, stepWeight]
      ring
    calc ∑ xs : Fin (m + 1) → ConnState k, ∫⁻ cs,
          pathDensity g b (m + 1) t x xs cs * pathObs S T (m + 1) t x xs cs
        = ∑ x0, ∑ xs' : Fin m → ConnState k, ∫⁻ cs, pathDensity g b (m + 1) t x
            (Fin.cons x0 xs') cs * pathObs S T (m + 1) t x (Fin.cons x0 xs') cs := by
          rw [← Fintype.sum_prod_type', ← (Fin.consEquiv fun _ ↦ ConnState k).sum_comp]
          rfl
      _ = ∑ x0, ∑ xs' : Fin m → ConnState k, ∫⁻ c, A x0 c *
            ∫⁻ cs', pathDensity g b m c x0 xs' cs' * pathObs S T m c x0 xs' cs' := by
          refine Finset.sum_congr rfl fun x0 _ ↦ Finset.sum_congr rfl fun xs' _ ↦ ?_
          have hFm : Measurable (fun cs : Fin (m + 1) → ℝ ↦ pathDensity g b (m + 1) t x
              (Fin.cons x0 xs') cs * pathObs S T (m + 1) t x (Fin.cons x0 xs') cs) := by
            have h1 := (measurable_pathDensity hg (m + 1) x (Fin.cons x0 xs')).comp
              (show Measurable (fun cs : Fin (m + 1) → ℝ ↦ (b, t, cs)) from
                measurable_const.prodMk (measurable_const.prodMk measurable_id))
            have h2 := (measurable_pathObs S T (m + 1) x (Fin.cons x0 xs')).comp
              (show Measurable (fun cs : Fin (m + 1) → ℝ ↦ (t, cs)) from
                measurable_const.prodMk measurable_id)
            exact h1.mul h2
          rw [lintegral_fin_cons _ hFm]
          refine lintegral_congr fun c ↦ ?_
          simp_rw [hcons]
          have hBc : Measurable (fun cs' : Fin m → ℝ ↦
              pathDensity g b m c x0 xs' cs' * pathObs S T m c x0 xs' cs') :=
            (hB x0 xs').comp (show Measurable (fun cs' : Fin m → ℝ ↦ (c, cs')) from
              measurable_const.prodMk measurable_id)
          rw [lintegral_const_mul _ hBc]
      _ = ∑ x0, ∫⁻ c, A x0 c * ∑ y, pathMass g b S T m 0 c x0 y := by
          refine Finset.sum_congr rfl fun x0 _ ↦ ?_
          have hm : ∀ xs' : Fin m → ConnState k, Measurable (fun c ↦ A x0 c * ∫⁻ cs',
              pathDensity g b m c x0 xs' cs' * pathObs S T m c x0 xs' cs') := fun xs' ↦
            (hAm x0).mul (hB x0 xs').lintegral_prod_right'
          rw [← lintegral_finsetSum _ fun xs' _ ↦ hm xs']
          refine lintegral_congr fun c ↦ ?_
          rw [← Finset.mul_sum, ih c x0]
      _ = ∑ y, pathMass g b S T (m + 1) 0 t x y := by
          simp only [pathMass]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun x0 _ ↦ ?_
          have hm : ∀ y, Measurable (fun c ↦ stepWeight g b S T x x0 c t *
              pathMass g b S T m 0 c x0 y) := fun y ↦
            (measurable_stepWeight_left hg b S T x x0 t).mul (measurable_pathMass hg b S T m 0 x0 y)
          rw [← lintegral_finsetSum _ fun y _ ↦ hm y]
          rw [show (fun c ↦ A x0 c * ∑ y, pathMass g b S T m 0 c x0 y) =
              fun c ↦ timeWeight c t * (stepWeight g b S T x x0 c t *
                ∑ y, pathMass g b S T m 0 c x0 y) from funext fun c ↦ by rw [hA]; ring,
            lintegral_timeWeight_mul]
          refine setLIntegral_congr_fun measurableSet_Ioc fun c _ ↦ ?_
          rw [Finset.mul_sum]

/-! ### Coalescence times of a merge history -/

/-- Pairwise coalescence times along a merge history from the state `x` at time `t`:
labels already related in `x` get `t`; labels never related get `0`. -/
noncomputable def coalTime : (m : ℕ) → ℝ → ConnState k → (Fin m → ConnState k) →
    (Fin m → ℝ) → Fin k → Fin k → ℝ
  | 0, t, x, _, _, j, l => if x j l = true then t else 0
  | m + 1, t, x, xs, cs, j, l => if x j l = true then t else
      coalTime m (cs 0) (xs 0) (Fin.tail xs) (Fin.tail cs) j l

theorem coalTime_of_true {m : ℕ} {t : ℝ} {x : ConnState k} {xs : Fin m → ConnState k}
    {cs : Fin m → ℝ} {j l : Fin k} (h : x j l = true) : coalTime m t x xs cs j l = t := by
  cases m <;> simp [coalTime, h]

theorem coalTime_le (m : ℕ) : ∀ {t : ℝ} {x : ConnState k} {xs : Fin m → ConnState k}
    {cs : Fin m → ℝ}, 0 ≤ t → pathDensity g b m t x xs cs ≠ 0 → ∀ j l,
      coalTime m t x xs cs j l ≤ t := by
  induction m with
  | zero =>
    intro t x xs cs ht _ j l
    simp only [coalTime]
    split_ifs <;> linarith
  | succ m ih =>
    intro t x xs cs ht hd j l
    simp only [coalTime]
    split_ifs
    · exact le_rfl
    · have htw : timeWeight (cs 0) t ≠ 0 := by
        intro h0
        apply hd
        simp [pathDensity, h0]
      have hc : 0 < cs 0 ∧ cs 0 < t := by
        by_contra hcon
        exact htw (by simp [timeWeight, hcon])
      have hd' : pathDensity g b m (cs 0) (xs 0) (Fin.tail xs) (Fin.tail cs) ≠ 0 := by
        intro h0
        apply hd
        simp [pathDensity, h0]
      exact (ih hc.1.le hd' j l).trans hc.2.le

theorem measurable_coalTime (m : ℕ) : ∀ (x : ConnState k) (xs : Fin m → ConnState k) (j l : Fin k),
    Measurable (fun p : ℝ × (Fin m → ℝ) ↦ coalTime m p.1 x xs p.2 j l) := by
  induction m with
  | zero =>
    intro x xs j l
    simp only [coalTime]
    split_ifs
    · exact measurable_fst
    · exact measurable_const
  | succ m ih =>
    intro x xs j l
    simp only [coalTime]
    split_ifs
    · exact measurable_fst
    · have h := (ih (xs 0) (Fin.tail xs) j l).comp (show Measurable
        (fun p : ℝ × (Fin (m + 1) → ℝ) ↦ (p.2 0, Fin.tail p.2)) from
          ((measurable_pi_apply 0).comp measurable_snd).prodMk
            (measurable_fin_tail.comp measurable_snd))
      exact h

/-- **Coalescence-time events as observation constraints.** On the support of the history
density, all pairwise coalescence times exceed thresholds `γ` (with nonzero off-diagonal
entries) below `t` exactly when the observation constraints of `γ` hold. -/
theorem pathObs_eq_ite {γ : Fin k → Fin k → ℝ} (hγ0 : ∀ j l, j ≠ l → γ j l ≠ 0) (m : ℕ) :
    ∀ {t : ℝ} {x : ConnState k} {xs : Fin m → ConnState k} {cs : Fin m → ℝ}, t ≤ 1 →
      pathDensity g b m t x xs cs ≠ 0 →
      pathObs (obsSet γ) (obsTimes γ) m t x xs cs = (open Classical in
        if ∀ j l, j ≠ l → γ j l < t → γ j l < coalTime m t x xs cs j l then 1 else 0) := by
  classical
  induction m with
  | zero =>
    intro t x xs cs ht1 _
    simp only [pathObs, obsWeight, coalTime]
    congr 1
    apply propext
    constructor
    · intro H j l hjl hγt
      by_cases hx : x j l = true
      · simpa [hx] using hγt
      · simp only [hx, Bool.false_eq_true, ↓reduceIte]
        by_contra hge
        have hpos : 0 < γ j l := lt_of_le_of_ne (not_lt.mp hge) (hγ0 j l hjl).symm
        have hmem : γ j l ∈ obsTimes γ :=
          mem_obsTimes.mpr ⟨j, l, hjl, hpos, hγt.trans_le ht1, rfl⟩
        exact hx (H _ hmem hpos.le hγt j l hjl rfl)
    · intro H τ hτ _ hτt j l hjl hγτ
      have hpos := (obsTimes_pos hτ).1
      have := H j l hjl (hγτ ▸ hτt)
      by_contra hx
      simp only [hx, ↓reduceIte] at this
      linarith
  | succ m ih =>
    intro t x xs cs ht1 hd
    have htw : timeWeight (cs 0) t ≠ 0 := by
      intro h0
      apply hd
      simp [pathDensity, h0]
    have hc : 0 < cs 0 ∧ cs 0 < t := by
      by_contra hcon
      exact htw (by simp [timeWeight, hcon])
    have hmr : mergeRate b (cs 0) x (xs 0) ≠ 0 := by
      intro h0
      apply hd
      simp [pathDensity, h0]
    have hm : IsMergeStep (bornAt b (cs 0)) x (xs 0) := by
      by_contra hcon
      exact hmr (by simp [mergeRate, hcon])
    have hd' : pathDensity g b m (cs 0) (xs 0) (Fin.tail xs) (Fin.tail cs) ≠ 0 := by
      intro h0
      apply hd
      simp [pathDensity, h0]
    have hle := coalTime_le m hc.1.le hd'
    have hiff : ((∀ τ ∈ obsTimes γ, cs 0 ≤ τ → τ < t → x ∈ obsSet γ τ) ∧
        (∀ j l, j ≠ l → γ j l < cs 0 →
          γ j l < coalTime m (cs 0) (xs 0) (Fin.tail xs) (Fin.tail cs) j l)) ↔
        (∀ j l, j ≠ l → γ j l < t → γ j l < coalTime (m + 1) t x xs cs j l) := by
      constructor
      · rintro ⟨hA, hB⟩ j l hjl hγt
        simp only [coalTime]
        split_ifs with hx
        · exact hγt
        · by_cases hγc : γ j l < cs 0
          · exact hB j l hjl hγc
          · exfalso
            have hpos : 0 < γ j l := hc.1.trans_le (not_lt.mp hγc)
            have hmem : γ j l ∈ obsTimes γ :=
              mem_obsTimes.mpr ⟨j, l, hjl, hpos, hγt.trans_le ht1, rfl⟩
            exact hx (hA _ hmem (not_lt.mp hγc) hγt j l hjl rfl)
      · intro H
        refine ⟨fun τ hτ hcτ hτt j l hjl hγτ ↦ ?_, fun j l hjl hγc ↦ ?_⟩
        · have h1 := H j l hjl (hγτ ▸ hτt)
          simp only [coalTime] at h1
          by_contra hx
          simp only [hx, ↓reduceIte] at h1
          have h2 := hle j l
          linarith
        · have h1 := H j l hjl (hγc.trans hc.2)
          simp only [coalTime] at h1
          split_ifs at h1 with hx
          · rw [coalTime_of_true (hm.ge hx)]
            exact hγc
          · exact h1
    rw [pathObs, ih (hc.2.le.trans ht1) hd']
    unfold obsWeight
    by_cases hA : ∀ τ ∈ obsTimes γ, cs 0 ≤ τ → τ < t → x ∈ obsSet γ τ
    · by_cases hB : ∀ j l, j ≠ l → γ j l < cs 0 →
          γ j l < coalTime m (cs 0) (xs 0) (Fin.tail xs) (Fin.tail cs) j l
      · rw [ite_eq_left hA, ite_eq_left hB, ite_eq_left (hiff.mp ⟨hA, hB⟩), one_mul]
      · rw [ite_eq_left hA, ite_eq_right hB, ite_eq_right fun h ↦ hB (hiff.mpr h).2, mul_zero]
    · rw [ite_eq_right hA, ite_eq_right fun h ↦ hA (hiff.mpr h).1, zero_mul]

theorem pathObs_empty (S : ℝ → Set (ConnState k)) (m : ℕ) : ∀ (t : ℝ) (x : ConnState k)
    (xs : Fin m → ConnState k) (cs : Fin m → ℝ), pathObs S ∅ m t x xs cs = 1 := by
  induction m with
  | zero => intro t x xs cs; simp [pathObs]
  | succ m ih => intro t x xs cs; simp [pathObs, ih]

/-! ### The law of the coalescent genealogy -/

/-- The births and pairwise coalescence times of the merge history `xs` with merge times
`cs`, started from singletons at time `1`. Diagonal entries are births, and two labels
whose clusters never merge have coalescence time `0`. -/
noncomputable def genealogyOf (m : ℕ) (xs : Fin m → ConnState k) (b : Fin k → ℝ)
    (cs : Fin m → ℝ) : GenealogySpace k :=
  (b, fun j l ↦ if j = l then b j else coalTime m 1 diagState xs cs j l)

theorem measurable_genealogyOf (m : ℕ) (xs : Fin m → ConnState k) :
    Measurable (fun p : (Fin k → ℝ) × (Fin m → ℝ) ↦ genealogyOf m xs p.1 p.2) := by
  have h2 : Measurable (fun p : (Fin k → ℝ) × (Fin m → ℝ) ↦
      fun j l ↦ if j = l then p.1 j else coalTime m 1 diagState xs p.2 j l) := by
    refine measurable_pi_iff.mpr fun j ↦ measurable_pi_iff.mpr fun l ↦ ?_
    by_cases hjl : j = l
    · simp only [hjl, ↓reduceIte]
      exact (measurable_pi_apply l).comp measurable_fst
    · simp only [hjl, ↓reduceIte]
      have h := (measurable_coalTime m diagState xs j l).comp
        (show Measurable (fun p : (Fin k → ℝ) × (Fin m → ℝ) ↦ ((1 : ℝ), p.2)) from
          measurable_const.prodMk measurable_snd)
      exact h
  exact measurable_fst.prodMk h2

/-- The law of the births and merge times along the merge history `xs` with `m` merges:
births are uniform on `[0, 1]^k`, merge times have the density `pathDensity`. -/
noncomputable def historyMeasure (g : ℝ → ℝ) (k m : ℕ) (xs : Fin m → ConnState k) :
    Measure ((Fin k → ℝ) × (Fin m → ℝ)) :=
  ((cubeMeasure k).prod volume).withDensity fun p ↦ pathDensity g p.1 m 1 diagState xs p.2

/-- **The law of the continuous coalescent genealogy**, defined from the density of merge
histories: the image on the genealogy space (births and pairwise coalescence times) of the
history laws, summed over the number `m` of merges and the merge histories `xs`. -/
noncomputable def coalescentLaw (g : ℝ → ℝ) (k : ℕ) : Measure (GenealogySpace k) :=
  Measure.sum fun m : ℕ ↦ ∑ xs : Fin m → ConnState k,
    (historyMeasure g k m xs).map fun p ↦ genealogyOf m xs p.1 p.2

theorem coalescentLaw_apply (hg : Measurable g) {E : Set (GenealogySpace k)}
    (hE : MeasurableSet E) :
    coalescentLaw g k E = ∫⁻ b, (∑' m, ∑ xs : Fin m → ConnState k, ∫⁻ cs : Fin m → ℝ,
      E.indicator 1 (genealogyOf m xs b cs) * pathDensity g b m 1 diagState xs cs)
        ∂cubeMeasure k := by
  have hF : ∀ m (xs : Fin m → ConnState k), Measurable (fun p : (Fin k → ℝ) × (Fin m → ℝ) ↦
      E.indicator 1 (genealogyOf m xs p.1 p.2) * pathDensity g p.1 m 1 diagState xs p.2) := by
    intro m xs
    have h1 : Measurable (fun p : (Fin k → ℝ) × (Fin m → ℝ) ↦
        E.indicator (1 : GenealogySpace k → ℝ≥0∞) (genealogyOf m xs p.1 p.2)) :=
      (measurable_one.indicator hE).comp (measurable_genealogyOf m xs)
    have h2 := (measurable_pathDensity hg m diagState xs).comp
      (show Measurable (fun p : (Fin k → ℝ) × (Fin m → ℝ) ↦ (p.1, (1 : ℝ), p.2)) from
        measurable_fst.prodMk (measurable_const.prodMk measurable_snd))
    exact h1.mul h2
  rw [coalescentLaw, Measure.sum_apply _ hE, lintegral_tsum fun m ↦
    (Finset.measurable_sum _ fun xs _ ↦ (hF m xs).lintegral_prod_right').aemeasurable]
  refine tsum_congr fun m ↦ ?_
  rw [Measure.coe_finsetSum, Finset.sum_apply, lintegral_finsetSum _ fun xs _ ↦
    (hF m xs).lintegral_prod_right']
  refine Finset.sum_congr rfl fun xs _ ↦ ?_
  rw [Measure.map_apply (measurable_genealogyOf m xs) hE, historyMeasure,
    withDensity_apply _ (measurable_genealogyOf m xs hE), ← lintegral_indicator
    (measurable_genealogyOf m xs hE), ← lintegral_prod _ (hF m xs).aemeasurable]
  refine lintegral_congr fun p ↦ ?_
  by_cases hp : genealogyOf m xs p.1 p.2 ∈ E
  · have hp' : p ∈ (fun p : (Fin k → ℝ) × (Fin m → ℝ) ↦ genealogyOf m xs p.1 p.2) ⁻¹' E := hp
    simp [Set.indicator, hp, hp']
  · have hp' : p ∉ (fun p : (Fin k → ℝ) × (Fin m → ℝ) ↦ genealogyOf m xs p.1 p.2) ⁻¹' E := hp
    simp [Set.indicator, hp, hp']

/-- **The upper-set masses at fixed births.** -/
theorem inner_upperSet (hg : Measurable g) (hg2 : LocSqIntegrable g) {α : Fin k → ℝ}
    {γ : Fin k → Fin k → ℝ} (hγ0 : ∀ j l, j ≠ l → γ j l ≠ 0) (hb1 : ∀ j, b j < 1) :
    ∑' m, ∑ xs : Fin m → ConnState k, ∫⁻ cs : Fin m → ℝ,
      (upperSet α γ).indicator 1 (genealogyOf m xs b cs) * pathDensity g b m 1 diagState xs cs =
        ENNReal.ofReal (upperIntegrand g α γ b) := by
  classical
  have hmem : ∀ m (xs : Fin m → ConnState k) cs, genealogyOf m xs b cs ∈ upperSet α γ ↔
      (∀ j, α j < b j ∧ γ j j < b j) ∧
        ∀ j l, j ≠ l → γ j l < coalTime m 1 diagState xs cs j l := by
    intro m xs cs
    simp only [upperSet, genealogyOf, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨fun j ↦ ⟨h1 j, by simpa using h2 j j⟩, fun j l hjl ↦ ?_⟩
      simpa [hjl] using h2 j l
    · rintro ⟨h1, h2⟩
      refine ⟨fun j ↦ (h1 j).1, fun j l ↦ ?_⟩
      by_cases hjl : j = l
      · subst hjl
        simpa using (h1 j).2
      · simpa [hjl] using h2 j l hjl
  by_cases hbirth : ∀ j, α j < b j ∧ γ j j < b j
  · by_cases hγ1 : ∀ j l, j ≠ l → γ j l < 1
    · have hterm : ∀ m (xs : Fin m → ConnState k) cs,
          (upperSet α γ).indicator 1 (genealogyOf m xs b cs) * pathDensity g b m 1 diagState xs cs =
            pathDensity g b m 1 diagState xs cs *
              pathObs (obsSet γ) (obsTimes γ) m 1 diagState xs cs := by
        intro m xs cs
        by_cases hd : pathDensity g b m 1 diagState xs cs = 0
        · simp [hd]
        · rw [pathObs_eq_ite hγ0 m le_rfl hd, mul_comm]
          congr 1
          simp only [Set.indicator, hmem, Pi.one_apply]
          congr 1
          apply propext
          constructor
          · rintro ⟨-, h⟩ j l hjl _
            exact h j l hjl
          · intro h
            exact ⟨hbirth, fun j l hjl ↦ h j l hjl (hγ1 j l hjl)⟩
      simp_rw [hterm, sum_lintegral_pathDensity hg]
      rw [Summable.tsum_finsetSum fun _ _ ↦ ENNReal.summable]
      rw [upperIntegrand, ite_eq_left ⟨hbirth, hγ1⟩, (coalescenceLimit_eq hg hg2 hb1 γ).2]
      rfl
    · have hzero : ∀ m (xs : Fin m → ConnState k) cs,
          (upperSet α γ).indicator 1 (genealogyOf m xs b cs) *
            pathDensity g b m 1 diagState xs cs = 0 := by
        intro m xs cs
        by_cases hd : pathDensity g b m 1 diagState xs cs = 0
        · simp [hd]
        · have hni : genealogyOf m xs b cs ∉ upperSet α γ := by
            rw [hmem]
            rintro ⟨-, h⟩
            obtain ⟨j, l, hjl, hγ⟩ : ∃ j l, j ≠ l ∧ 1 ≤ γ j l := by
              by_contra hcon
              exact hγ1 fun j l hjl ↦ by
                by_contra hlt
                exact hcon ⟨j, l, hjl, not_lt.mp hlt⟩
            have := coalTime_le m zero_le_one hd j l
            linarith [h j l hjl]
          simp [hni]
      simp only [hzero, lintegral_zero, Finset.sum_const_zero, tsum_zero, upperIntegrand]
      rw [ite_eq_right fun h ↦ hγ1 h.2, ENNReal.ofReal_zero]
  · have hzero : ∀ m (xs : Fin m → ConnState k) cs,
        (upperSet α γ).indicator 1 (genealogyOf m xs b cs) *
          pathDensity g b m 1 diagState xs cs = 0 := by
      intro m xs cs
      have hni : genealogyOf m xs b cs ∉ upperSet α γ := by
        rw [hmem]
        exact fun h ↦ hbirth h.1
      simp [hni]
    simp only [hzero, lintegral_zero, Finset.sum_const_zero, tsum_zero, upperIntegrand]
    rw [ite_eq_right fun h ↦ hbirth h.1, ENNReal.ofReal_zero]

/-- The total history mass at fixed births below one is one. -/
theorem inner_univ (hg : Measurable g) (hg2 : LocSqIntegrable g) (hb1 : ∀ j, b j < 1) :
    ∑' m, ∑ xs : Fin m → ConnState k, ∫⁻ cs : Fin m → ℝ, (univ : Set (GenealogySpace k)).indicator 1
      (genealogyOf m xs b cs) * pathDensity g b m 1 diagState xs cs = 1 := by
  classical
  have hterm : ∀ m (xs : Fin m → ConnState k) cs,
      (univ : Set (GenealogySpace k)).indicator 1 (genealogyOf m xs b cs) *
        pathDensity g b m 1 diagState xs cs =
          pathDensity g b m 1 diagState xs cs * pathObs (fun _ ↦ univ) ∅ m 1 diagState xs cs := by
    intro m xs cs
    rw [pathObs_empty]
    simp
  simp_rw [hterm, sum_lintegral_pathDensity hg]
  rw [Summable.tsum_finsetSum fun _ _ ↦ ENNReal.summable]
  have h := (contVec_top_eq hg hg2 hb1 (fun _ ↦ univ) ∅ (by simp)).2
  rw [show ∑ y, ∑' m, pathMass g b (fun _ ↦ univ) ∅ m 0 1 diagState y =
    ∑ y, transMass g b (fun _ ↦ univ) ∅ 0 1 diagState y from rfl, ← h]
  simp [contVec, diagVec]

theorem ae_cube_lt_one : ∀ᵐ b ∂cubeMeasure k, ∀ j, b j < 1 := by
  filter_upwards [ae_cube_good (k := k) ∅] with b hb j
  exact (hb.1 j).2.1

/-- **The coalescent law is a probability measure.** -/
theorem coalescentLaw_univ (hg : Measurable g) (hg2 : LocSqIntegrable g) :
    coalescentLaw g k univ = 1 := by
  rw [coalescentLaw_apply hg MeasurableSet.univ]
  rw [lintegral_congr_ae (ae_cube_lt_one.mono fun b hb ↦ inner_univ hg hg2 hb)]
  simp

/-- **Upper-set masses of the coalescent law.** -/
theorem coalescentLaw_upperSet (hg : Measurable g) (hg2 : LocSqIntegrable g)
    (α : Fin k → ℝ) (γ : Fin k → Fin k → ℝ) (hγ0 : ∀ j l, j ≠ l → γ j l ≠ 0) :
    coalescentLaw g k (upperSet α γ) = ENNReal.ofReal (upperLimit g α γ) ∧
      0 ≤ upperLimit g α γ := by
  have hE := (isOpen_upperSet α γ).measurableSet
  have hinner : (fun b ↦ ∑' m, ∑ xs : Fin m → ConnState k, ∫⁻ cs : Fin m → ℝ,
      (upperSet α γ).indicator 1 (genealogyOf m xs b cs) * pathDensity g b m 1 diagState xs cs)
      =ᵐ[cubeMeasure k]
      fun b ↦ ENNReal.ofReal (upperIntegrand g α γ b) :=
    ae_cube_lt_one.mono fun b hb ↦ inner_upperSet hg hg2 hγ0 hb
  have hnonneg : ∀ᵐ b ∂cubeMeasure k, 0 ≤ upperIntegrand g α γ b := by
    filter_upwards [ae_cube_lt_one (k := k)] with b hb
    unfold upperIntegrand
    split_ifs
    · exact (coalescenceLimit_eq hg hg2 hb γ).1
    · exact le_rfl
  have hmeasInner : Measurable (fun b ↦ ∑' m, ∑ xs : Fin m → ConnState k, ∫⁻ cs : Fin m → ℝ,
      (upperSet α γ).indicator 1 (genealogyOf m xs b cs) *
        pathDensity g b m 1 diagState xs cs) := by
    refine Measurable.tsum fun m ↦ Finset.measurable_sum _ fun xs _ ↦ ?_
    have h1 : Measurable (fun p : (Fin k → ℝ) × (Fin m → ℝ) ↦
        (upperSet α γ).indicator (1 : GenealogySpace k → ℝ≥0∞) (genealogyOf m xs p.1 p.2)) :=
      (measurable_one.indicator hE).comp (measurable_genealogyOf m xs)
    have h2 := (measurable_pathDensity hg m diagState xs).comp
      (show Measurable (fun p : (Fin k → ℝ) × (Fin m → ℝ) ↦ (p.1, (1 : ℝ), p.2)) from
        measurable_fst.prodMk (measurable_const.prodMk measurable_snd))
    exact (h1.mul h2).lintegral_prod_right'
  have hae : AEStronglyMeasurable (upperIntegrand g α γ) (cubeMeasure k) := by
    refine (hmeasInner.ennreal_toReal.aestronglyMeasurable).congr ?_
    filter_upwards [hinner, hnonneg] with b h1 h2
    rw [h1, ENNReal.toReal_ofReal h2]
  have hval : coalescentLaw g k (upperSet α γ) =
      ∫⁻ b, ENNReal.ofReal (upperIntegrand g α γ b) ∂cubeMeasure k := by
    rw [coalescentLaw_apply hg hE]
    exact lintegral_congr_ae hinner
  have hfin : coalescentLaw g k (upperSet α γ) ≠ ∞ :=
    ne_top_of_le_ne_top (by rw [coalescentLaw_univ hg hg2]; exact ENNReal.one_ne_top)
      (measure_mono (subset_univ _))
  have hint : upperLimit g α γ = (coalescentLaw g k (upperSet α γ)).toReal := by
    rw [upperLimit, integral_eq_lintegral_of_nonneg_ae hnonneg hae, hval]
  refine ⟨?_, ?_⟩
  · rw [hint, ENNReal.ofReal_toReal hfin]
  · rw [hint]
    exact ENNReal.toReal_nonneg

/-- The coalescent law as a probability measure. -/
noncomputable def coalescentLawPM (g : ℝ → ℝ) (k : ℕ) (hg : Measurable g)
    (hg2 : LocSqIntegrable g) : ProbabilityMeasure (GenealogySpace k) :=
  ⟨coalescentLaw g k, ⟨coalescentLaw_univ hg hg2⟩⟩

/-- **The density law satisfies the semigroup characterization** of the limiting
genealogy law. -/
theorem isGenealogyLimit_coalescentLaw (hg : Measurable g) (hg2 : LocSqIntegrable g) :
    IsGenealogyLimit g (coalescentLawPM g k hg hg2) := by
  intro α γ hγ0 _
  obtain ⟨h1, h2⟩ := coalescentLaw_upperSet hg hg2 α γ hγ0
  simp only [coalescentLawPM, ProbabilityMeasure.coe_mk, measureReal_def]
  rw [h1, ENNReal.toReal_ofReal h2]

/-- **The critical limiting genealogy law is the density law.** -/
theorem criticalGenealogyLimit_eq_coalescentLaw (hg : Measurable g) (hg2 : LocSqIntegrable g) :
    criticalGenealogyLimit g k = coalescentLawPM g k hg hg2 := by
  have hex : ∃ μ, IsGenealogyLimit g μ := ⟨_, isGenealogyLimit_coalescentLaw (k := k) hg hg2⟩
  exact (Classical.epsilon_spec hex).unique (isGenealogyLimit_coalescentLaw hg hg2)

/-- **Convergence of sampled genealogies to the density law.** In the critical regime,
the laws of the scaled births and pairwise coalescence times of `k` iid uniform vertices
converge to the coalescent law defined by the density of merge histories. -/
theorem tendsto_genealogyLaw_coalescentLaw {xa : ℕ → ℕ → ℤ} (hx : AdmissibleArray xa)
    (hL1 : HasL1ReciprocalProfile xa (1 / 2) g) (hpos : PositiveProfile g)
    (h2 : HasLocalSquareMomentProfile xa (1 / 2) g) (hg : Measurable g) (k : ℕ) :
    Tendsto (genealogyLaw hx k) atTop
      (𝓝 (coalescentLawPM g k hg fun a c ha hac hc ↦ (h2 a c ha hac hc).1)) := by
  have h := criticalGenealogyLimit_eq_coalescentLaw (k := k) hg
    fun a c ha hac hc ↦ (h2 a c ha hac hc).1
  rw [← h]
  exact tendsto_genealogyLaw_criticalGenealogyLimit hx hL1 hpos h2 k

/-! ### The explicit density `g_{r,k}` -/

/-- Admissible merge histories (the source's admissible triplets): the merge times
decrease in `(0, t)`, and each step merges two distinct clusters of labels already born at
the merge time. -/
noncomputable def IsAdmissible (b : Fin k → ℝ) : (m : ℕ) → ℝ → ConnState k → (Fin m → ConnState k) →
    (Fin m → ℝ) → Prop
  | 0, _, _, _, _ => True
  | m + 1, t, x, xs, cs => (0 < cs 0 ∧ cs 0 < t) ∧ IsMergeStep (bornAt b (cs 0)) x (xs 0) ∧
      IsAdmissible b m (cs 0) (xs 0) (Fin.tail xs) (Fin.tail cs)

/-- The state of a merge history at time `u`, after all merges at times `≥ u`. -/
noncomputable def stateAt : (m : ℕ) → ℝ → ConnState k → (Fin m → ConnState k) → (Fin m → ℝ) → ℝ →
    ConnState k
  | 0, _, x, _, _, _ => x
  | m + 1, _, x, xs, cs, u => if cs 0 < u then x else
      stateAt m (cs 0) (xs 0) (Fin.tail xs) (Fin.tail cs) u

/-- The number `a(u)` of clusters of the labels born at time `u`, for the merge history
`xs` with merge times `cs` started from singletons at time `1`. -/
noncomputable def clusterCount (b : Fin k → ℝ) (m : ℕ) (xs : Fin m → ConnState k)
    (cs : Fin m → ℝ) (u : ℝ) : ℕ :=
  classesOn (bornAt b u) (stateAt m 1 diagState xs cs u)

/-- The density of Proposition `loi du coalescent généralisé` for the non-plane genealogy:
`exp (-∫₀¹ C(a(u), 2) g(u)² du) ∏ⱼ g(cⱼ)²` on admissible histories, `0` elsewhere. Here
`g = 1/f` and the exponential of a divergent integral is `0`. -/
noncomputable def historyDensity (g : ℝ → ℝ) (b : Fin k → ℝ) (m : ℕ) (xs : Fin m → ConnState k)
    (cs : Fin m → ℝ) : ℝ≥0∞ :=
  (open Classical in if IsAdmissible b m 1 diagState xs cs then 1 else 0) *
    (∏ i, ENNReal.ofReal (g (cs i) ^ 2)) *
    expNeg (∫⁻ u in Ioc 0 1,
      ((clusterCount b m xs cs u).choose 2 : ℝ≥0∞) * ENNReal.ofReal (g u ^ 2))

/-- The recursive history density unfolds into the product formula. -/
theorem pathDensity_eq_prod (m : ℕ) : ∀ (t : ℝ) (x : ConnState k) (xs : Fin m → ConnState k)
    (cs : Fin m → ℝ), pathDensity g b m t x xs cs =
      (open Classical in if IsAdmissible b m t x xs cs then 1 else 0) *
        (∏ i, ENNReal.ofReal (g (cs i) ^ 2)) *
        expNeg (∫⁻ u in Ioc 0 t, hazard g b (stateAt m t x xs cs u) u) := by
  classical
  induction m with
  | zero =>
    intro t x xs cs
    simp [pathDensity, IsAdmissible, stateAt, surv, cumHazard]
  | succ m ih =>
    intro t x xs cs
    rw [pathDensity, ih]
    by_cases hc : 0 < cs 0 ∧ cs 0 < t
    · have hsplit : ∫⁻ u in Ioc 0 t, hazard g b (stateAt (m + 1) t x xs cs u) u =
          (∫⁻ u in Ioc 0 (cs 0),
            hazard g b (stateAt m (cs 0) (xs 0) (Fin.tail xs) (Fin.tail cs) u) u) +
            cumHazard g b x (cs 0) t := by
        rw [← Ioc_union_Ioc_eq_Ioc hc.1.le hc.2.le, lintegral_union measurableSet_Ioc
          (Ioc_disjoint_Ioc_of_le le_rfl), cumHazard]
        congr 1
        · apply setLIntegral_congr_fun measurableSet_Ioc
          intro u hu
          have hu2 : ¬ cs 0 < u := not_lt.mpr hu.2
          simp [stateAt, hu2]
        · apply setLIntegral_congr_fun measurableSet_Ioc
          intro u hu
          have hu1 : cs 0 < u := hu.1
          simp [stateAt, hu1]
      rw [hsplit, expNeg_add, Fin.prod_univ_succ]
      have htw : timeWeight (cs 0) t = 1 := by simp [timeWeight, hc]
      by_cases hm : IsMergeStep (bornAt b (cs 0)) x (xs 0)
      · have hmr : mergeRate b (cs 0) x (xs 0) = 1 := by simp [mergeRate, hm]
        by_cases ha : IsAdmissible b m (cs 0) (xs 0) (Fin.tail xs) (Fin.tail cs)
        · have hadm : IsAdmissible b (m + 1) t x xs cs := ⟨hc, hm, ha⟩
          simp only [htw, hmr, ha, hadm, ↓reduceIte, surv, Fin.tail]
          ring
        · have hadm : ¬ IsAdmissible b (m + 1) t x xs cs := fun h ↦ ha h.2.2
          simp [ha, hadm]
      · have hmr : mergeRate b (cs 0) x (xs 0) = 0 := by simp [mergeRate, hm]
        have hadm : ¬ IsAdmissible b (m + 1) t x xs cs := fun h ↦ hm h.2.1
        simp [hmr, hadm]
    · have htw : timeWeight (cs 0) t = 0 := by simp [timeWeight, hc]
      have hadm : ¬ IsAdmissible b (m + 1) t x xs cs := fun h ↦ hc h.1
      simp [htw, hadm]

theorem pathDensity_eq_historyDensity (m : ℕ) (xs : Fin m → ConnState k) (cs : Fin m → ℝ) :
    pathDensity g b m 1 diagState xs cs = historyDensity g b m xs cs := by
  rw [pathDensity_eq_prod, historyDensity]
  rfl

/-- **Proposition `loi du coalescent généralisé` (N11), non-plane form.** The law of the
continuous coalescent genealogy (births, pairwise coalescence times) is the image of the
measures with density `historyDensity` against Lebesgue measure on births in `[0, 1]^k`
and merge times, summed over the number `m = k - 1 - r` of positive merger times and over
the admissible merge histories. -/
theorem coalescentLaw_eq_historyDensity (g : ℝ → ℝ) (k : ℕ) :
    coalescentLaw g k = Measure.sum fun m : ℕ ↦ ∑ xs : Fin m → ConnState k,
      (((cubeMeasure k).prod volume).withDensity fun p ↦ historyDensity g p.1 m xs p.2).map
        fun p ↦ genealogyOf m xs p.1 p.2 := by
  simp only [coalescentLaw, historyMeasure, pathDensity_eq_historyDensity]

/-- The density of a plane merge history: the children of each of the `m` internal
vertices are ordered uniformly at random, independently, which gives the factor
`2^{-m} = 2^{-(k-1-r)}`. -/
noncomputable def planeDensity (g : ℝ → ℝ) (b : Fin k → ℝ) (m : ℕ) (xs : Fin m → ConnState k)
    (cs : Fin m → ℝ) : ℝ≥0∞ :=
  2⁻¹ ^ m * historyDensity g b m xs cs

/-- **Proposition `loi du coalescent généralisé` (N11), plane form.** A plane history is a
merge history `xs` together with the orders `σ : Fin m → Bool` of the two children of each
internal vertex; trees are ordered canonically (by root label), so no further factor
appears. With density `planeDensity = 2^{-m} historyDensity` for each plane history, the
image law of births and pairwise coalescence times is the coalescent law. -/
theorem coalescentLaw_eq_planeDensity (g : ℝ → ℝ) (k : ℕ) :
    coalescentLaw g k = Measure.sum fun m : ℕ ↦ ∑ xs : Fin m → ConnState k,
      ∑ _σ : Fin m → Bool,
        (((cubeMeasure k).prod volume).withDensity fun p ↦ planeDensity g p.1 m xs p.2).map
          fun p ↦ genealogyOf m xs p.1 p.2 := by
  rw [coalescentLaw_eq_historyDensity]
  congr 1
  funext m
  refine Finset.sum_congr rfl fun xs _ ↦ ?_
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
  have hdens : (fun p : (Fin k → ℝ) × (Fin m → ℝ) ↦ planeDensity g p.1 m xs p.2) =
      (2⁻¹ : ℝ≥0∞) ^ m • fun p ↦ historyDensity g p.1 m xs p.2 := rfl
  have h2 : ((2 ^ m : ℕ) : ℝ≥0∞) * (2⁻¹ : ℝ≥0∞) ^ m = 1 := by
    rw [Nat.cast_pow, Nat.cast_ofNat, ← mul_pow, ENNReal.mul_inv_cancel (by norm_num) (by norm_num),
      one_pow]
  rw [hdens, withDensity_smul' _ _ (by simp), Measure.map_smul,
    ← Nat.cast_smul_eq_nsmul ℝ≥0∞, smul_smul, h2, one_smul]
  exact (measurable_genealogyOf m xs).aemeasurable

/-! ### Cluster counts and the number of merges -/

open Classical in
theorem classesOn_diagState (β : Finset (Fin k)) : classesOn β diagState = β.card := by
  unfold classesOn
  refine Finset.card_image_of_injOn fun i hi j _ hij ↦ ?_
  have hmem : i ∈ β.filter (fun l ↦ diagState i l = true) := by
    simp [diagState, Finset.mem_coe.mp hi]
  have hij' : (β.filter fun l ↦ diagState i l = true) = β.filter fun l ↦ diagState j l = true := hij
  rw [hij'] at hmem
  simp only [Finset.mem_filter, diagState, decide_eq_true_eq] at hmem
  exact hmem.2.symm

open Classical in
/-- Merging two distinct clusters decreases the number of clusters by one. -/
theorem classesOn_mergeState {β : Finset (Fin k)} {x : ConnState k} (h : IsValid β x)
    {j₀ l₀ : Fin k} (hj₀ : j₀ ∈ β) (hl₀ : l₀ ∈ β) (hs : x j₀ l₀ = false) :
    classesOn β (mergeState x j₀ l₀) + 1 = classesOn β x := by
  set cls : Fin k → Finset (Fin k) := fun j ↦ β.filter fun l ↦ x j l = true with hclsdef
  set cls' : Fin k → Finset (Fin k) := fun j ↦ β.filter fun l ↦ mergeState x j₀ l₀ j l = true
    with hcls'def
  have hcl : classesOn β x = (β.image cls).card := rfl
  have hcl' : classesOn β (mergeState x j₀ l₀) = (β.image cls').card := rfl
  have hmem : ∀ i, ∀ j, j ∈ cls i ↔ j ∈ β ∧ x i j = true := fun i j ↦ by simp [hclsdef]
  have hself : ∀ j ∈ β, j ∈ cls j := fun j hj ↦ (hmem j j).mpr ⟨hj, h.refl j⟩
  have heq : ∀ i, ∀ j, x i j = true → cls i = cls j := by
    intro i j hij
    ext l
    rw [hmem, hmem]
    constructor
    · rintro ⟨hl, hx⟩
      exact ⟨hl, h.trans _ _ _ (h.symm _ _ hij) hx⟩
    · rintro ⟨hl, hx⟩
      exact ⟨hl, h.trans _ _ _ hij hx⟩
  set A := cls j₀ with hA
  set B := cls l₀ with hB
  have hxl₀ : ∀ j, x j j₀ = true → x j l₀ = false := by
    intro j hj
    by_contra hc
    rw [Bool.not_eq_false] at hc
    rw [h.trans _ _ _ (h.symm _ _ hj) hc] at hs
    simp at hs
  have hxj₀ : ∀ j, x j l₀ = true → x j j₀ = false := by
    intro j hj
    by_contra hc
    rw [Bool.not_eq_false] at hc
    exact absurd ((hxl₀ j hc).symm.trans hj) (by simp)
  have hcls' : ∀ j ∈ β, cls' j = if j ∈ A ∪ B then A ∪ B else cls j := by
    intro j hj
    ext l
    simp only [hcls'def, Finset.mem_filter, mergeState_iff]
    split_ifs with hAB
    · rw [Finset.mem_union] at hAB ⊢
      rw [hmem, hmem]
      rcases hAB with hjA | hjB
      · have hjj₀ : x j j₀ = true := h.symm _ _ ((hmem _ _).mp hjA).2
        have hjl₀ := hxl₀ j hjj₀
        constructor
        · rintro ⟨hl, h1 | ⟨-, h2⟩ | ⟨h2, -⟩⟩
          · exact Or.inl ⟨hl, h.trans _ _ _ (h.symm _ _ hjj₀) h1⟩
          · exact Or.inr ⟨hl, h.symm _ _ h2⟩
          · rw [hjl₀] at h2
            exact absurd h2 Bool.false_ne_true
        · rintro (⟨hl, h1⟩ | ⟨hl, h1⟩)
          · exact ⟨hl, Or.inl (h.trans _ _ _ hjj₀ h1)⟩
          · exact ⟨hl, Or.inr (Or.inl ⟨hjj₀, h.symm _ _ h1⟩)⟩
      · have hjl₀ : x j l₀ = true := h.symm _ _ ((hmem _ _).mp hjB).2
        have hjj₀ := hxj₀ j hjl₀
        constructor
        · rintro ⟨hl, h1 | ⟨h2, -⟩ | ⟨-, h2⟩⟩
          · exact Or.inr ⟨hl, h.trans _ _ _ (h.symm _ _ hjl₀) h1⟩
          · rw [hjj₀] at h2
            exact absurd h2 Bool.false_ne_true
          · exact Or.inl ⟨hl, h.symm _ _ h2⟩
        · rintro (⟨hl, h1⟩ | ⟨hl, h1⟩)
          · exact ⟨hl, Or.inr (Or.inr ⟨hjl₀, h.symm _ _ h1⟩)⟩
          · exact ⟨hl, Or.inl (h.trans _ _ _ hjl₀ h1)⟩
    · rw [Finset.mem_union, not_or] at hAB
      have hjj₀ : x j j₀ = false := by
        by_contra hc
        rw [Bool.not_eq_false] at hc
        exact hAB.1 ((hmem _ _).mpr ⟨hj, h.symm _ _ hc⟩)
      have hjl₀ : x j l₀ = false := by
        by_contra hc
        rw [Bool.not_eq_false] at hc
        exact hAB.2 ((hmem _ _).mpr ⟨hj, h.symm _ _ hc⟩)
      rw [hmem]
      simp [hjj₀, hjl₀]
  have hAB : A ≠ B := by
    intro hc
    have : l₀ ∈ A := hc ▸ hself l₀ hl₀
    rw [hmem] at this
    rw [this.2] at hs
    simp at hs
  have hAmem : A ∈ β.image cls := Finset.mem_image_of_mem cls hj₀
  have hBmem : B ∈ β.image cls := Finset.mem_image_of_mem cls hl₀
  have himage : β.image cls' = insert (A ∪ B) (((β.image cls).erase A).erase B) := by
    ext C
    simp only [Finset.mem_image, Finset.mem_insert, Finset.mem_erase]
    constructor
    · rintro ⟨j, hj, rfl⟩
      rw [hcls' j hj]
      split_ifs with hjAB
      · exact Or.inl rfl
      · rw [Finset.mem_union, not_or] at hjAB
        refine Or.inr ⟨fun hc ↦ hjAB.2 (hc ▸ hself j hj), fun hc ↦ hjAB.1 (hc ▸ hself j hj),
          j, hj, rfl⟩
    · rintro (rfl | ⟨hCB, hCA, j, hj, rfl⟩)
      · refine ⟨j₀, hj₀, ?_⟩
        rw [hcls' j₀ hj₀, ite_eq_left (Finset.mem_union_left _ (hself j₀ hj₀))]
      · refine ⟨j, hj, ?_⟩
        rw [hcls' j hj, ite_eq_right]
        rw [Finset.mem_union, not_or]
        refine ⟨fun hjA ↦ hCA ?_, fun hjB ↦ hCB ?_⟩
        · exact (heq _ _ ((hmem _ _).mp hjA).2).symm
        · exact (heq _ _ ((hmem _ _).mp hjB).2).symm
  have hnot : A ∪ B ∉ ((β.image cls).erase A).erase B := by
    simp only [Finset.mem_erase, Finset.mem_image]
    rintro ⟨hne1, hne2, j, hj, hjeq⟩
    have hj₀ : j₀ ∈ cls j := hjeq ▸ Finset.mem_union_left _ (hself j₀ hj₀)
    have : cls j = A := heq _ _ ((hmem _ _).mp hj₀).2
    rw [this] at hjeq
    have hl : l₀ ∈ A := hjeq ▸ Finset.mem_union_right _ (hself l₀ hl₀)
    rw [hmem] at hl
    rw [hl.2] at hs
    simp at hs
  have h2 : 2 ≤ (β.image cls).card := by
    have : ({A, B} : Finset (Finset (Fin k))) ⊆ β.image cls := by
      intro C hC
      simp only [Finset.mem_insert, Finset.mem_singleton] at hC
      rcases hC with rfl | rfl
      · exact hAmem
      · exact hBmem
    have := Finset.card_le_card this
    rwa [Finset.card_pair hAB] at this
  rw [hcl', himage, Finset.card_insert_of_notMem hnot,
    Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hAB.symm, hBmem⟩),
    Finset.card_erase_of_mem hAmem, hcl]
  omega

theorem IsAdmissible.time_mem {m : ℕ} : ∀ {t : ℝ} {x : ConnState k} {xs : Fin m → ConnState k}
    {cs : Fin m → ℝ}, IsAdmissible b m t x xs cs → ∀ i, 0 < cs i ∧ cs i < t := by
  induction m with
  | zero => intro t x xs cs _ i; exact i.elim0
  | succ m ih =>
    intro t x xs cs h i
    obtain ⟨hc, -, ha⟩ := h
    refine Fin.cases hc (fun i ↦ ?_) i
    have := ih ha i
    exact ⟨this.1, this.2.trans hc.2⟩

/-- **Cluster counts along an admissible history.** At time `u ≤ t`, the number of
clusters of born labels is the number of born labels minus the number of merges at times
`≥ u`, as in the source's formula for `a(t)`. -/
theorem classesOn_stateAt (m : ℕ) : ∀ {t : ℝ} {x : ConnState k} {xs : Fin m → ConnState k}
    {cs : Fin m → ℝ}, IsAdmissible b m t x xs cs → IsValid (bornAt b t) x → ∀ {u : ℝ}, u ≤ t →
      classesOn (bornAt b u) (stateAt m t x xs cs u) +
        (Finset.univ.filter fun i ↦ u ≤ cs i).card = classesOn (bornAt b u) x := by
  classical
  induction m with
  | zero =>
    intro t x xs cs _ _ u _
    simp [stateAt]
  | succ m ih =>
    intro t x xs cs h hx u hut
    obtain ⟨hc, hm, ha⟩ := h
    have hcount : (Finset.univ.filter fun i : Fin (m + 1) ↦ u ≤ cs i).card =
        (if u ≤ cs 0 then 1 else 0) +
          (Finset.univ.filter fun i : Fin m ↦ u ≤ Fin.tail cs i).card := by
      rw [Finset.card_filter, Finset.card_filter, Fin.sum_univ_succ]
      rfl
    rw [hcount]
    by_cases hu : u ≤ cs 0
    · have hx0 : IsValid (bornAt b (cs 0)) (xs 0) := hx.isMergeStep (bornAt_anti b hc.2.le) hm
      have hst : stateAt (m + 1) t x xs cs u =
          stateAt m (cs 0) (xs 0) (Fin.tail xs) (Fin.tail cs) u := by
        simp [stateAt, not_lt.mpr hu]
      rw [hst, ite_eq_left hu]
      have h1 := ih ha hx0 hu
      obtain ⟨-, j₀, hj₀, l₀, hl₀, hs, hx0eq⟩ := hm
      have h2 := classesOn_mergeState (hx.mono (bornAt_anti b (hu.trans hc.2.le)))
        (bornAt_anti b hu hj₀) (bornAt_anti b hu hl₀) hs
      rw [← hx0eq] at h2
      omega
    · have hst : stateAt (m + 1) t x xs cs u = x := by
        simp [stateAt, lt_of_not_ge hu]
      have hzero : (Finset.univ.filter fun i : Fin m ↦ u ≤ Fin.tail cs i).card = 0 := by
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro i _ hi
        exact hu (hi.trans (ha.time_mem i).2.le)
      rw [hst, ite_eq_right hu, hzero]
      simp

/-- **At most `k - 1` merges.** Admissible histories from singletons have at most `k - 1`
merges, so the number `r = k - 1 - m` of zero merger times lies in `[0, k - 1]`. -/
theorem IsAdmissible.le_card_sub_one {m : ℕ} {xs : Fin m → ConnState k} {cs : Fin m → ℝ}
    (h : IsAdmissible b m 1 diagState xs cs) : m ≤ k - 1 := by
  classical
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exact Nat.zero_le _
  obtain ⟨i, hi⟩ : ∃ i : Fin m, i = ⟨m - 1, by omega⟩ := ⟨_, rfl⟩
  set u := cs i with hu
  have hu1 : u ≤ 1 := (h.time_mem i).2.le
  have hkey := classesOn_stateAt m h (isValid_diagState _) hu1
  rw [classesOn_diagState] at hkey
  -- every merge time is at least `u`, and the last merge involves a born label
  have hall : (Finset.univ.filter fun j : Fin m ↦ u ≤ cs j).card = m := by
    rw [Finset.filter_true_of_mem, Finset.card_univ, Fintype.card_fin]
    intro j _
    -- merge times decrease along the history
    have hdec : ∀ (m : ℕ) (t : ℝ) (x : ConnState k) (xs : Fin m → ConnState k) (cs : Fin m → ℝ),
        IsAdmissible b m t x xs cs → ∀ a c : Fin m, a ≤ c → cs c ≤ cs a := by
      intro m
      induction m with
      | zero => intro t x xs cs _ a; exact a.elim0
      | succ m ih =>
        intro t x xs cs h a c hac
        obtain ⟨-, -, ha⟩ := h
        refine Fin.cases (fun _ ↦ ?_) (fun a hac ↦ ?_) a hac
        · refine Fin.cases le_rfl (fun c ↦ (ha.time_mem c).2.le) c
        · obtain ⟨c', rfl⟩ :=
            Fin.exists_succ_eq.mpr (ne_of_gt (lt_of_lt_of_le (Fin.succ_pos a) hac))
          exact ih _ _ _ _ ha a c' (Fin.succ_le_succ_iff.mp hac)
    exact hdec m 1 diagState xs cs h j i (by rw [hi]; exact Fin.mk_le_mk.mpr (by omega))
  rw [hall] at hkey
  have hcard : (bornAt b u).card ≤ k := (Finset.card_le_univ _).trans (by simp)
  have hpos : 1 ≤ classesOn (bornAt b u) (stateAt m 1 diagState xs cs u) := by
    -- the label merged last is born at time `u`
    have hlast : ∀ (m : ℕ) (t : ℝ) (x : ConnState k) (xs : Fin m → ConnState k)
        (cs : Fin m → ℝ), IsAdmissible b m t x xs cs → ∀ i : Fin m, ∃ j, j ∈ bornAt b (cs i) := by
      intro m
      induction m with
      | zero => intro t x xs cs _ i; exact i.elim0
      | succ m ih =>
        intro t x xs cs h i
        obtain ⟨-, hm, ha⟩ := h
        refine Fin.cases ?_ (fun i ↦ ih _ _ _ _ ha i) i
        obtain ⟨-, j₀, hj₀, -⟩ := hm
        exact ⟨j₀, hj₀⟩
    obtain ⟨j, hj⟩ := hlast m 1 diagState xs cs h i
    unfold classesOn
    rw [Nat.one_le_iff_ne_zero, Ne, Finset.card_eq_zero, Finset.image_eq_empty]
    exact Finset.ne_empty_of_mem hj
  omega

/-- The source's cluster count `a(u) = #{j : b j > u} - #{i : c i > u}`. -/
noncomputable def sourceClusterCount (b : Fin k → ℝ) {m : ℕ} (cs : Fin m → ℝ) (u : ℝ) : ℕ :=
  (Finset.univ.filter fun j ↦ u < b j).card - (Finset.univ.filter fun i ↦ u < cs i).card

/-- **The density of Proposition `loi du coalescent généralisé`** with the source's
formula for `a(u)`: on admissible histories,
`historyDensity = exp (-∫₀¹ C(a(u), 2) g(u)² du) ∏ⱼ g(cⱼ)²`. -/
theorem historyDensity_eq_source (g : ℝ → ℝ) (b : Fin k → ℝ) (m : ℕ) (xs : Fin m → ConnState k)
    (cs : Fin m → ℝ) :
    historyDensity g b m xs cs =
      (open Classical in if IsAdmissible b m 1 diagState xs cs then 1 else 0) *
        (∏ i, ENNReal.ofReal (g (cs i) ^ 2)) *
        expNeg (∫⁻ u in Ioc 0 1,
          ((sourceClusterCount b cs u).choose 2 : ℝ≥0∞) * ENNReal.ofReal (g u ^ 2)) := by
  classical
  unfold historyDensity
  by_cases ha : IsAdmissible b m 1 diagState xs cs
  · congr 2
    have hfin : (Set.range b ∪ Set.range cs).Finite :=
      (Set.finite_range b).union (Set.finite_range cs)
    refine setLIntegral_congr_fun_ae measurableSet_Ioc ?_
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp (hfin.measure_zero volume)] with u hu hu01
    simp only [Set.mem_union, Set.mem_range, not_or, not_exists] at hu
    have hkey := classesOn_stateAt m ha (isValid_diagState _) hu01.2
    rw [classesOn_diagState] at hkey
    have h1 : (bornAt b u).card = (Finset.univ.filter fun j ↦ u < b j).card := by
      congr 1
      ext j
      simp only [bornAt, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fun h ↦ lt_of_le_of_ne h fun e ↦ hu.1 j e.symm, le_of_lt⟩
    have h2 : (Finset.univ.filter fun i ↦ u ≤ cs i).card =
        (Finset.univ.filter fun i ↦ u < cs i).card := by
      congr 1
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fun h ↦ lt_of_le_of_ne h fun e ↦ hu.2 i e.symm, le_of_lt⟩
    have hcc : clusterCount b m xs cs u = sourceClusterCount b cs u := by
      unfold clusterCount sourceClusterCount
      omega
    rw [hcc]
  · simp [ha]

end Freezing2.CoalescentDensity
