module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Combinatorics.Enumerative.Catalan.Basic
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Data.List.GetD
public import Mathlib.Probability.ConditionalProbability
public import Mathlib.Probability.Distributions.Uniform
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity

/-!
# Two false displays in the proof of `cor:CRT`

Step 1 of the proof of `cor:CRT` in the source states a Kemperman-type formula
`eq:probalocale` and a uniform bound `eq:borne`. Both displays are false.
This file proves both refutations; the items are S15 and S16 of
`docs/source-inventory.md`.

## Model

An increment sequence of length `m` is a function `Fin m → Bool`, where `true` is a
step `+1` and `false` a step `-1`. `excursionWalk w i` is the position at time `i` of
the walk started from `1`. Simple random walk paths of a fixed length are equally
likely, so `S^{2n+1}` has the uniform law `excursionLaw n` on `excursionPaths n`. This
set contains the sequences of length `2n+1` whose walk stays at least `1` up to time
`2n` and equals `0` at time `2n+1`. `excursionLaw_eq_cond` shows that this is the
uniform law `srwLaw (2n+1)` conditioned on that event.

## Counting

`excursionEquivDyckWord` puts the excursions of length `2n+1` in bijection with
Dyck words of semilength `n`. Hence `card_excursionPaths` gives `catalan n`.
Removing an initial up-step and down-step identifies the excursions of length `2n+3`
with `S_2 = 1` with the excursions of length `2n+1`. Therefore, for `n ≥ 1`,
`excursionLaw_real_second_eq_one` gives `P(S_2 = 1) = C_{n-1}/C_n = (n+1)/(4n-2)`.

## Main results

* `not_kempermanDisplay` (S15): for `n = 1`, `i = 2`, `k = 1`, the left side of
  `eq:probalocale` is `1`, while its right side contains the factor `(k-1)/i = 0`.
  This holds whatever real values are used for the unconditioned probabilities.
  `not_kempermanDisplay_srw` specializes to the actual random-walk probabilities.
* `not_uniform_smallValue_bound` (S16): no `C > 0` satisfies `eq:borne` for all
  `n ≥ 1`, `0 < δ ≤ 1`, and `ε > 0`. For `n ≥ 2`, take `δ = 1/√n` and
  `ε = 1/(2√n)`. `quarter_lt_excursionLaw_real` gives `P(X_n(δ) ≥ ε) > 1/4`, while
  `C δ^2/ε = 2C/√n`.
* `not_bounded_sqrt_mul_sum_inv_rpow`: the factor `√n ∑_{i=1}^n i^{-3/2}` used in
  the last display of Step 1 is at least `√n`, so it is not uniformly bounded.

These results refute the displayed intermediate claims only. They do not refute
`cor:CRT`.
-/

@[expose] public section

open MeasureTheory

namespace Freezing2.Audit

/-! ### Increments and the walk started from `1` -/

/-- The increment of a step: `+1` for `true`, `-1` for `false`. -/
def stepValue (b : Bool) : ℤ := if b then 1 else -1

/-- The position at time `i` of the walk started from `1` with increments `w`. -/
def excursionWalk {m : ℕ} (w : Fin m → Bool) (i : ℕ) : ℤ :=
  1 + (((List.ofFn w).take i).map stepValue).sum

@[simp] theorem excursionWalk_zero {m : ℕ} (w : Fin m → Bool) : excursionWalk w 0 = 1 := by
  simp [excursionWalk]

theorem excursionWalk_cons_succ {m : ℕ} (a : Bool) (w : Fin m → Bool) (i : ℕ) :
    excursionWalk (Fin.cons a w : Fin (m + 1) → Bool) (i + 1) =
      excursionWalk w i + stepValue a := by
  simp [excursionWalk, List.ofFn_succ]
  ring

theorem excursionWalk_succ {m : ℕ} (w : Fin m → Bool) (i : ℕ) (hi : i < m) :
    excursionWalk w (i + 1) = excursionWalk w i + stepValue (w ⟨i, hi⟩) := by
  simp [excursionWalk, List.take_add_one, hi]
  ring

theorem sum_map_stepValue (l : List Bool) :
    (l.map stepValue).sum = (l.count true : ℤ) - l.count false := by
  induction l with
  | nil => simp
  | cons b l ih =>
    cases b <;> simp [stepValue, ih] <;> ring

theorem excursionWalk_eq_count {m : ℕ} (w : Fin m → Bool) (i : ℕ) :
    excursionWalk w i = 1 + (((List.ofFn w).take i).count true : ℤ)
      - ((List.ofFn w).take i).count false := by
  rw [excursionWalk, sum_map_stepValue]
  ring

/-! ### Excursions and their uniform law -/

/-- The walk stays at least `1` up to time `2n` and equals `0` at time `2n+1`. -/
def IsExcursionPath (n : ℕ) (w : Fin (2 * n + 1) → Bool) : Prop :=
  (∀ i ≤ 2 * n, 1 ≤ excursionWalk w i) ∧ excursionWalk w (2 * n + 1) = 0

instance (n : ℕ) : DecidablePred (IsExcursionPath n) := fun w => by
  unfold IsExcursionPath
  infer_instance

/-- The increment sequences of the walk from `1` that first hit `0` at time `2n+1`. -/
def excursionPaths (n : ℕ) : Finset (Fin (2 * n + 1) → Bool) :=
  {w | IsExcursionPath n w}

theorem mem_excursionPaths {n : ℕ} {w : Fin (2 * n + 1) → Bool} :
    w ∈ excursionPaths n ↔ IsExcursionPath n w := by
  simp [excursionPaths]

/-- The law of the increments of `S^{2n+1}`: uniform on `excursionPaths n`. -/
noncomputable def excursionLaw (n : ℕ) : Measure (Fin (2 * n + 1) → Bool) :=
  Measure.uniformOfFinset (excursionPaths n)

/-- The law of the first `m` increments of simple random walk. -/
noncomputable def srwLaw (m : ℕ) : Measure (Fin m → Bool) :=
  Measure.uniformOfFinset Finset.univ

/-- `P(S_i = k)` for simple random walk started from `1`. -/
noncomputable def srwProb (i : ℕ) (k : ℤ) : ℝ :=
  (srwLaw i).real {w | excursionWalk w i = k}

theorem card_filter_univ_mem_coe {α : Type*} [Fintype α] (s : Finset α)
    (h : DecidablePred (· ∈ (s : Set α))) :
    (@Finset.filter α (· ∈ (s : Set α)) h Finset.univ).card = s.card := by
  congr 1
  ext x
  simp

theorem card_filter_univ_mem_coe_inter {α : Type*} [Fintype α] (s : Finset α) (t : Set α)
    (h : DecidablePred (· ∈ (s : Set α) ∩ t)) (h' : DecidablePred (· ∈ t)) :
    (@Finset.filter α (· ∈ (s : Set α) ∩ t) h Finset.univ).card =
      (@Finset.filter α (· ∈ t) h' s).card := by
  congr 1
  ext x
  simp

open scoped ProbabilityTheory in
/-- The excursion law is the law of simple random walk increments conditioned on the
event that the walk from `1` first hits `0` at time `2n+1`. -/
theorem excursionLaw_eq_cond (n : ℕ) :
    excursionLaw n =
      (srwLaw (2 * n + 1))[|(excursionPaths n : Set (Fin (2 * n + 1) → Bool))] := by
  classical
  ext t ht
  rw [ProbabilityTheory.cond_apply (Finset.measurableSet _), excursionLaw, srwLaw,
    Measure.uniformOfFinset_apply, Measure.uniformOfFinset_apply,
    Measure.uniformOfFinset_apply, card_filter_univ_mem_coe,
    card_filter_univ_mem_coe_inter _ _ _ (fun _ => Classical.propDecidable _)]
  have hN0 : ((Finset.univ : Finset (Fin (2 * n + 1) → Bool)).card : ENNReal) ≠ 0 := by
    simp
  have hNt : ((Finset.univ : Finset (Fin (2 * n + 1) → Bool)).card : ENNReal) ≠ ⊤ :=
    ENNReal.natCast_ne_top _
  rw [ENNReal.inv_div (Or.inl hNt) (Or.inl hN0)]
  generalize ((Finset.univ : Finset (Fin (2 * n + 1) → Bool)).card : ENNReal) = N at hN0 hNt ⊢
  generalize (({x ∈ excursionPaths n | x ∈ t}).card : ENNReal) = a
  generalize ((excursionPaths n).card : ENNReal) = e
  rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv]
  calc a * e⁻¹ = a * e⁻¹ * (N * N⁻¹) := by rw [ENNReal.mul_inv_cancel hN0 hNt, mul_one]
    _ = N * e⁻¹ * (a * N⁻¹) := by ring

theorem excursionLaw_real_apply (n : ℕ) (t : Set (Fin (2 * n + 1) → Bool))
    [DecidablePred (· ∈ t)] :
    (excursionLaw n).real t =
      (({w ∈ excursionPaths n | w ∈ t}).card : ℝ) / (excursionPaths n).card := by
  rw [measureReal_def, excursionLaw, Measure.uniformOfFinset_apply, ENNReal.toReal_div,
    ENNReal.toReal_natCast, ENNReal.toReal_natCast]
  congr

theorem excursionLaw_real_mono {n : ℕ} {t₁ t₂ : Set (Fin (2 * n + 1) → Bool)}
    (h : ∀ w ∈ excursionPaths n, w ∈ t₁ → w ∈ t₂) :
    (excursionLaw n).real t₁ ≤ (excursionLaw n).real t₂ := by
  classical
  rw [excursionLaw_real_apply, excursionLaw_real_apply]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast Finset.card_le_card fun w hw => by
    simp only [Finset.mem_filter] at hw ⊢
    exact ⟨hw.1, h w hw.1 hw.2⟩

/-- On an excursion, the walk is at `1` at time `2n` and the last step is down. -/
theorem IsExcursionPath.last {n : ℕ} {w : Fin (2 * n + 1) → Bool} (hw : IsExcursionPath n w) :
    excursionWalk w (2 * n) = 1 ∧ w ⟨2 * n, by omega⟩ = false := by
  have h := excursionWalk_succ w (2 * n) (by omega)
  have h1 := hw.1 (2 * n) le_rfl
  rw [hw.2] at h
  cases hb : w ⟨2 * n, by omega⟩
  · simp only [hb, stepValue, Bool.false_eq_true, ↓reduceIte] at h
    exact ⟨by omega, rfl⟩
  · simp only [hb, stepValue, ↓reduceIte] at h
    omega

/-! ### Bijection with Dyck words -/

/-- Up-steps are `U` and down-steps are `D`. -/
def boolToDyckStep : Bool → DyckStep
  | true => .U
  | false => .D

/-- The inverse of `boolToDyckStep`. -/
def dyckStepToBool : DyckStep → Bool
  | .U => true
  | .D => false

@[simp] theorem dyckStepToBool_boolToDyckStep (b : Bool) :
    dyckStepToBool (boolToDyckStep b) = b := by
  cases b <;> rfl

@[simp] theorem boolToDyckStep_dyckStepToBool (s : DyckStep) :
    boolToDyckStep (dyckStepToBool s) = s := by
  cases s <;> rfl

theorem boolToDyckStep_injective : Function.Injective boolToDyckStep :=
  Function.LeftInverse.injective dyckStepToBool_boolToDyckStep

theorem dyckStepToBool_injective : Function.Injective dyckStepToBool :=
  Function.LeftInverse.injective boolToDyckStep_dyckStepToBool

theorem count_U_map_boolToDyckStep (l : List Bool) :
    (l.map boolToDyckStep).count .U = l.count true :=
  List.count_map_of_injective l boolToDyckStep boolToDyckStep_injective true

theorem count_D_map_boolToDyckStep (l : List Bool) :
    (l.map boolToDyckStep).count .D = l.count false :=
  List.count_map_of_injective l boolToDyckStep boolToDyckStep_injective false

theorem count_true_map_dyckStepToBool (l : List DyckStep) :
    (l.map dyckStepToBool).count true = l.count .U :=
  List.count_map_of_injective l dyckStepToBool dyckStepToBool_injective .U

theorem count_false_map_dyckStepToBool (l : List DyckStep) :
    (l.map dyckStepToBool).count false = l.count .D :=
  List.count_map_of_injective l dyckStepToBool dyckStepToBool_injective .D

/-- The Dyck word formed by the first `2n` steps of an excursion. -/
def toDyckWord {n : ℕ} (w : Fin (2 * n + 1) → Bool) (hw : IsExcursionPath n w) :
    DyckWord where
  toList := ((List.ofFn w).take (2 * n)).map boolToDyckStep
  count_U_eq_count_D := by
    have h := hw.last.1
    rw [excursionWalk_eq_count] at h
    rw [count_U_map_boolToDyckStep, count_D_map_boolToDyckStep]
    omega
  count_D_le_count_U i := by
    rw [← List.map_take, count_U_map_boolToDyckStep, count_D_map_boolToDyckStep,
      List.take_take]
    have h := hw.1 (min i (2 * n)) (min_le_right _ _)
    rw [excursionWalk_eq_count] at h
    omega

/-- The increment sequence of a Dyck word followed by a final down-step. -/
def ofDyckWord (n : ℕ) (p : DyckWord) : Fin (2 * n + 1) → Bool :=
  fun i => (p.toList.map dyckStepToBool).getD i false

theorem ofFn_ofDyckWord {n : ℕ} {p : DyckWord} (hp : p.semilength = n) :
    List.ofFn (ofDyckWord n p) = p.toList.map dyckStepToBool ++ [false] := by
  have hl : p.toList.length = 2 * n := by rw [← p.two_mul_semilength_eq_length, hp]
  apply List.ext_getElem
  · simp [hl]
  · intro i h1 h2
    simp only [List.getElem_ofFn, ofDyckWord, List.getElem_append]
    split_ifs with hi
    · rw [List.getD_eq_getElem _ _ hi]
    · rw [List.getD_eq_default _ _ (by omega)]
      simp

theorem isExcursionPath_ofDyckWord {n : ℕ} {p : DyckWord} (hp : p.semilength = n) :
    IsExcursionPath n (ofDyckWord n p) := by
  have hl : p.toList.length = 2 * n := by rw [← p.two_mul_semilength_eq_length, hp]
  refine ⟨fun i hi => ?_, ?_⟩
  · rw [excursionWalk_eq_count, ofFn_ofDyckWord hp,
      List.take_append_of_le_length (by simp [hl, hi]), ← List.map_take,
      count_true_map_dyckStepToBool, count_false_map_dyckStepToBool]
    have := p.count_D_le_count_U i
    omega
  · rw [excursionWalk_eq_count, ofFn_ofDyckWord hp, List.take_of_length_le (by simp [hl])]
    simp [List.count_append, count_true_map_dyckStepToBool, count_false_map_dyckStepToBool]
    have := p.count_U_eq_count_D
    omega

theorem semilength_toDyckWord {n : ℕ} {w : Fin (2 * n + 1) → Bool}
    (hw : IsExcursionPath n w) : (toDyckWord w hw).semilength = n := by
  have h := (toDyckWord w hw).two_mul_semilength_eq_length
  have hl : (toDyckWord w hw).toList.length = 2 * n := by simp [toDyckWord]
  omega

theorem ofDyckWord_toDyckWord {n : ℕ} {w : Fin (2 * n + 1) → Bool}
    (hw : IsExcursionPath n w) : ofDyckWord n (toDyckWord w hw) = w := by
  funext i
  simp only [ofDyckWord, toDyckWord, List.map_map]
  have hid : dyckStepToBool ∘ boolToDyckStep = id := funext dyckStepToBool_boolToDyckStep
  rw [hid, List.map_id]
  by_cases hi : i.val < 2 * n
  · rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_take, List.getElem_ofFn]
  · rw [List.getD_eq_default _ _ (by simp; omega)]
    have : i = ⟨2 * n, by omega⟩ := Fin.ext (by change i.val = 2 * n; omega)
    rw [this, hw.last.2]

theorem toDyckWord_ofDyckWord {n : ℕ} {p : DyckWord} (hp : p.semilength = n) :
    toDyckWord (ofDyckWord n p) (isExcursionPath_ofDyckWord hp) = p := by
  apply DyckWord.ext
  have hl : p.toList.length = 2 * n := by rw [← p.two_mul_semilength_eq_length, hp]
  simp only [toDyckWord, ofFn_ofDyckWord hp]
  rw [List.take_append_of_le_length (by simp [hl]), List.take_of_length_le (by simp [hl]),
    List.map_map]
  have hid : boolToDyckStep ∘ dyckStepToBool = id := funext boolToDyckStep_dyckStepToBool
  rw [hid, List.map_id]

/-- Excursions of length `2n+1` correspond to Dyck words of semilength `n`. -/
def excursionEquivDyckWord (n : ℕ) :
    {w // w ∈ excursionPaths n} ≃ {p : DyckWord // p.semilength = n} where
  toFun w := ⟨toDyckWord w.1 (mem_excursionPaths.1 w.2),
    semilength_toDyckWord (mem_excursionPaths.1 w.2)⟩
  invFun p := ⟨ofDyckWord n p.1, mem_excursionPaths.2 (isExcursionPath_ofDyckWord p.2)⟩
  left_inv w := Subtype.ext (ofDyckWord_toDyckWord (mem_excursionPaths.1 w.2))
  right_inv p := Subtype.ext (toDyckWord_ofDyckWord p.2)

/-- There are `C_n` excursions of length `2n+1`. -/
theorem card_excursionPaths (n : ℕ) : (excursionPaths n).card = catalan n := by
  rw [← Fintype.card_coe, Fintype.card_congr (excursionEquivDyckWord n),
    DyckWord.card_dyckWord_semilength_eq_catalan]

theorem catalan_pos (n : ℕ) : 0 < catalan n := by
  have h := succ_mul_catalan_eq_centralBinom n
  rcases Nat.eq_zero_or_pos (catalan n) with h0 | h0
  · rw [h0, mul_zero] at h
    exact absurd h.symm (Nat.centralBinom_ne_zero n)
  · exact h0

theorem excursionPaths_nonempty (n : ℕ) : (excursionPaths n).Nonempty := by
  rw [← Finset.card_pos, card_excursionPaths]
  exact catalan_pos n

instance isProbabilityMeasure_excursionLaw (n : ℕ) :
    IsProbabilityMeasure (excursionLaw n) := by
  classical
  constructor
  have h0 : ((excursionPaths n).card : ENNReal) ≠ 0 := by
    exact_mod_cast (excursionPaths_nonempty n).card_pos.ne'
  rw [excursionLaw, Measure.uniformOfFinset_apply]
  simp only [Set.mem_univ, Finset.filter_true]
  exact ENNReal.div_self h0 (ENNReal.natCast_ne_top _)

/-! ### Excursions starting with an up-step and a down-step -/

/-- Prepend an up-step and a down-step. -/
def upDownCons {n : ℕ} (w : Fin (2 * n + 1) → Bool) : Fin (2 * (n + 1) + 1) → Bool :=
  Fin.cons true (Fin.cons false w)

theorem excursionWalk_upDownCons_add_two {n : ℕ} (w : Fin (2 * n + 1) → Bool) (i : ℕ) :
    excursionWalk (upDownCons w) (i + 2) = excursionWalk w i := by
  rw [upDownCons, excursionWalk_cons_succ, excursionWalk_cons_succ]
  simp [stepValue]

theorem excursionWalk_upDownCons_one {n : ℕ} (w : Fin (2 * n + 1) → Bool) :
    excursionWalk (upDownCons w) 1 = 2 := by
  rw [upDownCons, excursionWalk_cons_succ]
  simp [stepValue]

theorem upDownCons_mem_iff {n : ℕ} (w : Fin (2 * n + 1) → Bool) :
    upDownCons w ∈ excursionPaths (n + 1) ↔ w ∈ excursionPaths n := by
  have hend : excursionWalk (upDownCons w) (2 * (n + 1) + 1) = excursionWalk w (2 * n + 1) :=
    excursionWalk_upDownCons_add_two w (2 * n + 1)
  rw [mem_excursionPaths, mem_excursionPaths, IsExcursionPath, IsExcursionPath, hend]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun i hi => ?_, h2⟩
    have := h1 (i + 2) (by omega)
    rwa [excursionWalk_upDownCons_add_two] at this
  · rintro ⟨h1, h2⟩
    refine ⟨fun i hi => ?_, h2⟩
    match i with
    | 0 => simp
    | 1 => rw [excursionWalk_upDownCons_one]; norm_num
    | j + 2 =>
      rw [excursionWalk_upDownCons_add_two]
      exact h1 j (by omega)

/-- The excursions whose value at time `2` is `1`. -/
def upDownExcursions (n : ℕ) : Finset (Fin (2 * n + 1) → Bool) :=
  {w ∈ excursionPaths n | excursionWalk w 2 = 1}

theorem eq_upDownCons_of_mem {n : ℕ} {w : Fin (2 * (n + 1) + 1) → Bool}
    (hw : w ∈ upDownExcursions (n + 1)) : upDownCons (Fin.tail (Fin.tail w)) = w := by
  simp only [upDownExcursions, Finset.mem_filter, mem_excursionPaths] at hw
  obtain ⟨⟨h1, -⟩, h2⟩ := hw
  have hw1 := h1 1 (by omega)
  have e1 := excursionWalk_succ w 0 (by omega)
  have e2 := excursionWalk_succ w 1 (by omega)
  have a0 : w 0 = true := by
    cases h : w 0 <;> simp_all [stepValue]
  have a1 : w 1 = false := by
    cases h : w 1 <;> simp_all [stepValue]
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [upDownCons, a0]
  · refine Fin.cases ?_ (fun k => ?_) j
    · simpa [upDownCons] using a1.symm
    · simp [upDownCons, Fin.tail]

theorem card_upDownExcursions_succ (n : ℕ) :
    (upDownExcursions (n + 1)).card = (excursionPaths n).card := by
  symm
  refine Finset.card_nbij' upDownCons (fun w => Fin.tail (Fin.tail w)) ?_ ?_ ?_ ?_
  · intro w hw
    simp only [Finset.mem_coe] at hw ⊢
    simp only [upDownExcursions, Finset.mem_filter]
    exact ⟨(upDownCons_mem_iff w).2 hw, by simpa using excursionWalk_upDownCons_add_two w 0⟩
  · intro w hw
    simp only [Finset.mem_coe] at hw ⊢
    rw [← upDownCons_mem_iff, eq_upDownCons_of_mem hw]
    exact (Finset.mem_filter.1 hw).1
  · intro w _
    simp [upDownCons]
  · intro w hw
    exact eq_upDownCons_of_mem hw

theorem succ_add_one_mul_catalan_succ (n : ℕ) :
    (n + 2) * catalan (n + 1) = 2 * (2 * n + 1) * catalan n := by
  have h1 := succ_mul_catalan_eq_centralBinom (n + 1)
  have h2 := Nat.succ_mul_centralBinom_succ n
  have h3 := succ_mul_catalan_eq_centralBinom n
  apply Nat.eq_of_mul_eq_mul_left (Nat.succ_pos n)
  calc (n + 1) * ((n + 2) * catalan (n + 1)) = (n + 1) * Nat.centralBinom (n + 1) := by
        rw [← h1]
    _ = 2 * (2 * n + 1) * Nat.centralBinom n := h2
    _ = (n + 1) * (2 * (2 * n + 1) * catalan n) := by rw [← h3]; ring

/-- `P(S^{2n+3}_2 = 1) = C_n / C_{n+1}`. -/
theorem excursionLaw_real_second_eq_one_succ (n : ℕ) :
    (excursionLaw (n + 1)).real {w | excursionWalk w 2 = 1} =
      (catalan n : ℝ) / catalan (n + 1) := by
  classical
  rw [excursionLaw_real_apply, ← card_excursionPaths n, ← card_excursionPaths (n + 1),
    ← card_upDownExcursions_succ n]
  rfl

/-- `P(S^{2n+1}_2 = 1) = C_{n-1}/C_n = (n+1)/(4n-2)` for `n ≥ 1`. -/
theorem excursionLaw_real_second_eq_one {n : ℕ} (hn : 1 ≤ n) :
    (excursionLaw n).real {w | excursionWalk w 2 = 1} = ((n : ℝ) + 1) / (4 * n - 2) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [excursionLaw_real_second_eq_one_succ]
  have h := succ_add_one_mul_catalan_succ m
  have hc' : (0 : ℝ) < catalan (m + 1) := by exact_mod_cast catalan_pos (m + 1)
  have h' : ((m : ℝ) + 2) * catalan (m + 1) = 2 * (2 * m + 1) * catalan m := by
    exact_mod_cast h
  rw [div_eq_div_iff hc'.ne' (by push_cast; linarith)]
  push_cast
  linarith

/-! ### S15: the displayed Kemperman formula -/

/-- The only excursion of length `3` has increments up, down, down. -/
theorem excursionPaths_one : excursionPaths 1 = {![true, false, false]} := by
  decide

/-- Its values are `1, 2, 1, 0`. -/
theorem excursionWalk_excursionPaths_one :
    (List.range 4).map (excursionWalk ![true, false, false]) = [1, 2, 1, 0] := by
  decide

theorem excursionLaw_one_second_eq_one :
    (excursionLaw 1).real {w | excursionWalk w 2 = 1} = 1 := by
  rw [excursionLaw_real_second_eq_one le_rfl]
  norm_num

/-- The right side of the displayed formula `eq:probalocale`. Here `p i k` stands for
`P(S_i = k)`, where `S` is simple random walk started from `1`. -/
noncomputable def kempermanDisplayRHS (p : ℕ → ℤ → ℝ) (n i : ℕ) (k : ℤ) : ℝ :=
  (2 * n + 1) / p (2 * n + 1) 0 * ((k - 1) / i * p i k) *
    (k / (2 * n - i + 1) * p (2 * n + 1 - i) (-k + 1))

theorem kempermanDisplayRHS_one_two_one (p : ℕ → ℤ → ℝ) :
    kempermanDisplayRHS p 1 2 1 = 0 := by
  simp [kempermanDisplayRHS]

/-- The displayed formula `eq:probalocale` fails at `n = 1`, `i = 2`, `k = 1`, whatever
real values are used for the unconditioned probabilities. -/
theorem not_kempermanDisplay (p : ℕ → ℤ → ℝ) :
    ¬ ∀ n : ℕ, 1 ≤ n → ∀ i : ℕ, 1 ≤ i → i ≤ 2 * n + 1 → ∀ k : ℤ, 1 ≤ k →
      (excursionLaw n).real {w | excursionWalk w i = k} = kempermanDisplayRHS p n i k := by
  intro h
  have := h 1 le_rfl 2 (by norm_num) (by norm_num) 1 le_rfl
  rw [excursionLaw_one_second_eq_one, kempermanDisplayRHS_one_two_one] at this
  norm_num at this

/-- The displayed formula `eq:probalocale` fails with the actual random-walk
probabilities. -/
theorem not_kempermanDisplay_srw :
    ¬ ∀ n : ℕ, 1 ≤ n → ∀ i : ℕ, 1 ≤ i → i ≤ 2 * n + 1 → ∀ k : ℤ, 1 ≤ k →
      (excursionLaw n).real {w | excursionWalk w i = k} = kempermanDisplayRHS srwProb n i k :=
  not_kempermanDisplay srwProb

/-! ### S16: the claimed bound on `X_n(δ)` -/

/-- The functional `X_n(δ)` of the source. -/
noncomputable def smallValueFunctional (n : ℕ) (δ : ℝ) (w : Fin (2 * n + 1) → Bool) : ℝ :=
  1 / Real.sqrt n * ∑ i ∈ Finset.Icc 1 n,
    1 / (excursionWalk w i : ℝ) * if (excursionWalk w i : ℝ) ≤ δ * Real.sqrt n then 1 else 0

/-- If `S_2 = 1`, then the term `i = 2` gives `X_n(1/√n) ≥ 1/√n`. -/
theorem inv_sqrt_le_smallValueFunctional {n : ℕ} (hn : 2 ≤ n) {w : Fin (2 * n + 1) → Bool}
    (hw : w ∈ excursionPaths n) (h2 : excursionWalk w 2 = 1) :
    1 / Real.sqrt n ≤ smallValueFunctional n (1 / Real.sqrt n) w := by
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.2 (by exact_mod_cast (by omega : 0 < n))
  have hw' := (mem_excursionPaths.1 hw).1
  have hsum : 1 ≤ ∑ i ∈ Finset.Icc 1 n, 1 / (excursionWalk w i : ℝ) *
      (if (excursionWalk w i : ℝ) ≤ 1 / Real.sqrt n * Real.sqrt n then 1 else 0) := by
    have hterm : 1 / (excursionWalk w 2 : ℝ) *
        (if (excursionWalk w 2 : ℝ) ≤ 1 / Real.sqrt n * Real.sqrt n then 1 else 0) = 1 := by
      rw [h2, one_div_mul_cancel hs.ne']
      norm_num
    refine hterm.symm.le.trans ?_
    refine Finset.single_le_sum (f := fun i => 1 / (excursionWalk w i : ℝ) *
      (if (excursionWalk w i : ℝ) ≤ 1 / Real.sqrt n * Real.sqrt n then 1 else 0)) ?_
      (Finset.mem_Icc.2 ⟨by norm_num, hn⟩ : 2 ∈ Finset.Icc 1 n)
    intro i hi
    have hpos : (0 : ℝ) < excursionWalk w i := by
      have := hw' i (by have := (Finset.mem_Icc.1 hi).2; omega)
      exact_mod_cast (by omega : (0 : ℤ) < excursionWalk w i)
    positivity
  rw [smallValueFunctional]
  calc 1 / Real.sqrt n = 1 / Real.sqrt n * 1 := (mul_one _).symm
    _ ≤ _ := by gcongr

/-- For `n ≥ 2`, `δ = 1/√n` and `ε = 1/(2√n)`, we have `P(X_n(δ) ≥ ε) > 1/4`. -/
theorem quarter_lt_excursionLaw_real {n : ℕ} (hn : 2 ≤ n) :
    1 / 4 < (excursionLaw n).real
      {w | 1 / (2 * Real.sqrt n) ≤ smallValueFunctional n (1 / Real.sqrt n) w} := by
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.2 (by exact_mod_cast (by omega : 0 < n))
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  calc (1 : ℝ) / 4 < ((n : ℝ) + 1) / (4 * n - 2) := by
        rw [div_lt_div_iff₀ (by norm_num) (by linarith)]
        linarith
    _ = (excursionLaw n).real {w | excursionWalk w 2 = 1} :=
        (excursionLaw_real_second_eq_one (by omega)).symm
    _ ≤ _ := by
        refine excursionLaw_real_mono fun w hw h2 => ?_
        refine le_trans ?_ (inv_sqrt_le_smallValueFunctional hn hw h2)
        rw [div_le_div_iff₀ (by positivity) hs]
        linarith

/-- No real constant `C` makes `eq:borne` hold for all `n ≥ 1`, `0 < δ ≤ 1` and `ε > 0`. -/
theorem not_uniform_smallValue_bound_of_real :
    ¬ ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n → ∀ δ ∈ Set.Ioc (0 : ℝ) 1, ∀ ε : ℝ, 0 < ε →
      (excursionLaw n).real {w | ε ≤ smallValueFunctional n δ w} ≤ C / ε * δ ^ 2 := by
  rintro ⟨C, hbound⟩
  set N : ℕ := ⌈64 * C ^ 2⌉₊ + 2 with hN
  have hN2 : 2 ≤ N := by omega
  have hNC : 64 * C ^ 2 < N := by
    have := Nat.le_ceil (64 * C ^ 2)
    rw [hN]
    push_cast
    linarith
  set s := Real.sqrt N with hs_def
  have hs : 0 < s := Real.sqrt_pos.2 (by exact_mod_cast (by omega : 0 < N))
  have hs1 : 1 ≤ s := Real.one_le_sqrt.2 (by exact_mod_cast (by omega : 1 ≤ N))
  have hss : s ^ 2 = N := Real.sq_sqrt (Nat.cast_nonneg _)
  have h8 : 8 * C < s := by nlinarith
  have hδ : 1 / s ∈ Set.Ioc (0 : ℝ) 1 := ⟨by positivity, by rw [div_le_one hs]; exact hs1⟩
  have key := hbound N (by omega) (1 / s) hδ (1 / (2 * s)) (by positivity)
  have hq := quarter_lt_excursionLaw_real hN2
  have hrhs : C / (1 / (2 * s)) * (1 / s) ^ 2 = 2 * C / s := by
    field_simp
  rw [hrhs] at key
  have := hq.trans_le key
  rw [lt_div_iff₀ hs] at this
  linarith

/-- The bound `eq:borne` is false: no `C > 0` makes it hold for all `n ≥ 1`,
`0 < δ ≤ 1` and `ε > 0`. -/
theorem not_uniform_smallValue_bound :
    ¬ ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n → ∀ δ ∈ Set.Ioc (0 : ℝ) 1, ∀ ε : ℝ, 0 < ε →
      (excursionLaw n).real {w | ε ≤ smallValueFunctional n δ w} ≤ C / ε * δ ^ 2 :=
  fun ⟨C, _, h⟩ => not_uniform_smallValue_bound_of_real ⟨C, h⟩

/-- The factor `√n ∑_{i=1}^n 1/i^{3/2}` is at least `√n`. -/
theorem sqrt_le_sqrt_mul_sum_inv_rpow {n : ℕ} (hn : 1 ≤ n) :
    Real.sqrt n ≤ Real.sqrt n * ∑ i ∈ Finset.Icc 1 n, 1 / (i : ℝ) ^ ((3 : ℝ) / 2) := by
  have h1 : (1 : ℝ) ≤ ∑ i ∈ Finset.Icc 1 n, 1 / (i : ℝ) ^ ((3 : ℝ) / 2) := by
    have := Finset.single_le_sum (f := fun i : ℕ => 1 / (i : ℝ) ^ ((3 : ℝ) / 2))
      (fun i _ => by positivity) (Finset.mem_Icc.2 ⟨le_rfl, hn⟩)
    simpa using this
  calc Real.sqrt n = Real.sqrt n * 1 := (mul_one _).symm
    _ ≤ _ := by gcongr

/-- The factor `√n ∑_{i=1}^n 1/i^{3/2}` is not uniformly bounded. -/
theorem not_bounded_sqrt_mul_sum_inv_rpow :
    ¬ ∃ B : ℝ, ∀ n : ℕ, 1 ≤ n →
      Real.sqrt n * ∑ i ∈ Finset.Icc 1 n, 1 / (i : ℝ) ^ ((3 : ℝ) / 2) ≤ B := by
  rintro ⟨B, hB⟩
  set N : ℕ := ⌈B ^ 2⌉₊ + 1 with hN
  have hBN : B ^ 2 < N := by
    have := Nat.le_ceil (B ^ 2)
    rw [hN]
    push_cast
    linarith
  have h1 := hB N (by omega)
  have h2 := sqrt_le_sqrt_mul_sum_inv_rpow (n := N) (by omega)
  have h3 := Real.lt_sqrt_of_sq_lt hBN
  linarith

end Freezing2.Audit
