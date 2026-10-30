module

/-
Vendored from the freezing1 companion project. Local imports are relocated;
namespace, statements, and proofs are preserved. See docs/companion-provenance.md.
-/

public import Mathlib.Analysis.SpecialFunctions.Log.Monotone
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
# The rate function and the linear-regime height constant

The Introduction of *Uniform attachment with freezing* defines `f(c)` as the
unique real number larger than one satisfying
`f(c) * (log (f(c)) - 1) = (c - 1) / (c + 1)`, for `0 < c ≤ 1`.
This module proves existence and uniqueness before defining that constant.
It also establishes the elementary properties of Bennett's rate function used
in the proofs of the height theorems (Sections 4 and 5).
-/

@[expose] public section

namespace Freezing1

open Set

/-- The function defining the height factor, strictly increasing on `[1, ∞)`. -/
noncomputable def heightRate (x : ℝ) : ℝ := x * Real.log x - x

/-- Bennett's rate function, used only at nonnegative arguments in this development. -/
noncomputable def bennettRate (u : ℝ) : ℝ := (1 + u) * Real.log (1 + u) - u

theorem heightRate_eq (x : ℝ) : heightRate x = x * (Real.log x - 1) := by
  unfold heightRate
  ring

theorem continuous_heightRate : Continuous heightRate :=
  Real.continuous_mul_log.sub continuous_id

theorem hasDerivAt_heightRate {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt heightRate (Real.log x) x := by
  convert (Real.hasDerivAt_mul_log hx).fun_sub (hasDerivAt_id' x) using 1
  · rfl
  · ring

theorem strictMonoOn_heightRate : StrictMonoOn heightRate (Ici 1) := by
  refine strictMonoOn_of_deriv_pos (convex_Ici _) continuous_heightRate.continuousOn ?_
  intro x hx
  have hx1 : 1 < x := by simpa using hx
  rw [(hasDerivAt_heightRate (by linarith)).deriv]
  exact Real.log_pos hx1

@[simp] theorem heightRate_one : heightRate 1 = -1 := by simp [heightRate]

@[simp] theorem heightRate_exp_one : heightRate (Real.exp 1) = 0 := by
  simp [heightRate]

/-- Existence and uniqueness of the number specified in Theorem `thm:lineaire` (III).
The quantifier ranges over all real numbers strictly larger than one. -/
theorem linearHeightFactor_existsUnique {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1) :
    ∃! x : ℝ, 1 < x ∧ x * (Real.log x - 1) = (c - 1) / (c + 1) := by
  have hc : 0 < c + 1 := by linarith
  have htarget : (c - 1) / (c + 1) ∈ Icc (heightRate 1) (heightRate (Real.exp 1)) := by
    simp only [heightRate_one, heightRate_exp_one, mem_Icc]
    constructor
    · rw [le_div_iff₀ hc]
      linarith
    · exact div_nonpos_of_nonpos_of_nonneg (by linarith) hc.le
  have he : (1 : ℝ) ≤ Real.exp 1 := (Real.one_lt_exp_iff.mpr zero_lt_one).le
  obtain ⟨x, hx, hxeq⟩ := intermediate_value_Icc he
    continuous_heightRate.continuousOn htarget
  have hx1 : 1 < x := by
    refine lt_of_le_of_ne hx.1 ?_
    intro h
    have ht : -1 < (c - 1) / (c + 1) := by
      rw [lt_div_iff₀ hc]
      linarith
    have : heightRate x = -1 := by rw [← h, heightRate_one]
    linarith
  refine ⟨x, ⟨hx1, by simpa [heightRate_eq] using hxeq⟩, ?_⟩
  intro y hy
  apply strictMonoOn_heightRate.injOn hy.1.le hx1.le
  rw [heightRate_eq, heightRate_eq, hy.2]
  simpa only [heightRate_eq] using hxeq.symm

/-- The admissible linear growth constants of Theorem `thm:lineaire`. -/
abbrev LinearRegimeParameter := Ioc (0 : ℝ) 1

/-- The height factor `f(c)`. Its domain records exactly `0 < c ≤ 1`.
The choice is justified by `linearHeightFactor_existsUnique`, and uniqueness
ensures that all later statements are independent of that choice. -/
noncomputable def linearHeightFactor (c : LinearRegimeParameter) : ℝ :=
  Classical.choose (linearHeightFactor_existsUnique c.property.1 c.property.2).exists

theorem linearHeightFactor_spec (c : LinearRegimeParameter) :
    1 < linearHeightFactor c ∧
      linearHeightFactor c * (Real.log (linearHeightFactor c) - 1) =
        ((c : ℝ) - 1) / ((c : ℝ) + 1) :=
  Classical.choose_spec (linearHeightFactor_existsUnique c.property.1 c.property.2).exists

theorem one_lt_linearHeightFactor (c : LinearRegimeParameter) : 1 < linearHeightFactor c :=
  (linearHeightFactor_spec c).1

theorem linearHeightFactor_unique (c : LinearRegimeParameter) {x : ℝ}
    (hx : 1 < x) (heq : x * (Real.log x - 1) = ((c : ℝ) - 1) / ((c : ℝ) + 1)) :
    x = linearHeightFactor c :=
  (linearHeightFactor_existsUnique c.property.1 c.property.2).unique
    ⟨hx, heq⟩ (linearHeightFactor_spec c)

theorem linearHeightFactor_le_exp_one (c : LinearRegimeParameter) :
    linearHeightFactor c ≤ Real.exp 1 := by
  by_contra h
  have hlt : Real.exp 1 < linearHeightFactor c := lt_of_not_ge h
  have he : (1 : ℝ) ≤ Real.exp 1 := (Real.one_lt_exp_iff.mpr zero_lt_one).le
  have hr := strictMonoOn_heightRate he (one_lt_linearHeightFactor c).le hlt
  rw [heightRate_exp_one, heightRate_eq, (linearHeightFactor_spec c).2] at hr
  have hnonpos : ((c : ℝ) - 1) / ((c : ℝ) + 1) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by linarith [c.property.2])
      (by linarith [c.property.1])
  exact (not_lt_of_ge hnonpos) hr

/-- Increasing the limiting active fraction increases the height factor `f(c)`. -/
theorem strictMono_linearHeightFactor : StrictMono linearHeightFactor := by
  intro a b hab
  have ha : 0 < (a : ℝ) + 1 := by linarith [a.property.1]
  have hb : 0 < (b : ℝ) + 1 := by linarith [b.property.1]
  have hab' : (a : ℝ) < (b : ℝ) := hab
  have ht : ((a : ℝ) - 1) / ((a : ℝ) + 1) <
      ((b : ℝ) - 1) / ((b : ℝ) + 1) := by
    apply (div_lt_div_iff₀ ha hb).2
    nlinarith
  by_contra h
  have hle : linearHeightFactor b ≤ linearHeightFactor a := le_of_not_gt h
  have hr := strictMonoOn_heightRate.monotoneOn
    (one_lt_linearHeightFactor b).le (one_lt_linearHeightFactor a).le hle
  rw [heightRate_eq, heightRate_eq, (linearHeightFactor_spec b).2,
    (linearHeightFactor_spec a).2] at hr
  exact (not_lt_of_ge hr) ht

@[simp] theorem linearHeightFactor_one :
    linearHeightFactor ⟨1, by constructor <;> norm_num⟩ = Real.exp 1 := by
  symm
  apply linearHeightFactor_unique
  · exact Real.one_lt_exp_iff.mpr zero_lt_one
  · simp

theorem bennettRate_eq_heightRate (u : ℝ) :
    bennettRate u = heightRate (1 + u) + 1 := by
  unfold bennettRate heightRate
  ring

@[simp] theorem bennettRate_zero : bennettRate 0 = 0 := by simp [bennettRate]

theorem strictMonoOn_bennettRate : StrictMonoOn bennettRate (Ici 0) := by
  intro x hx y hy hxy
  rw [bennettRate_eq_heightRate, bennettRate_eq_heightRate]
  have h := strictMonoOn_heightRate
    (show 1 + x ∈ Ici (1 : ℝ) by simp only [mem_Ici] at *; linarith)
    (show 1 + y ∈ Ici (1 : ℝ) by simp only [mem_Ici] at *; linarith)
    (show 1 + x < 1 + y by linarith)
  linarith

theorem bennettRate_pos {u : ℝ} (hu : 0 < u) : 0 < bennettRate u := by
  simpa using strictMonoOn_bennettRate (show (0 : ℝ) ∈ Ici 0 by simp) hu.le hu

theorem bennettRate_nonneg {u : ℝ} (hu : 0 ≤ u) : 0 ≤ bennettRate u := by
  simpa using strictMonoOn_bennettRate.monotoneOn
    (show (0 : ℝ) ∈ Ici 0 by simp) hu hu

/-- The normalization used in the upper bound of the linear-regime height theorem. -/
theorem bennettRate_linearHeightFactor (c : LinearRegimeParameter) :
    bennettRate (linearHeightFactor c - 1) = 2 * (c : ℝ) / ((c : ℝ) + 1) := by
  rw [bennettRate_eq_heightRate]
  have hs : 1 + (linearHeightFactor c - 1) = linearHeightFactor c := by ring
  rw [hs, heightRate_eq, (linearHeightFactor_spec c).2]
  have hc : (c : ℝ) + 1 ≠ 0 := by linarith [c.property.1]
  field_simp [hc]
  ring

/-- The strict rate inequality used when adding a positive margin to `f(c)`. -/
theorem bennettRate_linearHeightFactor_add {ε : ℝ} (c : LinearRegimeParameter)
    (hε : 0 < ε) :
    2 * (c : ℝ) / ((c : ℝ) + 1) < bennettRate (linearHeightFactor c - 1 + ε) := by
  rw [← bennettRate_linearHeightFactor c]
  have hf := one_lt_linearHeightFactor c
  apply strictMonoOn_bennettRate
  · simp only [mem_Ici]
    linarith
  · simp only [mem_Ici]
    linarith
  · linarith

@[simp] theorem bennettRate_exp_one_sub_one : bennettRate (Real.exp 1 - 1) = 1 := by
  rw [bennettRate_eq_heightRate]
  have hs : 1 + (Real.exp 1 - 1) = Real.exp 1 := by ring
  rw [hs, heightRate_exp_one]
  norm_num

theorem one_lt_bennettRate_exp_one_sub_one_add {ε : ℝ} (hε : 0 < ε) :
    1 < bennettRate (Real.exp 1 - 1 + ε) := by
  have he : (1 : ℝ) < Real.exp 1 := Real.one_lt_exp_iff.mpr zero_lt_one
  have h := strictMonoOn_bennettRate (show Real.exp 1 - 1 ∈ Ici 0 by
    simp only [mem_Ici]; linarith)
    (show Real.exp 1 - 1 + ε ∈ Ici 0 by simp only [mem_Ici]; linarith)
    (show Real.exp 1 - 1 < Real.exp 1 - 1 + ε by linarith)
  simpa using h

/-- A rate estimate used to control all real moments in the height argument. -/
theorem self_le_bennettRate {u : ℝ} (hu : Real.exp 2 - 1 ≤ u) : u ≤ bennettRate u := by
  have hpos : 0 < 1 + u := by linarith [Real.exp_pos 2]
  have hlog : 2 ≤ Real.log (1 + u) :=
    (Real.le_log_iff_exp_le hpos).mpr (by linarith)
  unfold bennettRate
  nlinarith

end Freezing1
