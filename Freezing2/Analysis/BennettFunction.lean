module

public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# The analytic function in Bennett's inequality

The paper defines `g(u) = (1 + u) log(1 + u) - u` in Proposition `prop:bennett`
and uses the monotonicity of `x ↦ x g(t/x)` in the proof of `height=ok`.
This module proves these analytic claims. The probabilistic concentration
inequality and its application to the random trees remain separate obligations.
-/

@[expose] public section

namespace Freezing2

/-- The function occurring in Bennett's exponential concentration bound. -/
noncomputable def bennettFunction (u : ℝ) : ℝ :=
  (1 + u) * Real.log (1 + u) - u

@[simp] theorem bennettFunction_zero : bennettFunction 0 = 0 := by
  simp [bennettFunction]

/-- The derivative on the logarithm's positive domain. -/
theorem hasDerivAt_bennettFunction {u : ℝ} (hu : -1 < u) :
    HasDerivAt bennettFunction (Real.log (1 + u)) u := by
  have hne : 1 + u ≠ 0 := by linarith
  have hsum := (hasDerivAt_id u).const_add 1
  convert (hsum.mul (hsum.log hne)).sub (hasDerivAt_id u) using 1
  · rfl
  · simp [hne]

/-- `g` is strictly increasing on the nonnegative half-line. -/
theorem strictMonoOn_bennettFunction : StrictMonoOn bennettFunction (Set.Ici 0) := by
  refine strictMonoOn_of_deriv_pos (convex_Ici 0) ?_ ?_
  · intro u hu
    have hu' : 0 ≤ u := hu
    exact (hasDerivAt_bennettFunction (by linarith)).continuousAt.continuousWithinAt
  · intro u hu
    have hu' : 0 < u := by simpa only [interior_Ici, Set.mem_Ioi] using hu
    rw [(hasDerivAt_bennettFunction (by linarith : -1 < u)).deriv]
    exact Real.log_pos (by linarith)

theorem bennettFunction_pos {u : ℝ} (hu : 0 < u) : 0 < bennettFunction u := by
  simpa using strictMonoOn_bennettFunction (show (0 : ℝ) ∈ Set.Ici 0 from le_rfl)
    (show u ∈ Set.Ici 0 from hu.le) hu

theorem bennettFunction_nonneg {u : ℝ} (hu : 0 ≤ u) : 0 ≤ bennettFunction u := by
  rcases hu.eq_or_lt with rfl | hu
  · simp
  · exact (bennettFunction_pos hu).le

/-- The positive exponent before the minus sign in Bennett's bound. -/
noncomputable def bennettExponent (t x : ℝ) : ℝ := x * bennettFunction (t / x)

theorem bennettExponent_pos {t x : ℝ} (ht : 0 < t) (hx : 0 < x) :
    0 < bennettExponent t x :=
  mul_pos hx (bennettFunction_pos (div_pos ht hx))

/-- The perspective derivative simplifies to `log(1+t/x) - t/x`. -/
theorem hasDerivAt_bennettExponent {t x : ℝ} (ht : 0 < t) (hx : 0 < x) :
    HasDerivAt (bennettExponent t) (Real.log (1 + t / x) - t / x) x := by
  have hxne : x ≠ 0 := ne_of_gt hx
  have hquot : HasDerivAt (fun y : ℝ ↦ t / y) (-t / x ^ 2) x := by
    convert (hasDerivAt_const x t).div (hasDerivAt_id x) hxne using 1
    · rfl
    · simp
  have hinner : -1 < t / x := by have := div_pos ht hx; linarith
  have hchain := (hasDerivAt_bennettFunction hinner).comp x hquot
  convert (hasDerivAt_id x).mul hchain using 1
  · rfl
  · dsimp [bennettFunction]
    field_simp
    ring

/-- The monotonicity used before the union bound in the proof of `height=ok`.
The strict version implies the non-strict estimate when the mean is increased. -/
theorem strictAntiOn_bennettExponent {t : ℝ} (ht : 0 < t) :
    StrictAntiOn (bennettExponent t) (Set.Ioi 0) := by
  refine strictAntiOn_of_deriv_neg (convex_Ioi 0) ?_ ?_
  · intro x hx
    exact (hasDerivAt_bennettExponent ht hx).continuousAt.continuousWithinAt
  · intro x hx
    have hx' : 0 < x := by simpa only [interior_Ioi, Set.mem_Ioi] using hx
    rw [(hasDerivAt_bennettExponent ht hx').deriv]
    have htx : 0 < t / x := div_pos ht hx'
    have hlog := Real.log_lt_sub_one_of_pos
      (show 0 < 1 + t / x by linarith) (show 1 + t / x ≠ 1 by linarith)
    linarith

theorem antitoneOn_bennettExponent {t : ℝ} (ht : 0 < t) :
    AntitoneOn (bennettExponent t) (Set.Ioi 0) :=
  (strictAntiOn_bennettExponent ht).antitoneOn

theorem bennettExponent_le_of_le {t x y : ℝ} (ht : 0 < t) (hx : 0 < x)
    (hxy : x ≤ y) : bennettExponent t y ≤ bennettExponent t x :=
  antitoneOn_bennettExponent ht hx (lt_of_lt_of_le hx hxy) hxy

/-- Increasing the Bernoulli mean gives the upper bound used in the paper. -/
theorem exp_neg_bennettExponent_le_of_le {t x y : ℝ} (ht : 0 < t) (hx : 0 < x)
    (hxy : x ≤ y) : Real.exp (-bennettExponent t x) ≤ Real.exp (-bennettExponent t y) :=
  Real.exp_le_exp.mpr (neg_le_neg (bennettExponent_le_of_le ht hx hxy))

end Freezing2
