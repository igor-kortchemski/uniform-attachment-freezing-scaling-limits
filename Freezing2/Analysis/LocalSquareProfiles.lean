module

public import Freezing2.Analysis.ProfileIntegrals
public import Freezing2.Analysis.SquareL1

/-!
# The source's local reciprocal-square moment hypothesis

`HasLocalSquareMomentProfile` records the convergence of integrals stated in
`Lim_{1/f²}`, with the standing local square-integrability requirement. It does
not assume convergence of the squares in L¹. That stronger-looking formulation
is proved equivalent using global L¹ convergence and the Scheffé argument in
`SquareL1`.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped Topology

namespace Freezing2

/-- The paper's local second-moment hypothesis, with `g = 1/f`.
The integrability clause is the standing requirement `1/f ∈ L²_loc((0,1))`. -/
def HasLocalSquareMomentProfile (x : ℕ → ℕ → ℤ) (α : ℝ) (g : ℝ → ℝ) : Prop :=
  ∀ a b : ℝ, 0 < a → a < b → b < 1 →
    IntegrableOn (fun t ↦ (g t) ^ 2) (Icc a b) volume ∧
      Tendsto (fun n : ℕ ↦ ∫ t in Icc a b, (reciprocalProfile x α n t) ^ 2)
        atTop (𝓝 (∫ t in Icc a b, (g t) ^ 2))

/-- On a subset of the unit interval, restriction of the profile measure is
ordinary restricted Lebesgue measure. -/
theorem profileMeasure_restrict_Icc {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1) :
    profileMeasure.restrict (Icc a b) = volume.restrict (Icc a b) := by
  apply Measure.restrict_restrict_of_subset
  intro t ht
  exact ⟨ha.trans ht.1, ht.2.trans hb⟩

/-- Squaring a finite mesh profile preserves integrability, even at horizon zero. -/
theorem integrable_sq_reciprocalProfile (x : ℕ → ℕ → ℤ) (α : ℝ) (n : ℕ) :
    Integrable (fun t ↦ (reciprocalProfile x α n t) ^ 2) profileMeasure := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [reciprocalProfile]
  · exact integrableOn_stepProfile_Icc
      (fun i ↦ ((n : ℝ) ^ α / (activeCount (x n) i : ℝ)) ^ 2) hn

/-- Integrability of the unsquared profile on every closed subinterval. -/
theorem integrableOn_reciprocalProfile (x : ℕ → ℕ → ℤ) (α : ℝ) (n : ℕ)
    {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1) :
    IntegrableOn (reciprocalProfile x α n) (Icc a b) volume := by
  have h := (integrable_reciprocalProfile x α n).restrict (s := Icc a b)
  rwa [profileMeasure_restrict_Icc ha hb] at h

/-- Integrability of the squared profile on every closed subinterval. -/
theorem integrableOn_sq_reciprocalProfile (x : ℕ → ℕ → ℤ) (α : ℝ) (n : ℕ)
    {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1) :
    IntegrableOn (fun t ↦ (reciprocalProfile x α n t) ^ 2) (Icc a b) volume := by
  have h := (integrable_sq_reciprocalProfile x α n).restrict (s := Icc a b)
  rwa [profileMeasure_restrict_Icc ha hb] at h

/-- Global L¹ convergence restricts to genuine L¹ convergence on every
subinterval of the unit interval. -/
theorem tendsto_integral_abs_profile_sub_local {x : ℕ → ℕ → ℤ} {α : ℝ} {g : ℝ → ℝ}
    (hL1 : HasL1ReciprocalProfile x α g) {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1) :
    Tendsto (fun n : ℕ ↦ ∫ t in Icc a b, |reciprocalProfile x α n t - g t|)
      atTop (𝓝 0) := by
  apply squeeze_zero (fun n ↦ integral_nonneg fun t ↦ abs_nonneg _) _ hL1.2
  intro n
  rw [← profileMeasure_restrict_Icc ha hb]
  exact setIntegral_le_integral ((integrable_reciprocalProfile x α n).sub hL1.1).abs
    (ae_of_all profileMeasure fun _ ↦ abs_nonneg _)

/-- The forward implication in the equivalence stated after `Lim_{1/f²}`:
local moment convergence and global L¹ convergence imply local L¹ convergence
of the squared reciprocal profiles. -/
theorem tendsto_integral_abs_sq_profile_sub_local
    {x : ℕ → ℕ → ℤ} {α : ℝ} {g : ℝ → ℝ}
    (hL1 : HasL1ReciprocalProfile x α g) (h2 : HasLocalSquareMomentProfile x α g)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < 1) :
    Tendsto (fun n : ℕ ↦ ∫ t in Icc a b,
      |(reciprocalProfile x α n t) ^ 2 - (g t) ^ 2|) atTop (𝓝 0) := by
  have hg : IntegrableOn g (Icc a b) volume := by
    have h := hL1.1.restrict (s := Icc a b)
    rwa [profileMeasure_restrict_Icc ha.le hb.le] at h
  exact tendsto_integral_abs_sq_sub_of_l1_of_moments
    (fun n ↦ integrableOn_reciprocalProfile x α n ha.le hb.le) hg
    (fun n ↦ integrableOn_sq_reciprocalProfile x α n ha.le hb.le)
    (h2 a b ha hab hb).1 (tendsto_integral_abs_profile_sub_local hL1 ha.le hb.le)
    (h2 a b ha hab hb).2

/-- Exact equivalence of the two local formulations in the source. Integrability
is present on both sides, so totalized divergent integrals cannot satisfy either. -/
theorem hasLocalSquareMomentProfile_iff_l1_squares
    {x : ℕ → ℕ → ℤ} {α : ℝ} {g : ℝ → ℝ}
    (hL1 : HasL1ReciprocalProfile x α g) :
    HasLocalSquareMomentProfile x α g ↔
      ∀ a b : ℝ, 0 < a → a < b → b < 1 →
        IntegrableOn (fun t ↦ (g t) ^ 2) (Icc a b) volume ∧
          Tendsto (fun n : ℕ ↦ ∫ t in Icc a b,
            |(reciprocalProfile x α n t) ^ 2 - (g t) ^ 2|) atTop (𝓝 0) := by
  constructor
  · intro h2 a b ha hab hb
    exact ⟨(h2 a b ha hab hb).1,
      tendsto_integral_abs_sq_profile_sub_local hL1 h2 ha hab hb⟩
  · intro h2 a b ha hab hb
    have hg := (h2 a b ha hab hb).1
    refine ⟨hg, ?_⟩
    simpa using tendsto_setIntegral_of_l1
      (fun n ↦ integrableOn_sq_reciprocalProfile x α n ha.le hb.le) hg
      (h2 a b ha hab hb).2 Set.univ

end Freezing2
