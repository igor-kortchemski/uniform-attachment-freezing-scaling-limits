module

public import Freezing2.Geometry.ProfileSegment
public import Mathlib.Topology.Homeomorph.Lemmas

/-!
# The invertible profile time change

The reciprocal primitive is strictly increasing on the unit interval, even
when the reciprocal profile is only positive almost everywhere. It induces
a homeomorphism onto the exact limiting segment. This supplies the inverse
used in the critical coalescent time-change remark; the stochastic time-change
identity remains a separate obligation.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped Topology Classical

namespace Freezing2

/-- Exact increments of the source primitive on its full domain. -/
theorem profilePrimitive_sub {g : ℝ → ℝ} (hg : Integrable g profileMeasure)
    {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1) (hab : a ≤ b) :
    profilePrimitive g b - profilePrimitive g a = (∫ t in Icc a b, g t) / 2 := by
  have he : Integrable ((Icc (0 : ℝ) 1).indicator g) volume :=
    (integrable_indicator_iff measurableSet_Icc).mpr hg
  unfold profilePrimitive
  rw [← sub_div, intervalIntegral.integral_interval_sub_left he.intervalIntegrable
    he.intervalIntegrable, intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc]
  congr 1
  apply setIntegral_congr_fun measurableSet_Icc
  intro t ht
  exact Set.indicator_of_mem (show t ∈ Icc (0 : ℝ) 1 from
    ⟨ha.trans ht.1, ht.2.trans hb⟩) g

/-- Positivity a.e. is enough for strict increase, with both endpoints kept. -/
theorem profilePrimitive_strictMonoOn {g : ℝ → ℝ} (hg : Integrable g profileMeasure)
    (hpos : PositiveProfile g) : StrictMonoOn (profilePrimitive g) (Icc (0 : ℝ) 1) := by
  intro a ha b hb hab
  have hsub : Icc a b ⊆ Icc (0 : ℝ) 1 := Icc_subset_Icc ha.1 hb.2
  have hne : profileMeasure (Icc a b) ≠ 0 := by
    simp only [profileMeasure, Measure.restrict_apply measurableSet_Icc,
      Set.inter_eq_left.mpr hsub, Real.volume_Icc, ne_eq, ENNReal.ofReal_eq_zero]
    linarith
  have hp := setIntegral_pos_of_ae_pos hg hpos hne
  rw [profileMeasure_restrict_Icc ha.1 hb.2] at hp
  apply sub_pos.mp
  rw [profilePrimitive_sub hg ha.1 hb.2 hab.le]
  exact div_pos hp (by norm_num)

/-- The time change with precisely the source interval and image interval. -/
noncomputable def profileTimeChange {g : ℝ → ℝ} (hg : Integrable g profileMeasure)
    (hpos : PositiveProfile g) : Icc (0 : ℝ) 1 → Icc (0 : ℝ) (profilePrimitive g 1) :=
  fun t ↦ ⟨profilePrimitive g t, by
    rw [← profilePrimitive_image_unitInterval hg hpos]
    exact ⟨t, t.property, rfl⟩⟩

theorem continuous_profileTimeChange {g : ℝ → ℝ} (hg : Integrable g profileMeasure)
    (hpos : PositiveProfile g) : Continuous (profileTimeChange hg hpos) :=
  ((continuous_profilePrimitive hg).comp continuous_subtype_val).subtype_mk _

theorem bijective_profileTimeChange {g : ℝ → ℝ} (hg : Integrable g profileMeasure)
    (hpos : PositiveProfile g) : Function.Bijective (profileTimeChange hg hpos) := by
  constructor
  · intro a b hab
    apply Subtype.ext
    exact (profilePrimitive_strictMonoOn hg hpos).injOn a.property b.property
      (congrArg Subtype.val hab)
  · intro y
    have hy : (y : ℝ) ∈ profilePrimitive g '' Icc (0 : ℝ) 1 := by
      simpa only [profilePrimitive_image_unitInterval hg hpos] using y.property
    obtain ⟨t, ht, hty⟩ := hy
    exact ⟨⟨t, ht⟩, Subtype.ext hty⟩

/-- The source inverse exists and is continuous on the whole limiting segment.
No continuity or pointwise positivity of the original profile is added. -/
noncomputable def profileTimeHomeomorph {g : ℝ → ℝ} (hg : Integrable g profileMeasure)
    (hpos : PositiveProfile g) : Icc (0 : ℝ) 1 ≃ₜ Icc (0 : ℝ) (profilePrimitive g 1) :=
  IsHomeomorph.homeomorph (profileTimeChange hg hpos)
    (isHomeomorph_iff_continuous_bijective.mpr
      ⟨continuous_profileTimeChange hg hpos, bijective_profileTimeChange hg hpos⟩)

@[simp] theorem profileTimeHomeomorph_apply {g : ℝ → ℝ} (hg : Integrable g profileMeasure)
    (hpos : PositiveProfile g) (t : Icc (0 : ℝ) 1) :
    (profileTimeHomeomorph hg hpos t : ℝ) = profilePrimitive g t := rfl

theorem profilePrimitive_one_pos {g : ℝ → ℝ} (hg : Integrable g profileMeasure)
    (hpos : PositiveProfile g) : 0 < profilePrimitive g 1 := by
  have h := profilePrimitive_strictMonoOn hg hpos
    (show (0 : ℝ) ∈ Icc 0 1 by norm_num) (show (1 : ℝ) ∈ Icc 0 1 by norm_num)
    (by norm_num : (0 : ℝ) < 1)
  simpa only [show profilePrimitive g 0 = 0 by simp [profilePrimitive]] using h

/-- The inverse time change, extended by one above the terminal height as in
the source. The additional extension below zero is zero. -/
noncomputable def profileInverse {g : ℝ → ℝ} (hg : Integrable g profileMeasure)
    (hpos : PositiveProfile g) (y : ℝ) : ℝ :=
  ((profileTimeHomeomorph hg hpos).symm
    ⟨max 0 (min (profilePrimitive g 1) y), le_max_left _ _,
      max_le (profilePrimitive_one_pos hg hpos).le (min_le_left _ _)⟩ : ℝ)

theorem continuous_profileInverse {g : ℝ → ℝ} (hg : Integrable g profileMeasure)
    (hpos : PositiveProfile g) : Continuous (profileInverse hg hpos) := by
  have hc : Continuous (fun y : ℝ ↦
      (⟨max 0 (min (profilePrimitive g 1) y), le_max_left _ _,
        max_le (profilePrimitive_one_pos hg hpos).le (min_le_left _ _)⟩ :
          Icc (0 : ℝ) (profilePrimitive g 1))) :=
    (continuous_const.max (continuous_const.min continuous_id)).subtype_mk _
  exact continuous_subtype_val.comp ((profileTimeHomeomorph hg hpos).symm.continuous.comp hc)

/-- The continuous extension really inverts the original primitive everywhere
on the unit interval, including both endpoints. -/
theorem profileInverse_primitive {g : ℝ → ℝ} (hg : Integrable g profileMeasure)
    (hpos : PositiveProfile g) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    profileInverse hg hpos (profilePrimitive g t) = t := by
  let z : Icc (0 : ℝ) 1 := ⟨t, ht⟩
  have hz := (profileTimeChange hg hpos z).property
  change 0 ≤ profilePrimitive g t ∧ profilePrimitive g t ≤ profilePrimitive g 1 at hz
  have he : (⟨max 0 (min (profilePrimitive g 1) (profilePrimitive g t)), le_max_left _ _,
      max_le (profilePrimitive_one_pos hg hpos).le (min_le_left _ _)⟩ :
        Icc (0 : ℝ) (profilePrimitive g 1)) = profileTimeHomeomorph hg hpos z := by
    apply Subtype.ext
    simp only [profileTimeHomeomorph_apply, min_eq_right hz.2, max_eq_right hz.1]
    rfl
  unfold profileInverse
  rw [he, Homeomorph.symm_apply_apply]

theorem profileInverse_eq_one_of_le {g : ℝ → ℝ} (hg : Integrable g profileMeasure)
    (hpos : PositiveProfile g) {y : ℝ} (hy : profilePrimitive g 1 ≤ y) :
    profileInverse hg hpos y = 1 := by
  have he : max 0 (min (profilePrimitive g 1) y) =
      max 0 (min (profilePrimitive g 1) (profilePrimitive g 1)) := by
    rw [min_eq_left hy, min_self]
  have h : profileInverse hg hpos y = profileInverse hg hpos (profilePrimitive g 1) := by
    unfold profileInverse
    congr 2
    exact Subtype.ext he
  rw [h]
  exact profileInverse_primitive hg hpos (by norm_num)

end Freezing2
