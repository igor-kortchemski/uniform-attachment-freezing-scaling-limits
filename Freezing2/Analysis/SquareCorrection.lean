module

public import Freezing2.Analysis.LocalSquareProfiles
public import Freezing2.Analysis.ReciprocalCorrection

/-!
# The local reciprocal-square correction

The squared reciprocal profile and the denominator `S(S+1)` have the same
local L¹ limit. The missing correction is `u³/(c+u)`, for `u=c/S` and `c=n^α`.
A scalar bound transfers local L¹ convergence of the squares to this correction;
dominated convergence handles the fixed limiting profile. This makes explicit
the correction step used in the proof of Lemma `lem:hnalpha(v)`.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped Topology

namespace Freezing2

/-- The scalar error in replacing `1/S²` by `1/(S(S+1))`. -/
noncomputable def squareCorrection (c u : ℝ) : ℝ := u ^ 3 / (c + u)

theorem squareCorrection_nonneg {c u : ℝ} (hc : 0 < c) (hu : 0 ≤ u) :
    0 ≤ squareCorrection c u := by
  unfold squareCorrection
  positivity

theorem squareCorrection_le_sq {c u : ℝ} (hc : 0 < c) (hu : 0 ≤ u) :
    squareCorrection c u ≤ u ^ 2 := by
  unfold squareCorrection
  apply (div_le_iff₀ (show 0 < c + u by linarith)).mpr
  nlinarith [mul_nonneg hc.le (sq_nonneg u)]

/-- A correction at `u` is controlled by the squared error from `v` and a
fixed correction at `v`. The constants do not depend on the positive parameter. -/
theorem squareCorrection_le_sq_error {c u v : ℝ}
    (hc : 0 < c) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    squareCorrection c u ≤ 2 * |u ^ 2 - v ^ 2| + 8 * squareCorrection c v := by
  by_cases huv : u ≤ 2 * v
  · have hu2 : u ^ 2 ≤ 4 * v ^ 2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr huv) (show 0 ≤ 2 * v + u by positivity)]
    have hf : u / (c + u) ≤ (2 * v) / (c + v) := by
      apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
      nlinarith [mul_nonneg hc.le (sub_nonneg.mpr huv), mul_nonneg hu hv]
    have he : squareCorrection c u ≤ 8 * squareCorrection c v := by
      calc
        _ = u ^ 2 * (u / (c + u)) := by unfold squareCorrection; ring
        _ ≤ (4 * v ^ 2) * ((2 * v) / (c + v)) :=
          mul_le_mul hu2 hf (by positivity) (by positivity)
        _ = _ := by unfold squareCorrection; ring
    linarith [abs_nonneg (u ^ 2 - v ^ 2)]
  · have hu2 : 4 * v ^ 2 ≤ u ^ 2 := by
      nlinarith [mul_nonneg (show 0 ≤ u - 2 * v by linarith) (show 0 ≤ u + 2 * v by positivity)]
    have hs := squareCorrection_le_sq hc hu
    have hv0 := squareCorrection_nonneg hc hv
    have ha := le_abs_self (u ^ 2 - v ^ 2)
    nlinarith

theorem tendsto_squareCorrection {c : ℕ → ℝ}
    (hc : Tendsto c atTop atTop) (u : ℝ) :
    Tendsto (fun n ↦ squareCorrection (c n) u) atTop (𝓝 0) :=
  tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right atTop u hc)

section Integral

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

theorem aestronglyMeasurable_squareCorrection {f : Ω → ℝ}
    (hf : AEStronglyMeasurable f μ) (c : ℝ) :
    AEStronglyMeasurable (fun ω ↦ squareCorrection c (f ω)) μ := by
  unfold squareCorrection
  exact ((hf.aemeasurable.pow_const 3).div
    (aemeasurable_const.add hf.aemeasurable)).aestronglyMeasurable

theorem integrable_squareCorrection {f : Ω → ℝ}
    (hf : AEStronglyMeasurable f μ) (hf2 : Integrable (fun ω ↦ (f ω) ^ 2) μ)
    (hf0 : ∀ᵐ ω ∂μ, 0 ≤ f ω) {c : ℝ} (hc : 0 < c) :
    Integrable (fun ω ↦ squareCorrection c (f ω)) μ := by
  apply hf2.mono' (aestronglyMeasurable_squareCorrection hf c)
  filter_upwards [hf0] with ω hω
  rw [Real.norm_eq_abs, abs_of_nonneg (squareCorrection_nonneg hc hω)]
  exact squareCorrection_le_sq hc hω

/-- Dominated convergence of the correction of a fixed square-integrable function. -/
theorem tendsto_integral_squareCorrection_fixed {g : Ω → ℝ}
    (hg : AEStronglyMeasurable g μ) (hg2 : Integrable (fun ω ↦ (g ω) ^ 2) μ)
    (hg0 : ∀ᵐ ω ∂μ, 0 ≤ g ω) {c : ℕ → ℝ} (hc0 : ∀ n, 0 < c n)
    (hc : Tendsto c atTop atTop) :
    Tendsto (fun n ↦ ∫ ω, squareCorrection (c n) (g ω) ∂μ) atTop (𝓝 0) := by
  have h := tendsto_integral_of_dominated_convergence (μ := μ)
    (F := fun n ω ↦ squareCorrection (c n) (g ω)) (f := fun _ ↦ (0 : ℝ))
    (fun ω ↦ (g ω) ^ 2)
    (fun n ↦ aestronglyMeasurable_squareCorrection hg (c n)) hg2
    (fun n ↦ ?_) (Eventually.of_forall fun ω ↦ tendsto_squareCorrection hc (g ω))
  · simpa using h
  · filter_upwards [hg0] with ω hω
    rw [Real.norm_eq_abs, abs_of_nonneg (squareCorrection_nonneg (hc0 n) hω)]
    exact squareCorrection_le_sq (hc0 n) hω

/-- Local L¹ convergence of squares makes the varying correction vanish.
The conclusion needs no uniform pointwise bound on the approximating profiles. -/
theorem tendsto_integral_squareCorrection_of_l1_squares
    {f : ℕ → Ω → ℝ} {g : Ω → ℝ}
    (hf : ∀ n, AEStronglyMeasurable (f n) μ) (hg : AEStronglyMeasurable g μ)
    (hf2 : ∀ n, Integrable (fun ω ↦ (f n ω) ^ 2) μ)
    (hg2 : Integrable (fun ω ↦ (g ω) ^ 2) μ)
    (hf0 : ∀ n, ∀ᵐ ω ∂μ, 0 ≤ f n ω) (hg0 : ∀ᵐ ω ∂μ, 0 ≤ g ω)
    {c : ℕ → ℝ} (hc0 : ∀ n, 0 < c n) (hc : Tendsto c atTop atTop)
    (hfg : Tendsto (fun n ↦ ∫ ω, |(f n ω) ^ 2 - (g ω) ^ 2| ∂μ) atTop (𝓝 0)) :
    Tendsto (fun n ↦ ∫ ω, squareCorrection (c n) (f n ω) ∂μ) atTop (𝓝 0) := by
  have hfixed := tendsto_integral_squareCorrection_fixed hg hg2 hg0 hc0 hc
  have hbound (n : ℕ) :
      (∫ ω, squareCorrection (c n) (f n ω) ∂μ) ≤
        2 * (∫ ω, |(f n ω) ^ 2 - (g ω) ^ 2| ∂μ) +
          8 * (∫ ω, squareCorrection (c n) (g ω) ∂μ) := by
    have he : Integrable (fun ω ↦ |(f n ω) ^ 2 - (g ω) ^ 2|) μ :=
      ((hf2 n).sub hg2).abs
    have hgint := integrable_squareCorrection hg hg2 hg0 (hc0 n)
    calc
      _ ≤ ∫ ω, 2 * |(f n ω) ^ 2 - (g ω) ^ 2| +
          8 * squareCorrection (c n) (g ω) ∂μ := by
        apply integral_mono_ae (integrable_squareCorrection (hf n) (hf2 n) (hf0 n) (hc0 n))
          ((he.const_mul 2).add (hgint.const_mul 8))
        filter_upwards [hf0 n, hg0] with ω hfn hgn
        exact squareCorrection_le_sq_error (hc0 n) hfn hgn
      _ = _ := by
        rw [integral_add (he.const_mul 2) (hgint.const_mul 8)]
        simp only [integral_const_mul]
  have hnonneg (n : ℕ) : 0 ≤ ∫ ω, squareCorrection (c n) (f n ω) ∂μ := by
    apply integral_nonneg_of_ae
    filter_upwards [hf0 n] with ω hω
    exact squareCorrection_nonneg (hc0 n) hω
  exact squeeze_zero hnonneg hbound (by simpa using (hfg.const_mul 2).add (hfixed.const_mul 8))

end Integral

/-- Exact reciprocal specialization, with all denominators strictly positive. -/
theorem squareCorrection_div {c s : ℝ} (hc : 0 < c) (hs : 0 < s) :
    squareCorrection c (c / s) = (c / s) ^ 2 - c ^ 2 / (s * (s + 1)) := by
  have hcne := ne_of_gt hc
  have hsne := ne_of_gt hs
  have hs1 : s + 1 ≠ 0 := by positivity
  unfold squareCorrection
  field_simp
  ring

/-- Vanishing of the actual local reciprocal-profile correction. -/
theorem tendsto_integral_squareCorrection_profile
    {x : ℕ → ℕ → ℤ} {α : ℝ} {g : ℝ → ℝ}
    (hx : AdmissibleArray x) (hα : 0 < α)
    (hL1 : HasL1ReciprocalProfile x α g) (h2 : HasLocalSquareMomentProfile x α g)
    (hg0 : ∀ᵐ t ∂profileMeasure, 0 ≤ g t)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < 1) :
    Tendsto (fun n : ℕ ↦ ∫ t in Icc a b,
      squareCorrection ((n : ℝ) ^ α) (reciprocalProfile x α n t)) atTop (𝓝 0) := by
  let μ : Measure ℝ := volume.restrict (Icc a b)
  have hμ : profileMeasure.restrict (Icc a b) = μ := profileMeasure_restrict_Icc ha.le hb.le
  have hf0 (n : ℕ) : ∀ᵐ t ∂μ, 0 ≤ reciprocalProfile x α n t := by
    rw [← hμ]
    exact ae_restrict_of_ae (reciprocalProfile_nonneg_ae hx α n)
  have hg0' : ∀ᵐ t ∂μ, 0 ≤ g t := by
    rw [← hμ]
    exact ae_restrict_of_ae hg0
  have hg : Integrable g μ := by
    rw [← hμ]
    exact hL1.1.restrict
  let c : ℕ → ℝ := fun n ↦ if n = 0 then 1 else (n : ℝ) ^ α
  have hcpos (n : ℕ) : 0 < c n := by
    dsimp [c]
    split_ifs with hn
    · norm_num
    · exact Real.rpow_pos_of_pos (by exact_mod_cast Nat.pos_of_ne_zero hn) _
  have hc_eq : c =ᶠ[atTop] (fun n : ℕ ↦ (n : ℝ) ^ α) := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    simp [c, Nat.ne_of_gt hn]
  have hc : Tendsto c atTop atTop :=
    ((tendsto_rpow_atTop hα).comp (tendsto_natCast_atTop_atTop (R := ℝ))).congr' hc_eq.symm
  have h := tendsto_integral_squareCorrection_of_l1_squares
    (fun n ↦ (integrableOn_reciprocalProfile x α n ha.le hb.le).aestronglyMeasurable)
    hg.aestronglyMeasurable
    (fun n ↦ integrableOn_sq_reciprocalProfile x α n ha.le hb.le)
    (h2 a b ha hab hb).1 hf0 hg0' hcpos hc
    (tendsto_integral_abs_sq_profile_sub_local hL1 h2 ha hab hb)
  apply h.congr'
  filter_upwards [hc_eq] with n hn
  rw [hn]

/-- Replacing the squared reciprocal denominator by `S(S+1)` preserves its
local L¹ limit. The numerator `(n^α)²` equals `n^(2α)` at every positive horizon. -/
theorem tendsto_integral_abs_sq_profile_sub_shifted
    {x : ℕ → ℕ → ℤ} {α : ℝ} {g : ℝ → ℝ}
    (hx : AdmissibleArray x) (hα : 0 < α)
    (hL1 : HasL1ReciprocalProfile x α g) (h2 : HasLocalSquareMomentProfile x α g)
    (hg0 : ∀ᵐ t ∂profileMeasure, 0 ≤ g t)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < 1) :
    Tendsto (fun n : ℕ ↦ ∫ t in Icc a b,
      |(reciprocalProfile x α n t) ^ 2 -
        ((n : ℝ) ^ α) ^ 2 /
          ((activeCount (x n) ⌊(n : ℝ) * t⌋₊ : ℝ) *
            ((activeCount (x n) ⌊(n : ℝ) * t⌋₊ : ℝ) + 1))|) atTop (𝓝 0) := by
  apply (tendsto_integral_squareCorrection_profile hx hα hL1 h2 hg0 ha hab hb).congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  have hmem : t ∈ Icc (0 : ℝ) 1 := ⟨ha.le.trans ht.1, ht.2.trans hb.le⟩
  have hi : ⌊(n : ℝ) * t⌋₊ ≤ n := by
    apply Nat.floor_le_of_le
    simpa using mul_le_mul_of_nonneg_left hmem.2 (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  have hs := activeCount_real_pos hx n hi
  have hc : 0 < (n : ℝ) ^ α := Real.rpow_pos_of_pos (by exact_mod_cast hn) _
  have hnonneg := squareCorrection_nonneg hc (reciprocalProfile_nonneg hx α n hmem)
  unfold reciprocalProfile at *
  rw [squareCorrection_div hc hs] at hnonneg ⊢
  exact (abs_of_nonneg hnonneg).symm

/-- The reciprocal-square profile with the corrected denominator `S(S+1)`. -/
noncomputable def shiftedSquareProfile (x : ℕ → ℕ → ℤ) (α : ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  ((n : ℝ) ^ α) ^ 2 /
    ((activeCount (x n) ⌊(n : ℝ) * t⌋₊ : ℝ) *
      ((activeCount (x n) ⌊(n : ℝ) * t⌋₊ : ℝ) + 1))

/-- The shifted denominator still gives a finite step profile. -/
theorem integrable_shiftedSquareProfile (x : ℕ → ℕ → ℤ) (α : ℝ) (n : ℕ) :
    Integrable (shiftedSquareProfile x α n) profileMeasure := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · change Integrable (fun t : ℝ ↦ shiftedSquareProfile x α 0 t) profileMeasure
    simp only [shiftedSquareProfile, Nat.cast_zero, zero_mul, Nat.floor_zero,
      activeCount_zero, Int.cast_one, one_mul]
    exact integrable_const _
  · exact integrableOn_stepProfile_Icc
      (fun i ↦ ((n : ℝ) ^ α) ^ 2 /
        ((activeCount (x n) i : ℝ) * ((activeCount (x n) i : ℝ) + 1))) hn

theorem integrableOn_shiftedSquareProfile (x : ℕ → ℕ → ℤ) (α : ℝ) (n : ℕ)
    {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1) :
    IntegrableOn (shiftedSquareProfile x α n) (Icc a b) volume := by
  have h := (integrable_shiftedSquareProfile x α n).restrict (s := Icc a b)
  rwa [profileMeasure_restrict_Icc ha hb] at h

/-- The denominator `S(S+1)` has the same local L¹ limit `g²` as the squared
reciprocal profile, with integrability proved rather than assumed. -/
theorem tendsto_integral_abs_shiftedSquareProfile_sub_local
    {x : ℕ → ℕ → ℤ} {α : ℝ} {g : ℝ → ℝ}
    (hx : AdmissibleArray x) (hα : 0 < α)
    (hL1 : HasL1ReciprocalProfile x α g) (h2 : HasLocalSquareMomentProfile x α g)
    (hg0 : ∀ᵐ t ∂profileMeasure, 0 ≤ g t)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < 1) :
    Tendsto (fun n : ℕ ↦ ∫ t in Icc a b,
      |shiftedSquareProfile x α n t - (g t) ^ 2|) atTop (𝓝 0) := by
  have hdiff : Tendsto (fun n : ℕ ↦ ∫ t in Icc a b,
      |(reciprocalProfile x α n t) ^ 2 - shiftedSquareProfile x α n t|)
      atTop (𝓝 0) :=
    tendsto_integral_abs_sq_profile_sub_shifted hx hα hL1 h2 hg0 ha hab hb
  have hsq := tendsto_integral_abs_sq_profile_sub_local hL1 h2 ha hab hb
  apply squeeze_zero (fun n ↦ integral_nonneg fun _ ↦ abs_nonneg _) _
    (by simpa using hdiff.add hsq)
  intro n
  have hp := integrableOn_shiftedSquareProfile x α n ha.le hb.le
  have hq := integrableOn_sq_reciprocalProfile x α n ha.le hb.le
  have hg := (h2 a b ha hab hb).1
  have he1 : IntegrableOn (fun t ↦
      |(reciprocalProfile x α n t) ^ 2 - shiftedSquareProfile x α n t|) (Icc a b) volume :=
    (hq.sub hp).abs
  have he2 : IntegrableOn (fun t ↦
      |(reciprocalProfile x α n t) ^ 2 - (g t) ^ 2|) (Icc a b) volume :=
    (hq.sub hg).abs
  calc
    _ ≤ ∫ t in Icc a b,
        |(reciprocalProfile x α n t) ^ 2 - shiftedSquareProfile x α n t| +
        |(reciprocalProfile x α n t) ^ 2 - (g t) ^ 2| := by
      apply integral_mono_ae (hp.sub hg).abs (he1.add he2)
      apply Eventually.of_forall
      intro t
      simpa only [Pi.sub_apply, Pi.add_apply,
        abs_sub_comm (shiftedSquareProfile x α n t)] using
        abs_sub_le (shiftedSquareProfile x α n t) ((reciprocalProfile x α n t) ^ 2) ((g t) ^ 2)
    _ = _ := integral_add he1 he2

end Freezing2
