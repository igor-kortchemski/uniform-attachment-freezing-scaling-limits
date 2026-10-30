module

public import Freezing2.Analysis.SquareL1

/-!
# Conservation of mass for a finite family of nonnegative densities

Source U29 invokes Fatou and Scheffé to pass from pointwise convergence of
finite genealogy densities to convergence of expectations and L¹ norms.
Here a direct minimum-function proof supplies that analytic implication.
The actual genealogy densities and their mass conservation remain separate.
-/

@[expose] public section

open Filter MeasureTheory
open scoped Topology BigOperators

namespace Freezing2

variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] {μ : Measure Ω}

/-- For a finite family, a.e. convergence and convergence of the total mass
force every nonnegative component to converge in L¹. The common total need
not be one, and the ambient measure need not be finite. -/
theorem finite_family_scheffe
    {f : ℕ → ι → Ω → ℝ} {g : ι → Ω → ℝ}
    (hf : ∀ n i, Integrable (f n i) μ) (hg : ∀ i, Integrable (g i) μ)
    (hf0 : ∀ n i, ∀ᵐ ω ∂μ, 0 ≤ f n i ω)
    (hg0 : ∀ i, ∀ᵐ ω ∂μ, 0 ≤ g i ω)
    (hae : ∀ i, ∀ᵐ ω ∂μ, Tendsto (fun n ↦ f n i ω) atTop (𝓝 (g i ω)))
    (hmass : Tendsto (fun n ↦ ∑ i, ∫ ω, f n i ω ∂μ) atTop
      (𝓝 (∑ i, ∫ ω, g i ω ∂μ))) :
    ∀ i, Tendsto (fun n ↦ ∫ ω, |f n i ω - g i ω| ∂μ) atTop (𝓝 0) := by
  have hmin_int (n : ℕ) (i : ι) : Integrable (fun ω ↦ min (f n i ω) (g i ω)) μ :=
    (hf n i).inf (hg i)
  have hmin (i : ι) : Tendsto (fun n ↦ ∫ ω, min (f n i ω) (g i ω) ∂μ)
      atTop (𝓝 (∫ ω, g i ω ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence (g i)
      (fun n ↦ (hmin_int n i).aestronglyMeasurable) (hg i)
    · intro n
      filter_upwards [hf0 n i, hg0 i] with ω hfn hgn
      rw [Real.norm_eq_abs, abs_of_nonneg (le_min hfn hgn)]
      exact min_le_right _ _
    · filter_upwards [hae i] with ω hω
      simpa only [min_self] using hω.min
        (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ g i ω) atTop (𝓝 (g i ω)))
  have hsummin := tendsto_finsetSum Finset.univ (fun i _ ↦ hmin i)
  have hcomb := (hmass.add_const (∑ i, ∫ ω, g i ω ∂μ)).sub (hsummin.const_mul 2)
  have hzero : (∑ i, ∫ ω, g i ω ∂μ) + (∑ i, ∫ ω, g i ω ∂μ) -
      2 * (∑ i, ∫ ω, g i ω ∂μ) = 0 := by ring
  rw [hzero] at hcomb
  have he (n : ℕ) (i : ι) : (∫ ω, |f n i ω - g i ω| ∂μ) =
      (∫ ω, f n i ω ∂μ) + (∫ ω, g i ω ∂μ) -
        2 * (∫ ω, min (f n i ω) (g i ω) ∂μ) := by
    simp_rw [abs_sub_eq_add_sub_two_min]
    have hsum_int : Integrable (fun ω ↦ f n i ω + g i ω) μ := (hf n i).add (hg i)
    rw [integral_sub hsum_int ((hmin_int n i).const_mul 2),
      integral_add (hf n i) (hg i), integral_const_mul]
  have hsum : Tendsto (fun n ↦ ∑ i, ∫ ω, |f n i ω - g i ω| ∂μ)
      atTop (𝓝 0) := by
    convert hcomb using 1
    ext n
    simp only [he, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum]
  intro i
  apply squeeze_zero (fun n ↦ integral_nonneg (fun ω ↦ abs_nonneg _)) _ hsum
  intro n
  exact Finset.single_le_sum (f := fun j ↦ ∫ ω, |f n j ω - g j ω| ∂μ)
    (fun j _ ↦ integral_nonneg (fun ω ↦ abs_nonneg _))
    (Finset.mem_univ i)

/-- In particular, each component's expectation converges. -/
theorem finite_family_integral_tendsto
    {f : ℕ → ι → Ω → ℝ} {g : ι → Ω → ℝ}
    (hf : ∀ n i, Integrable (f n i) μ) (hg : ∀ i, Integrable (g i) μ)
    (hf0 : ∀ n i, ∀ᵐ ω ∂μ, 0 ≤ f n i ω)
    (hg0 : ∀ i, ∀ᵐ ω ∂μ, 0 ≤ g i ω)
    (hae : ∀ i, ∀ᵐ ω ∂μ, Tendsto (fun n ↦ f n i ω) atTop (𝓝 (g i ω)))
    (hmass : Tendsto (fun n ↦ ∑ i, ∫ ω, f n i ω ∂μ) atTop
      (𝓝 (∑ i, ∫ ω, g i ω ∂μ))) :
    ∀ i, Tendsto (fun n ↦ ∫ ω, f n i ω ∂μ) atTop (𝓝 (∫ ω, g i ω ∂μ)) := by
  intro i
  simpa using tendsto_setIntegral_of_l1 (fun n ↦ hf n i) (hg i)
    (finite_family_scheffe hf hg hf0 hg0 hae hmass i) Set.univ

end Freezing2
