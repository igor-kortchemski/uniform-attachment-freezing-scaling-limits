module

/-
Vendored from the freezing1 companion project. Local imports are relocated;
namespace, statements, and proofs are preserved. See docs/companion-provenance.md.
-/

public import Freezing2.Companion.ForwardLaw
public import Freezing2.Companion.HeightScale
public import Mathlib.Probability.Moments.Basic
public import Mathlib.Probability.Kernel.Composition.IntegralCompProd

/-!
# Active-height averaging in the forward construction

For a test function on heights, the empirical average over active vertices
evolves by a Bernoulli shift at an attachment step. At a freezing step its
average over the uniform deleted vertex is unchanged. This is a direct route
to the active-height law, independent of the reverse-forest equivalence.
-/

@[expose] public section

namespace Freezing1.Forward

open MeasureTheory
open scoped BigOperators ENNReal ProbabilityTheory

/-- The sum of a test function over active vertex heights. -/
def activeSum (s : State) (f : ℕ → ℝ) : ℝ := ∑ v ∈ s.active, f (s.height v)

/-- Expectation of a test function at a uniform active vertex. -/
noncomputable def activeMean (s : State) (f : ℕ → ℝ) : ℝ := activeSum s f / s.active.card

theorem activeSum_attach {n : ℕ} {s : State} (h : ValidAt n s)
    {v : ℕ} (_hv : v ∈ s.active) (f : ℕ → ℝ) :
    activeSum (attach s (n + 1) v) f = activeSum s f + f (s.height v + 1) := by
  have hfresh : n + 1 ∉ s.active := by
    intro ht; have := h.vertices_le _ (h.active_subset ht); omega
  unfold activeSum
  simp only [attach]
  rw [Finset.sum_insert hfresh]
  simp only [Function.update_self]
  rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro w hw
  have hwne : w ≠ n + 1 := by intro he; exact hfresh (he ▸ hw)
  simp [hwne]

theorem activeSum_freeze {s : State} {v : ℕ} (hv : v ∈ s.active)
    (t : ℕ) (f : ℕ → ℝ) :
    activeSum (freeze s t v) f = activeSum s f - f (s.height v) := by
  have hsum := Finset.sum_erase_add s.active (fun w => f (s.height w)) hv
  simp only [activeSum, freeze]
  linarith

/-- Conditional average after attaching, before averaging over the previous random state. -/
theorem average_activeMean_attach {n : ℕ} {s : State} (h : ValidAt n s)
    (hs : s.active.Nonempty) (f : ℕ → ℝ) :
    (∑ v ∈ s.active, activeMean (attach s (n + 1) v) f) / s.active.card =
      ((s.active.card : ℝ) / (s.active.card + 1)) * activeMean s f +
      (1 / (s.active.card + 1)) * activeMean s (fun k => f (k + 1)) := by
  have hfresh : n + 1 ∉ s.active := by
    intro ht; have := h.vertices_le _ (h.active_subset ht); omega
  have hcard : (s.active.card : ℝ) ≠ 0 := by exact_mod_cast hs.card_pos.ne'
  have hcard1 : (s.active.card : ℝ) + 1 ≠ 0 := by positivity
  have heq : ∀ v ∈ s.active, activeMean (attach s (n + 1) v) f =
      (activeSum s f + f (s.height v + 1)) / (s.active.card + 1) := by
    intro v hv
    rw [activeMean, activeSum_attach h hv]
    simp [attach, hfresh]
  simp_rw [Finset.sum_congr rfl heq, ← Finset.sum_div, Finset.sum_add_distrib,
    Finset.sum_const, nsmul_eq_mul]
  unfold activeMean activeSum
  field_simp

/-- Uniform freezing preserves the law of a uniform active survivor. -/
theorem average_activeMean_freeze {s : State} (hs : 1 < s.active.card)
    (t : ℕ) (f : ℕ → ℝ) :
    (∑ v ∈ s.active, activeMean (freeze s t v) f) / s.active.card = activeMean s f := by
  have hcard : (s.active.card : ℝ) ≠ 0 := by exact_mod_cast (by omega : s.active.card ≠ 0)
  have hcard1 : (s.active.card : ℝ) - 1 ≠ 0 := by
    have : (1 : ℝ) < s.active.card := by exact_mod_cast hs
    linarith
  have heq : ∀ v ∈ s.active, activeMean (freeze s t v) f =
      (activeSum s f - f (s.height v)) / ((s.active.card : ℝ) - 1) := by
    intro v hv
    rw [activeMean, activeSum_freeze hv, show (freeze s t v).active = s.active.erase v from rfl,
      Finset.card_erase_of_mem hv, Nat.cast_sub (by omega), Nat.cast_one]
  rw [Finset.sum_congr rfl heq, ← Finset.sum_div, Finset.sum_sub_distrib,
    Finset.sum_const, nsmul_eq_mul]
  unfold activeMean activeSum
  field_simp

theorem integral_uniform_active (s : State) (hs : s.active.Nonempty) (f : ℕ → ℝ) :
    (∫ v, f v ∂Measure.uniformOfFinset s.active) = (∑ v ∈ s.active, f v) / s.active.card := by
  unfold Measure.uniformOfFinset
  rw [integral_finsetSum_measure]
  · simp only [integral_smul_measure, integral_dirac, smul_eq_mul, ENNReal.toReal_inv,
      ENNReal.toReal_natCast]
    rw [← Finset.mul_sum]
    ring
  · intro v _
    apply Integrable.smul_measure (integrable_dirac (by simp))
    simp [hs.ne_empty]

theorem transitionLaw_integral (s : State) (t : ℕ) (sign : Bool)
    (hs : s.active.Nonempty) (f : State → ℝ) :
    (∫ s', f s' ∂transitionLaw s t sign) =
      (∑ v ∈ s.active, f (step s t sign v)) / s.active.card := by
  rw [transitionLaw, ite_eq_left hs, integral_map (by fun_prop) measurable_from_top.aestronglyMeasurable]
  exact integral_uniform_active s hs _

/-- The actual conditional active-height distribution undergoes a Bernoulli shift. -/
theorem transitionLaw_activeMean_attach {n : ℕ} {s : State} (h : ValidAt n s)
    (hs : s.active.Nonempty) (f : ℕ → ℝ) :
    (∫ s', activeMean s' f ∂transitionLaw s (n + 1) true) =
      ((s.active.card : ℝ) / (s.active.card + 1)) * activeMean s f +
      (1 / (s.active.card + 1)) * activeMean s (fun k => f (k + 1)) := by
  rw [transitionLaw_integral s _ _ hs]
  convert average_activeMean_attach h hs f using 1
  congr 1
  apply Finset.sum_congr rfl
  intro v hv
  simp [Forward.step, hv]

/-- Uniform freezing leaves the conditional uniform-survivor height law unchanged. -/
theorem transitionLaw_activeMean_freeze {s : State} (hs : 1 < s.active.card)
    (t : ℕ) (f : ℕ → ℝ) :
    (∫ s', activeMean s' f ∂transitionLaw s t false) = activeMean s f := by
  rw [transitionLaw_integral s _ _ (Finset.card_pos.mp (by omega))]
  convert average_activeMean_freeze hs t f using 1
  congr 1
  apply Finset.sum_congr rfl
  intro v hv
  simp [Forward.step, hv]

theorem ValidAt.height_le_id {n : ℕ} {s : State} (h : ValidAt n s)
    (v : ℕ) (hv : v ∈ s.vertices) : s.height v ≤ v := by
  induction v using Nat.strong_induction_on with
  | h v ih =>
    by_cases hv0 : v = 0
    · subst v; simp [h.height_root]
    · have hlt := h.parent_lt v hv hv0
      have hp := ih (s.parent v) hlt (h.parent_mem v hv)
      rw [h.height_parent v hv hv0]
      omega

theorem activeMean_bound {s : State} {f : ℕ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hf : ∀ v ∈ s.active, |f (s.height v)| ≤ C) : |activeMean s f| ≤ C := by
  by_cases hs : s.active.Nonempty
  · have hc : (0 : ℝ) < s.active.card := by exact_mod_cast hs.card_pos
    rw [activeMean, abs_div, abs_of_pos hc, div_le_iff₀ hc]
    calc
      |activeSum s f| ≤ ∑ v ∈ s.active, |f (s.height v)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _v ∈ s.active, C := Finset.sum_le_sum hf
      _ = C * s.active.card := by simp [mul_comm]
  · have he := Finset.not_nonempty_iff_eq_empty.mp hs
    simpa [activeMean, activeSum, he] using hC

/-- Every test function on the finite possible height range is integrable. -/
theorem treeLaw_integrable_activeMean (x : SignSequence) (n : ℕ) (f : ℕ → ℝ) :
    Integrable (fun s => activeMean s f) (treeLaw x n) := by
  let C : ℝ := ∑ k ∈ Finset.range (n + 1), |f k|
  have hC : 0 ≤ C := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  apply (integrable_const C).mono' measurable_from_top.aestronglyMeasurable
  filter_upwards [treeLaw_valid x n] with s hs
  rw [Real.norm_eq_abs]
  apply activeMean_bound hC
  intro v hv
  have hh : s.height v ≤ n := (hs.height_le_id v (hs.active_subset hv)).trans
    (hs.vertices_le v (hs.active_subset hv))
  exact Finset.single_le_sum (f := fun k => |f k|) (fun _ _ => abs_nonneg _)
    (Finset.mem_range.mpr (show s.height v < n + 1 by omega))

/-- Bochner integration through the actual forward transition. -/
theorem integral_treeLaw_succ (x : SignSequence) (n : ℕ) (f : ℕ → ℝ) :
    (∫ s', activeMean s' f ∂treeLaw x (n + 1)) =
      ∫ s, (∫ s', activeMean s' f ∂transitionLaw s (n + 1) (x (n + 1))) ∂treeLaw x n := by
  let K : ProbabilityTheory.Kernel State State := ⟨fun s => transitionLaw s (n + 1) (x (n + 1)),
    measurable_from_top⟩
  have hi := treeLaw_integrable_activeMean x (n + 1) f
  rw [treeLaw] at hi
  have hi' : Integrable (fun s => activeMean s f)
      ((K ∘ₖ ProbabilityTheory.Kernel.const Unit (treeLaw x n)) ()) := by
    simpa only [K, ProbabilityTheory.Kernel.coe_mk, ProbabilityTheory.Kernel.comp_apply, ProbabilityTheory.Kernel.const_apply] using hi
  have hh := ProbabilityTheory.Kernel.integral_comp hi'
  simpa only [K, treeLaw, ProbabilityTheory.Kernel.coe_mk, ProbabilityTheory.Kernel.comp_apply, ProbabilityTheory.Kernel.const_apply] using hh

/-- Exact recursion for the uniform active height, averaged over the random tree. -/
theorem treeLaw_activeMean_succ (x : SignSequence) (n : ℕ)
    (hτ : ((n + 1 : ℕ) : ℕ∞) < extinctionTime x) (f : ℕ → ℝ) :
    (∫ s, activeMean s f ∂treeLaw x (n + 1)) =
      if x (n + 1) then
        (1 - 1 / (activeCount x (n + 1) : ℝ)) * (∫ s, activeMean s f ∂treeLaw x n) +
        (1 / (activeCount x (n + 1) : ℝ)) *
          (∫ s, activeMean s (fun k => f (k + 1)) ∂treeLaw x n)
      else ∫ s, activeMean s f ∂treeLaw x n := by
  have hnτ : (n : ℕ∞) < extinctionTime x :=
    lt_trans (by exact_mod_cast Nat.lt_succ_self n) hτ
  rw [integral_treeLaw_succ]
  cases hx : x (n + 1)
  · simp only [Bool.false_eq_true, ↓reduceIte]
    apply integral_congr_ae
    filter_upwards [treeLaw_counts x n hnτ.le] with s hs
    have hpos := ((lt_extinctionTime_iff x (n + 1)).mp hτ) (n + 1) le_rfl
    rw [activeCount_succ, hx] at hpos
    have hc : 1 < s.active.card := by simp only [Bool.false_eq_true, ↓reduceIte] at hpos; omega
    exact transitionLaw_activeMean_freeze hc _ f
  · simp only [↓reduceIte]
    have hrec : ∀ᵐ s ∂treeLaw x n,
        (∫ s', activeMean s' f ∂transitionLaw s (n + 1) true) =
        (1 - 1 / (activeCount x (n + 1) : ℝ)) * activeMean s f +
        (1 / (activeCount x (n + 1) : ℝ)) * activeMean s (fun k => f (k + 1)) := by
      filter_upwards [treeLaw_valid x n, treeLaw_counts x n hnτ.le,
        treeLaw_active_nonempty x n hnτ] with s hs hc hne
      rw [transitionLaw_activeMean_attach hs hne f]
      have hcount : (activeCount x (n + 1) : ℝ) = s.active.card + 1 := by
        rw [activeCount_succ, hx]
        simp only [↓reduceIte, Int.cast_add, Int.cast_one, ← hc.1, Int.cast_natCast]
      rw [hcount]
      have hd : (s.active.card : ℝ) + 1 ≠ 0 := by positivity
      field_simp
      ring
    rw [integral_congr_ae hrec, integral_add]
    · rw [integral_const_mul, integral_const_mul]
    · exact (treeLaw_integrable_activeMean x n f).const_mul _
    · exact (treeLaw_integrable_activeMean x n (fun k => f (k + 1))).const_mul _

/-- Conditional law of a uniform active vertex height; zero is used only in absorbed states. -/
noncomputable def activeHeightKernel : ProbabilityTheory.Kernel State ℕ where
  toFun s := if s.active.Nonempty then (Measure.uniformOfFinset s.active).map s.height
    else Measure.dirac 0
  measurable' := measurable_from_top

instance activeHeightKernel_probability (s : State) : IsProbabilityMeasure (activeHeightKernel s) := by
  change IsProbabilityMeasure (if s.active.Nonempty then _ else _)
  split_ifs with h
  · have := uniform_active_probability s h
    infer_instance
  · infer_instance

/-- The height law for a vertex sampled uniformly among the active vertices of the random tree. -/
noncomputable def uniformActiveHeightLaw (x : SignSequence) (n : ℕ) : Measure ℕ :=
  (treeLaw x n).bind activeHeightKernel

instance uniformActiveHeightLaw_probability (x : SignSequence) (n : ℕ) :
    IsProbabilityMeasure (uniformActiveHeightLaw x n) :=
  isProbabilityMeasure_bind activeHeightKernel.measurable.aemeasurable
    (Filter.Eventually.of_forall activeHeightKernel_probability)

theorem activeHeightKernel_integral (s : State) (hs : s.active.Nonempty) (f : ℕ → ℝ) :
    (∫ k, f k ∂activeHeightKernel s) = activeMean s f := by
  change (∫ k, f k ∂(if s.active.Nonempty then _ else _)) = _
  rw [ite_eq_left hs, integral_map (by fun_prop) (by fun_prop), integral_uniform_active s hs]
  rfl

theorem activeHeightKernel_le {n : ℕ} {s : State} (hs : ValidAt n s) :
    activeHeightKernel s {k | k ≤ n} = 1 := by
  change (if s.active.Nonempty then (Measure.uniformOfFinset s.active).map s.height
    else Measure.dirac 0) {k | k ≤ n} = 1
  split_ifs with h
  · rw [Measure.map_apply (by fun_prop) (by measurability), Measure.uniformOfFinset_apply]
    have hf : s.active.filter (fun v => s.height v ≤ n) = s.active := by
      apply Finset.filter_eq_self.mpr
      intro v hv
      exact (hs.height_le_id v (hs.active_subset hv)).trans (hs.vertices_le v (hs.active_subset hv))
    simp only [Set.mem_preimage, Set.mem_ofPred_eq]
    rw [hf]
    exact ENNReal.div_self (by exact_mod_cast h.card_pos.ne') (by simp)
  · simp

theorem uniformActiveHeightLaw_le (x : SignSequence) (n : ℕ) :
    ∀ᵐ k ∂uniformActiveHeightLaw x n, k ≤ n := by
  apply (ae_iff_prob_eq_one (by measurability)).mpr
  rw [uniformActiveHeightLaw, Measure.bind_apply (by measurability) activeHeightKernel.measurable.aemeasurable]
  calc
    _ = ∫⁻ _s, (1 : ℝ≥0∞) ∂treeLaw x n := by
      apply lintegral_congr_ae
      filter_upwards [treeLaw_valid x n] with s hs using activeHeightKernel_le hs
    _ = 1 := by simp

theorem uniformActiveHeightLaw_integrable (x : SignSequence) (n : ℕ) (f : ℕ → ℝ) :
    Integrable f (uniformActiveHeightLaw x n) := by
  let C : ℝ := ∑ k ∈ Finset.range (n + 1), |f k|
  apply (integrable_const C).mono' (by fun_prop)
  filter_upwards [uniformActiveHeightLaw_le x n] with k hk
  rw [Real.norm_eq_abs]
  exact Finset.single_le_sum (f := fun k => |f k|) (fun _ _ => abs_nonneg _)
    (Finset.mem_range.mpr (by omega))

/-- The empirical active average is exactly integration against the sampled height law. -/
theorem uniformActiveHeightLaw_integral (x : SignSequence) (n : ℕ)
    (hτ : (n : ℕ∞) < extinctionTime x) (f : ℕ → ℝ) :
    (∫ k, f k ∂uniformActiveHeightLaw x n) = ∫ s, activeMean s f ∂treeLaw x n := by
  have hi := uniformActiveHeightLaw_integrable x n f
  unfold uniformActiveHeightLaw at hi ⊢
  have hi' : Integrable f ((activeHeightKernel ∘ₖ ProbabilityTheory.Kernel.const Unit (treeLaw x n)) ()) := by
    simpa only [ProbabilityTheory.Kernel.comp_apply, ProbabilityTheory.Kernel.const_apply] using hi
  have hh := ProbabilityTheory.Kernel.integral_comp hi'
  simp only [ProbabilityTheory.Kernel.comp_apply, ProbabilityTheory.Kernel.const_apply] at hh
  rw [hh]
  apply integral_congr_ae
  filter_upwards [treeLaw_active_nonempty x n hτ] with s hs using activeHeightKernel_integral s hs f

/-- Distributional recursion for the genuine uniform active vertex height in Algorithm 1. -/
theorem uniformActiveHeightLaw_integral_succ (x : SignSequence) (n : ℕ)
    (hτ : ((n + 1 : ℕ) : ℕ∞) < extinctionTime x) (f : ℕ → ℝ) :
    (∫ k, f k ∂uniformActiveHeightLaw x (n + 1)) =
      if x (n + 1) then
        (1 - 1 / (activeCount x (n + 1) : ℝ)) * (∫ k, f k ∂uniformActiveHeightLaw x n) +
        (1 / (activeCount x (n + 1) : ℝ)) *
          (∫ k, f (k + 1) ∂uniformActiveHeightLaw x n)
      else ∫ k, f k ∂uniformActiveHeightLaw x n := by
  have hnτ : (n : ℕ∞) < extinctionTime x :=
    lt_trans (by exact_mod_cast Nat.lt_succ_self n) hτ
  rw [uniformActiveHeightLaw_integral x (n + 1) hτ,
    treeLaw_activeMean_succ x n hτ, uniformActiveHeightLaw_integral x n hnτ,
    uniformActiveHeightLaw_integral x n hnτ]

/-- All exponential moments of the actual active-height law exist. -/
theorem uniformActiveHeightLaw_integrable_exp (x : SignSequence) (n : ℕ) (θ : ℝ) :
    Integrable (fun k : ℕ => Real.exp (θ * (k : ℝ))) (uniformActiveHeightLaw x n) :=
  uniformActiveHeightLaw_integrable x n _

/-- Sub-Poisson MGF bound for the genuine uniform active vertex height.
This is proved directly from Algorithm 1, without assuming a Bernoulli representation. -/
theorem uniformActiveHeightLaw_mgf_le (x : SignSequence) (n : ℕ)
    (hτ : (n : ℕ∞) < extinctionTime x) (θ : ℝ) :
    ProbabilityTheory.mgf (fun k : ℕ => (k : ℝ)) (uniformActiveHeightLaw x n) θ ≤
      Real.exp (heightScale x n * (Real.exp θ - 1)) := by
  change (∫ k : ℕ, Real.exp (θ * (k : ℝ)) ∂uniformActiveHeightLaw x n) ≤ _
  induction n with
  | zero =>
    rw [uniformActiveHeightLaw_integral x 0 hτ]
    simp [treeLaw, activeMean, activeSum, initial]
  | succ n ih =>
    have hnτ : (n : ℕ∞) < extinctionTime x :=
      lt_trans (by exact_mod_cast Nat.lt_succ_self n) hτ
    have ih := ih hnτ
    rw [uniformActiveHeightLaw_integral_succ x n hτ, heightScale_succ]
    cases hx : x (n + 1)
    · simp only [Bool.false_eq_true, ↓reduceIte, add_zero]
      exact ih
    · simp only [↓reduceIte]
      let p : ℝ := 1 / (activeCount x (n + 1) : ℝ)
      have hs : (1 : ℤ) ≤ activeCount x (n + 1) := by
        have := ((lt_extinctionTime_iff x (n + 1)).mp hτ) (n + 1) le_rfl
        omega
      have hsR : (1 : ℝ) ≤ activeCount x (n + 1) := by exact_mod_cast hs
      have hp0 : 0 ≤ p := by dsimp [p]; positivity
      have hp1 : p ≤ 1 := (div_le_one (by linarith)).mpr hsR
      have hfac : 0 ≤ 1 + p * (Real.exp θ - 1) := by
        have he := Real.exp_pos θ
        nlinarith
      have hshift : (∫ k : ℕ, Real.exp (θ * ((k + 1 : ℕ) : ℝ)) ∂uniformActiveHeightLaw x n) =
          Real.exp θ * (∫ k : ℕ, Real.exp (θ * (k : ℝ)) ∂uniformActiveHeightLaw x n) := by
        simp_rw [Nat.cast_add, Nat.cast_one, mul_add, mul_one, Real.exp_add, mul_comm _ (Real.exp θ)]
        exact integral_const_mul _ _
      rw [hshift]
      calc
        _ = (1 + p * (Real.exp θ - 1)) *
            (∫ k : ℕ, Real.exp (θ * (k : ℝ)) ∂uniformActiveHeightLaw x n) := by dsimp [p]; ring
        _ ≤ (1 + p * (Real.exp θ - 1)) * Real.exp (heightScale x n * (Real.exp θ - 1)) :=
          mul_le_mul_of_nonneg_left ih hfac
        _ ≤ Real.exp (p * (Real.exp θ - 1)) * Real.exp (heightScale x n * (Real.exp θ - 1)) := by
          apply mul_le_mul_of_nonneg_right
          · linarith [Real.add_one_le_exp (p * (Real.exp θ - 1))]
          · positivity
        _ = Real.exp ((heightScale x n + 1 / (activeCount x (n + 1) : ℝ)) * (Real.exp θ - 1)) := by
          rw [← Real.exp_add]
          congr 1
          dsimp [p]
          ring

end Freezing1.Forward
