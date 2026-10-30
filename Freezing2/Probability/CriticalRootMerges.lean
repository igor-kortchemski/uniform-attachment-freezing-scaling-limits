module

public import Freezing2.Probability.CriticalMergeAtoms

/-!
# Root mergers and early births in the critical limit

Three estimates for the limiting genealogy `criticalGenealogyLimit g k` of `k` uniform
vertices in the critical regime.

* If `∫₀ g² = ∞`, two distinct samples almost surely coalesce at a positive time. In the
  discrete model, two labels born after `β n` merge before `ε n` with probability at most
  the survival product over `(ε n, β n]`, which is bounded by the exponential of minus the
  hazard sum there, approximately `∫_ε^β g²`.
* Two samples born before `δ` merge at a positive time with probability at most
  `δ² ∫₀^δ g²`: a merger after `θ n` has probability at most the hazard sum over the window
  up to the smaller birth, and both births are below `δ n` with probability about `δ²`.
* All samples of a group are born after `δ` with probability at most `(1 - δ / 2) ^ card`.

Each bound is proved for the sampled discrete genealogies, retaining the collision
probability of the uniform samples, and is transferred to the limit with the
portmanteau theorem for open sets.
-/

@[expose] public section

open MeasureTheory Set Filter Topology

namespace Freezing2.CriticalGenealogy

open ReverseHistory ReverseCoalescence MeasuredGHSpace

/-- A bound on sections supported in a parameter set `A`, outside a bad parameter set `B`,
remains valid after independent sampling. -/
theorem measureReal_prod_event_le_bad_add_mul {Ω P : Type*} [MeasurableSpace Ω]
    [MeasurableSpace P] {μ : Measure Ω} {ν : Measure P} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {E : Set (Ω × P)} (hE : MeasurableSet E)
    {B A : Set P} (hB : MeasurableSet B) (hA : MeasurableSet A) {η : ℝ} (hη : 0 ≤ η)
    (hbound : ∀ᵐ p ∂ν, p ∉ B → μ.real {ω | (ω, p) ∈ E} ≤ A.indicator (fun _ ↦ η) p) :
    (μ.prod ν).real E ≤ ν.real B + ν.real A * η := by
  classical
  have hf : Integrable (fun p ↦ μ.real {ω | (ω, p) ∈ E}) ν := by
    have hi := ((integrable_const (1 : ℝ) : Integrable (fun _ : Ω × P ↦ (1 : ℝ))
      (μ.prod ν)).indicator hE).integral_prod_right
    simpa only [integral_indicator_section hE] using hi
  have hBint : Integrable (B.indicator (fun _ ↦ (1 : ℝ))) ν :=
    (integrable_const (1 : ℝ)).indicator hB
  have hAint : Integrable (A.indicator (fun _ ↦ η)) ν :=
    (integrable_const η).indicator hA
  rw [measureReal_prod_eq_integral_sections hE]
  calc
    _ ≤ ∫ p, B.indicator (fun _ ↦ (1 : ℝ)) p + A.indicator (fun _ ↦ η) p ∂ν := by
      apply integral_mono_ae hf (hBint.add hAint)
      filter_upwards [hbound] with p hp
      rw [Pi.add_apply]
      by_cases hmem : p ∈ B
      · rw [Set.indicator_of_mem hmem]
        have h1 := measureReal_le_one (μ := μ) (s := {ω | (ω, p) ∈ E})
        have h2 : 0 ≤ A.indicator (fun _ ↦ η) p := Set.indicator_nonneg (fun _ _ ↦ hη) p
        linarith
      · rw [Set.indicator_of_notMem hmem, zero_add]
        exact hp hmem
    _ = _ := by
      have hiB : (∫ p, B.indicator (fun _ ↦ (1 : ℝ)) p ∂ν) = ν.real B :=
        integral_indicator_one hB
      rw [integral_add hBint hAint, hiB, integral_indicator_const η hA, smul_eq_mul]

/-- An upper bound holding at every positive parameter passes to the parameter zero. -/
theorem le_ofReal_of_forall_pos {a : ENNReal} {f : ℝ → ℝ} (hf : Continuous f)
    (h : ∀ η : ℝ, 0 < η → a ≤ ENNReal.ofReal (f η)) : a ≤ ENNReal.ofReal (f 0) := by
  have ht : Tendsto (fun η ↦ ENNReal.ofReal (f η)) (𝓝[>] 0) (𝓝 (ENNReal.ofReal (f 0))) :=
    ((ENNReal.continuous_ofReal.comp hf).tendsto 0).mono_left nhdsWithin_le_nhds
  exact ge_of_tendsto ht (eventually_nhdsWithin_of_forall fun η hη ↦ h η hη)

/-- A liminf is at most the limit of eventual real upper bounds. -/
theorem liminf_le_ofReal_of_tendsto {m : ℕ → ENNReal} {u : ℕ → ℝ} {L : ℝ}
    (hm : ∀ᶠ n in atTop, m n ≤ ENNReal.ofReal (u n)) (hu : Tendsto u atTop (𝓝 L)) :
    liminf m atTop ≤ ENNReal.ofReal L :=
  (liminf_le_liminf hm).trans_eq ((ENNReal.continuous_ofReal.tendsto L).comp hu).liminf_eq

/-- Coalescence hazard sums inside the surviving horizon are nonnegative. -/
theorem coalescenceUpSum_nonneg_of_le (x : ℕ → ℤ) {n a m : ℕ} (hs : SurvivesThrough x n)
    (ham : a + m ≤ n) : 0 ≤ coalescenceUpSum x a m := by
  unfold coalescenceUpSum
  exact Finset.sum_nonneg fun i hi ↦
    coalescenceUpSum_term_nonneg x hs (by have := Finset.mem_range.mp hi; omega)

/-- Distinct labels both born at or after phase `b` merge before phase `a ≤ b` with
probability at most the exponential of minus the hazard sum over `(a, b]`. -/
theorem source_coalescence_lt_probability_le_exp (x : ℕ → ℤ) (hx : IsSigned x) {n : ℕ}
    (hs : SurvivesThrough x n) {u v : VertexLabel}
    (hu : u ∈ vertexLabels x n) (hv : v ∈ vertexLabels x n) (huv : u ≠ v) {a b : ℕ}
    (hab : a ≤ b) (hbu : b ≤ birthTime n u) (hbv : b ≤ birthTime n v) :
    (jointLaw (companionSchedule x) n).real {ω | sourceCoalescenceTime n u v ω < a} ≤
      Real.exp (-2 * coalescenceUpSum x a (b - a)) := by
  set m := min (birthTime n u) (birthTime n v) with hm_def
  have hbm : b ≤ m := le_min hbu hbv
  have hmn : m ≤ n := (min_le_left _ _).trans (birthTime_le x hu)
  have hne : toCompanionLabel u ≠ toCompanionLabel v := by
    intro h
    apply huv
    have he := congrArg fromCompanionLabel h
    simpa only [from_toCompanionLabel hu, from_toCompanionLabel hv] using he
  have ham : a ≤ commonBirth n (toCompanionLabel u) (toCompanionLabel v) := by
    simpa only [commonBirth, companion_birthTime] using hab.trans hbm
  have htail := coalescenceTime_lt_probability (companion_before_extinction x hx hs).le
    (toCompanionLabel_mem x hx hu) (toCompanionLabel_mem x hx hv) hne ham
  have htail' : (jointLaw (companionSchedule x) n).real
      {ω | sourceCoalescenceTime n u v ω < a} =
      ∏ j ∈ Finset.Ioc a m, (1 - coalescenceHazard (companionSchedule x) j) := by
    simpa only [sourceCoalescenceTime, commonBirth, companion_birthTime, m] using htail
  rw [htail', ← Finset.prod_Ioc_consecutive _ hab hbm]
  have h0 : ∀ j ∈ Finset.Ioc a m, 0 ≤ 1 - coalescenceHazard (companionSchedule x) j := by
    intro j hj
    have := Finset.mem_Ioc.mp hj
    exact sub_nonneg.mpr (companion_coalescenceHazard_le_one x hx hs (by omega) (by omega))
  have h1 : ∀ j ∈ Finset.Ioc a m, 1 - coalescenceHazard (companionSchedule x) j ≤ 1 := by
    intro j hj
    have := Finset.mem_Ioc.mp hj
    linarith [companion_coalescenceHazard_nonneg x hx hs (i := j) (by omega)]
  have hleft : 0 ≤ ∏ j ∈ Finset.Ioc a b, (1 - coalescenceHazard (companionSchedule x) j) :=
    Finset.prod_nonneg fun j hj ↦ h0 j (Finset.Ioc_subset_Ioc_right hbm hj)
  have hright : ∏ j ∈ Finset.Ioc b m, (1 - coalescenceHazard (companionSchedule x) j) ≤ 1 :=
    Finset.prod_le_one₀ (fun j hj ↦ h0 j (Finset.Ioc_subset_Ioc_left hab hj))
      (fun j hj ↦ h1 j (Finset.Ioc_subset_Ioc_left hab hj))
  have hexp := companion_survival_product_le_exp x hx hs (a := a) (m := b - a)
    (by omega : a + (b - a) ≤ n)
  rw [Nat.add_sub_of_le hab] at hexp
  calc _ ≤ ∏ j ∈ Finset.Ioc a b, (1 - coalescenceHazard (companionSchedule x) j) :=
        mul_le_of_le_one_right hleft hright
    _ ≤ _ := hexp

/-- Distinct labels with smaller birth at most `b` merge at or after phase `a ≤ b` with
probability at most twice the hazard sum over `(a, b]`. -/
theorem source_coalescence_ge_probability_le_window (x : ℕ → ℤ) (hx : IsSigned x) {n : ℕ}
    (hs : SurvivesThrough x n) {u v : VertexLabel}
    (hu : u ∈ vertexLabels x n) (hv : v ∈ vertexLabels x n) (huv : u ≠ v) {a b : ℕ}
    (hab : a ≤ b) (hbn : b ≤ n) (hmb : min (birthTime n u) (birthTime n v) ≤ b) :
    (jointLaw (companionSchedule x) n).real {ω | a ≤ sourceCoalescenceTime n u v ω} ≤
      2 * coalescenceUpSum x a (b - a) := by
  set m := min (birthTime n u) (birthTime n v) with hm_def
  have hnonneg : 0 ≤ coalescenceUpSum x a (b - a) :=
    coalescenceUpSum_nonneg_of_le x hs (by omega)
  by_cases ham : a ≤ m
  · refine (source_coalescence_ge_probability_le_sum x hx hs hu hv huv ham).trans ?_
    have hmono := coalescenceUpSum_mono_interval x hs (a := a) (m := b - a) (b := a)
      (k := m - a) (by omega) le_rfl (by omega)
    linarith
  · have hcoal (ω : History) : sourceCoalescenceTime n u v ω ≤ m := by
      simpa only [sourceCoalescenceTime, commonBirth, companion_birthTime, m] using
        coalescenceTime_le_commonBirth n (toCompanionLabel u) (toCompanionLabel v) ω
    have he : {ω | a ≤ sourceCoalescenceTime n u v ω} = ∅ := by
      ext ω
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_le]
      have := hcoal ω
      omega
    rw [he, measureReal_empty]
    linarith

section Limit

variable {xa : ℕ → ℕ → ℤ} {g : ℝ → ℝ} {k : ℕ}

/-- Twice the hazard sums over valid interior windows are eventually uniformly close to the
integrals of `g²`. -/
theorem eventually_twice_coalescenceUpSum_approx (hx : AdmissibleArray xa)
    (hL1 : HasL1ReciprocalProfile xa (1 / 2) g) (hpos : PositiveProfile g)
    (h2 : HasLocalSquareMomentProfile xa (1 / 2) g) {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) :
    ∀ᶠ n in atTop, ∀ a b : ℕ, CoalescenceInterval ε n a b →
      |2 * coalescenceUpSum (xa n) (a - 1) (b + 1 - a) -
        ∫ t in Icc ((a : ℝ) / n) ((b : ℝ) / n), g t ^ 2| < η := by
  have herr := tendsto_coalescenceIntervalErrorMax hx (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1) hL1 hpos h2 hε
  filter_upwards [herr.eventually (gt_mem_nhds (show (0 : ℝ) < η / 2 by positivity)),
    eventually_gt_atTop 0] with n hn hn0 a b hab
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn0
  have hle : coalescenceIntervalError xa (1 / 2) g n a b ≤
      coalescenceIntervalErrorMax xa (1 / 2) g ε n := by
    unfold coalescenceIntervalErrorMax
    have hmem : ((⟨a, by have := hab.2.1; have := hab.2.2.1; omega⟩ : Fin (n + 1)),
        (⟨b, by have := hab.2.2.1; omega⟩ : Fin (n + 1))) ∈ Finset.univ := Finset.mem_univ _
    refine le_trans ?_ (Finset.le_sup' _ hmem)
    simp only [hab, ↓reduceIte, le_refl]
  have hscale : ((n : ℝ) ^ (2 * (1 / 2 : ℝ)) / n) = 1 := by
    rw [show (2 : ℝ) * (1 / 2) = 1 by norm_num, Real.rpow_one, div_self hnr.ne']
  have herr' := hle.trans_lt hn
  unfold coalescenceIntervalError at herr'
  rw [hscale, one_mul, abs_lt] at herr'
  rw [abs_lt]
  constructor <;> linarith [herr'.1, herr'.2]

/-! ### No coalescence at time zero -/

/-- The two-sample event of an early merger of two late-born labels. -/
def earlyMergeEvent (n : ℕ) (ε β : ℝ) : Set (History × (VertexLabel × VertexLabel)) :=
  {q | (sourceCoalescenceTime n q.2.1 q.2.2 q.1 : ℝ) < ε * n ∧
    β * n < (birthTime n q.2.1 : ℝ) ∧ β * n < (birthTime n q.2.2 : ℝ)}

theorem measurableSet_earlyMergeEvent (n : ℕ) (ε β : ℝ) :
    MeasurableSet (earlyMergeEvent n ε β) := by
  apply measurable_from_prod_countable_left (fun p ↦ ?_) |>.setOf
  show Measurable fun ω : History ↦ (sourceCoalescenceTime n p.1 p.2 ω : ℝ) < ε * n ∧
    β * n < (birthTime n p.1 : ℝ) ∧ β * n < (birthTime n p.2 : ℝ)
  exact (((measurable_of_countable (fun c : ℕ ↦ (c : ℝ))).comp
    (measurable_sourceCoalescenceTime n p.1 p.2)).lt measurable_const).and
      (measurable_const.and measurable_const)

/-- Two samples born after `β` merge before `ε` with probability at most
`exp (-∫_{ε'}^{β'} g²)` in the limit, for `ε < ε' < β' < β`. -/
theorem criticalGenealogyLimit_early_coalescence_le (hx : AdmissibleArray xa)
    (hL1 : HasL1ReciprocalProfile xa (1 / 2) g) (hpos : PositiveProfile g)
    (h2 : HasLocalSquareMomentProfile xa (1 / 2) g) {i j : Fin k} (hij : i ≠ j)
    {ε ε' β' β : ℝ} (hε : 0 < ε) (hεε' : ε < ε') (hε'β' : ε' < β') (hβ'β : β' < β)
    (hβ : β < 1 / 2) :
    (criticalGenealogyLimit g k : Measure (GenealogySpace k))
      {z | z.2 i j < ε ∧ β < z.1 i ∧ β < z.1 j} ≤
        ENNReal.ofReal (Real.exp (-∫ t in Icc ε' β', g t ^ 2)) := by
  set I := ∫ t in Icc ε' β', g t ^ 2 with hI_def
  set O : Set (GenealogySpace k) := {z | z.2 i j < ε ∧ β < z.1 i ∧ β < z.1 j}
  have hO : IsOpen O := by
    have hbi : Continuous fun z : GenealogySpace k ↦ z.1 i :=
      (continuous_apply i).comp continuous_fst
    have hbj : Continuous fun z : GenealogySpace k ↦ z.1 j :=
      (continuous_apply j).comp continuous_fst
    have hc : Continuous fun z : GenealogySpace k ↦ z.2 i j :=
      (continuous_apply j).comp ((continuous_apply i).comp continuous_snd)
    exact (isOpen_lt hc continuous_const).inter ((isOpen_lt continuous_const hbi).inter
      (isOpen_lt continuous_const hbj))
  have hlim := ProbabilityMeasure.le_liminf_measure_open_of_tendsto
    (tendsto_genealogyLaw_criticalGenealogyLimit hx hL1 hpos h2 k) hO
  have hgint : IntegrableOn (fun t ↦ g t ^ 2) (Icc ε β) volume :=
    (h2 ε β hε (by linarith) (by linarith)).1
  have hcoll := tendsto_uniformVertex_collision hx (by norm_num : (1 / 2 : ℝ) < 1) hL1 hpos
  have key : ∀ η : ℝ, 0 < η → (criticalGenealogyLimit g k : Measure (GenealogySpace k)) O ≤
      ENNReal.ofReal (Real.exp (-(I - η))) := by
    intro η hη
    refine hlim.trans (liminf_le_ofReal_of_tendsto
      (u := fun n ↦ ((uniformVertex (xa n) n).prod (uniformVertex (xa n) n)).real
        {p | p.1 = p.2} + Real.exp (-(I - η))) ?_ (by simpa using hcoll.add_const _))
    have h2n := (tendsto_const_div_atTop_nhds_zero_nat (2 : ℝ)).eventually
      (gt_mem_nhds (sub_pos.mpr hεε'))
    have h1n := (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)).eventually
      (gt_mem_nhds (sub_pos.mpr hβ'β))
    filter_upwards [eventually_twice_coalescenceUpSum_approx hx hL1 hpos h2 (half_pos hε) hη,
      h2n, h1n, eventually_gt_atTop 0] with n happrox hn2 hn1 hn0
    have hnr : (0 : ℝ) < n := by exact_mod_cast hn0
    rw [div_lt_iff₀ hnr] at hn2 hn1
    set a := ⌈ε * n⌉₊ with ha_def
    set b := ⌊β * n⌋₊ with hb_def
    have ha_lt : (a : ℝ) < ε * n + 1 := Nat.ceil_lt_add_one (by positivity)
    have hb_le : (b : ℝ) ≤ β * n := Nat.floor_le (mul_pos (by linarith) hnr).le
    have hb_gt : β * n - 1 < b := by have := Nat.lt_floor_add_one (β * n); linarith
    have hεβn : ε' * n < β' * n := mul_lt_mul_of_pos_right hε'β' hnr
    have hab1 : a + 1 ≤ b := by
      have : (a : ℝ) + 1 ≤ b := by nlinarith
      exact_mod_cast this
    have hval : CoalescenceInterval (ε / 2) n (a + 1) b := by
      refine ⟨by omega, hab1, ?_, ?_, ?_⟩
      · have : (b : ℝ) ≤ n := by nlinarith
        exact_mod_cast this
      · have : ε * n ≤ a := Nat.le_ceil _
        push_cast
        nlinarith
      · nlinarith
    have happ := happrox (a + 1) b hval
    simp only [Nat.add_sub_cancel, Nat.add_sub_add_right] at happ
    have hsub : Icc ε' β' ⊆ Icc (((a + 1 : ℕ) : ℝ) / n) ((b : ℝ) / n) := by
      apply Icc_subset_Icc
      · rw [div_le_iff₀ hnr]
        push_cast
        linarith
      · rw [le_div_iff₀ hnr]
        linarith
    have hint_le : I ≤ ∫ t in Icc (((a + 1 : ℕ) : ℝ) / n) ((b : ℝ) / n), g t ^ 2 := by
      apply setIntegral_mono_set
      · apply hgint.mono_set
        apply Icc_subset_Icc
        · rw [le_div_iff₀ hnr]
          push_cast
          have : ε * n ≤ a := Nat.le_ceil _
          linarith
        · rw [div_le_iff₀ hnr]
          exact hb_le
      · exact Eventually.of_forall fun t ↦ sq_nonneg (g t)
      · exact Eventually.of_forall fun _ ht ↦ hsub ht
    have hsum : I - η < 2 * coalescenceUpSum (xa n) a (b - a) := by
      rw [abs_lt] at happ
      linarith [happ.1]
    have hbound : Real.exp (-2 * coalescenceUpSum (xa n) a (b - a)) ≤ Real.exp (-(I - η)) :=
      Real.exp_le_exp.mpr (by linarith)
    have hmem : ∀ᵐ p ∂(uniformVertex (xa n) n).prod (uniformVertex (xa n) n),
        p.1 ∈ vertexLabels (xa n) n ∧ p.2 ∈ vertexLabels (xa n) n := by
      let := uniformVertex_isProbabilityMeasure (xa n) (hx n).1 ((hx n).2 n le_rfl).le
      apply (Measure.ae_prod_iff_ae_ae (by exact (Set.to_countable _).measurableSet)).mpr
      filter_upwards [uniformVertex_mem (xa n) (hx n).1 ((hx n).2 n le_rfl).le] with u hu
      exact (uniformVertex_mem (xa n) (hx n).1 ((hx n).2 n le_rfl).le).mono fun v hv ↦ ⟨hu, hv⟩
    have hsections : ∀ᵐ p ∂(uniformVertex (xa n) n).prod (uniformVertex (xa n) n),
        p ∉ {p : VertexLabel × VertexLabel | p.1 = p.2} →
          (jointLaw (companionSchedule (xa n)) n).real
            {ω | (ω, p) ∈ earlyMergeEvent n ε β} ≤ Real.exp (-(I - η)) := by
      filter_upwards [hmem] with p hp hnot
      have hne : p.1 ≠ p.2 := fun h ↦ hnot h
      by_cases hb : β * n < (birthTime n p.1 : ℝ) ∧ β * n < (birthTime n p.2 : ℝ)
      · have hb1 : b ≤ birthTime n p.1 := by
          have : (b : ℝ) ≤ birthTime n p.1 := hb_le.trans hb.1.le
          exact_mod_cast this
        have hb2 : b ≤ birthTime n p.2 := by
          have : (b : ℝ) ≤ birthTime n p.2 := hb_le.trans hb.2.le
          exact_mod_cast this
        refine (measureReal_mono (s₂ := {ω | sourceCoalescenceTime n p.1 p.2 ω < a})
          (fun ω hω ↦ ?_)).trans ((source_coalescence_lt_probability_le_exp (xa n) (hx n).1
            (hx n).2 hp.1 hp.2 hne (by omega) hb1 hb2).trans hbound)
        exact Nat.lt_ceil.mpr hω.1
      · have he : {ω | (ω, p) ∈ earlyMergeEvent n ε β} = ∅ := by
          ext ω
          simp only [earlyMergeEvent, mem_ofPred_eq, mem_empty_iff_false, iff_false]
          exact fun h ↦ hb ⟨h.2.1, h.2.2⟩
        rw [he, measureReal_empty]
        positivity
    let := uniformVertex_isProbabilityMeasure (xa n) (hx n).1 ((hx n).2 n le_rfl).le
    have hprod := measureReal_prod_event_le_bad_add
      (μ := jointLaw (companionSchedule (xa n)) n)
      (ν := (uniformVertex (xa n) n).prod (uniformVertex (xa n) n))
      (E := earlyMergeEvent n ε β) (B := {p : VertexLabel × VertexLabel | p.1 = p.2})
      (measurableSet_earlyMergeEvent n ε β)
      (show MeasurableSet {p : VertexLabel × VertexLabel | p.1 = p.2} from
        (Set.to_countable _).measurableSet) (Real.exp_pos _).le hsections
    have heq := genealogyLaw_real_pair hx n hij hO.measurableSet
      (measurableSet_earlyMergeEvent n ε β) (by
        ext q
        simp only [mem_preimage, genealogyVector, O, earlyMergeEvent, mem_ofPred_eq]
        rw [div_lt_iff₀ hnr, lt_div_iff₀ hnr, lt_div_iff₀ hnr])
    rw [← ENNReal.ofReal_toReal (measure_ne_top _ O), ← measureReal_def, heq]
    exact ENNReal.ofReal_le_ofReal hprod
  have := le_ofReal_of_forall_pos (f := fun η ↦ Real.exp (-(I - η))) (by fun_prop) key
  simpa only [sub_zero] using this

/-- If `∫₀ g² = ∞`, then `∫_a^b g²` is arbitrarily large for small `a > 0`. -/
theorem exists_large_setIntegral_sq (h2 : HasLocalSquareMomentProfile xa (1 / 2) g)
    (hinf : ∫⁻ t in Ioc 0 (1 / 2), ENNReal.ofReal (g t ^ 2) = ⊤) {b : ℝ} (hb0 : 0 < b)
    (hb : b < 1 / 2) (M : ℝ) :
    ∃ a, 0 < a ∧ a < b ∧ M ≤ ∫ t in Icc a b, g t ^ 2 := by
  set F : ℝ → ENNReal := fun t ↦ ENNReal.ofReal (g t ^ 2) with hF_def
  have hsplit : ∫⁻ t in Ioc 0 (1 / 2), F t ≤
      (∫⁻ t in Ioc 0 b, F t) + ∫⁻ t in Icc b (1 / 2), F t :=
    calc _ ≤ ∫⁻ t in Ioc 0 b ∪ Icc b (1 / 2), F t := by
          apply lintegral_mono_set
          intro t ht
          rcases le_or_gt t b with htb | htb
          · exact Or.inl ⟨ht.1, htb⟩
          · exact Or.inr ⟨htb.le, ht.2⟩
      _ ≤ _ := lintegral_union_le _ _ _
  have hfin : ∫⁻ t in Icc b (1 / 2), F t < ⊤ :=
    (h2 b (1 / 2) hb0 hb (by norm_num)).1.setLIntegral_lt_top
  have htop : ∫⁻ t in Ioc 0 b, F t = ⊤ := by
    by_contra hne
    have hlt := ENNReal.add_lt_top.mpr ⟨lt_top_iff_ne_top.mpr hne, hfin⟩
    rw [hinf, top_le_iff] at hsplit
    exact hlt.ne hsplit
  set s : ℕ → Set ℝ := fun m ↦ Icc (b / ((m : ℝ) + 2)) b with hs_def
  have hmono : Monotone s := by
    intro m m' hmm' t ht
    refine ⟨le_trans ?_ ht.1, ht.2⟩
    have : (m : ℝ) ≤ m' := by exact_mod_cast hmm'
    exact div_le_div_of_nonneg_left hb0.le (by positivity) (by linarith)
  have hU : Ioc 0 b ⊆ ⋃ m, s m := by
    intro t ht
    obtain ⟨m, hm⟩ := exists_nat_one_div_lt (div_pos ht.1 hb0)
    rw [lt_div_iff₀ hb0] at hm
    refine mem_iUnion.mpr ⟨m, ?_, ht.2⟩
    calc b / ((m : ℝ) + 2) ≤ b / ((m : ℝ) + 1) :=
          div_le_div_of_nonneg_left hb0.le (by positivity) (by linarith)
      _ = 1 / ((m : ℝ) + 1) * b := by ring
      _ ≤ t := hm.le
  set ν := volume.withDensity F with hν_def
  have hν : ∀ t : Set ℝ, MeasurableSet t → ν t = ∫⁻ x in t, F x :=
    fun t ht ↦ withDensity_apply F ht
  have hsup : ⨆ m, ν (s m) = ⊤ := by
    rw [← hmono.measure_iUnion, ← top_le_iff, ← htop, ← hν _ measurableSet_Ioc]
    exact measure_mono hU
  obtain ⟨m, hm⟩ := (iSup_eq_top.mp hsup) (ENNReal.ofReal M) ENNReal.ofReal_lt_top
  have hpos2 : (0 : ℝ) < (m : ℝ) + 2 := by positivity
  have ha0 : 0 < b / ((m : ℝ) + 2) := by positivity
  have hab : b / ((m : ℝ) + 2) < b := div_lt_self hb0 (by linarith [(m.cast_nonneg : (0 : ℝ) ≤ m)])
  refine ⟨b / ((m : ℝ) + 2), ha0, hab, ?_⟩
  have hint : IntegrableOn (fun t ↦ g t ^ 2) (Icc (b / ((m : ℝ) + 2)) b) volume :=
    (h2 _ _ ha0 hab (by linarith)).1
  rw [hν _ measurableSet_Icc, hF_def,
    ← ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun t ↦ sq_nonneg (g t))]
    at hm
  exact (ENNReal.ofReal_lt_ofReal_iff'.mp hm).1.le

/-- **No coalescence at time zero when `∫₀ g² = ∞`.** Two distinct samples almost surely
coalesce at a positive time. -/
theorem criticalGenealogyLimit_coalescence_nonpos_null (hx : AdmissibleArray xa)
    (hL1 : HasL1ReciprocalProfile xa (1 / 2) g) (hpos : PositiveProfile g)
    (h2 : HasLocalSquareMomentProfile xa (1 / 2) g)
    (hinf : ∫⁻ t in Ioc 0 (1 / 2), ENNReal.ofReal (g t ^ 2) = ⊤) {i j : Fin k} (hij : i ≠ j) :
    (criticalGenealogyLimit g k : Measure (GenealogySpace k)) {z | z.2 i j ≤ 0} = 0 := by
  set μ := (criticalGenealogyLimit g k : Measure (GenealogySpace k))
  apply le_antisymm _ bot_le
  apply ENNReal.le_of_forall_pos_le_add
  intro η hη _
  rw [bot_eq_zero, zero_add]
  have hη' : (0 : ℝ) < η := by exact_mod_cast hη
  set β := min ((η : ℝ) / 8) (1 / 4) with hβ_def
  have hβ0 : 0 < β := lt_min (by positivity) (by norm_num)
  have hβ8 : β ≤ η / 8 := min_le_left _ _
  have hβ4 : β ≤ 1 / 4 := min_le_right _ _
  obtain ⟨ε', hε'0, hε'β, hM⟩ :=
    exists_large_setIntegral_sq h2 hinf (b := β / 2) (by positivity) (by linarith) (2 / η)
  have hO := criticalGenealogyLimit_early_coalescence_le hx hL1 hpos h2 hij
    (ε := ε' / 2) (ε' := ε') (β' := β / 2) (β := β) (by positivity) (by linarith) hε'β
    (by linarith) (by linarith)
  have hbi := criticalGenealogyLimit_birth_lt_le hx hL1 hpos h2 hij (θ := 2 * β)
    (by positivity) (by linarith)
  have hbj := criticalGenealogyLimit_birth_lt_le hx hL1 hpos h2 hij.symm (θ := 2 * β)
    (by positivity) (by linarith)
  have hsub : {z : GenealogySpace k | z.2 i j ≤ 0} ⊆
      {z | z.2 i j < ε' / 2 ∧ β < z.1 i ∧ β < z.1 j} ∪ {z | z.1 i < 2 * β} ∪
        {z | z.1 j < 2 * β} := by
    intro z hz
    have hz' : z.2 i j ≤ 0 := hz
    by_cases h1 : z.1 i < 2 * β
    · exact Or.inl (Or.inr h1)
    by_cases h3 : z.1 j < 2 * β
    · exact Or.inr h3
    push Not at h1 h3
    exact Or.inl (Or.inl ⟨by linarith, by linarith, by linarith⟩)
  set I := ∫ t in Icc ε' (β / 2), g t ^ 2 with hI_def
  have hIpos : 0 < I := lt_of_lt_of_le (by positivity) hM
  have hexp : Real.exp (-I) ≤ η / 2 := by
    rw [Real.exp_neg]
    have h1 : I + 1 ≤ Real.exp I := Real.add_one_le_exp I
    have h2' : 2 ≤ I * η := (div_le_iff₀ hη').mp hM
    rw [inv_le_iff_one_le_mul₀ (Real.exp_pos I)]
    nlinarith
  calc μ {z | z.2 i j ≤ 0}
      ≤ μ ({z | z.2 i j < ε' / 2 ∧ β < z.1 i ∧ β < z.1 j} ∪ {z | z.1 i < 2 * β} ∪
        {z | z.1 j < 2 * β}) := measure_mono hsub
    _ ≤ μ {z | z.2 i j < ε' / 2 ∧ β < z.1 i ∧ β < z.1 j} + μ {z | z.1 i < 2 * β} +
        μ {z | z.1 j < 2 * β} :=
      (measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)
    _ ≤ ENNReal.ofReal (η / 2) + ENNReal.ofReal (η / 4) + ENNReal.ofReal (η / 4) := by
      gcongr
      · exact hO.trans (ENNReal.ofReal_le_ofReal hexp)
      · exact hbi.trans (ENNReal.ofReal_le_ofReal (by linarith))
      · exact hbj.trans (ENNReal.ofReal_le_ofReal (by linarith))
    _ = η := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity),
        ← ENNReal.ofReal_add (by positivity) (by positivity),
        show (η : ℝ) / 2 + η / 4 + η / 4 = η by ring, ENNReal.ofReal_coe_nnreal]

/-! ### Mergers of two early-born samples -/

/-- The two-sample event of a late merger of two early-born labels. -/
def lateMergeEvent (n : ℕ) (θ δ : ℝ) : Set (History × (VertexLabel × VertexLabel)) :=
  {q | (birthTime n q.2.1 : ℝ) < δ * n ∧ (birthTime n q.2.2 : ℝ) < δ * n ∧
    θ * n < (sourceCoalescenceTime n q.2.1 q.2.2 q.1 : ℝ)}

theorem measurableSet_lateMergeEvent (n : ℕ) (θ δ : ℝ) :
    MeasurableSet (lateMergeEvent n θ δ) := by
  apply measurable_from_prod_countable_left (fun p ↦ ?_) |>.setOf
  show Measurable fun ω : History ↦ (birthTime n p.1 : ℝ) < δ * n ∧
    (birthTime n p.2 : ℝ) < δ * n ∧ θ * n < (sourceCoalescenceTime n p.1 p.2 ω : ℝ)
  exact measurable_const.and (measurable_const.and (measurable_const.lt
    ((measurable_of_countable (fun c : ℕ ↦ (c : ℝ))).comp
      (measurable_sourceCoalescenceTime n p.1 p.2))))

/-- Two samples born before `δ` merge after `θ` with probability at most
`δ² ∫_θ^δ g²` in the limit. -/
theorem criticalGenealogyLimit_late_merge_le (hx : AdmissibleArray xa)
    (hL1 : HasL1ReciprocalProfile xa (1 / 2) g) (hpos : PositiveProfile g)
    (h2 : HasLocalSquareMomentProfile xa (1 / 2) g) {i j : Fin k} (hij : i ≠ j)
    {θ δ : ℝ} (hθ : 0 < θ) (hθδ : θ < δ) (hδ : δ < 1 / 2) :
    (criticalGenealogyLimit g k : Measure (GenealogySpace k))
      {z | z.1 i < δ ∧ z.1 j < δ ∧ θ < z.2 i j} ≤
        ENNReal.ofReal (δ ^ 2 * ∫ t in Icc θ δ, g t ^ 2) := by
  set I := ∫ t in Icc θ δ, g t ^ 2 with hI_def
  set O : Set (GenealogySpace k) := {z | z.1 i < δ ∧ z.1 j < δ ∧ θ < z.2 i j}
  have hO : IsOpen O := by
    have hbi : Continuous fun z : GenealogySpace k ↦ z.1 i :=
      (continuous_apply i).comp continuous_fst
    have hbj : Continuous fun z : GenealogySpace k ↦ z.1 j :=
      (continuous_apply j).comp continuous_fst
    have hc : Continuous fun z : GenealogySpace k ↦ z.2 i j :=
      (continuous_apply j).comp ((continuous_apply i).comp continuous_snd)
    exact (isOpen_lt hbi continuous_const).inter ((isOpen_lt hbj continuous_const).inter
      (isOpen_lt continuous_const hc))
  have hlim := ProbabilityMeasure.le_liminf_measure_open_of_tendsto
    (tendsto_genealogyLaw_criticalGenealogyLimit hx hL1 hpos h2 k) hO
  have hgint : IntegrableOn (fun t ↦ g t ^ 2) (Icc θ δ) volume :=
    (h2 θ δ hθ hθδ (by linarith)).1
  have hI0 : 0 ≤ I := setIntegral_nonneg measurableSet_Icc fun t _ ↦ sq_nonneg (g t)
  have hcoll := tendsto_uniformVertex_collision hx (by norm_num : (1 / 2 : ℝ) < 1) hL1 hpos
  have hlate := tendsto_lateBirthProbability hx (by norm_num : (1 / 2 : ℝ) < 1) hL1 hpos
    (r := δ) (by linarith) (by linarith)
  have key : ∀ η : ℝ, 0 < η → (criticalGenealogyLimit g k : Measure (GenealogySpace k)) O ≤
      ENNReal.ofReal (δ ^ 2 * (I + η)) := by
    intro η hη
    have hu : Tendsto (fun n ↦ ((uniformVertex (xa n) n).prod (uniformVertex (xa n) n)).real
        {p | p.1 = p.2} + (1 - lateBirthProbability (xa n) n δ) ^ 2 * (I + η)) atTop
        (𝓝 (δ ^ 2 * (I + η))) := by
      have h1 : Tendsto (fun n ↦ 1 - lateBirthProbability (xa n) n δ) atTop (𝓝 δ) := by
        have := (tendsto_const_nhds (x := (1 : ℝ))).sub hlate
        rwa [sub_sub_cancel] at this
      have := hcoll.add ((h1.pow 2).mul_const (I + η))
      rwa [zero_add] at this
    refine hlim.trans (liminf_le_ofReal_of_tendsto ?_ hu)
    have h3n := (tendsto_const_div_atTop_nhds_zero_nat (3 : ℝ)).eventually
      (gt_mem_nhds (sub_pos.mpr hθδ))
    filter_upwards [eventually_twice_coalescenceUpSum_approx hx hL1 hpos h2 (half_pos hθ) hη,
      h3n, eventually_gt_atTop 0] with n happrox hn3 hn0
    have hnr : (0 : ℝ) < n := by exact_mod_cast hn0
    rw [div_lt_iff₀ hnr] at hn3
    set a := ⌊θ * n⌋₊ + 1 with ha_def
    set b := ⌊δ * n⌋₊ with hb_def
    have ha_gt : θ * n < (a : ℝ) := by
      simp only [a]
      push_cast
      exact Nat.lt_floor_add_one _
    have ha_le : (a : ℝ) ≤ θ * n + 1 := by
      simp only [a]
      push_cast
      linarith [Nat.floor_le (show 0 ≤ θ * n by positivity)]
    have hb_le : (b : ℝ) ≤ δ * n := Nat.floor_le (mul_pos (by linarith) hnr).le
    have hb_gt : δ * n - 1 < b := by have := Nat.lt_floor_add_one (δ * n); linarith
    have hab1 : a + 1 ≤ b := by
      have : (a : ℝ) + 1 ≤ b := by nlinarith
      exact_mod_cast this
    have hbn : b ≤ n := by
      have : (b : ℝ) ≤ n := by nlinarith
      exact_mod_cast this
    have hval : CoalescenceInterval (θ / 2) n (a + 1) b := by
      refine ⟨by omega, hab1, hbn, ?_, ?_⟩
      · push_cast
        nlinarith
      · nlinarith
    have happ := happrox (a + 1) b hval
    simp only [Nat.add_sub_cancel, Nat.add_sub_add_right] at happ
    have hint_le : ∫ t in Icc (((a + 1 : ℕ) : ℝ) / n) ((b : ℝ) / n), g t ^ 2 ≤ I := by
      apply setIntegral_mono_set hgint
      · exact Eventually.of_forall fun t ↦ sq_nonneg (g t)
      · have hsub2 : Icc (((a + 1 : ℕ) : ℝ) / n) ((b : ℝ) / n) ⊆ Icc θ δ := by
          apply Icc_subset_Icc
          · rw [le_div_iff₀ hnr]
            push_cast
            linarith
          · rw [div_le_iff₀ hnr]
            exact hb_le
        exact Eventually.of_forall fun _ ht ↦ hsub2 ht
    have hsum : 2 * coalescenceUpSum (xa n) a (b - a) ≤ I + η := by
      rw [abs_lt] at happ
      linarith [happ.2]
    have hmem : ∀ᵐ p ∂(uniformVertex (xa n) n).prod (uniformVertex (xa n) n),
        p.1 ∈ vertexLabels (xa n) n ∧ p.2 ∈ vertexLabels (xa n) n := by
      let := uniformVertex_isProbabilityMeasure (xa n) (hx n).1 ((hx n).2 n le_rfl).le
      apply (Measure.ae_prod_iff_ae_ae (by exact (Set.to_countable _).measurableSet)).mpr
      filter_upwards [uniformVertex_mem (xa n) (hx n).1 ((hx n).2 n le_rfl).le] with u hu
      exact (uniformVertex_mem (xa n) (hx n).1 ((hx n).2 n le_rfl).le).mono fun v hv ↦ ⟨hu, hv⟩
    set A : Set (VertexLabel × VertexLabel) :=
      {p | (birthTime n p.1 : ℝ) < δ * n ∧ (birthTime n p.2 : ℝ) < δ * n} with hA_def
    have hsections : ∀ᵐ p ∂(uniformVertex (xa n) n).prod (uniformVertex (xa n) n),
        p ∉ {p : VertexLabel × VertexLabel | p.1 = p.2} →
          (jointLaw (companionSchedule (xa n)) n).real
            {ω | (ω, p) ∈ lateMergeEvent n θ δ} ≤ A.indicator (fun _ ↦ I + η) p := by
      filter_upwards [hmem] with p hp hnot
      have hne : p.1 ≠ p.2 := fun h ↦ hnot h
      by_cases hpA : p ∈ A
      · rw [Set.indicator_of_mem hpA]
        have hb1 : birthTime n p.1 ≤ b := Nat.le_floor hpA.1.le
        refine (measureReal_mono (s₂ := {ω | a ≤ sourceCoalescenceTime n p.1 p.2 ω})
          (fun ω hω ↦ ?_)).trans ((source_coalescence_ge_probability_le_window (xa n) (hx n).1
            (hx n).2 hp.1 hp.2 hne (by omega) hbn ((min_le_left _ _).trans hb1)).trans hsum)
        have hc : θ * n < (sourceCoalescenceTime n p.1 p.2 ω : ℝ) := hω.2.2
        have := (Nat.floor_lt (show 0 ≤ θ * n by positivity)).mpr hc
        show ⌊θ * n⌋₊ + 1 ≤ sourceCoalescenceTime n p.1 p.2 ω
        omega
      · rw [Set.indicator_of_notMem hpA]
        have he : {ω | (ω, p) ∈ lateMergeEvent n θ δ} = ∅ := by
          ext ω
          simp only [lateMergeEvent, mem_ofPred_eq, mem_empty_iff_false, iff_false]
          exact fun h ↦ hpA ⟨h.1, h.2.1⟩
        rw [he, measureReal_empty]
    let := uniformVertex_isProbabilityMeasure (xa n) (hx n).1 ((hx n).2 n le_rfl).le
    have hAmeas : MeasurableSet A := (Set.to_countable _).measurableSet
    have hprod := measureReal_prod_event_le_bad_add_mul
      (μ := jointLaw (companionSchedule (xa n)) n)
      (ν := (uniformVertex (xa n) n).prod (uniformVertex (xa n) n))
      (E := lateMergeEvent n θ δ) (B := {p : VertexLabel × VertexLabel | p.1 = p.2})
      (measurableSet_lateMergeEvent n θ δ)
      (show MeasurableSet {p : VertexLabel × VertexLabel | p.1 = p.2} from
        (Set.to_countable _).measurableSet) hAmeas (by linarith) hsections
    have hAreal : ((uniformVertex (xa n) n).prod (uniformVertex (xa n) n)).real A ≤
        (1 - lateBirthProbability (xa n) n δ) ^ 2 := by
      have hAeq : A = {v : VertexLabel | (birthTime n v : ℝ) < δ * n} ×ˢ
          {v : VertexLabel | (birthTime n v : ℝ) < δ * n} := by
        ext p
        simp [A]
      have hS : (uniformVertex (xa n) n).real {v : VertexLabel | (birthTime n v : ℝ) < δ * n} ≤
          1 - lateBirthProbability (xa n) n δ := by
        unfold lateBirthProbability
        have hc : {v : VertexLabel | (birthTime n v : ℝ) < δ * n} ⊆
            {v | δ * n < (birthTime n v : ℝ)}ᶜ :=
          fun v (hv : (birthTime n v : ℝ) < δ * n) (h : δ * n < (birthTime n v : ℝ)) ↦
            lt_asymm hv h
        rw [← probReal_compl_eq_one_sub (by exact (measurable_of_countable _).setOf)]
        exact measureReal_mono hc
      rw [hAeq, measureReal_prod_prod, sq]
      exact mul_self_le_mul_self measureReal_nonneg hS
    have heq := genealogyLaw_real_pair hx n hij hO.measurableSet
      (measurableSet_lateMergeEvent n θ δ) (by
        ext q
        simp only [mem_preimage, genealogyVector, O, lateMergeEvent, mem_ofPred_eq]
        rw [div_lt_iff₀ hnr, div_lt_iff₀ hnr, lt_div_iff₀ hnr])
    rw [← ENNReal.ofReal_toReal (measure_ne_top _ O), ← measureReal_def, heq]
    apply ENNReal.ofReal_le_ofReal
    refine hprod.trans (add_le_add le_rfl ?_)
    exact mul_le_mul_of_nonneg_right hAreal (by linarith)
  have := le_ofReal_of_forall_pos (f := fun η ↦ δ ^ 2 * (I + η)) (by fun_prop) key
  simpa only [add_zero] using this

/-- Two samples born before `δ` merge at a positive time with probability at most
`δ² ∫₀^δ g²`. -/
theorem criticalGenealogyLimit_early_merge_le (hx : AdmissibleArray xa)
    (hL1 : HasL1ReciprocalProfile xa (1 / 2) g) (hpos : PositiveProfile g)
    (h2 : HasLocalSquareMomentProfile xa (1 / 2) g)
    {i j : Fin k} (hij : i ≠ j) {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ < 1 / 2) :
    (criticalGenealogyLimit g k : Measure (GenealogySpace k))
      {z | z.1 i < δ ∧ z.1 j < δ ∧ 0 < z.2 i j} ≤
        ENNReal.ofReal (δ ^ 2) * ∫⁻ t in Ioc 0 δ, ENNReal.ofReal (g t ^ 2) := by
  set μ := (criticalGenealogyLimit g k : Measure (GenealogySpace k))
  set O : ℕ → Set (GenealogySpace k) :=
    fun m ↦ {z | z.1 i < δ ∧ z.1 j < δ ∧ δ / ((m : ℝ) + 2) < z.2 i j} with hO_def
  have hθ0 : ∀ m : ℕ, 0 < δ / ((m : ℝ) + 2) := fun m ↦ by positivity
  have hθδ : ∀ m : ℕ, δ / ((m : ℝ) + 2) < δ := fun m ↦
    div_lt_self hδ0 (by linarith [(m.cast_nonneg : (0 : ℝ) ≤ m)])
  have hmono : Monotone O := by
    intro m m' hmm' z hz
    refine ⟨hz.1, hz.2.1, lt_of_le_of_lt ?_ hz.2.2⟩
    have : (m : ℝ) ≤ m' := by exact_mod_cast hmm'
    exact div_le_div_of_nonneg_left hδ0.le (by positivity) (by linarith)
  have hsub : {z : GenealogySpace k | z.1 i < δ ∧ z.1 j < δ ∧ 0 < z.2 i j} ⊆ ⋃ m, O m := by
    intro z hz
    obtain ⟨m, hm⟩ := exists_nat_one_div_lt (div_pos hz.2.2 hδ0)
    rw [lt_div_iff₀ hδ0] at hm
    refine mem_iUnion.mpr ⟨m, hz.1, hz.2.1, ?_⟩
    calc δ / ((m : ℝ) + 2) ≤ δ / ((m : ℝ) + 1) :=
          div_le_div_of_nonneg_left hδ0.le (by positivity) (by linarith)
      _ = 1 / ((m : ℝ) + 1) * δ := by ring
      _ < z.2 i j := hm
  have hbound : ∀ m, μ (O m) ≤
      ENNReal.ofReal (δ ^ 2) * ∫⁻ t in Ioc 0 δ, ENNReal.ofReal (g t ^ 2) := by
    intro m
    refine (criticalGenealogyLimit_late_merge_le hx hL1 hpos h2 hij (hθ0 m) (hθδ m) hδ).trans ?_
    have hint := (h2 (δ / ((m : ℝ) + 2)) δ (hθ0 m) (hθδ m) (by linarith)).1
    rw [ENNReal.ofReal_mul (sq_nonneg δ),
      ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun t ↦ sq_nonneg (g t))]
    exact mul_le_mul' le_rfl (lintegral_mono_set (Icc_subset_Ioc (hθ0 m) le_rfl))
  calc μ {z | z.1 i < δ ∧ z.1 j < δ ∧ 0 < z.2 i j} ≤ μ (⋃ m, O m) := measure_mono hsub
    _ = ⨆ m, μ (O m) := hmono.measure_iUnion
    _ ≤ _ := iSup_le hbound

/-! ### Late births of a group of samples -/

/-- All samples of a group are born after `δ` with probability at most
`(1 - δ / 2) ^ card`. -/
theorem criticalGenealogyLimit_births_ge_le (hx : AdmissibleArray xa)
    (hL1 : HasL1ReciprocalProfile xa (1 / 2) g) (hpos : PositiveProfile g)
    (h2 : HasLocalSquareMomentProfile xa (1 / 2) g)
    (S : Finset (Fin k)) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    (criticalGenealogyLimit g k : Measure (GenealogySpace k)) {z | ∀ i ∈ S, δ ≤ z.1 i} ≤
      ENNReal.ofReal ((1 - δ / 2) ^ S.card) := by
  set O : Set (GenealogySpace k) := {z | ∀ i ∈ S, δ / 2 < z.1 i} with hO_def
  have hO : IsOpen O := by
    have hOeq : O = ⋂ i ∈ S, {z : GenealogySpace k | δ / 2 < z.1 i} := by
      ext z
      simp [O]
    rw [hOeq]
    exact isOpen_biInter_finset fun i _ ↦
      isOpen_lt continuous_const ((continuous_apply i).comp continuous_fst)
  have hsub : {z : GenealogySpace k | ∀ i ∈ S, δ ≤ z.1 i} ⊆ O := fun z hz i hi ↦ by
    have := hz i hi
    linarith
  have hlim := ProbabilityMeasure.le_liminf_measure_open_of_tendsto
    (tendsto_genealogyLaw_criticalGenealogyLimit hx hL1 hpos h2 k) hO
  refine (measure_mono hsub).trans (hlim.trans ?_)
  have hlate := tendsto_lateBirthProbability hx (by norm_num : (1 / 2 : ℝ) < 1) hL1 hpos
    (r := δ / 2) (by positivity) (by linarith)
  have heqn : ∀ᶠ n in atTop, (genealogyLaw hx k n : Measure (GenealogySpace k)) O =
      ENNReal.ofReal (lateBirthProbability (xa n) n (δ / 2) ^ S.card) := by
    filter_upwards [eventually_gt_atTop 0] with n hn0
    have hnr : (0 : ℝ) < n := by exact_mod_cast hn0
    let := uniformVertex_isProbabilityMeasure (xa n) (hx n).1 ((hx n).2 n le_rfl).le
    set L : Set VertexLabel := {v | δ / 2 * n < (birthTime n v : ℝ)} with hL_def
    have hpre : genealogyVector n ⁻¹' O = (univ : Set History) ×ˢ
        (Set.pi univ fun i ↦ if i ∈ S then L else univ) := by
      ext q
      simp only [mem_preimage, genealogyVector, O, mem_ofPred_eq, mem_prod, mem_univ, true_and,
        mem_univ_pi]
      constructor
      · intro h i
        split_ifs with hi
        · exact (lt_div_iff₀ hnr).mp (h i hi)
        · trivial
      · intro h i hi
        have := h i
        rw [ite_eq_left hi] at this
        exact (lt_div_iff₀ hnr).mpr this
    have hfac : ∀ i : Fin k, uniformVertex (xa n) n (if i ∈ S then L else univ) =
        if i ∈ S then uniformVertex (xa n) n L else 1 := by
      intro i
      split_ifs
      · rfl
      · exact measure_univ
    simp only [genealogyLaw, ProbabilityMeasure.coe_mk]
    rw [Measure.map_apply (measurable_genealogyVector n) hO.measurableSet, hpre,
      sampledReverseVectorLaw, Measure.prod_prod, measure_univ, one_mul, Measure.pi_pi]
    simp only [hfac, Finset.prod_ite_mem, Finset.univ_inter, Finset.prod_const]
    rw [lateBirthProbability, ENNReal.ofReal_pow measureReal_nonneg, measureReal_def,
      ENNReal.ofReal_toReal (measure_ne_top _ _)]
  have hlim1 : Tendsto (fun n ↦ ENNReal.ofReal (lateBirthProbability (xa n) n (δ / 2) ^ S.card))
      atTop (𝓝 (ENNReal.ofReal ((1 - δ / 2) ^ S.card))) :=
    (ENNReal.continuous_ofReal.tendsto _).comp (hlate.pow _)
  rw [liminf_congr heqn, hlim1.liminf_eq]

end Limit

end Freezing2.CriticalGenealogy
