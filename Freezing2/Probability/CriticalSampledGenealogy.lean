module

public import Freezing2.Probability.CriticalGenealogyLimit
public import Freezing2.Probability.SupercriticalMatrixApproximation

/-!
# Sampled genealogies in the critical regime: convergence on upper sets

For `k` iid uniform vertices of the actual reverse construction, the genealogy
vector records their scaled birth times and scaled pairwise coalescence times.
For thresholds `α` (births) and `γ` (coalescence times), the probability that every
coordinate exceeds its threshold converges to an explicit integral over the unit
cube of the continuous coalescence limits. The proof realizes the iid vertices
through the quantile coupling, so that the scaled births converge almost surely,
and applies dominated convergence.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory

namespace Freezing2.CriticalGenealogy

open Freezing1 TrackedGenealogy ReverseCoalescence ReverseHistory

variable {k : ℕ}

/-- The space of scaled birth and coalescence times of `k` sampled vertices. -/
abbrev GenealogySpace (k : ℕ) := (Fin k → ℝ) × (Fin k → Fin k → ℝ)

/-- Scaled birth times and scaled pairwise coalescence times of sampled labels. -/
noncomputable def genealogyVector (n : ℕ) (q : History × (Fin k → VertexLabel)) :
    GenealogySpace k :=
  (fun j ↦ (Freezing2.birthTime n (q.2 j) : ℝ) / n,
    fun j l ↦ (sourceCoalescenceTime n (q.2 j) (q.2 l) q.1 : ℝ) / n)

theorem measurable_genealogyVector (n : ℕ) :
    Measurable (genealogyVector (k := k) n) := by
  apply measurable_from_prod_countable_left
  intro V
  refine Measurable.prodMk ?_ ?_
  · exact (measurable_const : Measurable fun _ : History ↦
      fun j ↦ (Freezing2.birthTime n (V j) : ℝ) / n)
  · exact measurable_pi_iff.mpr fun j ↦ measurable_pi_iff.mpr fun l ↦
      (measurable_from_top (f := fun c : ℕ ↦ (c : ℝ) / n)).comp
        (measurable_sourceCoalescenceTime n (V j) (V l))

/-- Points all of whose coordinates exceed the thresholds. -/
def upperSet (α : Fin k → ℝ) (γ : Fin k → Fin k → ℝ) : Set (GenealogySpace k) :=
  {z | (∀ j, α j < z.1 j) ∧ ∀ j l, γ j l < z.2 j l}

theorem isOpen_upperSet (α : Fin k → ℝ) (γ : Fin k → Fin k → ℝ) : IsOpen (upperSet α γ) := by
  have h1 : IsOpen {z : GenealogySpace k | ∀ j, α j < z.1 j} := by
    simp only [ofPred_forall]
    exact isOpen_iInter_of_finite fun j ↦
      isOpen_lt continuous_const ((continuous_apply j).comp continuous_fst)
  have h2 : IsOpen {z : GenealogySpace k | ∀ j l, γ j l < z.2 j l} := by
    simp only [ofPred_forall]
    exact isOpen_iInter_of_finite fun j ↦ isOpen_iInter_of_finite fun l ↦
      isOpen_lt continuous_const ((continuous_apply l).comp ((continuous_apply j).comp
        continuous_snd))
  exact h1.inter h2

/-- Lebesgue measure on the unit cube. -/
noncomputable def cubeMeasure (k : ℕ) : Measure (Fin k → ℝ) :=
  Measure.pi fun _ : Fin k ↦ volume.restrict (Icc (0 : ℝ) 1)

instance isProbabilityMeasure_unitInterval :
    IsProbabilityMeasure (volume.restrict (Icc (0 : ℝ) 1)) :=
  ⟨by simp [Real.volume_Icc]⟩

instance (k : ℕ) : IsProbabilityMeasure (cubeMeasure k) := by
  unfold cubeMeasure
  infer_instance

/-- The limit integrand of an upper set at births `U`. -/
noncomputable def upperIntegrand (g : ℝ → ℝ) (α : Fin k → ℝ) (γ : Fin k → Fin k → ℝ)
    (U : Fin k → ℝ) : ℝ :=
  open Classical in
  if (∀ j, α j < U j ∧ γ j j < U j) ∧ ∀ j l, j ≠ l → γ j l < 1 then coalescenceLimit g U γ
  else 0

/-- The limit probability of an upper set. -/
noncomputable def upperLimit (g : ℝ → ℝ) (α : Fin k → ℝ) (γ : Fin k → Fin k → ℝ) : ℝ :=
  ∫ U, upperIntegrand g α γ U ∂cubeMeasure k

/-- The iid uniform vertices realized from a point of the cube. -/
noncomputable def cubeVertices (x : ℕ → ℤ) (n : ℕ) (U : Fin k → ℝ) : Fin k → VertexLabel :=
  fun j ↦ vertexQuantile x n (U j)

theorem measurable_cubeVertices (x : ℕ → ℤ) (n : ℕ) :
    Measurable (cubeVertices (k := k) x n) :=
  measurable_pi_iff.mpr fun j ↦ (measurable_vertexQuantile x n).comp (measurable_pi_apply j)

theorem map_cubeVertices (x : ℕ → ℤ) {n : ℕ} (hN : 0 < vertexCount x n) :
    (cubeMeasure k).map (cubeVertices x n) = Measure.pi fun _ : Fin k ↦ uniformVertex x n := by
  unfold cubeMeasure cubeVertices
  rw [Measure.pi_map_pi (fun _ ↦ (measurable_vertexQuantile x n).aemeasurable)]
  simp_rw [map_vertexQuantile x n hN]

/-- Sampled events as integrals over the cube. -/
theorem sampledReverseVectorLaw_real_eq_integral (x : ℕ → ℤ) (hx : IsSigned x) {n : ℕ}
    (hs : SurvivesThrough x n) {E : Set (History × (Fin k → VertexLabel))}
    (hE : MeasurableSet E) :
    (sampledReverseVectorLaw x n k).real E =
      ∫ U, (jointLaw (companionSchedule x) n).real {ω | (ω, cubeVertices x n U) ∈ E}
        ∂cubeMeasure k := by
  let := uniformVertex_isProbabilityMeasure x hx (hs n le_rfl).le
  have hN : 0 < vertexCount x n := vertexCount_pos hs
  rw [measureReal_def, sampledReverseVectorLaw, Measure.prod_apply_symm hE,
    ← map_cubeVertices x hN,
    lintegral_map (measurable_of_countable _) (measurable_cubeVertices x n)]
  have hmeas : Measurable (fun a ↦ (jointLaw (companionSchedule x) n)
      ((fun ω ↦ (ω, cubeVertices x n a)) ⁻¹' E)) :=
    (measurable_of_countable (fun V : Fin k → VertexLabel ↦ (jointLaw (companionSchedule x) n)
      ((fun ω ↦ (ω, V)) ⁻¹' E))).comp (measurable_cubeVertices x n)
  rw [← integral_toReal hmeas.aemeasurable (Eventually.of_forall fun _ ↦ measure_lt_top _ _)]
  rfl

theorem genealogyVector_mem_upperSet_iff (n : ℕ) (α : Fin k → ℝ) (γ : Fin k → Fin k → ℝ)
    (V : Fin k → VertexLabel) (ω : History) :
    genealogyVector n (ω, V) ∈ upperSet α γ ↔
      (∀ j, α j < (Freezing2.birthTime n (V j) : ℝ) / n ∧
        γ j j < (Freezing2.birthTime n (V j) : ℝ) / n) ∧
      ∀ j l, j ≠ l → γ j l < (sourceCoalescenceTime n (V j) (V l) ω : ℝ) / n := by
  simp only [upperSet, genealogyVector, mem_ofPred_eq]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun j ↦ ⟨h1 j, ?_⟩, fun j l _ ↦ h2 j l⟩
    simpa using h2 j j
  · rintro ⟨h1, h2⟩
    refine ⟨fun j ↦ (h1 j).1, fun j l ↦ ?_⟩
    by_cases hjl : j = l
    · subst hjl
      simpa using (h1 j).2
    · exact h2 j l hjl

section AlmostEverywhere

theorem ae_cube_coord (j : Fin k) {P : ℝ → Prop}
    (h : ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) 1), P t) : ∀ᵐ U ∂cubeMeasure k, P (U j) := by
  have hmap := (measurePreserving_eval (fun _ : Fin k ↦ volume.restrict (Icc (0 : ℝ) 1)) j).map_eq
  rw [← hmap] at h
  exact ae_of_ae_map (measurable_pi_apply j).aemeasurable h

theorem ae_unitInterval_good (s : Finset ℝ) :
    ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) 1), 0 < t ∧ t < 1 ∧ t ∉ s := by
  have hfin : ((s : Set ℝ) ∪ {0, 1}).Finite := (s.finite_toSet).union (by simp)
  have hnull : volume.restrict (Icc (0 : ℝ) 1) ((s : Set ℝ) ∪ {0, 1}) = 0 :=
    nonpos_iff_eq_zero.mp ((Measure.restrict_apply_le _ _).trans (hfin.measure_zero volume).le)
  filter_upwards [ae_restrict_mem measurableSet_Icc, measure_eq_zero_iff_ae_notMem.mp hnull]
    with t ht hts
  simp only [mem_union, Finset.mem_coe, mem_insert_iff, mem_singleton_iff, not_or] at hts
  exact ⟨lt_of_le_of_ne ht.1 (Ne.symm hts.2.1), lt_of_le_of_ne ht.2 hts.2.2, hts.1⟩

theorem ae_cube_ne {j l : Fin k} (hjl : j ≠ l) : ∀ᵐ U ∂cubeMeasure k, U j ≠ U l := by
  set μ := volume.restrict (Icc (0 : ℝ) 1)
  have hi := iIndepFun_pi (μ := fun _ : Fin k ↦ μ) (X := fun _ ↦ id) (fun _ ↦ aemeasurable_id)
  have hm := (hi.indepFun hjl).map_prod_eq_prod_map_map
    (measurable_pi_apply j).aemeasurable (measurable_pi_apply l).aemeasurable
  rw [(measurePreserving_eval (fun _ : Fin k ↦ μ) j).map_eq,
    (measurePreserving_eval (fun _ : Fin k ↦ μ) l).map_eq] at hm
  have hdiag : (μ.prod μ) {p : ℝ × ℝ | p.1 = p.2} = 0 := by
    rw [Measure.prod_apply (measurableSet_eq_fun measurable_fst measurable_snd)]
    have : ∀ a : ℝ, μ (Prod.mk a ⁻¹' {p : ℝ × ℝ | p.1 = p.2}) = 0 := by
      intro a
      have : Prod.mk a ⁻¹' {p : ℝ × ℝ | p.1 = p.2} = {a} := by
        ext b
        simp [eq_comm]
      rw [this]
      exact nonpos_iff_eq_zero.mp ((Measure.restrict_apply_le _ _).trans (measure_singleton a).le)
    simp only [this, MeasureTheory.lintegral_const, zero_mul]
  have hae : ∀ᵐ p ∂(μ.prod μ), p.1 ≠ p.2 := measure_eq_zero_iff_ae_notMem.mp hdiag
  rw [← hm] at hae
  exact ae_of_ae_map ((measurable_pi_apply j).prodMk (measurable_pi_apply l)).aemeasurable hae

/-- Almost every point of the cube has distinct interior coordinates avoiding a
given finite set. -/
theorem ae_cube_good (s : Finset ℝ) :
    ∀ᵐ U ∂cubeMeasure k, (∀ j, 0 < U j ∧ U j < 1 ∧ U j ∉ s) ∧ Function.Injective U := by
  have h1 : ∀ᵐ U ∂cubeMeasure k, ∀ j, 0 < U j ∧ U j < 1 ∧ U j ∉ s :=
    ae_all_iff.mpr fun j ↦ ae_cube_coord j (ae_unitInterval_good s)
  have h2 : ∀ᵐ U ∂cubeMeasure k, ∀ p : Fin k × Fin k, p.1 ≠ p.2 → U p.1 ≠ U p.2 :=
    ae_all_iff.mpr fun p ↦ by
      by_cases hp : p.1 = p.2
      · exact Eventually.of_forall fun _ h ↦ absurd hp h
      · exact (ae_cube_ne hp).mono fun _ h _ ↦ h
  filter_upwards [h1, h2] with U hU1 hU2
  refine ⟨hU1, fun j l h ↦ ?_⟩
  by_contra hjl
  exact hU2 (j, l) hjl h

end AlmostEverywhere

theorem birthTime_le_of_mem {x : ℕ → ℤ} {n : ℕ} {v : VertexLabel} (hv : v ∈ vertexLabels x n) :
    Freezing2.birthTime n v ≤ n := by
  cases v with
  | inl i =>
    have := (Finset.mem_Ioc.mp (Finset.mem_filter.mp (Finset.inl_mem_disjSum.mp hv)).1).2
    simp only [birthTime_frozen]
    omega
  | inr j => simp [Freezing2.birthTime]

theorem eventually_lt_div_iff {B : ℕ → ℕ} {c b : ℝ}
    (hB : Tendsto (fun n ↦ (B n : ℝ) / n) atTop (𝓝 b)) (hcb : c ≠ b) :
    ∀ᶠ n in atTop, (c < (B n : ℝ) / n ↔ c < b) := by
  rcases lt_or_gt_of_ne hcb with h | h
  · filter_upwards [hB.eventually (lt_mem_nhds h)] with n hn
    exact ⟨fun _ ↦ h, fun _ ↦ hn⟩
  · filter_upwards [hB.eventually (gt_mem_nhds h)] with n hn
    exact ⟨fun h' ↦ absurd (h'.trans hn) (lt_irrefl _), fun h' ↦ absurd (h'.trans h) (lt_irrefl _)⟩

/-- **Convergence on upper sets.** For births above `α` and coalescence times above
`γ` (with no off-diagonal threshold equal to zero), the probability for `k` iid
uniform vertices converges to the explicit limit `upperLimit g α γ`. -/
theorem tendsto_upperSet {xa : ℕ → ℕ → ℤ} {g : ℝ → ℝ} (hx : AdmissibleArray xa)
    (hL1 : HasL1ReciprocalProfile xa (1 / 2) g) (hpos : PositiveProfile g)
    (h2 : HasLocalSquareMomentProfile xa (1 / 2) g)
    (α : Fin k → ℝ) {γ : Fin k → Fin k → ℝ} (hγ0 : ∀ j l, j ≠ l → γ j l ≠ 0) :
    Tendsto (fun n ↦ (sampledReverseVectorLaw (xa n) n k).real
      (genealogyVector n ⁻¹' upperSet α γ)) atTop (𝓝 (upperLimit g α γ)) := by
  classical
  set E : ℕ → Set (History × (Fin k → VertexLabel)) := fun n ↦ genealogyVector n ⁻¹' upperSet α γ
  have hE : ∀ n, MeasurableSet (E n) := fun n ↦
    (measurable_genealogyVector n) (isOpen_upperSet α γ).measurableSet
  set h : ℕ → (Fin k → ℝ) → ℝ := fun n U ↦
    (jointLaw (companionSchedule (xa n)) n).real {ω | (ω, cubeVertices (xa n) n U) ∈ E n}
  have heq : ∀ n, (sampledReverseVectorLaw (xa n) n k).real (E n) = ∫ U, h n U ∂cubeMeasure k :=
    fun n ↦ sampledReverseVectorLaw_real_eq_integral (xa n) (hx n).1 (hx n).2 (hE n)
  simp_rw [show ∀ n, (sampledReverseVectorLaw (xa n) n k).real (genealogyVector n ⁻¹'
    upperSet α γ) = ∫ U, h n U ∂cubeMeasure k from heq]
  apply tendsto_integral_of_dominated_convergence (fun _ ↦ (1 : ℝ))
  · intro n
    exact ((measurable_of_countable (fun V : Fin k → VertexLabel ↦
      (jointLaw (companionSchedule (xa n)) n).real {ω | (ω, V) ∈ E n})).comp
        (measurable_cubeVertices (xa n) n)).aestronglyMeasurable
  · exact integrable_const 1
  · intro n
    exact Eventually.of_forall fun U ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
      exact measureReal_le_one
  -- pointwise convergence on the good set
  set s : Finset ℝ := obsTimes γ ∪ Finset.univ.image α ∪ Finset.univ.image fun j ↦ γ j j
  filter_upwards [ae_cube_good (k := k) s] with U ⟨hU, hUinj⟩
  have hUs : ∀ j, U j ∉ obsTimes γ ∧ U j ≠ α j ∧ U j ≠ γ j j := by
    intro j
    have := (hU j).2.2
    simp only [s, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and, not_or,
      not_exists] at this
    exact ⟨this.1.1, fun h ↦ this.1.2 j h.symm, fun h ↦ this.2 j h.symm⟩
  set V : ℕ → Fin k → VertexLabel := fun n ↦ cubeVertices (xa n) n U
  have hBn : ∀ j, Tendsto (fun n ↦ (Freezing2.birthTime n (V n j) : ℝ) / n) atTop (𝓝 (U j)) :=
    fun j ↦ (tendsto_birthTime_vertexQuantile hx (by norm_num) hL1 hpos (hU j).1 (hU j).2.1).2
  have hmemV : ∀ n j, V n j ∈ vertexLabels (xa n) n := fun n j ↦
    vertexQuantile_mem (xa n) n (vertexCount_pos (hx n).2) (hU j).1.le (hU j).2.1
  have hset : ∀ n, {ω | (ω, V n) ∈ E n} =
      {ω | (∀ j, α j < (Freezing2.birthTime n (V n j) : ℝ) / n ∧
        γ j j < (Freezing2.birthTime n (V n j) : ℝ) / n) ∧
        ∀ j l, j ≠ l → γ j l < (sourceCoalescenceTime n (V n j) (V n l) ω : ℝ) / n} := by
    intro n
    ext ω
    exact genealogyVector_mem_upperSet_iff n α γ (V n) ω
  have hBcond : ∀ᶠ n in atTop, ((∀ j, α j < (Freezing2.birthTime n (V n j) : ℝ) / n ∧
      γ j j < (Freezing2.birthTime n (V n j) : ℝ) / n) ↔ ∀ j, α j < U j ∧ γ j j < U j) := by
    have hj : ∀ j, ∀ᶠ n in atTop, ((α j < (Freezing2.birthTime n (V n j) : ℝ) / n ∧
        γ j j < (Freezing2.birthTime n (V n j) : ℝ) / n) ↔ (α j < U j ∧ γ j j < U j)) := by
      intro j
      filter_upwards [eventually_lt_div_iff (hBn j) (hUs j).2.1.symm,
        eventually_lt_div_iff (hBn j) (hUs j).2.2.symm] with n h1 h2
      rw [h1, h2]
    filter_upwards [eventually_all.mpr hj] with n hn
    exact forall_congr' hn
  show Tendsto (fun n ↦ (jointLaw (companionSchedule (xa n)) n).real {ω | (ω, V n) ∈ E n})
    atTop (𝓝 (upperIntegrand g α γ U))
  simp_rw [hset]
  by_cases hγ1 : ∀ j l, j ≠ l → γ j l < 1
  · by_cases hb : ∀ j, α j < U j ∧ γ j j < U j
    · have hval : upperIntegrand g α γ U = coalescenceLimit g U γ := by
        unfold upperIntegrand
        rw [ite_eq_left ⟨hb, hγ1⟩]
      rw [hval]
      have hlim := tendsto_coalescence_gt hx hL1 hpos h2 hγ0 hγ1 (fun j ↦ ⟨(hU j).1, (hU j).2.1⟩)
        hUinj (fun j ↦ (hUs j).1)
      apply hlim.congr'
      filter_upwards [hBcond] with n hn
      congr 1
      ext ω
      simp only [mem_ofPred_eq]
      exact ⟨fun h' ↦ ⟨hn.mpr hb, h'⟩, fun h' ↦ h'.2⟩
    · have hval : upperIntegrand g α γ U = 0 := by simp [upperIntegrand, hb]
      rw [hval]
      apply tendsto_const_nhds.congr'
      filter_upwards [hBcond] with n hn
      have : {ω : History | (∀ j, α j < (Freezing2.birthTime n (V n j) : ℝ) / n ∧
          γ j j < (Freezing2.birthTime n (V n j) : ℝ) / n) ∧
          ∀ j l, j ≠ l → γ j l < (sourceCoalescenceTime n (V n j) (V n l) ω : ℝ) / n} = ∅ := by
        ext ω
        simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
        exact fun h ↦ absurd (hn.mp h) hb
      rw [this, measureReal_empty]
  · have hval : upperIntegrand g α γ U = 0 := by simp [upperIntegrand, hγ1]
    rw [hval]
    push Not at hγ1
    obtain ⟨j₀, l₀, hjl, hge⟩ := hγ1
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop 0] with n hn
    have : {ω : History | (∀ j, α j < (Freezing2.birthTime n (V n j) : ℝ) / n ∧
        γ j j < (Freezing2.birthTime n (V n j) : ℝ) / n) ∧
        ∀ j l, j ≠ l → γ j l < (sourceCoalescenceTime n (V n j) (V n l) ω : ℝ) / n} = ∅ := by
      ext ω
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
      intro _ h
      have hlt := h j₀ l₀ hjl
      have hC : sourceCoalescenceTime n (V n j₀) (V n l₀) ω ≤ n := by
        have h1 := coalescenceTime_le_commonBirth n (toCompanionLabel (V n j₀))
          (toCompanionLabel (V n l₀)) ω
        have h2 : commonBirth n (toCompanionLabel (V n j₀)) (toCompanionLabel (V n l₀)) ≤
            Freezing1.birthTime n (toCompanionLabel (V n j₀)) := min_le_left _ _
        rw [companion_birthTime] at h2
        exact h1.trans (h2.trans (birthTime_le_of_mem (hmemV n j₀)))
      have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
      have : (sourceCoalescenceTime n (V n j₀) (V n l₀) ω : ℝ) / n ≤ 1 := by
        rw [div_le_one hnpos]
        exact_mod_cast hC
      linarith
    rw [this, measureReal_empty]

end Freezing2.CriticalGenealogy
