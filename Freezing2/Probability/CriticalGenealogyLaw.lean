module

public import Freezing2.Probability.CriticalSampledGenealogy
public import Freezing2.Probability.RootedSampledMatrix
public import Mathlib.MeasureTheory.Measure.Prokhorov
public import Mathlib.MeasureTheory.Measure.Portmanteau
public import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
public import Mathlib.Topology.Algebra.Module.Cardinality

/-!
# The limiting law of sampled genealogies in the critical regime

Upper sets with thresholds in a co-countable set of reals form a π-system that
generates the Borel σ-algebra of the genealogy space. A probability measure is
therefore determined by its values on upper sets whose thresholds avoid its
atoms, and those values are prescribed by the explicit limits `upperLimit g`.

The laws of the genealogy vectors of `k` iid uniform vertices are supported in
the unit cube, hence tight; every subsequential weak limit has the prescribed
values on upper sets with null frontier, by the portmanteau theorem. Hence the
laws converge, and the limit is characterized by `g` alone.
-/

@[expose] public section

open MeasureTheory Set Filter Topology MeasurableSpace
open scoped NNReal ENNReal

namespace Freezing2.CriticalGenealogy

open ReverseHistory ReverseCoalescence

variable {k : ℕ}

section Generation

theorem dense_of_countable_compl {D : Set ℝ} (hD : Dᶜ.Countable) : Dense D := by
  simpa using hD.dense_compl ℝ

/-- Open rays above points of `D`. -/
def raysIn (D : Set ℝ) : Set (Set ℝ) := {S | ∃ d ∈ D, S = Ioi d}

theorem borel_eq_generateFrom_raysIn {D : Set ℝ} (hD : Dᶜ.Countable) :
    borel ℝ = generateFrom (raysIn D) := by
  have hdense := dense_of_countable_compl hD
  apply le_antisymm
  · rw [borel_eq_generateFrom_Ioi]
    apply generateFrom_le
    rintro _ ⟨c, rfl⟩
    have hd : ∀ m : ℕ, ∃ d ∈ D, d ∈ Ioo c (c + 1 / ((m : ℝ) + 1)) := fun m ↦
      hdense.exists_between (lt_add_of_pos_right c (by positivity))
    choose d hdD hdI using hd
    have hc : Ioi c = ⋃ m, Ioi (d m) := by
      ext y
      simp only [mem_Ioi, mem_iUnion]
      constructor
      · intro hy
        obtain ⟨m, hm⟩ := exists_nat_one_div_lt (sub_pos.mpr hy)
        exact ⟨m, by linarith [(hdI m).2]⟩
      · rintro ⟨m, hm⟩
        exact lt_trans (hdI m).1 hm
    rw [hc]
    exact MeasurableSet.iUnion fun m ↦ measurableSet_generateFrom ⟨d m, hdD m, rfl⟩
  · apply generateFrom_le
    rintro _ ⟨d, -, rfl⟩
    exact measurableSet_Ioi

theorem isCountablySpanning_raysIn {D : Set ℝ} (hD : Dᶜ.Countable) :
    IsCountablySpanning (raysIn D) := by
  have hdense := dense_of_countable_compl hD
  have hd : ∀ m : ℕ, ∃ d ∈ D, d ∈ Ioo (-(m : ℝ) - 1) (-(m : ℝ)) := fun m ↦
    hdense.exists_between (by linarith)
  choose d hdD hdI using hd
  refine ⟨fun m ↦ Ioi (d m), fun m ↦ ⟨d m, hdD m, rfl⟩, ?_⟩
  ext y
  simp only [mem_iUnion, mem_Ioi, mem_univ, iff_true]
  obtain ⟨m, hm⟩ := exists_nat_gt (-y)
  exact ⟨m, by linarith [(hdI m).2]⟩

/-- Upper sets with thresholds in `D`. -/
def upperSets (D : Set ℝ) : Set (Set (GenealogySpace k)) :=
  {S | ∃ α γ, (∀ j, α j ∈ D) ∧ (∀ j l, γ j l ∈ D) ∧ S = upperSet α γ}

theorem upperSet_eq_prod (α : Fin k → ℝ) (γ : Fin k → Fin k → ℝ) :
    upperSet α γ = (pi univ fun j ↦ Ioi (α j)) ×ˢ pi univ fun j ↦ pi univ fun l ↦ Ioi (γ j l) := by
  ext z
  simp [upperSet]

theorem measurableSpace_eq_generateFrom_upperSets {D : Set ℝ} (hD : Dᶜ.Countable) :
    (inferInstance : MeasurableSpace (GenealogySpace k)) = generateFrom (upperSets D) := by
  have hspan := isCountablySpanning_raysIn hD
  have hR : (inferInstance : MeasurableSpace ℝ) = generateFrom (raysIn D) :=
    (borel_eq_generateFrom_raysIn hD).symm ▸ rfl
  have hinst : (inferInstance : MeasurableSpace (GenealogySpace k)) =
      @Prod.instMeasurableSpace _ _
        (@MeasurableSpace.pi (Fin k) (fun _ ↦ ℝ) fun _ ↦ generateFrom (raysIn D))
        (@MeasurableSpace.pi (Fin k) (fun _ ↦ Fin k → ℝ) fun _ ↦
          @MeasurableSpace.pi (Fin k) (fun _ ↦ ℝ) fun _ ↦ generateFrom (raysIn D)) := by
    rw [← hR]
  rw [hinst, generateFrom_pi_eq (fun _ ↦ hspan),
    generateFrom_pi_eq (fun _ ↦ IsCountablySpanning.pi fun _ ↦ hspan),
    generateFrom_prod_eq (IsCountablySpanning.pi fun _ ↦ hspan)
      (IsCountablySpanning.pi fun _ ↦ IsCountablySpanning.pi fun _ ↦ hspan)]
  congr 1
  ext S
  simp only [mem_image2, mem_image, Set.mem_univ_pi, upperSets, mem_ofPred_eq]
  constructor
  · rintro ⟨A, ⟨t, ht, rfl⟩, B, ⟨t', ht', rfl⟩, rfl⟩
    choose α hαD hα using ht
    choose s hs hs' using ht'
    choose γ hγD hγ using hs
    refine ⟨α, γ, hαD, hγD, ?_⟩
    rw [upperSet_eq_prod]
    congr 1
    · exact congrArg (pi univ) (funext hα)
    · congr 1
      funext j
      rw [← hs' j]
      exact congrArg (pi univ) (funext (hγ j))
  · rintro ⟨α, γ, hα, hγ, rfl⟩
    refine ⟨_, ⟨fun j ↦ Ioi (α j), fun j ↦ ⟨α j, hα j, rfl⟩, rfl⟩, _,
      ⟨fun j ↦ pi univ fun l ↦ Ioi (γ j l), fun j ↦ ⟨fun l ↦ Ioi (γ j l),
        fun l ↦ ⟨γ j l, hγ j l, rfl⟩, rfl⟩, rfl⟩, (upperSet_eq_prod α γ).symm⟩

theorem isPiSystem_upperSets (D : Set ℝ) : IsPiSystem (upperSets (k := k) D) := by
  rintro _ ⟨α, γ, hα, hγ, rfl⟩ _ ⟨α', γ', hα', hγ', rfl⟩ _
  refine ⟨fun j ↦ max (α j) (α' j), fun j l ↦ max (γ j l) (γ' j l), fun j ↦ ?_,
    fun j l ↦ ?_, ?_⟩
  · show max (α j) (α' j) ∈ D
    rcases le_total (α j) (α' j) with h | h
    · rw [max_eq_right h]; exact hα' j
    · rw [max_eq_left h]; exact hα j
  · show max (γ j l) (γ' j l) ∈ D
    rcases le_total (γ j l) (γ' j l) with h | h
    · rw [max_eq_right h]; exact hγ' j l
    · rw [max_eq_left h]; exact hγ j l
  · ext z
    simp only [upperSet, mem_inter_iff, mem_ofPred_eq, max_lt_iff]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3, h4⟩
      exact ⟨fun j ↦ ⟨h1 j, h3 j⟩, fun j l ↦ ⟨h2 j l, h4 j l⟩⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨fun j ↦ (h1 j).1, fun j l ↦ (h2 j l).1⟩, fun j ↦ (h1 j).2, fun j l ↦ (h2 j l).2⟩

/-- Two finite measures with equal mass that agree on upper sets with thresholds in a
co-countable set are equal. -/
theorem ext_of_upperSets {μ ν : Measure (GenealogySpace k)} [IsFiniteMeasure μ]
    {D : Set ℝ} (hD : Dᶜ.Countable)
    (h : ∀ α γ, (∀ j, α j ∈ D) → (∀ j l, γ j l ∈ D) → μ (upperSet α γ) = ν (upperSet α γ))
    (huniv : μ univ = ν univ) : μ = ν :=
  ext_of_generate_finite _ (measurableSpace_eq_generateFrom_upperSets hD)
    (isPiSystem_upperSets D) (by rintro _ ⟨α, γ, hα, hγ, rfl⟩; exact h α γ hα hγ) huniv

end Generation

section Atoms

/-- Values carrying positive mass in some coordinate. -/
def atoms (μ : Measure (GenealogySpace k)) : Set ℝ :=
  (⋃ j, {c | 0 < μ {z | z.1 j = c}}) ∪ ⋃ j, ⋃ l, {c | 0 < μ {z | z.2 j l = c}}

theorem countable_atoms (μ : Measure (GenealogySpace k)) [IsFiniteMeasure μ] :
    (atoms μ).Countable := by
  refine Countable.union (countable_iUnion fun j ↦ ?_)
    (countable_iUnion fun j ↦ countable_iUnion fun l ↦ ?_)
  · exact Measure.countable_meas_pos_of_disjoint_iUnion
      (fun c ↦ measurableSet_eq_fun ((measurable_pi_apply j).comp measurable_fst)
        measurable_const)
      fun c c' hcc' ↦ Set.disjoint_left.mpr fun z h h' ↦ hcc' (h.symm.trans h')
  · exact Measure.countable_meas_pos_of_disjoint_iUnion
      (fun c ↦ measurableSet_eq_fun ((measurable_pi_apply l).comp ((measurable_pi_apply j).comp
        measurable_snd)) measurable_const)
      fun c c' hcc' ↦ Set.disjoint_left.mpr fun z h h' ↦ hcc' (h.symm.trans h')

theorem frontier_upperSet_subset (α : Fin k → ℝ) (γ : Fin k → Fin k → ℝ) :
    frontier (upperSet α γ) ⊆
      (⋃ j, {z : GenealogySpace k | z.1 j = α j}) ∪ ⋃ j, ⋃ l, {z | z.2 j l = γ j l} := by
  rw [(isOpen_upperSet α γ).frontier_eq]
  rintro z ⟨hcl, hnot⟩
  have hclosed : IsClosed {z : GenealogySpace k | (∀ j, α j ≤ z.1 j) ∧ ∀ j l, γ j l ≤ z.2 j l} := by
    have h1 : IsClosed {z : GenealogySpace k | ∀ j, α j ≤ z.1 j} := by
      simp only [ofPred_forall]
      exact isClosed_iInter fun j ↦
        isClosed_le continuous_const ((continuous_apply j).comp continuous_fst)
    have h2 : IsClosed {z : GenealogySpace k | ∀ j l, γ j l ≤ z.2 j l} := by
      simp only [ofPred_forall]
      exact isClosed_iInter fun j ↦ isClosed_iInter fun l ↦
        isClosed_le continuous_const ((continuous_apply l).comp ((continuous_apply j).comp
          continuous_snd))
    exact h1.inter h2
  have hsub : upperSet α γ ⊆
      {z : GenealogySpace k | (∀ j, α j ≤ z.1 j) ∧ ∀ j l, γ j l ≤ z.2 j l} :=
    fun z hz ↦ ⟨fun j ↦ (hz.1 j).le, fun j l ↦ (hz.2 j l).le⟩
  have hz := closure_minimal hsub hclosed hcl
  by_contra h
  simp only [mem_union, mem_iUnion, mem_ofPred_eq, not_or, not_exists] at h
  exact hnot ⟨fun j ↦ lt_of_le_of_ne (hz.1 j) fun e ↦ h.1 j e.symm,
    fun j l ↦ lt_of_le_of_ne (hz.2 j l) fun e ↦ h.2 j l e.symm⟩

theorem measure_frontier_upperSet (μ : Measure (GenealogySpace k)) {α : Fin k → ℝ}
    {γ : Fin k → Fin k → ℝ} (hα : ∀ j, α j ∉ atoms μ) (hγ : ∀ j l, γ j l ∉ atoms μ) :
    μ (frontier (upperSet α γ)) = 0 := by
  apply measure_mono_null (frontier_upperSet_subset α γ)
  apply measure_union_null
  · refine measure_iUnion_null fun j ↦ ?_
    have := hα j
    simp only [atoms, mem_union, mem_iUnion, mem_ofPred_eq, not_or, not_exists, not_lt,
      nonpos_iff_eq_zero] at this
    exact this.1 j
  · refine measure_iUnion_null fun j ↦ measure_iUnion_null fun l ↦ ?_
    have := hγ j l
    simp only [atoms, mem_union, mem_iUnion, mem_ofPred_eq, not_or, not_exists, not_lt,
      nonpos_iff_eq_zero] at this
    exact this.2 j l

end Atoms

/-- `μ` takes the explicit limit values on every upper set with null frontier and no
off-diagonal coalescence threshold at zero. -/
def IsGenealogyLimit (g : ℝ → ℝ) (μ : ProbabilityMeasure (GenealogySpace k)) : Prop :=
  ∀ α γ, (∀ j l, j ≠ l → γ j l ≠ 0) → (μ : Measure (GenealogySpace k)) (frontier (upperSet α γ)) = 0 →
    (μ : Measure (GenealogySpace k)).real (upperSet α γ) = upperLimit g α γ

/-- **Uniqueness of the limit law.** -/
theorem IsGenealogyLimit.unique {g : ℝ → ℝ} {μ ν : ProbabilityMeasure (GenealogySpace k)}
    (hμ : IsGenealogyLimit g μ) (hν : IsGenealogyLimit g ν) : μ = ν := by
  set D : Set ℝ := (atoms (μ : Measure (GenealogySpace k)) ∪ atoms (ν : Measure (GenealogySpace k))
    ∪ {0})ᶜ
  have hD : Dᶜ.Countable := by
    simp only [D, compl_compl]
    exact ((countable_atoms _).union (countable_atoms _)).union (countable_singleton 0)
  apply ProbabilityMeasure.toMeasure_injective
  apply ext_of_upperSets hD
  · intro α γ hα hγ
    have hαμ : ∀ j, α j ∉ atoms (μ : Measure (GenealogySpace k)) := fun j h ↦
      hα j (mem_union_left _ (mem_union_left _ h))
    have hαν : ∀ j, α j ∉ atoms (ν : Measure (GenealogySpace k)) := fun j h ↦
      hα j (mem_union_left _ (mem_union_right _ h))
    have hγμ : ∀ j l, γ j l ∉ atoms (μ : Measure (GenealogySpace k)) := fun j l h ↦
      hγ j l (mem_union_left _ (mem_union_left _ h))
    have hγν : ∀ j l, γ j l ∉ atoms (ν : Measure (GenealogySpace k)) := fun j l h ↦
      hγ j l (mem_union_left _ (mem_union_right _ h))
    have hγ0 : ∀ j l, j ≠ l → γ j l ≠ 0 := fun j l _ h ↦ hγ j l (mem_union_right _ h)
    have h1 := hμ α γ hγ0 (measure_frontier_upperSet _ hαμ hγμ)
    have h2 := hν α γ hγ0 (measure_frontier_upperSet _ hαν hγν)
    have e : ((μ : Measure (GenealogySpace k)) (upperSet α γ)).toReal =
        ((ν : Measure (GenealogySpace k)) (upperSet α γ)).toReal := by
      rw [← measureReal_def, ← measureReal_def, h1, h2]
    exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp e
  · simp

/-- The law of the genealogy vector of `k` iid uniform vertices at horizon `n`. -/
noncomputable def genealogyLaw {xa : ℕ → ℕ → ℤ} (hx : AdmissibleArray xa) (k n : ℕ) :
    ProbabilityMeasure (GenealogySpace k) :=
  let := sampledReverseVectorLaw_probability (xa n) (hx n).1 (k := k) (hx n).2
  ⟨(sampledReverseVectorLaw (xa n) n k).map (genealogyVector n),
    (Measure.isProbabilityMeasure_map_iff (measurable_genealogyVector n).aemeasurable).mpr
      inferInstance⟩

theorem genealogyLaw_real_upperSet {xa : ℕ → ℕ → ℤ} (hx : AdmissibleArray xa) (n : ℕ)
    (α : Fin k → ℝ) (γ : Fin k → Fin k → ℝ) :
    (genealogyLaw hx k n : Measure (GenealogySpace k)).real (upperSet α γ) =
      (sampledReverseVectorLaw (xa n) n k).real (genealogyVector n ⁻¹' upperSet α γ) := by
  simp only [genealogyLaw, ProbabilityMeasure.coe_mk, measureReal_def]
  rw [Measure.map_apply (measurable_genealogyVector n) (isOpen_upperSet α γ).measurableSet]

/-- The unit cube of the genealogy space. -/
def unitCube (k : ℕ) : Set (GenealogySpace k) :=
  (pi univ fun _ ↦ Icc 0 1) ×ˢ pi univ fun _ ↦ pi univ fun _ ↦ Icc 0 1

theorem isCompact_unitCube (k : ℕ) : IsCompact (unitCube k) :=
  (isCompact_univ_pi fun _ ↦ isCompact_Icc).prod
    (isCompact_univ_pi fun _ ↦ isCompact_univ_pi fun _ ↦ isCompact_Icc)

theorem genealogyLaw_unitCube_compl {xa : ℕ → ℕ → ℤ} (hx : AdmissibleArray xa) (n : ℕ) :
    (genealogyLaw hx k n : Measure (GenealogySpace k)) (unitCube k)ᶜ = 0 := by
  simp only [genealogyLaw, ProbabilityMeasure.coe_mk]
  rw [Measure.map_apply (measurable_genealogyVector n)
    (isCompact_unitCube k).isClosed.measurableSet.compl]
  rw [← compl_compl (genealogyVector n ⁻¹' (unitCube k)ᶜ), ← mem_ae_iff, preimage_compl,
    compl_compl]
  filter_upwards [sampledReverseVectorLaw_ae_legal (xa n) (hx n).1 (k := k) (hx n).2] with q hq
  have hdiv : ∀ m : ℕ, m ≤ n → (m : ℝ) / n ∈ Icc (0 : ℝ) 1 := by
    intro m hm
    refine ⟨by positivity, ?_⟩
    rcases Nat.eq_zero_or_pos n with h0 | hn
    · simp [h0]
    · rw [div_le_one (by exact_mod_cast hn)]
      exact_mod_cast hm
  refine ⟨fun j _ ↦ hdiv _ (birthTime_le_of_mem (hq j)), fun j _ l _ ↦ hdiv _ ?_⟩
  have h1 := coalescenceTime_le_commonBirth n (toCompanionLabel (q.2 j)) (toCompanionLabel (q.2 l))
    q.1
  have h2 : commonBirth n (toCompanionLabel (q.2 j)) (toCompanionLabel (q.2 l)) ≤
      Freezing1.birthTime n (toCompanionLabel (q.2 j)) := min_le_left _ _
  rw [companion_birthTime] at h2
  exact h1.trans (h2.trans (birthTime_le_of_mem (hq j)))

/-- **Convergence of the sampled genealogy laws.** -/
theorem exists_tendsto_genealogyLaw {xa : ℕ → ℕ → ℤ} {g : ℝ → ℝ} (hx : AdmissibleArray xa)
    (hL1 : HasL1ReciprocalProfile xa (1 / 2) g) (hpos : PositiveProfile g)
    (h2 : HasLocalSquareMomentProfile xa (1 / 2) g) (k : ℕ) :
    ∃ μ : ProbabilityMeasure (GenealogySpace k),
      Tendsto (genealogyLaw hx k) atTop (𝓝 μ) ∧ IsGenealogyLimit g μ := by
  set P := genealogyLaw hx k
  have hcomp : IsCompact (closure (range P)) := by
    apply isCompact_closure_of_isTightMeasureSet
    rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
    intro ε hε
    refine ⟨unitCube k, isCompact_unitCube k, ?_⟩
    rintro _ ⟨μ, ⟨n, rfl⟩, rfl⟩
    rw [genealogyLaw_unitCube_compl hx n]
    exact bot_le
  have hlimit {φ : ℕ → ℕ} (hφ : Tendsto φ atTop atTop) {μ : ProbabilityMeasure (GenealogySpace k)}
      (hμ : Tendsto (P ∘ φ) atTop (𝓝 μ)) : IsGenealogyLimit g μ := by
    intro α γ hγ0 hfr
    have h1 := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' hμ hfr
    have h1' : Tendsto (fun n ↦ ((P (φ n) : Measure (GenealogySpace k))).real (upperSet α γ)) atTop
        (𝓝 ((μ : Measure (GenealogySpace k)).real (upperSet α γ))) :=
      (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp h1
    have h2' := (tendsto_upperSet hx hL1 hpos h2 α hγ0).comp hφ
    simp only [P] at h1'
    simp_rw [← genealogyLaw_real_upperSet hx] at h2'
    exact tendsto_nhds_unique h1' h2'
  obtain ⟨μ₀, -, φ₀, hφ₀, hμ₀⟩ := hcomp.tendsto_subseq fun n ↦ subset_closure (mem_range_self n)
  have hμ₀L := hlimit hφ₀.tendsto_atTop hμ₀
  refine ⟨μ₀, ?_, hμ₀L⟩
  apply tendsto_of_subseq_tendsto
  intro ψ hψ
  obtain ⟨μ₁, -, φ₁, hφ₁, hμ₁⟩ :=
    hcomp.tendsto_subseq fun n ↦ subset_closure (mem_range_self (ψ n))
  have hμ₁L := hlimit (hψ.comp hφ₁.tendsto_atTop) hμ₁
  exact ⟨φ₁, (hμ₁L.unique hμ₀L) ▸ hμ₁⟩

end Freezing2.CriticalGenealogy
