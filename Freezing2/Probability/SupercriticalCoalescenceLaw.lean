module

public import Freezing2.Probability.SubcriticalCoalescenceLaw
public import Freezing2.Probability.ProductEventBound
public import Freezing2.Probability.VertexSampling
public import Freezing2.Analysis.SupercriticalCoalescence

/-!
# Coalescence near zero for actual independently sampled vertices

The sampled law is the product of the actual reverse history and two uniform
vertex laws. Coincident samples are retained explicitly. Outside collisions
and a late-birth event, the exact distinct-label survival product is bounded
by the proved local sum of merger hazards.
-/

@[expose] public section

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal Topology Classical BigOperators

namespace Freezing2

open ReverseHistory ReverseCoalescence

theorem one_sub_prod_one_sub_le_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    (h0 : ∀ i ∈ s, 0 ≤ f i) (h1 : ∀ i ∈ s, f i ≤ 1) :
    1 - ∏ i ∈ s, (1 - f i) ≤ ∑ i ∈ s, f i := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have hs0 : ∀ i ∈ s, 0 ≤ f i := fun i hi ↦ h0 i (Finset.mem_insert_of_mem hi)
    have hs1 : ∀ i ∈ s, f i ≤ 1 := fun i hi ↦ h1 i (Finset.mem_insert_of_mem hi)
    have hprod : (∏ i ∈ s, (1 - f i)) ≤ 1 :=
      Finset.prod_le_one₀ (fun i hi ↦ sub_nonneg.mpr (hs1 i hi))
        (fun i hi ↦ by linarith [hs0 i hi])
    have hmul := mul_le_mul_of_nonneg_left hprod (h0 a (Finset.mem_insert_self _ _))
    have hs := ih hs0 hs1
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    nlinarith

theorem companion_coalescenceHazard_nonneg (x : ℕ → ℤ) (hx : IsSigned x) {n i : ℕ}
    (hs : SurvivesThrough x n) (hin : i ≤ n) :
    0 ≤ coalescenceHazard (companionSchedule x) i := by
  by_cases hup : companionSchedule x i = true
  · rw [coalescenceHazard_eq_inv_choose (companion_before_extinction x hx hs).le hin hup]
    positivity
  · simp [coalescenceHazard, hup]

/-- A merger before the given source cutoff has probability at most the sum
of the actual pairwise hazards. The distinct-label condition is essential. -/
theorem source_coalescence_ge_probability_le_sum (x : ℕ → ℤ) (hx : IsSigned x) {n i : ℕ}
    (hs : SurvivesThrough x n) {u v : VertexLabel}
    (hu : u ∈ vertexLabels x n) (hv : v ∈ vertexLabels x n) (huv : u ≠ v)
    (hi : i ≤ min (birthTime n u) (birthTime n v)) :
    (jointLaw (companionSchedule x) n).real {ω | i ≤ sourceCoalescenceTime n u v ω} ≤
      2 * coalescenceUpSum x i (min (birthTime n u) (birthTime n v) - i) := by
  let b := min (birthTime n u) (birthTime n v)
  have hbn : b ≤ n := (min_le_left _ _).trans (birthTime_le x hu)
  have hne : toCompanionLabel u ≠ toCompanionLabel v := by
    intro h
    apply huv
    have he := congrArg fromCompanionLabel h
    simpa only [from_toCompanionLabel hu, from_toCompanionLabel hv] using he
  have hib : i ≤ commonBirth n (toCompanionLabel u) (toCompanionLabel v) := by
    simpa only [commonBirth, companion_birthTime] using hi
  have htail := coalescenceTime_lt_probability (companion_before_extinction x hx hs).le
    (toCompanionLabel_mem x hx hu) (toCompanionLabel_mem x hx hv) hne hib
  have he : {ω | i ≤ sourceCoalescenceTime n u v ω} =
      {ω | sourceCoalescenceTime n u v ω < i}ᶜ := by
    ext ω
    simp only [mem_ofPred_eq, mem_compl_iff, not_lt]
  rw [he, probReal_compl_eq_one_sub
    ((measurable_sourceCoalescenceTime n u v).lt measurable_const).setOf]
  have htail' : (jointLaw (companionSchedule x) n).real
      {ω | sourceCoalescenceTime n u v ω < i} =
      ∏ j ∈ Finset.Ioc i b, (1 - coalescenceHazard (companionSchedule x) j) := by
    simpa only [sourceCoalescenceTime, commonBirth, companion_birthTime, b] using htail
  rw [htail']
  calc
    _ ≤ ∑ j ∈ Finset.Ioc i b, coalescenceHazard (companionSchedule x) j := by
      apply one_sub_prod_one_sub_le_sum
      · intro j hj
        exact companion_coalescenceHazard_nonneg x hx hs ((Finset.mem_Ioc.mp hj).2.trans hbn)
      · intro j hj
        exact companion_coalescenceHazard_le_one x hx hs
          (by have := (Finset.mem_Ioc.mp hj).1; omega) ((Finset.mem_Ioc.mp hj).2.trans hbn)
    _ = _ := by
      have hb : i + (b - i) = b := Nat.add_sub_of_le hi
      simpa only [hb] using sum_companion_coalescenceHazard x hx i (b - i)

noncomputable def lateBirthProbability (x : ℕ → ℤ) (n : ℕ) (r : ℝ) : ℝ :=
  (uniformVertex x n).real {v | r * n < (birthTime n v : ℝ)}

/-- The late-birth probability is exactly a shifted frozen-count complement. -/
theorem lateBirthProbability_eq (x : ℕ → ℤ) (hx : IsSigned x) {n : ℕ}
    (hs : SurvivesThrough x n) (hn : 0 < n) {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) :
    lateBirthProbability x n r = 1 -
      ((downSteps x 0 (⌊(n : ℝ) * r⌋₊ + 1)).card : ℝ) / (vertexLabels x n).card := by
  let := uniformVertex_isProbabilityMeasure x hx (hs n le_rfl).le
  have hnr : 0 ≤ (n : ℝ) * r := mul_nonneg (Nat.cast_nonneg n) hr
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hfloor : ⌊(n : ℝ) * r⌋₊ < n :=
    Nat.floor_lt hnr |>.mpr (by nlinarith)
  have he : {v | r * n < (birthTime n v : ℝ)} =
      {v | birthTime n v < ⌊(n : ℝ) * r⌋₊ + 1}ᶜ := by
    ext v
    simp only [mem_ofPred_eq, mem_compl_iff, Nat.lt_succ_iff]
    rw [Nat.le_floor_iff hnr]
    simp only [not_le, mul_comm]
  unfold lateBirthProbability
  rw [he, probReal_compl_eq_one_sub (by exact (measurable_of_countable _).setOf),
    uniformVertex_birth_lt_count x (Nat.succ_le_of_lt hfloor)]

theorem tendsto_lateBirthProbability {x : ℕ → ℕ → ℤ} {α : ℝ} {g : ℝ → ℝ}
    (hx : AdmissibleArray x) (hα : α < 1)
    (hL1 : HasL1ReciprocalProfile x α g) (hpos : PositiveProfile g)
    {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) :
    Tendsto (fun n ↦ lateBirthProbability (x n) n r) atTop (𝓝 (1 - r)) := by
  have hratio := (tendsto_downSteps_shifted hx hα hL1 hpos hr hr1.le).div
    (tendsto_normalized_vertexLabels_card hx hα hL1 hpos) (by norm_num : (1 : ℝ) ≠ 0)
  simp only [div_one] at hratio
  have hlim := (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (𝓝 1)).sub hratio
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  rw [lateBirthProbability_eq (x n) (hx n).1 (hx n).2 hn hr hr1]
  congr 1
  exact mul_div_mul_left _ _ (div_ne_zero (by norm_num) (by exact_mod_cast hn.ne'))

/-- Actual independent choices: one reverse history and two uniform labels. -/
noncomputable def sampledReverseLaw (x : ℕ → ℤ) (n : ℕ) :
    Measure (History × (VertexLabel × VertexLabel)) :=
  (jointLaw (companionSchedule x) n).prod ((uniformVertex x n).prod (uniformVertex x n))

theorem sampledReverseLaw_probability (x : ℕ → ℤ) (hx : IsSigned x) {n : ℕ}
    (hs : SurvivesThrough x n) : IsProbabilityMeasure (sampledReverseLaw x n) := by
  let := uniformVertex_isProbabilityMeasure x hx (hs n le_rfl).le
  unfold sampledReverseLaw
  infer_instance

def sampledCoalescenceEvent (n : ℕ) (ε : ℝ) : Set (History × (VertexLabel × VertexLabel)) :=
  {q | ε * n < (sourceCoalescenceTime n q.2.1 q.2.2 q.1 : ℝ)}

theorem measurableSet_sampledCoalescenceEvent (n : ℕ) (ε : ℝ) :
    MeasurableSet (sampledCoalescenceEvent n ε) := by
  apply (measurable_from_prod_countable_left fun p ↦ ?_).setOf
  exact measurable_const.lt ((measurable_of_countable (fun c : ℕ ↦ (c : ℝ))).comp
    (measurable_sourceCoalescenceTime n p.1 p.2))

def collisionOrLateBirth (n : ℕ) (r : ℝ) : Set (VertexLabel × VertexLabel) :=
  {p | p.1 = p.2} ∪ {p | r * n < (birthTime n p.1 : ℝ)}

theorem collisionOrLateBirth_probability_le (x : ℕ → ℤ) (hx : IsSigned x) {n : ℕ}
    (hs : SurvivesThrough x n) (r : ℝ) :
    ((uniformVertex x n).prod (uniformVertex x n)).real (collisionOrLateBirth n r) ≤
      1 / (vertexLabels x n).card + lateBirthProbability x n r := by
  let := uniformVertex_isProbabilityMeasure x hx (hs n le_rfl).le
  have he : {p : VertexLabel × VertexLabel | r * n < (birthTime n p.1 : ℝ)} =
      {v | r * n < (birthTime n v : ℝ)} ×ˢ univ := by ext p; simp
  unfold collisionOrLateBirth
  calc
    _ ≤ _ := measureReal_union_le _ _
    _ = _ := by
      rw [uniformVertex_collision x hx (hs n le_rfl).le, he, measureReal_prod_prod]
      simp only [probReal_univ, mul_one, lateBirthProbability]

/-- Away from collisions and the terminal birth region, the actual pair's
coalescence tail is controlled by a single uniform interior hazard bound. -/
theorem source_pair_coalescence_probability_le (x : ℕ → ℤ) (hx : IsSigned x) {n : ℕ}
    (hs : SurvivesThrough x n) {ε r η : ℝ} (hε : 0 < ε) (hη : 0 ≤ η)
    (hbound : ∀ a b, CoalescenceInterval (min ε (1 - r)) n a b →
      2 * coalescenceUpSum x (a - 1) (b + 1 - a) < η)
    {u v : VertexLabel} (hu : u ∈ vertexLabels x n) (hv : v ∈ vertexLabels x n)
    (huv : u ≠ v) (hlate : (birthTime n u : ℝ) ≤ r * n) :
    (jointLaw (companionSchedule x) n).real
      {ω | ε * n < (sourceCoalescenceTime n u v ω : ℝ)} ≤ η := by
  let b := min (birthTime n u) (birthTime n v)
  let i := ⌊ε * (n : ℝ)⌋₊
  have hfloor : (i : ℝ) ≤ ε * n :=
    Nat.floor_le (mul_nonneg hε.le (Nat.cast_nonneg n))
  have hcoal (ω : History) : sourceCoalescenceTime n u v ω ≤ b := by
    simpa only [sourceCoalescenceTime, commonBirth, companion_birthTime, b] using
      coalescenceTime_le_commonBirth n (toCompanionLabel u) (toCompanionLabel v) ω
  by_cases hbi : b ≤ i
  · have he : {ω | ε * n < (sourceCoalescenceTime n u v ω : ℝ)} = ∅ := by
      ext ω
      constructor
      · intro h
        have hc : (sourceCoalescenceTime n u v ω : ℝ) ≤ i := by
          exact_mod_cast (hcoal ω).trans hbi
        exact (not_lt_of_ge (hc.trans hfloor)) h
      · exact False.elim
    rw [he, measureReal_empty]
    exact hη
  have hib : i < b := lt_of_not_ge hbi
  have hbn : b ≤ n := (min_le_left _ _).trans (birthTime_le x hu)
  have hvalid : CoalescenceInterval (min ε (1 - r)) n (i + 1) b := by
    refine ⟨by omega, by omega, hbn, ?_, ?_⟩
    · have hlo := Nat.lt_floor_add_one (ε * (n : ℝ))
      have hm := mul_le_mul_of_nonneg_right (min_le_left ε (1 - r)) (Nat.cast_nonneg n)
      dsimp [i]
      push_cast
      linarith
    · have hb : (b : ℝ) ≤ birthTime n u := by exact_mod_cast (min_le_left (birthTime n u) _)
      have he := min_le_right ε (1 - r)
      have hm : r * (n : ℝ) ≤ (1 - min ε (1 - r)) * n :=
        mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg n)
      exact hb.trans (hlate.trans hm)
  have hsmall : 2 * coalescenceUpSum x i (b - i) < η := by
    simpa only [Nat.add_sub_cancel, Nat.add_sub_add_right] using hbound (i + 1) b hvalid
  calc
    _ ≤ (jointLaw (companionSchedule x) n).real
        {ω | i ≤ sourceCoalescenceTime n u v ω} := by
      apply measureReal_mono (h₂ := measure_ne_top _ _)
      intro ω hω
      have hc : (i : ℝ) < sourceCoalescenceTime n u v ω := hfloor.trans_lt hω
      exact_mod_cast hc.le
    _ ≤ 2 * coalescenceUpSum x i (b - i) :=
      source_coalescence_ge_probability_le_sum x hx hs hu hv huv hib.le
    _ ≤ η := hsmall.le

/-- The finite-$n$ sampled bound retains repeated samples and a terminal-birth
error. Bounding the common late birth by the first sample alone is sufficient. -/
theorem sampledCoalescence_probability_le (x : ℕ → ℤ) (hx : IsSigned x) {n : ℕ}
    (hs : SurvivesThrough x n) {ε r η : ℝ} (hε : 0 < ε) (hη : 0 ≤ η)
    (hbound : ∀ a b, CoalescenceInterval (min ε (1 - r)) n a b →
      2 * coalescenceUpSum x (a - 1) (b + 1 - a) < η) :
    (sampledReverseLaw x n).real (sampledCoalescenceEvent n ε) ≤
      1 / (vertexLabels x n).card + lateBirthProbability x n r + η := by
  let := uniformVertex_isProbabilityMeasure x hx (hs n le_rfl).le
  have hmem : ∀ᵐ p ∂(uniformVertex x n).prod (uniformVertex x n),
      p.1 ∈ vertexLabels x n ∧ p.2 ∈ vertexLabels x n := by
    apply (Measure.ae_prod_iff_ae_ae (by exact (Set.to_countable _).measurableSet)).mpr
    filter_upwards [uniformVertex_mem x hx (hs n le_rfl).le] with u hu
    exact (uniformVertex_mem x hx (hs n le_rfl).le).mono fun v hv ↦ ⟨hu, hv⟩
  have hsections : ∀ᵐ p ∂(uniformVertex x n).prod (uniformVertex x n),
      p ∉ collisionOrLateBirth n r → (jointLaw (companionSchedule x) n).real
        {ω | (ω, p) ∈ sampledCoalescenceEvent n ε} ≤ η := by
    filter_upwards [hmem] with p hp hnot
    have hne : p.1 ≠ p.2 := fun h ↦ hnot (Or.inl h)
    have hlate : (birthTime n p.1 : ℝ) ≤ r * n :=
      le_of_not_gt (fun h ↦ hnot (Or.inr h))
    change (jointLaw (companionSchedule x) n).real
      {ω | ε * n < (sourceCoalescenceTime n p.1 p.2 ω : ℝ)} ≤ η
    exact source_pair_coalescence_probability_le x hx hs hε hη hbound hp.1 hp.2 hne hlate
  have h := measureReal_prod_event_le_bad_add
    (μ := jointLaw (companionSchedule x) n)
    (ν := (uniformVertex x n).prod (uniformVertex x n))
    (E := sampledCoalescenceEvent n ε) (B := collisionOrLateBirth n r)
    (measurableSet_sampledCoalescenceEvent n ε)
    (show MeasurableSet (collisionOrLateBirth n r) from (Set.to_countable _).measurableSet)
    hη hsections
  apply h.trans
  linarith [collisionOrLateBirth_probability_le x hx hs r]

/-- Source N10: the coalescence phase divided by `n` tends to zero in
probability for two actually independent uniform samples of the reverse tree. -/
theorem tendsto_sampledCoalescence_probability
    {x : ℕ → ℕ → ℤ} {α : ℝ} {g : ℝ → ℝ}
    (hx : AdmissibleArray x) (hαhalf : 1 / 2 < α) (hα1 : α < 1)
    (hL1 : HasL1ReciprocalProfile x α g) (hpos : PositiveProfile g)
    (h2 : HasLocalSquareMomentProfile x α g) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n ↦ (sampledReverseLaw (x n) n).real (sampledCoalescenceEvent n ε))
      atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ζ hζ
  let δ : ℝ := min (ζ / 8) (1 / 4)
  let r : ℝ := 1 - δ
  have hδ : 0 < δ := lt_min (by positivity) (by norm_num)
  have hδζ : δ ≤ ζ / 8 := min_le_left _ _
  have hδsmall : δ ≤ 1 / 4 := min_le_right _ _
  have hr : 0 ≤ r := by dsimp [r]; linarith
  have hr1 : r < 1 := by dsimp [r]; linarith
  have hcut : 0 < min ε (1 - r) := lt_min hε (by linarith)
  have hlate : Tendsto (fun n ↦ lateBirthProbability (x n) n r) atTop (𝓝 δ) := by
    simpa only [r, sub_sub_cancel] using tendsto_lateBirthProbability hx hα1 hL1 hpos hr hr1
  have hcoll := tendsto_uniformVertex_collision hx hα1 hL1 hpos
  filter_upwards [eventually_uniform_supercritical_coalescence_bound hx hαhalf hα1 hL1 hpos h2
      hcut (show 0 < ζ / 4 by positivity),
    hlate.eventually_lt_const (show δ < δ + ζ / 4 by linarith),
    hcoll.eventually_lt_const (show 0 < ζ / 4 by positivity)] with n hN hlateN hcollN
  rw [uniformVertex_collision (x n) (hx n).1 ((hx n).2 n le_rfl).le] at hcollN
  have hb := sampledCoalescence_probability_le (x n) (hx n).1 (hx n).2 hε
    (show 0 ≤ ζ / 4 by positivity) hN
  rw [Real.dist_eq, sub_zero, abs_of_nonneg measureReal_nonneg]
  exact hb.trans_lt (by linarith)

/-- The source normalization and absolute-value event, under the concrete
independent sample law. -/
theorem tendsto_normalized_sampledCoalescence_probability
    {x : ℕ → ℕ → ℤ} {α : ℝ} {g : ℝ → ℝ}
    (hx : AdmissibleArray x) (hαhalf : 1 / 2 < α) (hα1 : α < 1)
    (hL1 : HasL1ReciprocalProfile x α g) (hpos : PositiveProfile g)
    (h2 : HasLocalSquareMomentProfile x α g) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n ↦ (sampledReverseLaw (x n) n).real
      {q | ε < |(sourceCoalescenceTime n q.2.1 q.2.2 q.1 : ℝ) / n|})
      atTop (𝓝 0) := by
  apply (tendsto_sampledCoalescence_probability hx hαhalf hα1 hL1 hpos h2 hε).congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  congr 1
  ext q
  have hnonneg : 0 ≤ (sourceCoalescenceTime n q.2.1 q.2.2 q.1 : ℝ) / n :=
    div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  simp only [sampledCoalescenceEvent, mem_ofPred_eq]
  rw [abs_of_nonneg hnonneg, lt_div_iff₀ (show (0 : ℝ) < n by exact_mod_cast hn)]

/-- N10 with the paper's reciprocal profile and admissibility only at its
positive horizons; no extra row-zero hypothesis is imposed. -/
theorem tendsto_normalized_sampledCoalescence_probability_positive_horizons
    {x : ℕ → ℕ → ℤ} {α : ℝ} {f : ℝ → ℝ}
    (hx : ∀ n : ℕ, 0 < n → IsSigned (x n) ∧ SurvivesThrough (x n) n)
    (hαhalf : 1 / 2 < α) (hα1 : α < 1)
    (hf : ∀ᵐ t ∂profileMeasure, 0 < f t)
    (hL1 : HasL1ReciprocalProfile x α (fun t ↦ 1 / f t))
    (h2 : HasLocalSquareMomentProfile x α (fun t ↦ 1 / f t)) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n ↦ (sampledReverseLaw (x n) n).real
      {q | ε < |(sourceCoalescenceTime n q.2.1 q.2.2 q.1 : ℝ) / n|})
      atTop (𝓝 0) := by
  apply (tendsto_normalized_sampledCoalescence_probability (admissible_initialRowExtension hx)
    hαhalf hα1 (hasL1ReciprocalProfile_initialRowExtension hL1)
    (positiveProfile_reciprocal hf) (hasLocalSquareMomentProfile_initialRowExtension h2) hε).congr'
  filter_upwards [initialRowExtension_eventually_eq x] with n hn
  rw [hn]

end Freezing2
