module

public import Freezing2.Analysis.PopulationLemma

public import Freezing2.Probability.CoalescenceHistory
public import Freezing2.Analysis.SubcriticalCoalescence
public import Freezing2.Analysis.SourceHypotheses

/-!
# Fast coalescence under the actual reverse joint law

The exact survival product is bounded by its exponential hazard sum and then
summed over every pair of actual vertex labels. A window of half the requested
length avoids the weak-inequality/integer-rounding endpoint in the manuscript's
displayed union bound. The analytic lower bound is used only after this concrete
probability estimate has been proved.
-/

@[expose] public section

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal Topology Classical

namespace Freezing2

open ReverseHistory ReverseCoalescence

/-- A genuine up-step hazard never exceeds one. -/
theorem companion_coalescenceHazard_le_one (x : ℕ → ℤ) (hx : IsSigned x) {n i : ℕ}
    (hs : SurvivesThrough x n) (hi : 0 < i) (hin : i ≤ n) :
    coalescenceHazard (companionSchedule x) i ≤ 1 := by
  simp only [coalescenceHazard, companionSchedule, companion_activeCount x hx,
    decide_eq_true_eq]
  split_ifs with hup
  · have htwo : (2 : ℝ) ≤ activeCount x i := by
      simpa only [Nat.sub_add_cancel hi] using
        activeCount_ge_two_of_up x hs (show i - 1 < n by omega)
          (by simpa only [Nat.sub_add_cancel hi] using hup)
    have hd : 0 < (activeCount x i : ℝ) * ((activeCount x i : ℝ) - 1) :=
      mul_pos (by linarith) (by linarith)
    apply (div_le_iff₀ hd).mpr
    nlinarith
  · norm_num

/-- The sum of concrete merger hazards is twice the paper's coalescence sum. -/
theorem sum_companion_coalescenceHazard (x : ℕ → ℤ) (hx : IsSigned x) (a m : ℕ) :
    (∑ i ∈ Finset.Ioc a (a + m), coalescenceHazard (companionSchedule x) i) =
      2 * coalescenceUpSum x a m := by
  have hI : Finset.Ioc a (a + m) = Finset.Ico (a + 1) (a + m + 1) := by
    ext i
    simp only [Finset.mem_Ioc, Finset.mem_Ico]
    omega
  rw [hI, sum_Ico_one_based_interval]
  simp only [coalescenceHazard, companionSchedule, companion_activeCount x hx,
    decide_eq_true_eq, coalescenceUpSum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> simp [div_eq_mul_inv]

/-- The survival product has the usual exponential bound, with all factors
proved nonnegative from the legal signed population walk. -/
theorem companion_survival_product_le_exp (x : ℕ → ℤ) (hx : IsSigned x) {n a m : ℕ}
    (hs : SurvivesThrough x n) (ham : a + m ≤ n) :
    (∏ i ∈ Finset.Ioc a (a + m), (1 - coalescenceHazard (companionSchedule x) i)) ≤
      Real.exp (-2 * coalescenceUpSum x a m) := by
  calc
    _ ≤ ∏ i ∈ Finset.Ioc a (a + m), Real.exp (-coalescenceHazard (companionSchedule x) i) := by
      apply Finset.prod_le_prod₀
      · intro i hi
        apply sub_nonneg.mpr
        exact companion_coalescenceHazard_le_one x hx hs
          (by have := (Finset.mem_Ioc.mp hi).1; omega) ((Finset.mem_Ioc.mp hi).2.trans ham)
      · intro i _
        exact Real.one_sub_le_exp_neg _
    _ = _ := by
      rw [← Real.exp_sum, Finset.sum_neg_distrib, sum_companion_coalescenceHazard x hx]
      congr 1
      ring

/-- Exact source-label tail bound under the actual joint history law. -/
theorem source_coalescence_tail_le_exp (x : ℕ → ℤ) (hx : IsSigned x) {n : ℕ}
    (hs : SurvivesThrough x n) {u v : VertexLabel}
    (hu : u ∈ vertexLabels x n) (hv : v ∈ vertexLabels x n) (huv : u ≠ v)
    {a m : ℕ} (hab : a + m = min (birthTime n u) (birthTime n v)) :
    (jointLaw (companionSchedule x) n).real {ω | sourceCoalescenceTime n u v ω < a} ≤
      Real.exp (-2 * coalescenceUpSum x a m) := by
  have huc := toCompanionLabel_mem x hx hu
  have hvc := toCompanionLabel_mem x hx hv
  have hne : toCompanionLabel u ≠ toCompanionLabel v := by
    intro h
    apply huv
    have h' := congrArg fromCompanionLabel h
    simpa only [from_toCompanionLabel hu, from_toCompanionLabel hv] using h'
  have hbirth : commonBirth n (toCompanionLabel u) (toCompanionLabel v) = a + m := by
    simpa only [commonBirth, companion_birthTime] using hab.symm
  have htail := coalescenceTime_lt_probability (companion_before_extinction x hx hs).le
    huc hvc hne (show a ≤ commonBirth n (toCompanionLabel u) (toCompanionLabel v) by
      rw [hbirth]; omega)
  change (jointLaw (companionSchedule x) n).real
    {ω | coalescenceTime n (toCompanionLabel u) (toCompanionLabel v) ω < a} ≤ _
  rw [htail, hbirth]
  apply companion_survival_product_le_exp x hx hs
  rw [hab]
  exact (min_le_left _ _).trans (birthTime_le x hu)

/-- Every legitimate window term is bounded by the deterministic finite maximum. -/
theorem coalescence_exp_le_unionBound (x : ℕ → ℕ → ℤ) (δ : ℝ) {n a m : ℕ}
    (ham : a + m ≤ n) (hlen : δ * n ≤ (m : ℝ)) :
    Real.exp (-2 * coalescenceUpSum (x n) a m) ≤
      subcriticalCoalescenceUnionBound x δ n / (((n : ℝ) + 1) ^ 2) := by
  have hapos : a < n + 1 := by omega
  have hmpos : m < n + 1 := by omega
  have hmax := Finset.le_sup'
    (s := (Finset.univ : Finset (Fin (n + 1) × Fin (n + 1))))
    (f := fun p ↦ if p.1.val + p.2.val ≤ n ∧ δ * n ≤ (p.2.val : ℝ) then
      ((n : ℝ) + 1) ^ 2 * Real.exp (-2 * coalescenceUpSum (x n) p.1.val p.2.val) else 0)
    (Finset.mem_univ ((⟨a, hapos⟩, ⟨m, hmpos⟩) : Fin (n + 1) × Fin (n + 1)))
  have hmax' : ((n : ℝ) + 1) ^ 2 * Real.exp (-2 * coalescenceUpSum (x n) a m) ≤
      subcriticalCoalescenceUnionBound x δ n := by
    simpa only [ham, hlen, and_self, ↓reduceIte, subcriticalCoalescenceUnionBound] using hmax
  apply (le_div_iff₀ (by positivity : 0 < ((n : ℝ) + 1) ^ 2)).mpr
  simpa only [mul_comm] using hmax'

/-- One pair's large-delay event, in the paper's displayed labels. -/
def slowPairEvent (n : ℕ) (ε : ℝ) (u v : VertexLabel) : Set History :=
  {ω | ε * n ≤ ((min (birthTime n u) (birthTime n v) : ℕ) : ℝ) - sourceCoalescenceTime n u v ω}

/-- The half-size window makes the tail inclusion valid even when `ε*n` is an integer. -/
theorem slowPair_probability_le_unionBound (x : ℕ → ℕ → ℤ) (hx : AdmissibleArray x)
    {n : ℕ} {ε : ℝ} (hlarge : 4 ≤ ε * (n : ℝ)) {u v : VertexLabel}
    (hu : u ∈ vertexLabels (x n) n) (hv : v ∈ vertexLabels (x n) n) :
    (jointLaw (companionSchedule (x n)) n).real (slowPairEvent n ε u v) ≤
      subcriticalCoalescenceUnionBound x (ε / 4) n / (((n : ℝ) + 1) ^ 2) := by
  have hq : 0 ≤ subcriticalCoalescenceUnionBound x (ε / 4) n / (((n : ℝ) + 1) ^ 2) :=
    div_nonneg (subcriticalCoalescenceUnionBound_nonneg x _ n) (sq_nonneg _)
  by_cases huv : u = v
  · subst v
    have he : slowPairEvent n ε u u = ∅ := by
      ext ω
      constructor
      · intro h
        have h' : ε * (n : ℝ) ≤ 0 := by simpa [slowPairEvent] using h
        linarith
      · intro h
        exact False.elim h
    rw [he, measureReal_empty]
    exact hq
  let b := min (birthTime n u) (birthTime n v)
  by_cases hb : (b : ℝ) < ε * n
  · have he : slowPairEvent n ε u v = ∅ := by
      ext ω
      constructor
      · intro h
        have h' : ε * (n : ℝ) ≤ (b : ℝ) - sourceCoalescenceTime n u v ω := h
        have hc : 0 ≤ (sourceCoalescenceTime n u v ω : ℝ) := Nat.cast_nonneg _
        linarith
      · intro h
        exact False.elim h
    rw [he, measureReal_empty]
    exact hq
  have hb' : ε * (n : ℝ) ≤ b := le_of_not_gt hb
  let m := ⌊ε * (n : ℝ) / 2⌋₊
  let a := b - m
  have hmupper : (m : ℝ) ≤ ε * n / 2 := Nat.floor_le (by linarith)
  have hmlower : ε / 4 * n ≤ (m : ℝ) := by
    have hf := Nat.lt_floor_add_one (ε * (n : ℝ) / 2)
    dsimp [m]
    nlinarith
  have hmb : m ≤ b := by exact_mod_cast (show (m : ℝ) ≤ b by linarith)
  have hab : a + m = b := Nat.sub_add_cancel hmb
  have hbn : b ≤ n := (min_le_left _ _).trans (birthTime_le (x n) hu)
  have hincl : slowPairEvent n ε u v ⊆ {ω | sourceCoalescenceTime n u v ω < a} := by
    intro ω hω
    have hω' : ε * n ≤ (b : ℝ) - sourceCoalescenceTime n u v ω := hω
    by_contra hnot
    have hc : (a : ℝ) ≤ sourceCoalescenceTime n u v ω := by exact_mod_cast (Nat.le_of_not_gt hnot)
    have hab' : (a : ℝ) + m = b := by exact_mod_cast hab
    nlinarith
  calc
    _ ≤ (jointLaw (companionSchedule (x n)) n).real
        {ω | sourceCoalescenceTime n u v ω < a} := measureReal_mono hincl
    _ ≤ Real.exp (-2 * coalescenceUpSum (x n) a m) :=
      source_coalescence_tail_le_exp (x n) (hx n).1 (hx n).2 hu hv huv hab
    _ ≤ _ := coalescence_exp_le_unionBound x (ε / 4) (by omega) hmlower

/-- All vertex-pair delay events, under one actual sampled reverse history. -/
def slowCoalescenceEvent (x : ℕ → ℤ) (n : ℕ) (ε : ℝ) : Set History :=
  ⋃ p ∈ (vertexLabels x n).product (vertexLabels x n), slowPairEvent n ε p.1 p.2

theorem measurableSet_slowPairEvent (n : ℕ) (ε : ℝ) (u v : VertexLabel) :
    MeasurableSet (slowPairEvent n ε u v) := by
  have hc : Measurable (fun ω : History ↦ (sourceCoalescenceTime n u v ω : ℝ)) :=
    (measurable_of_countable (fun k : ℕ ↦ (k : ℝ))).comp (measurable_sourceCoalescenceTime n u v)
  exact measurableSet_le measurable_const (measurable_const.sub hc)

theorem measurableSet_slowCoalescenceEvent (x : ℕ → ℤ) (n : ℕ) (ε : ℝ) :
    MeasurableSet (slowCoalescenceEvent x n ε) :=
  MeasurableSet.biUnion (Finset.countable_toSet _) (fun p _ ↦ measurableSet_slowPairEvent n ε p.1 p.2)

/-- The true number of pairs is at most the quadratic factor used in the
analytic bound; the proof uses the actual deterministic label count. -/
theorem vertexLabels_card_le_succ (x : ℕ → ℤ) (hx : IsSigned x) {n : ℕ}
    (hs : SurvivesThrough x n) : (vertexLabels x n).card ≤ n + 1 := by
  rw [vertexLabels_card x hx (hs n le_rfl).le]
  have h := upSteps_card_add_downSteps_card x hx (a := 0) (b := n)
  omega

/-- A finite union over all actual labels yields the deterministic uniform bound. -/
theorem slowCoalescence_probability_le_unionBound (x : ℕ → ℕ → ℤ) (hx : AdmissibleArray x)
    {n : ℕ} {ε : ℝ} (hlarge : 4 ≤ ε * (n : ℝ)) :
    (jointLaw (companionSchedule (x n)) n).real (slowCoalescenceEvent (x n) n ε) ≤
      subcriticalCoalescenceUnionBound x (ε / 4) n := by
  let q := subcriticalCoalescenceUnionBound x (ε / 4) n / (((n : ℝ) + 1) ^ 2)
  have hq : 0 ≤ q :=
    div_nonneg (subcriticalCoalescenceUnionBound_nonneg x _ n) (sq_nonneg _)
  have hc : (((vertexLabels (x n) n).product (vertexLabels (x n) n)).card : ℝ) ≤
      ((n : ℝ) + 1) ^ 2 := by
    rw [Finset.product_eq_sprod, Finset.card_product, Nat.cast_mul]
    have h := vertexLabels_card_le_succ (x n) (hx n).1 (hx n).2
    have h' : ((vertexLabels (x n) n).card : ℝ) ≤ (n : ℝ) + 1 := by exact_mod_cast h
    have hz : (0 : ℝ) ≤ (vertexLabels (x n) n).card := Nat.cast_nonneg _
    nlinarith
  calc
    _ ≤ ∑ p ∈ (vertexLabels (x n) n).product (vertexLabels (x n) n),
        (jointLaw (companionSchedule (x n)) n).real (slowPairEvent n ε p.1 p.2) :=
      measureReal_biUnion_finset_le _ _
    _ ≤ ∑ _p ∈ (vertexLabels (x n) n).product (vertexLabels (x n) n), q := by
      apply Finset.sum_le_sum
      intro p hp
      exact slowPair_probability_le_unionBound x hx hlarge (Finset.mem_product.mp hp).1
        (Finset.mem_product.mp hp).2
    _ = (((vertexLabels (x n) n).product (vertexLabels (x n) n)).card : ℝ) * q := by simp
    _ ≤ ((n : ℝ) + 1) ^ 2 * q := mul_le_mul_of_nonneg_right hc hq
    _ = _ := by
      dsimp [q]
      field_simp

/-- Source N08, in an equivalent all-pairs event formulation under the actual
reverse law. Every hypothesis is the source profile hypothesis. -/
theorem tendsto_slowCoalescence_probability
    {x : ℕ → ℕ → ℤ} {α : ℝ} {g : ℝ → ℝ}
    (hx : AdmissibleArray x) (hα0 : 0 < α) (hαhalf : α < 1 / 2)
    (hL1 : HasL1ReciprocalProfile x α g) (hpos : PositiveProfile g)
    (h2 : HasLocalSquareMomentProfile x α g) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n ↦ (jointLaw (companionSchedule (x n)) n).real
      (slowCoalescenceEvent (x n) n ε)) atTop (𝓝 0) := by
  have hlarge : ∀ᶠ n : ℕ in atTop, 4 ≤ ε * (n : ℝ) := by
    have h := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually (eventually_ge_atTop (4 / ε))
    filter_upwards [h] with n hn
    have h' := (div_le_iff₀ hε).mp hn
    simpa only [mul_comm] using h'
  apply squeeze_zero' (Eventually.of_forall fun _ ↦ measureReal_nonneg) ?_
    (tendsto_subcriticalCoalescenceUnionBound hx hα0 hαhalf hL1 hpos h2
      (show 0 < ε / 4 by positivity))
  filter_upwards [hlarge] with n hn
  exact slowCoalescence_probability_le_unionBound x hx hn

/-- The integer delay between common birth and coalescence. -/
noncomputable def coalescenceGap (n : ℕ) (u v : VertexLabel) (ω : History) : ℕ :=
  min (birthTime n u) (birthTime n v) - sourceCoalescenceTime n u v ω

theorem sourceCoalescenceTime_le_commonBirth (n : ℕ) (u v : VertexLabel) (ω : History) :
    sourceCoalescenceTime n u v ω ≤ min (birthTime n u) (birthTime n v) := by
  simpa only [sourceCoalescenceTime, commonBirth, companion_birthTime] using
    coalescenceTime_le_commonBirth n (toCompanionLabel u) (toCompanionLabel v) ω

theorem coalescenceGap_cast (n : ℕ) (u v : VertexLabel) (ω : History) :
    (coalescenceGap n u v ω : ℝ) =
      ((min (birthTime n u) (birthTime n v) : ℕ) : ℝ) - sourceCoalescenceTime n u v ω := by
  simp only [coalescenceGap, Nat.cast_sub (sourceCoalescenceTime_le_commonBirth n u v ω)]

/-- The natural delay is exactly the absolute real difference printed in N08. -/
theorem coalescenceGap_cast_eq_abs (n : ℕ) (u v : VertexLabel) (ω : History) :
    (coalescenceGap n u v ω : ℝ) =
      |((min (birthTime n u) (birthTime n v) : ℕ) : ℝ) - sourceCoalescenceTime n u v ω| := by
  rw [← coalescenceGap_cast, abs_of_nonneg (Nat.cast_nonneg _)]

/-- The source maximum over all actual vertex pairs, including its zero diagonal. -/
noncomputable def coalescenceGapMax (x : ℕ → ℤ) (n : ℕ) (ω : History) : ℕ :=
  ((vertexLabels x n).product (vertexLabels x n)).sup
    (fun p ↦ coalescenceGap n p.1 p.2 ω)

theorem measurable_coalescenceGapMax (x : ℕ → ℤ) (n : ℕ) :
    Measurable (coalescenceGapMax x n) := by
  have hg (p : VertexLabel × VertexLabel) : Measurable (coalescenceGap n p.1 p.2) :=
    (measurable_of_countable (fun k : ℕ ↦ min (birthTime n p.1) (birthTime n p.2) - k)).comp
      (measurable_sourceCoalescenceTime n p.1 p.2)
  have hm (s : Finset (VertexLabel × VertexLabel)) :
      Measurable (fun ω : History ↦ s.sup (fun p ↦ coalescenceGap n p.1 p.2 ω)) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert p s hp ih =>
      simpa only [Finset.sup_insert] using (hg p).max ih
  exact hm _

theorem coalescenceGapMax_le (x : ℕ → ℤ) (n : ℕ) (ω : History) :
    coalescenceGapMax x n ω ≤ n := by
  apply Finset.sup_le
  intro p hp
  exact (Nat.sub_le _ _).trans ((min_le_left _ _).trans
    (birthTime_le x (Finset.mem_product.mp hp).1))

/-- The event formulation and the displayed maximum are exactly equivalent. -/
theorem slowCoalescenceEvent_eq_max (x : ℕ → ℤ) (hx : IsSigned x) {n : ℕ}
    (hs : SurvivesThrough x n) (ε : ℝ) :
    slowCoalescenceEvent x n ε = {ω | ε * n ≤ (coalescenceGapMax x n ω : ℝ)} := by
  have hne := vertexLabels_nonempty x hx (hs n le_rfl).le
  have hpne : ((vertexLabels x n).product (vertexLabels x n)).Nonempty :=
    Finset.Nonempty.product hne hne
  ext ω
  simp only [slowCoalescenceEvent, slowPairEvent, Set.mem_iUnion, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨p, hp, hslow⟩
    have hgap : ε * n ≤ (coalescenceGap n p.1 p.2 ω : ℝ) := by
      rw [coalescenceGap_cast]
      exact hslow
    have hmax : coalescenceGap n p.1 p.2 ω ≤ coalescenceGapMax x n ω := by
      change coalescenceGap n p.1 p.2 ω ≤ ((vertexLabels x n).product (vertexLabels x n)).sup
        (fun q ↦ coalescenceGap n q.1 q.2 ω)
      exact Finset.le_sup (f := fun q : VertexLabel × VertexLabel ↦
        coalescenceGap n q.1 q.2 ω) hp
    exact hgap.trans (by exact_mod_cast hmax)
  · intro hmax
    obtain ⟨p, hp, heq⟩ := Finset.sup_mem_of_nonempty
      (f := fun p : VertexLabel × VertexLabel ↦ coalescenceGap n p.1 p.2 ω) hpne
    refine ⟨p, hp, ?_⟩
    change coalescenceGap n p.1 p.2 ω = coalescenceGapMax x n ω at heq
    rw [← coalescenceGap_cast, heq]
    exact hmax

/-- Source N08: the maximum coalescence delay divided by `n` converges to zero
in probability, under the actual constructed law for each row. -/
theorem tendsto_normalized_coalescenceGapMax_probability
    {x : ℕ → ℕ → ℤ} {α : ℝ} {g : ℝ → ℝ}
    (hx : AdmissibleArray x) (hα0 : 0 < α) (hαhalf : α < 1 / 2)
    (hL1 : HasL1ReciprocalProfile x α g) (hpos : PositiveProfile g)
    (h2 : HasLocalSquareMomentProfile x α g) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n ↦ (jointLaw (companionSchedule (x n)) n).real
      {ω | ε ≤ (coalescenceGapMax (x n) n ω : ℝ) / n}) atTop (𝓝 0) := by
  apply (tendsto_slowCoalescence_probability hx hα0 hαhalf hL1 hpos h2 hε).congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  rw [slowCoalescenceEvent_eq_max (x n) (hx n).1 (hx n).2 ε]
  congr 1
  ext ω
  exact (le_div_iff₀ (show (0 : ℝ) < n by exact_mod_cast hn)).symm

/-- The source-facing N08 statement requires admissibility only at the positive
horizons used in the manuscript and uses its reciprocal profile notation. -/
theorem tendsto_normalized_coalescenceGapMax_probability_positive_horizons
    {x : ℕ → ℕ → ℤ} {α : ℝ} {f : ℝ → ℝ}
    (hx : ∀ n : ℕ, 0 < n → IsSigned (x n) ∧ SurvivesThrough (x n) n)
    (hα0 : 0 < α) (hαhalf : α < 1 / 2)
    (hf : ∀ᵐ t ∂profileMeasure, 0 < f t)
    (hL1 : HasL1ReciprocalProfile x α (fun t ↦ 1 / f t))
    (h2 : HasLocalSquareMomentProfile x α (fun t ↦ 1 / f t)) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n ↦ (jointLaw (companionSchedule (x n)) n).real
      {ω | ε ≤ (coalescenceGapMax (x n) n ω : ℝ) / n}) atTop (𝓝 0) := by
  apply (tendsto_normalized_coalescenceGapMax_probability (admissible_initialRowExtension hx)
    hα0 hαhalf (hasL1ReciprocalProfile_initialRowExtension hL1)
    (positiveProfile_reciprocal hf) (hasLocalSquareMomentProfile_initialRowExtension h2) hε).congr'
  filter_upwards [initialRowExtension_eventually_eq x] with n hn
  rw [hn]

end Freezing2
