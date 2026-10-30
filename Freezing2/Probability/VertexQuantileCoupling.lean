module

public import Freezing2.Analysis.SignCounts
public import Freezing2.Discrete.Labels
public import Freezing2.Probability.UniformTransport
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Constructions.Pi

/-!
# A quantile coupling of uniform vertices with Lebesgue measure

The uniform law on the vertex labels at horizon `n` is the image of Lebesgue
measure on `[0, 1]` under an explicit quantile map: the index `⌊t N⌋` (with `N`
the number of vertices) selects the frozen label of the corresponding down-step
through the inverse of the down-step counting function, and the remaining indices
select active labels.

In a regime where down-steps have asymptotic density one half and the population
is sublinear, the scaled birth time of the label selected by `t ∈ (0, 1)` converges
to `t`. Consequently iid uniform vertices are realized on one probability space
(Lebesgue measure on the cube) so that their scaled birth times converge almost
surely; this replaces a Skorokhod representation for the sampled births.
-/

@[expose] public section

open MeasureTheory Set Filter Topology

namespace Freezing2

/-- The number of down-steps up to time `M`. -/
def downCount (x : ℕ → ℤ) (M : ℕ) : ℕ := (downSteps x 0 M).card

theorem downCount_mono (x : ℕ → ℤ) : Monotone (downCount x) := by
  intro M M' h
  apply Finset.card_le_card
  intro i hi
  simp only [downSteps, Finset.mem_filter, Finset.mem_Ioc] at hi ⊢
  exact ⟨⟨hi.1.1, hi.1.2.trans h⟩, hi.2⟩

theorem downCount_zero (x : ℕ → ℤ) : downCount x 0 = 0 := by
  simp [downCount, downSteps]

theorem downCount_succ (x : ℕ → ℤ) (M : ℕ) :
    downCount x (M + 1) = downCount x M + if x (M + 1) = -1 then 1 else 0 := by
  classical
  have hset : downSteps x 0 (M + 1) =
      if x (M + 1) = -1 then insert (M + 1) (downSteps x 0 M) else downSteps x 0 M := by
    ext i
    split_ifs with h <;>
      simp only [downSteps, Finset.mem_filter, Finset.mem_Ioc, Finset.mem_insert] <;>
      constructor <;> intro hi
    · by_cases hiM : i = M + 1
      · exact Or.inl hiM
      · exact Or.inr ⟨⟨hi.1.1, by omega⟩, hi.2⟩
    · rcases hi with hi | hi
      · subst hi
        exact ⟨⟨by omega, le_rfl⟩, h⟩
      · exact ⟨⟨hi.1.1, by omega⟩, hi.2⟩
    · refine ⟨⟨hi.1.1, ?_⟩, hi.2⟩
      by_contra hc
      have : i = M + 1 := by omega
      exact h (this ▸ hi.2)
    · exact ⟨⟨hi.1.1, by omega⟩, hi.2⟩
  unfold downCount
  rw [hset]
  split_ifs with h
  · rw [Finset.card_insert_of_notMem]
    simp [downSteps]
  · rfl

theorem downCount_succ_le (x : ℕ → ℤ) (M : ℕ) : downCount x (M + 1) ≤ downCount x M + 1 := by
  rw [downCount_succ]
  split_ifs <;> omega

theorem exists_lt_downCount {x : ℕ → ℤ} {n r : ℕ} (hr : r < downCount x n) :
    ∃ M, r < downCount x M := ⟨n, hr⟩

/-- The down-step at which the down-step count first exceeds `r`. -/
noncomputable def downQuantile (x : ℕ → ℤ) (n r : ℕ) : ℕ :=
  open Classical in if h : r < downCount x n then Nat.find (exists_lt_downCount h) else 0

theorem downQuantile_spec {x : ℕ → ℤ} {n r : ℕ} (hr : r < downCount x n) :
    r < downCount x (downQuantile x n r) ∧
      ∀ M < downQuantile x n r, downCount x M ≤ r := by
  classical
  simp only [downQuantile, dite_eq_left_of_eq_true (eq_true hr)]
  refine ⟨Nat.find_spec (exists_lt_downCount hr), fun M hM ↦ ?_⟩
  exact not_lt.mp (Nat.find_min (exists_lt_downCount hr) hM)

theorem downQuantile_le_iff {x : ℕ → ℤ} {n r : ℕ} (hr : r < downCount x n) (M : ℕ) :
    downQuantile x n r ≤ M ↔ r < downCount x M := by
  obtain ⟨h1, h2⟩ := downQuantile_spec hr
  constructor
  · intro h
    exact lt_of_lt_of_le h1 (downCount_mono x h)
  · intro h
    by_contra hc
    exact absurd (h2 M (not_le.mp hc)) (not_le.mpr h)

theorem downQuantile_le {x : ℕ → ℤ} {n r : ℕ} (hr : r < downCount x n) :
    downQuantile x n r ≤ n :=
  (downQuantile_le_iff hr n).mpr hr

theorem downQuantile_mem {x : ℕ → ℤ} {n r : ℕ} (hr : r < downCount x n) :
    downQuantile x n r ∈ downSteps x 0 n ∧ downCount x (downQuantile x n r) = r + 1 := by
  obtain ⟨h1, h2⟩ := downQuantile_spec hr
  set d := downQuantile x n r
  have hd0 : 0 < d := by
    by_contra h
    have : d = 0 := by omega
    rw [this, downCount_zero] at h1
    omega
  have hprev := h2 (d - 1) (by omega)
  have hsucc := downCount_succ x (d - 1)
  rw [show d - 1 + 1 = d by omega] at hsucc
  have hdown : x d = -1 := by
    by_contra hx
    simp only [hx, ↓reduceIte, add_zero] at hsucc
    omega
  simp only [hdown, ↓reduceIte] at hsucc
  refine ⟨?_, by omega⟩
  simp only [downSteps, Finset.mem_filter, Finset.mem_Ioc]
  exact ⟨⟨hd0, downQuantile_le hr⟩, hdown⟩

theorem downQuantile_downCount {x : ℕ → ℤ} {n d : ℕ} (hd : d ∈ downSteps x 0 n) :
    downCount x d - 1 < downCount x n ∧ downQuantile x n (downCount x d - 1) = d := by
  simp only [downSteps, Finset.mem_filter, Finset.mem_Ioc] at hd
  obtain ⟨⟨hd0, hdn⟩, hdown⟩ := hd
  have hsucc := downCount_succ x (d - 1)
  rw [show d - 1 + 1 = d by omega] at hsucc
  simp only [hdown, ↓reduceIte] at hsucc
  have hlt : downCount x d - 1 < downCount x n := by
    have := downCount_mono x hdn
    omega
  refine ⟨hlt, le_antisymm ?_ ?_⟩
  · exact (downQuantile_le_iff hlt d).mpr (by omega)
  · by_contra hc
    have := (downQuantile_le_iff hlt (d - 1)).mp (by omega)
    omega

/-- Index `r` of the vertex list: frozen labels in increasing order of their
down-steps, then the active labels. -/
noncomputable def vertexAtIndex (x : ℕ → ℤ) (n r : ℕ) : VertexLabel :=
  if r < downCount x n then .inl (downQuantile x n r) else .inr (r - downCount x n + 1)

/-- The number of vertex labels. -/
def vertexCount (x : ℕ → ℤ) (n : ℕ) : ℕ := downCount x n + (activeCount x n).toNat

theorem card_vertexLabels (x : ℕ → ℤ) (n : ℕ) : (vertexLabels x n).card = vertexCount x n := by
  simp [vertexLabels, vertexCount, downCount, Finset.card_disjSum]

theorem injOn_vertexAtIndex (x : ℕ → ℤ) (n : ℕ) :
    Set.InjOn (vertexAtIndex x n) (Finset.range (vertexCount x n) : Set ℕ) := by
  intro r hr r' hr' h
  simp only [vertexAtIndex] at h
  by_cases h1 : r < downCount x n <;> by_cases h2 : r' < downCount x n <;>
    simp only [h1, h2, ↓reduceIte, reduceCtorEq] at h
  · have e := Sum.inl.inj h
    have a1 := (downQuantile_mem h1).2
    have a2 := (downQuantile_mem h2).2
    rw [e] at a1
    omega
  · have e := Sum.inr.inj h
    omega

theorem image_vertexAtIndex (x : ℕ → ℤ) (n : ℕ) :
    (Finset.range (vertexCount x n)).image (vertexAtIndex x n) = vertexLabels x n := by
  classical
  ext v
  simp only [Finset.mem_image, Finset.mem_range, vertexLabels, vertexCount]
  constructor
  · rintro ⟨r, hr, rfl⟩
    unfold vertexAtIndex
    split_ifs with h
    · exact Finset.inl_mem_disjSum.mpr (downQuantile_mem h).1
    · exact Finset.inr_mem_disjSum.mpr (Finset.mem_Ioc.mpr ⟨by omega, by omega⟩)
  · intro hv
    cases v with
    | inl d =>
      have hd := Finset.inl_mem_disjSum.mp hv
      obtain ⟨hlt, heq⟩ := downQuantile_downCount hd
      exact ⟨downCount x d - 1, by omega, by simp [vertexAtIndex, hlt, heq]⟩
    | inr j =>
      have hj := Finset.mem_Ioc.mp (Finset.inr_mem_disjSum.mp hv)
      refine ⟨downCount x n + j - 1, by omega, ?_⟩
      simp only [vertexAtIndex, show ¬ downCount x n + j - 1 < downCount x n by omega,
        ↓reduceIte]
      congr 1
      omega

/-- The quantile map from `[0, 1]` to vertex labels. -/
noncomputable def vertexQuantile (x : ℕ → ℤ) (n : ℕ) (t : ℝ) : VertexLabel :=
  vertexAtIndex x n ⌊t * vertexCount x n⌋₊

theorem measurable_vertexQuantile (x : ℕ → ℤ) (n : ℕ) : Measurable (vertexQuantile x n) :=
  (measurable_from_top (f := vertexAtIndex x n)).comp
    ((measurable_id.mul_const _).nat_floor)

/-- Lebesgue measure on `[0, 1]` pushed by `t ↦ ⌊t N⌋` is uniform on `{0, …, N - 1}`. -/
theorem map_floor_mul_uniform {N : ℕ} (hN : 0 < N) :
    (volume.restrict (Icc (0 : ℝ) 1)).map (fun t : ℝ ↦ ⌊t * N⌋₊) =
      Measure.uniformOfFinset (Finset.range N) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hmeas : Measurable fun t : ℝ ↦ ⌊t * N⌋₊ := (measurable_id.mul_const _).nat_floor
  apply Measure.ext_of_singleton
  intro r
  rw [Measure.map_apply hmeas (measurableSet_singleton r),
    Measure.restrict_apply (hmeas (measurableSet_singleton r))]
  by_cases hr : r < N
  · rw [Measure.uniformOfFinset_apply_singleton_of_mem (Finset.mem_range.mpr hr),
      Finset.card_range]
    have hset : (fun t : ℝ ↦ ⌊t * N⌋₊) ⁻¹' {r} ∩ Icc 0 1 = Ico ((r : ℝ) / N) ((r + 1) / N) := by
      ext t
      simp only [mem_inter_iff, mem_preimage, mem_singleton_iff, mem_Icc, mem_Ico]
      constructor
      · rintro ⟨h, h0, _⟩
        have hfl := (Nat.floor_eq_iff (mul_nonneg h0 hNr.le)).mp h
        exact ⟨(div_le_iff₀ hNr).mpr hfl.1, (lt_div_iff₀ hNr).mpr hfl.2⟩
      · rintro ⟨h1, h2⟩
        have h1' := (div_le_iff₀ hNr).mp h1
        have h2' := (lt_div_iff₀ hNr).mp h2
        have ht0 : 0 ≤ t := le_trans (by positivity) h1
        refine ⟨(Nat.floor_eq_iff (mul_nonneg ht0 hNr.le)).mpr ⟨h1', h2'⟩, ht0, ?_⟩
        have : ((r : ℝ) + 1) / N ≤ 1 := by
          rw [div_le_one hNr]
          exact_mod_cast hr
        linarith
    rw [hset, Real.volume_Ico, show ((r : ℝ) + 1) / N - r / N = 1 / N by ring,
      ENNReal.ofReal_div_of_pos hNr, ENNReal.ofReal_one, ENNReal.ofReal_natCast, one_div]
  · rw [Measure.uniformOfFinset_apply_singleton_of_notMem (by simpa using hr)]
    apply measure_mono_null (t := {1})
    · intro t ht
      simp only [mem_inter_iff, mem_preimage, mem_singleton_iff, mem_Icc] at ht
      obtain ⟨h, h0, h1⟩ := ht
      have hfl := (Nat.floor_eq_iff (mul_nonneg h0 hNr.le)).mp h
      have hrN : (N : ℝ) ≤ r := by exact_mod_cast not_lt.mp hr
      have : (N : ℝ) ≤ t * N := hrN.trans hfl.1
      have ht1 : 1 ≤ t := by
        by_contra hc
        have := mul_lt_mul_of_pos_right (not_le.mp hc) hNr
        linarith
      exact le_antisymm h1 ht1
    · exact measure_singleton 1

/-- **Quantile coupling.** The uniform vertex law is the image of Lebesgue measure on
`[0, 1]` under `vertexQuantile`. -/
theorem map_vertexQuantile (x : ℕ → ℤ) (n : ℕ) (hN : 0 < vertexCount x n) :
    (volume.restrict (Icc (0 : ℝ) 1)).map (vertexQuantile x n) = uniformVertex x n := by
  classical
  have hmeas : Measurable fun t : ℝ ↦ ⌊t * vertexCount x n⌋₊ :=
    (measurable_id.mul_const _).nat_floor
  rw [show vertexQuantile x n = vertexAtIndex x n ∘ fun t : ℝ ↦ ⌊t * vertexCount x n⌋₊ from rfl,
    ← Measure.map_map measurable_from_top hmeas, map_floor_mul_uniform hN,
    map_uniformOfFinset_of_injOn _ _ measurable_from_top (injOn_vertexAtIndex x n),
    image_vertexAtIndex, uniformVertex]

section Limits

variable {x : ℕ → ℕ → ℤ} {α : ℝ} {g : ℝ → ℝ}

theorem tendsto_downCount_floor (hx : AdmissibleArray x) (hα : α < 1)
    (hL1 : HasL1ReciprocalProfile x α g) (hpos : PositiveProfile g)
    {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    Tendsto (fun n : ℕ ↦ (2 / (n : ℝ)) * downCount (x n) ⌊(n : ℝ) * θ⌋₊) atTop (𝓝 θ) := by
  simpa [downCount] using tendsto_downSteps_macroscopic hx hα hL1 hpos (a := 0) le_rfl hθ0 hθ1

theorem tendsto_vertexCount_div (hx : AdmissibleArray x) (hα : α < 1)
    (hL1 : HasL1ReciprocalProfile x α g) (hpos : PositiveProfile g) :
    Tendsto (fun n : ℕ ↦ (2 / (n : ℝ)) * vertexCount (x n) n) atTop (𝓝 1) := by
  have hd := tendsto_downCount_floor hx hα hL1 hpos zero_le_one le_rfl
  have ha := population_sublinear_at_nonneg hx hα hL1 hpos zero_le_one le_rfl
  have ha2 := ha.const_mul 2
  rw [mul_zero] at ha2
  have := hd.add ha2
  rw [add_zero] at this
  apply this.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hA : 0 ≤ activeCount (x n) n := by
    have := (hx n).2 n le_rfl
    omega
  simp only [mul_one, Nat.floor_natCast, vertexCount, Nat.cast_add]
  rw [show ((activeCount (x n) n).toNat : ℝ) = (activeCount (x n) n : ℝ) by
    exact_mod_cast Int.toNat_of_nonneg hA]
  ring

theorem tendsto_two_floor_mul_vertexCount (hx : AdmissibleArray x) (hα : α < 1)
    (hL1 : HasL1ReciprocalProfile x α g) (hpos : PositiveProfile g) {t : ℝ} (ht : 0 ≤ t) :
    Tendsto (fun n : ℕ ↦ (2 / (n : ℝ)) * (⌊t * vertexCount (x n) n⌋₊ : ℝ)) atTop (𝓝 t) := by
  have hV := tendsto_vertexCount_div hx hα hL1 hpos
  have hVtop : Tendsto (fun n : ℕ ↦ (vertexCount (x n) n : ℝ)) atTop atTop := by
    have h2 : Tendsto (fun n : ℕ ↦ ((n : ℝ) / 2) * ((2 / (n : ℝ)) * vertexCount (x n) n))
        atTop atTop :=
      (tendsto_natCast_atTop_atTop.atTop_div_const (by norm_num)).atTop_mul_pos one_pos hV
    apply h2.congr'
    filter_upwards [eventually_gt_atTop 0] with n hn
    have : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    field_simp
  have hfl : Tendsto (fun n : ℕ ↦ (⌊t * vertexCount (x n) n⌋₊ : ℝ) / vertexCount (x n) n)
      atTop (𝓝 t) := by
    have := (tendsto_nat_floor_mul_div_atTop ht).comp hVtop
    simpa [Function.comp_def, mul_comm] using this
  have := hfl.mul hV
  rw [mul_one] at this
  apply this.congr'
  filter_upwards [hVtop.eventually (eventually_gt_atTop 0)] with n hn
  field_simp

/-- **Births under the quantile coupling.** For `t ∈ (0, 1)`, the label selected
by `t` is eventually frozen and its scaled birth time converges to `t`. -/
theorem tendsto_birthTime_vertexQuantile (hx : AdmissibleArray x) (hα : α < 1)
    (hL1 : HasL1ReciprocalProfile x α g) (hpos : PositiveProfile g) {t : ℝ}
    (ht0 : 0 < t) (ht1 : t < 1) :
    (∀ᶠ n in atTop, ∃ d, vertexQuantile (x n) n t = .inl d) ∧
      Tendsto (fun n : ℕ ↦ (birthTime n (vertexQuantile (x n) n t) : ℝ) / n) atTop (𝓝 t) := by
  set r : ℕ → ℕ := fun n ↦ ⌊t * vertexCount (x n) n⌋₊
  have hr := tendsto_two_floor_mul_vertexCount hx hα hL1 hpos ht0.le
  have hD := tendsto_downCount_floor hx hα hL1 hpos zero_le_one le_rfl
  simp only [mul_one, Nat.floor_natCast] at hD
  -- eventually the index selects a frozen label
  have hfrozen : ∀ᶠ n in atTop, r n < downCount (x n) n := by
    filter_upwards [hr.eventually (gt_mem_nhds (show t < (t + 1) / 2 by linarith)),
      hD.eventually (lt_mem_nhds (show (t + 1) / 2 < 1 by linarith)), eventually_gt_atTop 0]
      with n h1 h2 hn
    have hnpos : (0 : ℝ) < 2 / n := by positivity
    have := lt_of_mul_lt_mul_left (h1.trans h2) hnpos.le
    exact_mod_cast this
  have hq : ∀ᶠ n in atTop, vertexQuantile (x n) n t = .inl (downQuantile (x n) n (r n)) := by
    filter_upwards [hfrozen] with n hn
    simp [vertexQuantile, vertexAtIndex, r, hn]
  refine ⟨hq.mono fun n h ↦ ⟨_, h⟩, ?_⟩
  -- the selected down-step is close to `t n`
  have hupper : ∀ ε > 0, ∀ᶠ n in atTop,
      (downQuantile (x n) n (r n) : ℝ) ≤ (t + ε) * n := by
    intro ε hε
    by_cases htε : 1 ≤ t + ε
    · filter_upwards [hfrozen] with n hn
      have := downQuantile_le hn
      calc (downQuantile (x n) n (r n) : ℝ) ≤ n := by exact_mod_cast this
        _ ≤ (t + ε) * n := le_mul_of_one_le_left (Nat.cast_nonneg _) htε
    · have hθ := tendsto_downCount_floor hx hα hL1 hpos (by linarith) (not_le.mp htε).le
      filter_upwards [hfrozen, hr.eventually (gt_mem_nhds (show t < t + ε / 2 by linarith)),
        hθ.eventually (lt_mem_nhds (show t + ε / 2 < t + ε by linarith)),
        eventually_gt_atTop 0] with n hn h1 h2 hn0
      have hnpos : (0 : ℝ) < 2 / n := by positivity
      have hlt : (r n : ℝ) < downCount (x n) ⌊(n : ℝ) * (t + ε)⌋₊ :=
        lt_of_mul_lt_mul_left (h1.trans h2) hnpos.le
      have hle := (downQuantile_le_iff hn _).mpr (by exact_mod_cast hlt)
      calc (downQuantile (x n) n (r n) : ℝ) ≤ ⌊(n : ℝ) * (t + ε)⌋₊ := by exact_mod_cast hle
        _ ≤ (n : ℝ) * (t + ε) := Nat.floor_le (by positivity)
        _ = (t + ε) * n := mul_comm _ _
  have hlower : ∀ ε > 0, ε < t → ∀ᶠ n in atTop,
      (t - ε) * n < (downQuantile (x n) n (r n) : ℝ) := by
    intro ε hε hεt
    have hθ := tendsto_downCount_floor hx hα hL1 hpos (by linarith) (by linarith : t - ε ≤ 1)
    filter_upwards [hfrozen, hr.eventually (lt_mem_nhds (show t - ε / 2 < t by linarith)),
      hθ.eventually (gt_mem_nhds (show t - ε < t - ε / 2 by linarith)),
      eventually_gt_atTop 0] with n hn h1 h2 hn0
    have hnpos : (0 : ℝ) < 2 / n := by positivity
    have hlt : (downCount (x n) ⌊(n : ℝ) * (t - ε)⌋₊ : ℝ) < r n :=
      lt_of_mul_lt_mul_left (h2.trans h1) hnpos.le
    have hnot : ¬ downQuantile (x n) n (r n) ≤ ⌊(n : ℝ) * (t - ε)⌋₊ := by
      rw [downQuantile_le_iff hn]
      exact not_lt.mpr (by exact_mod_cast hlt.le)
    have h3 : (n : ℝ) * (t - ε) < ⌊(n : ℝ) * (t - ε)⌋₊ + 1 := Nat.lt_floor_add_one _
    have h4 : ((⌊(n : ℝ) * (t - ε)⌋₊ + 1 : ℕ) : ℝ) ≤ downQuantile (x n) n (r n) := by
      exact_mod_cast not_le.mp hnot
    push_cast at h4
    linarith
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hε' : 0 < min (ε / 2) (t / 2) := lt_min (by linarith) (by linarith)
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp ((hupper (ε / 4) (by linarith)).and
    ((hlower (min (ε / 2) (t / 2)) hε' (lt_of_le_of_lt (min_le_right _ _) (by linarith))).and
      (hq.and ((eventually_gt_atTop 0).and
        (eventually_gt_atTop (⌈4 / ε⌉₊))))))
  refine ⟨N₁, fun n hn ↦ ?_⟩
  obtain ⟨h1, h2, h3, h4, h5⟩ := hN₁ n hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast h4
  rw [h3, birthTime_frozen, Real.dist_eq]
  have hd1 : 1 ≤ downQuantile (x n) n (r n) := by
    have := (downQuantile_mem (show r n < downCount (x n) n from by
      by_contra hc
      simp [vertexQuantile, vertexAtIndex, r, hc] at h3)).1
    simp only [downSteps, Finset.mem_filter, Finset.mem_Ioc] at this
    exact this.1.1
  rw [Nat.cast_sub hd1, Nat.cast_one]
  have hinv : 1 / (n : ℝ) < ε / 4 := by
    have hceil : 4 / ε ≤ ⌈4 / ε⌉₊ := Nat.le_ceil _
    have : (4 / ε : ℝ) < n := lt_of_le_of_lt hceil (by exact_mod_cast h5)
    rw [div_lt_iff₀ hnpos]
    rw [div_lt_iff₀ hε] at this
    linarith
  have hmin : min (ε / 2) (t / 2) ≤ ε / 2 := min_le_left _ _
  rw [abs_lt]
  constructor
  · have : (t - min (ε / 2) (t / 2)) * n < downQuantile (x n) n (r n) := h2
    have h' : t - ε / 2 < (downQuantile (x n) n (r n) : ℝ) / n := by
      rw [lt_div_iff₀ hnpos]
      nlinarith
    rw [sub_div]
    linarith
  · have h' : (downQuantile (x n) n (r n) : ℝ) / n ≤ t + ε / 4 := by
      rw [div_le_iff₀ hnpos]
      exact h1
    have : 0 ≤ 1 / (n : ℝ) := by positivity
    rw [sub_div]
    linarith

end Limits

end Freezing2
