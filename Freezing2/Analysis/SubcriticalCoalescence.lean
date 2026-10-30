module

public import Freezing2.Analysis.CoalescenceLimit
public import Freezing2.Analysis.ExponentialDecay
public import Mathlib.Topology.Order.Compact

/-!
# Deterministic bounds for fast subcritical coalescence

A macroscopic interval may reach either endpoint, whereas the reciprocal-square
hypothesis is only local inside `(0,1)`. The estimates here retain a shorter
interval in a fixed compact interior region before using Lemma `hnalpha(v)`.
No stochastic coalescence law or pairwise union bound is assumed or proved.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped Topology Classical BigOperators

namespace Freezing2

/-- An integrable function positive almost everywhere on a compact interval has
a positive common lower integral on all subintervals of a fixed positive length. -/
theorem exists_pos_uniform_interval_integral {f : ℝ → ℝ} {A B ℓ : ℝ}
    (hf : IntegrableOn f (Icc A B) volume)
    (hpos : ∀ᵐ t ∂volume.restrict (Icc A B), 0 < f t) (hℓ : 0 < ℓ) :
    ∃ c : ℝ, 0 < c ∧ ∀ u v : ℝ,
      A ≤ u → u ≤ v → v ≤ B → ℓ ≤ v - u → c ≤ ∫ t in Icc u v, f t := by
  let P : Set (ℝ × ℝ) := (Icc A B ×ˢ Icc A B) ∩ {p | ℓ ≤ p.2 - p.1}
  let F : ℝ × ℝ → ℝ := fun p ↦ (∫ t in Icc A p.2, f t) - ∫ t in Icc A p.1, f t
  have hcompact : IsCompact P :=
    (isCompact_Icc.prod isCompact_Icc).inter_right
      (isClosed_le continuous_const (continuous_snd.sub continuous_fst))
  have hcont : ContinuousOn F P := by
    have hp := intervalIntegral.continuousOn_primitive_Icc hf
    exact (hp.comp continuous_snd.continuousOn (fun _ h ↦ h.1.2)).sub
      (hp.comp continuous_fst.continuousOn (fun _ h ↦ h.1.1))
  have heq (u v : ℝ) (hu : A ≤ u) (huv : u ≤ v) (hv : v ≤ B) :
      F (u, v) = ∫ t in Icc u v, f t := by
    exact setIntegral_Icc_sub_left hu huv
      (hf.mono_set (fun _ ht ↦ ⟨ht.1, ht.2.trans hv⟩))
  have hpositive : ∀ p ∈ P, 0 < F p := by
    intro p hp
    have huv : p.1 < p.2 := by
      have hlen : ℓ ≤ p.2 - p.1 := hp.2
      linarith
    have hsub : Icc p.1 p.2 ⊆ Icc A B :=
      fun _ ht ↦ ⟨hp.1.1.1.trans ht.1, ht.2.trans hp.1.2.2⟩
    have hμ : (volume.restrict (Icc A B)) (Icc p.1 p.2) ≠ 0 := by
      rw [Measure.restrict_apply measurableSet_Icc, inter_eq_left.mpr hsub, Real.volume_Icc]
      exact ne_of_gt (ENNReal.ofReal_pos.mpr (sub_pos.mpr huv))
    have h := setIntegral_pos_of_ae_pos hf hpos hμ
    rw [Measure.restrict_restrict_of_subset hsub] at h
    simpa only [heq p.1 p.2 hp.1.1.1 huv.le hp.1.2.2] using h
  obtain ⟨c, hc, hbound⟩ := hcompact.exists_forall_le' hcont hpositive
  refine ⟨c, hc, ?_⟩
  intro u v hu huv hv hlen
  have hp : (u, v) ∈ P := ⟨⟨⟨hu, huv.trans hv⟩, ⟨hu.trans huv, hv⟩⟩, hlen⟩
  simpa only [heq u v hu huv hv] using hbound (u, v) hp

/-- Coalescence weights are nonnegative on every genuine upward step. -/
theorem coalescenceUpSum_term_nonneg (x : ℕ → ℤ) {N i : ℕ}
    (hs : SurvivesThrough x N) (hi : i < N) :
    0 ≤ (if x (i + 1) = 1 then
      ((activeCount x (i + 1) : ℝ) * ((activeCount x (i + 1) : ℝ) - 1))⁻¹ else 0) := by
  split_ifs with hup
  · have hS := activeCount_ge_two_of_up x hs hi hup
    have h₁ : 0 ≤ (activeCount x (i + 1) : ℝ) := by linarith
    have h₂ : 0 ≤ (activeCount x (i + 1) : ℝ) - 1 := by linarith
    exact inv_nonneg.mpr (mul_nonneg h₁ h₂)
  · exact le_rfl

/-- Enlarging the time interval increases the coalescence hazard sum. -/
theorem coalescenceUpSum_mono_interval (x : ℕ → ℤ) {N a m b k : ℕ}
    (hs : SurvivesThrough x N) (ham : a + m ≤ N)
    (hab : a ≤ b) (hbk : b + k ≤ a + m) :
    coalescenceUpSum x b k ≤ coalescenceUpSum x a m := by
  unfold coalescenceUpSum
  apply Finset.sum_le_sum_of_injOn (fun i ↦ b - a + i)
  · intro i _ j _ hij
    exact Nat.add_left_cancel hij
  · intro j hj
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
    apply Finset.mem_range.mpr
    have := Finset.mem_range.mp hi
    omega
  · intro i _
    have he : a + (b - a + i) + 1 = b + i + 1 := by omega
    simp only [he, le_refl]
  · intro i hi _
    exact coalescenceUpSum_term_nonneg x hs (by have := Finset.mem_range.mp hi; omega)

/-- Clip a long integer interval to a fixed interior region. Rounding loses
at most three steps, and the surviving real-time length stays uniformly positive. -/
theorem exists_interior_coalescence_interval {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) {N a m : ℕ} (hN : 0 < N)
    (hlarge : 12 ≤ ε * (N : ℝ)) (ham : a + m ≤ N) (hlen : ε * (N : ℝ) ≤ m) :
    ∃ l r : ℕ, a < l ∧ r ≤ a + m ∧
      CoalescenceInterval (ε / 8) N l r ∧
      ε / 2 ≤ (r : ℝ) / N - (l : ℝ) / N := by
  let δ : ℝ := ε / 8
  let l : ℕ := max (a + 1) (⌊δ * (N : ℝ)⌋₊ + 1)
  let r : ℕ := min (a + m) ⌊(1 - δ) * (N : ℝ)⌋₊
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδ1 : δ ≤ 1 / 8 := by dsimp [δ]; linarith
  have hl₁ : a + 1 ≤ l := le_max_left _ _
  have hl₂ : ⌊δ * (N : ℝ)⌋₊ + 1 ≤ l := le_max_right _ _
  have hr₁ : r ≤ a + m := min_le_left _ _
  have hr₂ : r ≤ ⌊(1 - δ) * (N : ℝ)⌋₊ := min_le_right _ _
  have hlfloor := Nat.floor_le (mul_nonneg hδ.le hNp.le)
  have hlfloor' := Nat.lt_floor_add_one (δ * (N : ℝ))
  have hrfloor := Nat.floor_le (mul_nonneg (show 0 ≤ 1 - δ by linarith) hNp.le)
  have hrfloor' := Nat.lt_floor_add_one ((1 - δ) * (N : ℝ))
  have hlupper : (l : ℝ) ≤ a + δ * N + 2 := by
    dsimp [l]
    rw [Nat.cast_max, Nat.cast_add, Nat.cast_one, Nat.cast_add, Nat.cast_one]
    apply max_le
    · nlinarith
    · nlinarith [(Nat.cast_nonneg a : (0 : ℝ) ≤ a)]
  have hrlower : (a : ℝ) + m - δ * N - 1 ≤ r := by
    dsimp [r]
    rw [Nat.cast_min, Nat.cast_add]
    apply le_min
    · nlinarith
    · have hsum : (a : ℝ) + m ≤ N := by exact_mod_cast ham
      nlinarith
  have hdiff : ε / 2 * (N : ℝ) ≤ (r : ℝ) - l := by
    dsimp [δ] at *
    nlinarith
  have hlr : l ≤ r := by
    have hrpos : (l : ℝ) < r := by nlinarith
    exact_mod_cast hrpos.le
  refine ⟨l, r, by omega, hr₁, ?_, ?_⟩
  · refine ⟨by omega, hlr, hr₁.trans ham, ?_, ?_⟩
    · have hl₂' : (⌊δ * (N : ℝ)⌋₊ : ℝ) + 1 ≤ l := by exact_mod_cast hl₂
      change δ * (N : ℝ) ≤ l
      linarith
    · have hr₂' : (r : ℝ) ≤ ⌊(1 - δ) * (N : ℝ)⌋₊ := by exact_mod_cast hr₂
      change (r : ℝ) ≤ (1 - δ) * N
      exact hr₂'.trans hrfloor
  · rw [← sub_div]
    exact (le_div_iff₀ hNp).mpr hdiff

/-- A positive polynomial lower bound on the cumulative coalescence hazard,
uniform over all macroscopic windows, including windows touching the endpoints. -/
theorem exists_uniform_coalescence_lower_bound
    {x : ℕ → ℕ → ℤ} {α : ℝ} {g : ℝ → ℝ}
    (hx : AdmissibleArray x) (hα0 : 0 < α) (hα1 : α < 1)
    (hL1 : HasL1ReciprocalProfile x α g) (hpos : PositiveProfile g)
    (h2 : HasLocalSquareMomentProfile x α g) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop, ∀ a m : ℕ,
      a + m ≤ N → ε * N ≤ (m : ℝ) →
        c * (N : ℝ) ^ (1 - 2 * α) ≤ coalescenceUpSum (x N) a m := by
  let δ : ℝ := ε / 8
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδsmall : δ ≤ 1 / 8 := by dsimp [δ]; linarith
  have hδgap : δ < 1 - δ := by linarith
  have hδ1 : 1 - δ < 1 := by linarith
  have hg2 := (h2 δ (1 - δ) hδ hδgap hδ1).1
  have hgpos : ∀ᵐ t ∂volume.restrict (Icc δ (1 - δ)), 0 < (g t) ^ 2 := by
    rw [← profileMeasure_restrict_Icc hδ.le (show 1 - δ ≤ 1 by linarith)]
    exact (ae_restrict_of_ae hpos).mono fun _ ht ↦ pow_pos ht 2
  obtain ⟨c, hc, hbound⟩ := exists_pos_uniform_interval_integral hg2 hgpos
    (show 0 < ε / 2 by positivity)
  refine ⟨c / 4, by positivity, ?_⟩
  have hlarge : ∀ᶠ N : ℕ in atTop, 12 ≤ ε * (N : ℝ) := by
    have h := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually
      (eventually_ge_atTop (12 / ε))
    filter_upwards [h] with N hN
    have h' := (div_le_iff₀ hε).mp hN
    simpa only [mul_comm] using h'
  filter_upwards [eventually_coalescenceIntervalError_lt hx hα0 hα1 hL1 hpos h2
      hδ (show 0 < c / 4 by positivity), hlarge, eventually_gt_atTop 0]
    with N herr hlarge hN
  intro a m ham hlen
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  obtain ⟨l, r, hal, hrm, hvalid, hlen'⟩ :=
    exists_interior_coalescence_interval hε hε1 hN hlarge ham hlen
  have he := herr l r hvalid
  rcases hvalid with ⟨hl1, hlr, hrN, hlo, hhi⟩
  have hI : c ≤ ∫ t in Icc ((l : ℝ) / N) ((r : ℝ) / N), (g t) ^ 2 := by
    apply hbound
    · exact (le_div_iff₀ hNp).mpr hlo
    · exact div_le_div_of_nonneg_right (by exact_mod_cast hlr) hNp.le
    · exact (div_le_iff₀ hNp).mpr hhi
    · exact hlen'
  let C : ℝ := (N : ℝ) ^ (2 * α) / N
  have hC : 0 < C := div_pos (Real.rpow_pos_of_pos hNp _) hNp
  have hsub : c / 4 ≤ C * coalescenceUpSum (x N) (l - 1) (r + 1 - l) := by
    change |C * coalescenceUpSum (x N) (l - 1) (r + 1 - l) -
      (∫ t in Icc ((l : ℝ) / N) ((r : ℝ) / N), (g t) ^ 2) / 2| < c / 4 at he
    have he' := (abs_lt.mp he).1
    linarith
  have hmono := coalescenceUpSum_mono_interval (x N) (hx N).2 ham
    (show a ≤ l - 1 by omega) (show l - 1 + (r + 1 - l) ≤ a + m by omega)
  have horig : c / 4 ≤ C * coalescenceUpSum (x N) a m :=
    hsub.trans (mul_le_mul_of_nonneg_left hmono hC.le)
  have hdiv : (c / 4) / C ≤ coalescenceUpSum (x N) a m :=
    (div_le_iff₀ hC).mpr (by simpa only [mul_comm] using horig)
  convert hdiv using 1
  dsimp [C]
  rw [Real.rpow_sub hNp, Real.rpow_one, div_div_eq_mul_div]
  ring

/-- The exponential bound decays uniformly over all macroscopic windows.
This is the deterministic analytic part of the fast-coalescence union bound. -/
theorem eventually_uniform_subcritical_coalescence_bound
    {x : ℕ → ℕ → ℤ} {α : ℝ} {g : ℝ → ℝ}
    (hx : AdmissibleArray x) (hα0 : 0 < α) (hαhalf : α < 1 / 2)
    (hL1 : HasL1ReciprocalProfile x α g) (hpos : PositiveProfile g)
    (h2 : HasLocalSquareMomentProfile x α g) {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) :
    ∀ᶠ N : ℕ in atTop, ∀ a m : ℕ, a + m ≤ N → ε * N ≤ (m : ℝ) →
      ((N : ℝ) + 1) ^ 2 * Real.exp (-2 * coalescenceUpSum (x N) a m) < η := by
  let ε₀ : ℝ := min ε 1
  have hε₀ : 0 < ε₀ := lt_min hε zero_lt_one
  obtain ⟨c, hc, hbound⟩ := exists_uniform_coalescence_lower_bound hx hα0 (by linarith)
    hL1 hpos h2 hε₀ (min_le_right ε 1)
  have hlim := tendsto_subcritical_pair_bound hαhalf (show 0 < 2 * c by positivity)
  filter_upwards [hbound, hlim.eventually_lt_const hη] with N hN hsmall
  intro a m ham hlen
  have hlen₀ : ε₀ * (N : ℝ) ≤ m :=
    (mul_le_mul_of_nonneg_right (min_le_left ε 1) (Nat.cast_nonneg N)).trans hlen
  have hu := hN a m ham hlen₀
  have he : Real.exp (-2 * coalescenceUpSum (x N) a m) ≤
      Real.exp (-(2 * c) * (N : ℝ) ^ (1 - 2 * α)) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  exact (mul_le_mul_of_nonneg_left he (sq_nonneg _)).trans_lt hsmall

/-- A finite maximum of the deterministic pair-bound terms. Zero represents
an empty family of macroscopic windows. -/
noncomputable def subcriticalCoalescenceUnionBound (x : ℕ → ℕ → ℤ) (ε : ℝ) (N : ℕ) : ℝ :=
  (Finset.univ : Finset (Fin (N + 1) × Fin (N + 1))).sup' Finset.univ_nonempty
    (fun p ↦ if p.1.val + p.2.val ≤ N ∧ ε * N ≤ (p.2.val : ℝ) then
      ((N : ℝ) + 1) ^ 2 * Real.exp (-2 * coalescenceUpSum (x N) p.1.val p.2.val)
      else 0)

theorem subcriticalCoalescenceUnionBound_nonneg (x : ℕ → ℕ → ℤ) (ε : ℝ) (N : ℕ) :
    0 ≤ subcriticalCoalescenceUnionBound x ε N := by
  unfold subcriticalCoalescenceUnionBound
  rw [Finset.le_sup'_iff]
  refine ⟨((0, 0) : Fin (N + 1) × Fin (N + 1)), Finset.mem_univ _, ?_⟩
  split_ifs <;> positivity

/-- The full deterministic uniform bound tends to zero in the subcritical regime.
Its interpretation as a probability bound still requires the stochastic law. -/
theorem tendsto_subcriticalCoalescenceUnionBound
    {x : ℕ → ℕ → ℤ} {α : ℝ} {g : ℝ → ℝ}
    (hx : AdmissibleArray x) (hα0 : 0 < α) (hαhalf : α < 1 / 2)
    (hL1 : HasL1ReciprocalProfile x α g) (hpos : PositiveProfile g)
    (h2 : HasLocalSquareMomentProfile x α g) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (subcriticalCoalescenceUnionBound x ε) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro η hη
  filter_upwards [eventually_uniform_subcritical_coalescence_bound hx hα0 hαhalf
    hL1 hpos h2 hε hη] with N hN
  rw [Real.dist_eq, sub_zero,
    abs_of_nonneg (subcriticalCoalescenceUnionBound_nonneg x ε N)]
  unfold subcriticalCoalescenceUnionBound
  rw [Finset.sup'_lt_iff]
  intro p _
  split_ifs with hp
  · exact hN p.1.val p.2.val hp.1 hp.2
  · exact hη

/-- The floor-length windows printed in the source are also covered uniformly;
the loss of one rounding step is absorbed by using the positive cutoff `ε/2`. -/
theorem eventually_uniform_floor_coalescence_bound
    {x : ℕ → ℕ → ℤ} {α : ℝ} {g : ℝ → ℝ}
    (hx : AdmissibleArray x) (hα0 : 0 < α) (hαhalf : α < 1 / 2)
    (hL1 : HasL1ReciprocalProfile x α g) (hpos : PositiveProfile g)
    (h2 : HasLocalSquareMomentProfile x α g) {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) :
    ∀ᶠ N : ℕ in atTop, ∀ b : ℕ, ⌊ε * (N : ℝ)⌋₊ + 1 ≤ b → b ≤ N →
      ((N : ℝ) + 1) ^ 2 * Real.exp
        (-2 * coalescenceUpSum (x N) (b - ⌊ε * (N : ℝ)⌋₊) ⌊ε * (N : ℝ)⌋₊) < η := by
  have hlarge : ∀ᶠ N : ℕ in atTop, 2 ≤ ε * (N : ℝ) := by
    have h := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually
      (eventually_ge_atTop (2 / ε))
    filter_upwards [h] with N hN
    have h' := (div_le_iff₀ hε).mp hN
    simpa only [mul_comm] using h'
  filter_upwards [eventually_uniform_subcritical_coalescence_bound hx hα0 hαhalf hL1 hpos h2
    (show 0 < ε / 2 by positivity) hη, hlarge] with N hN hlarge
  intro b hb hbN
  apply hN
  · omega
  · have hf := Nat.lt_floor_add_one (ε * (N : ℝ))
    nlinarith

end Freezing2
