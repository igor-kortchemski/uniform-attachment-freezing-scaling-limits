module

public import Freezing2.Probability.TrackedChain
public import Freezing2.Analysis.MatrixProductLimit
public import Freezing2.Probability.CriticalSurvivalProduct

/-!
# Continuous limit of the tracked connectivity chain

At an attachment step the transition matrix of the tracked connectivity chain is
`1 + h • G`, where `h` is the actual coalescence hazard and `G` is the Kingman
generator on the tracked labels already born; at a freezing step it is the
identity. In the critical regime, the hazards over a macroscopic window sum to
`∫ g²` (with `g = 1/f`) and are uniformly small, so the products over birth-free
windows converge to matrix exponentials.

The continuous propagator `propagator g b s t` of the time-inhomogeneous chain
with births `b` multiplies these exponentials over the successive birth-free
windows of `[s, t]`. The main theorem `tendsto_chainPower_propagator` shows that
the discrete transition matrices from phase `≈ tn` to phase `≈ sn` converge to it,
for actual tracked labels whose scaled birth phases converge to distinct limits.
-/

@[expose] public section

open MeasureTheory Set Filter Topology NormedSpace

namespace Freezing2.TrackedGenealogy

open Freezing1 ReverseCoalescence

variable {k : ℕ}

/-- The number of components of the labels in `β` in a connectivity state. -/
noncomputable def classesOn (β : Finset (Fin k)) (s : Fin k → Fin k → Bool) : ℕ :=
  open Classical in (β.image fun j ↦ β.filter fun l ↦ s j l = true).card

/-- `s'` merges two distinct components of labels in `β`. -/
def MergeOn (β : Finset (Fin k)) (s s' : Fin k → Fin k → Bool) : Prop :=
  ∃ j₀ ∈ β, ∃ l₀ ∈ β, s j₀ l₀ = false ∧ s' = mergeState s j₀ l₀

open Classical in
/-- The Kingman generator on tracked connectivity states with born labels `β`: every
pair of components merges at rate one. -/
noncomputable def kingGen (β : Finset (Fin k)) :
    Matrix (Fin k → Fin k → Bool) (Fin k → Fin k → Bool) ℝ :=
  fun s s' ↦ if s' = s then -((classesOn β s).choose 2 : ℝ) else if MergeOn β s s' then 1 else 0

variable {n p : ℕ} {u : Fin k → ℕ ⊕ ℕ} {x : SignSequence}

theorem stateClasses_eq_classesOn (s : Fin k → Fin k → Bool) :
    stateClasses n p u s = classesOn (bornSet n p u) s := by
  classical
  simp only [stateClasses, classesOn]

theorem isMerge_iff_mergeOn (s s' : Fin k → Fin k → Bool) :
    IsMerge n p u s s' ↔ MergeOn (bornSet n p u) s s' := by
  classical
  simp only [IsMerge, MergeOn, bornSet, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨j₀, l₀, hj, hl, hs, rfl⟩
    exact ⟨j₀, hj, l₀, hl, hs, rfl⟩
  · rintro ⟨j₀, hj, l₀, hl, hs, rfl⟩
    exact ⟨j₀, l₀, hj, hl, hs, rfl⟩

/-- The one-step matrix is `1 + h • G` with the actual coalescence hazard `h`. -/
theorem chainMatrix_eq (hn : (n : ℕ∞) ≤ extinctionTime x) (hp : p < n) :
    chainMatrix x n p u = 1 + coalescenceHazard x (p + 1) • kingGen (bornSet n (p + 1) u) := by
  classical
  ext s s'
  simp only [chainMatrix, chainStep, kingGen, Matrix.add_apply, Matrix.one_apply,
    Matrix.smul_apply, smul_eq_mul]
  rw [stateClasses_eq_classesOn, isMerge_iff_mergeOn]
  by_cases hx : x (p + 1) = true
  · rw [coalescenceHazard_eq_inv_choose hn (by omega) hx]
    by_cases hss : s' = s
    · subst hss
      simp only [hx, ↓reduceIte]
      ring
    · have hne : ¬ s = s' := fun h ↦ hss h.symm
      by_cases hm : MergeOn (bornSet n (p + 1) u) s s' <;> simp [hx, hss, hne, hm]
  · have hxf : x (p + 1) = false := by simpa using hx
    have h0 : coalescenceHazard x (p + 1) = 0 := by simp [coalescenceHazard, hxf]
    rw [h0]
    by_cases hss : s' = s
    · subst hss
      simp [hxf]
    · have hne : ¬ s = s' := fun h ↦ hss h.symm
      simp [hxf, hss, hne]

theorem chainPower_eq_orderedProd (x : SignSequence) (n a : ℕ) (u : Fin k → ℕ ⊕ ℕ) (d : ℕ) :
    chainPower x n a u d = orderedProd (fun i ↦ chainMatrix x n (a - (i + 1)) u) d := by
  induction d with
  | zero => rfl
  | succ d ih => rw [chainPower, ih, orderedProd]

/-- Transition matrices over consecutive windows multiply. -/
theorem chainPower_add (x : SignSequence) (n a : ℕ) (u : Fin k → ℕ ⊕ ℕ) (d e : ℕ) :
    chainPower x n a u (d + e) = chainPower x n a u d * chainPower x n (a - d) u e := by
  rw [chainPower_eq_orderedProd, chainPower_eq_orderedProd, chainPower_eq_orderedProd,
    orderedProd_add]
  congr 1
  apply orderedProd_congr
  intro i _
  rw [Nat.sub_sub, add_assoc]

theorem sum_range_sub_eq_sum_Icc (f : ℕ → ℝ) {a d : ℕ} (hd : d ≤ a) :
    ∑ i ∈ Finset.range d, f (a - i) = ∑ q ∈ Finset.Icc (a + 1 - d) a, f q := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [Finset.sum_range_succ, ih (by omega)]
    have hset : Finset.Icc (a + 1 - (d + 1)) a = insert (a - d) (Finset.Icc (a + 1 - d) a) := by
      ext q
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    rw [hset, Finset.sum_insert (by simp only [Finset.mem_Icc]; omega), add_comm]

theorem eventually_lt_mul_of_tendsto {a : ℕ → ℕ} {t r : ℝ}
    (ha : Tendsto (fun n ↦ (a n : ℝ) / n) atTop (𝓝 t)) (h : t < r) :
    ∀ᶠ n in atTop, (a n : ℝ) < r * n := by
  filter_upwards [ha.eventually (gt_mem_nhds h), eventually_gt_atTop 0] with n h1 h2
  have hn : (0 : ℝ) < n := by exact_mod_cast h2
  rwa [div_lt_iff₀ hn] at h1

theorem eventually_mul_lt_of_tendsto {a : ℕ → ℕ} {t r : ℝ}
    (ha : Tendsto (fun n ↦ (a n : ℝ) / n) atTop (𝓝 t)) (h : r < t) :
    ∀ᶠ n in atTop, r * n < a n := by
  filter_upwards [ha.eventually (lt_mem_nhds h), eventually_gt_atTop 0] with n h1 h2
  have hn : (0 : ℝ) < n := by exact_mod_cast h2
  rwa [lt_div_iff₀ hn] at h1

theorem eventually_lt_of_tendsto_div {v w : ℕ → ℕ} {r₁ r₂ : ℝ}
    (hv : Tendsto (fun n ↦ (v n : ℝ) / n) atTop (𝓝 r₁))
    (hw : Tendsto (fun n ↦ (w n : ℝ) / n) atTop (𝓝 r₂)) (h : r₁ < r₂) :
    ∀ᶠ n in atTop, v n < w n := by
  have hm1 : r₁ < (r₁ + r₂) / 2 := by linarith
  have hm2 : (r₁ + r₂) / 2 < r₂ := by linarith
  filter_upwards [eventually_lt_mul_of_tendsto hv hm1, eventually_mul_lt_of_tendsto hw hm2]
    with n h1 h2
  exact_mod_cast h1.trans h2

theorem tendsto_succ_div {c : ℕ → ℕ} {s : ℝ}
    (hc : Tendsto (fun n ↦ (c n : ℝ) / n) atTop (𝓝 s)) :
    Tendsto (fun n ↦ ((c n + 1 : ℕ) : ℝ) / n) atTop (𝓝 s) := by
  have h1 : Tendsto (fun n : ℕ ↦ (1 : ℝ) / n) atTop (𝓝 0) := tendsto_one_div_atTop_nhds_zero_nat
  simpa [add_div] using hc.add h1

/-- **Birth-free windows.** If the born tracked labels are the same `β` throughout
the window from phase `c n` to `a n`, the transition matrices converge to the
exponential of the integrated hazard times the Kingman generator on `β`. -/
theorem tendsto_chainPower_block {xa : ℕ → ℕ → ℤ} {g : ℝ → ℝ} (hx : AdmissibleArray xa)
    (hL1 : HasL1ReciprocalProfile xa (1 / 2) g) (hpos : PositiveProfile g)
    (h2 : HasLocalSquareMomentProfile xa (1 / 2) g)
    {s t : ℝ} (hs : 0 < s) (hst : s < t) (ht : t < 1)
    {a c : ℕ → ℕ} (ha : Tendsto (fun n ↦ (a n : ℝ) / n) atTop (𝓝 t))
    (hc : Tendsto (fun n ↦ (c n : ℝ) / n) atTop (𝓝 s))
    (u : ℕ → Fin k → ℕ ⊕ ℕ) (β : Finset (Fin k))
    (hβ : ∀ᶠ n in atTop, ∀ q, c n < q → q ≤ a n → bornSet n q (u n) = β) :
    Tendsto (fun n ↦ chainPower (companionSchedule (xa n)) n (a n) (u n) (a n - c n)) atTop
      (𝓝 (exp ((∫ τ in Icc s t, g τ ^ 2) • kingGen β))) := by
  set ε := min s (1 - t) / 2 with hεdef
  have hε : 0 < ε := by
    have : 0 < min s (1 - t) := lt_min hs (by linarith)
    linarith
  have hεs : ε < s := by
    have := min_le_left s (1 - t)
    linarith
  have hεt : t < 1 - ε := by
    have := min_le_right s (1 - t)
    linarith
  have hεhalf : ε < 1 / 2 := by
    have := min_le_left s (1 - t)
    have := min_le_right s (1 - t)
    linarith
  have hca : ∀ᶠ n in atTop, c n < a n := eventually_lt_of_tendsto_div hc ha hst
  have hwin : ∀ᶠ n in atTop, CoalescenceInterval ε n (c n + 1) (a n) := by
    filter_upwards [hca, eventually_lt_mul_of_tendsto ha (show t < 1 by linarith),
      eventually_lt_mul_of_tendsto ha hεt, eventually_mul_lt_of_tendsto hc hεs] with n h1 h2 h3 h4
    refine ⟨by omega, by omega, ?_, ?_, h3.le⟩
    · have : (a n : ℝ) < n := by simpa using h2
      exact_mod_cast this.le
    · push_cast
      linarith
  set h : ℕ → ℕ → ℝ := fun n i ↦ coalescenceHazard (companionSchedule (xa n)) (a n - i)
  have heq : ∀ᶠ n in atTop, chainPower (companionSchedule (xa n)) n (a n) (u n) (a n - c n) =
      orderedProd (fun i ↦ 1 + h n i • kingGen β) (a n - c n) := by
    filter_upwards [hwin, hβ] with n hn hβn
    rw [chainPower_eq_orderedProd]
    apply orderedProd_congr
    intro i hi
    have hext : (n : ℕ∞) ≤ extinctionTime (companionSchedule (xa n)) :=
      (companion_before_extinction (xa n) (hx n).1 (hx n).2).le
    rw [chainMatrix_eq hext (by have := hn.2.2.1; omega),
      show a n - (i + 1) + 1 = a n - i by omega, hβn (a n - i) (by omega) (by omega)]
  -- the hazard sums converge
  have hsum : Tendsto (fun n ↦ ∑ i ∈ Finset.range (a n - c n), h n i) atTop
      (𝓝 (∫ τ in Icc s t, g τ ^ 2)) := by
    apply (tendsto_critical_coalescence_hazard_sum hx hL1 hpos h2 hε hεhalf
      (tendsto_succ_div hc) ha hwin).congr'
    filter_upwards [hwin] with n hn
    simp only [h]
    rw [sum_range_sub_eq_sum_Icc (fun q ↦ coalescenceHazard (companionSchedule (xa n)) q)
      (by omega), show a n + 1 - (a n - c n) = c n + 1 by have := hn.2.1; omega]
  -- uniform smallness and nonnegativity of the hazards
  let M : ℕ → ℝ := fun n ↦ activeCount (xa n) (interiorMinimizer xa n ε (1 - ε))
  have hM : Tendsto M atTop atTop :=
    tendsto_interiorMinimum_atTop hx (by norm_num : (1 / 2 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1) hL1 hpos h2 hε (by linarith) (by linarith)
  have hmem : ∀ᶠ n in atTop, ∀ i < a n - c n,
      (a n - i ≤ n) ∧ M n ≤ (activeCount (xa n) (a n - i) : ℝ) := by
    filter_upwards [hwin] with n hn i hi
    rcases hn with ⟨hu1, huv, hvn, hlo, hhi⟩
    have himem : a n - i ∈ interiorTimes n ε (1 - ε) := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_range.mpr (by omega), ?_, ?_⟩
      · refine hlo.trans ?_
        exact_mod_cast (show c n + 1 ≤ a n - i by omega)
      · exact le_trans (by exact_mod_cast (show a n - i ≤ a n by omega)) hhi
    refine ⟨by omega, ?_⟩
    dsimp only [M]
    exact_mod_cast interiorMinimizer_min xa n ε (1 - ε) himem
  have hh : ∀ᶠ n in atTop, ∀ i < a n - c n, 0 ≤ h n i := by
    filter_upwards [hmem] with n hn i hi
    exact companion_coalescenceHazard_nonneg (xa n) (hx n).1 (hx n).2 (hn i hi).1
  have hmax : ∀ δ > 0, ∀ᶠ n in atTop, ∀ i < a n - c n, h n i ≤ δ := by
    intro δ hδ
    have hinv : Tendsto (fun n ↦ 4 * ((M n)⁻¹) ^ 2) atTop (𝓝 0) := by
      simpa using ((tendsto_inv_atTop_zero.comp hM).pow 2).const_mul 4
    filter_upwards [hmem, hM.eventually (eventually_ge_atTop 2),
      hinv.eventually (ge_mem_nhds hδ)] with n hn hMn hδn i hi
    exact (companion_coalescenceHazard_le_four_inv_sq (xa n) (hx n).1 (a n - i) hMn
      (hn i hi).2).trans hδn
  exact (tendsto_orderedProd_exp hh hsum hmax).congr' (heq.mono fun n h ↦ h.symm)

/-- Tracked labels born at time `t` of the continuous model. -/
noncomputable def bornAt (b : Fin k → ℝ) (t : ℝ) : Finset (Fin k) :=
  open Classical in Finset.univ.filter fun j ↦ t ≤ b j

/-- Tracked labels born strictly between `s` and `t`. -/
noncomputable def birthsIn (b : Fin k → ℝ) (s t : ℝ) : Finset (Fin k) :=
  open Classical in Finset.univ.filter fun j ↦ s < b j ∧ b j < t

/-- The continuous propagator from time `t` down to time `s`, peeling off at most
`m` births: on each birth-free window the exponential of the integrated hazard
`∫ g²` times the Kingman generator on the labels born at the top of the window. -/
noncomputable def propagatorAux (g : ℝ → ℝ) (b : Fin k → ℝ) (s : ℝ) :
    ℕ → ℝ → Matrix (Fin k → Fin k → Bool) (Fin k → Fin k → Bool) ℝ
  | 0, t => exp ((∫ τ in Icc s t, g τ ^ 2) • kingGen (bornAt b t))
  | m + 1, t =>
    if h : (birthsIn b s t).Nonempty then
      exp ((∫ τ in Icc ((birthsIn b s t).sup' h b) t, g τ ^ 2) • kingGen (bornAt b t)) *
        propagatorAux g b s m ((birthsIn b s t).sup' h b)
    else exp ((∫ τ in Icc s t, g τ ^ 2) • kingGen (bornAt b t))

/-- The continuous propagator of the tracked chain with births `b` and hazard
density `g²`, from time `t` down to time `s`. -/
noncomputable def propagator (g : ℝ → ℝ) (b : Fin k → ℝ) (s t : ℝ) :
    Matrix (Fin k → Fin k → Bool) (Fin k → Fin k → Bool) ℝ :=
  propagatorAux g b s k t

theorem eventually_bornSet_eq {u : ℕ → Fin k → ℕ ⊕ ℕ} {b : Fin k → ℝ} {t : ℝ}
    {a e : ℕ → ℕ}
    (htop : ∀ j, ∀ᶠ n in atTop, (a n ≤ Freezing1.birthTime n (u n j) ↔ t ≤ b j))
    (hlow : ∀ j, b j < t → ∀ᶠ n in atTop, Freezing1.birthTime n (u n j) ≤ e n) :
    ∀ᶠ n in atTop, ∀ q, e n < q → q ≤ a n → bornSet n q (u n) = bornAt b t := by
  classical
  have hlow' : ∀ j, ∀ᶠ n in atTop, b j < t → Freezing1.birthTime n (u n j) ≤ e n := by
    intro j
    by_cases hj : b j < t
    · exact (hlow j hj).mono fun n hn _ ↦ hn
    · exact Eventually.of_forall fun n h ↦ absurd h hj
  filter_upwards [eventually_all.mpr htop, eventually_all.mpr hlow'] with n h1 h3 q hq1 hq2
  ext j
  have hmemq : j ∈ bornSet n q (u n) ↔ q ≤ Freezing1.birthTime n (u n j) := by
    rw [bornSet, Finset.mem_filter]
    exact ⟨fun h ↦ h.2, fun h ↦ ⟨Finset.mem_univ _, h⟩⟩
  have hmemt : j ∈ bornAt b t ↔ t ≤ b j := by simp [bornAt]
  rw [hmemq, hmemt]
  constructor
  · intro hq
    by_contra hbt
    have := h3 j (lt_of_not_ge hbt)
    omega
  · intro hbt
    exact hq2.trans ((h1 j).mpr hbt)

theorem tendsto_chainPower_noBirths {xa : ℕ → ℕ → ℤ} {g : ℝ → ℝ} (hx : AdmissibleArray xa)
    (hL1 : HasL1ReciprocalProfile xa (1 / 2) g) (hpos : PositiveProfile g)
    (h2 : HasLocalSquareMomentProfile xa (1 / 2) g)
    {s t : ℝ} (hs : 0 < s) (hst : s < t) (ht : t < 1)
    {a c : ℕ → ℕ} (ha : Tendsto (fun n ↦ (a n : ℝ) / n) atTop (𝓝 t))
    (hc : Tendsto (fun n ↦ (c n : ℝ) / n) atTop (𝓝 s))
    {u : ℕ → Fin k → ℕ ⊕ ℕ} {b : Fin k → ℝ} (hbs : ∀ j, b j ≠ s)
    (hB : ∀ j, Tendsto (fun n ↦ (Freezing1.birthTime n (u n j) : ℝ) / n) atTop (𝓝 (b j)))
    (hempty : birthsIn b s t = ∅)
    (htop : ∀ j, ∀ᶠ n in atTop, (a n ≤ Freezing1.birthTime n (u n j) ↔ t ≤ b j)) :
    Tendsto (fun n ↦ chainPower (companionSchedule (xa n)) n (a n) (u n) (a n - c n)) atTop
      (𝓝 (exp ((∫ τ in Icc s t, g τ ^ 2) • kingGen (bornAt b t)))) := by
  classical
  apply tendsto_chainPower_block hx hL1 hpos h2 hs hst ht ha hc u (bornAt b t)
  apply eventually_bornSet_eq htop
  intro j hj
  have hjs : b j < s := by
    rcases lt_or_gt_of_ne (hbs j) with h | h
    · exact h
    · have : j ∈ birthsIn b s t := by simp [birthsIn, h, hj]
      simp [hempty] at this
  exact (eventually_lt_of_tendsto_div (hB j) hc hjs).mono fun n h ↦ h.le

/-- Induction on the number of births inside the window. -/
theorem tendsto_chainPower_propagatorAux {xa : ℕ → ℕ → ℤ} {g : ℝ → ℝ}
    (hx : AdmissibleArray xa) (hL1 : HasL1ReciprocalProfile xa (1 / 2) g)
    (hpos : PositiveProfile g) (h2 : HasLocalSquareMomentProfile xa (1 / 2) g)
    {s : ℝ} (hs : 0 < s) {c : ℕ → ℕ} (hc : Tendsto (fun n ↦ (c n : ℝ) / n) atTop (𝓝 s))
    {u : ℕ → Fin k → ℕ ⊕ ℕ} {b : Fin k → ℝ} (hb : Function.Injective b)
    (hbs : ∀ j, b j ≠ s)
    (hB : ∀ j, Tendsto (fun n ↦ (Freezing1.birthTime n (u n j) : ℝ) / n) atTop (𝓝 (b j))) :
    ∀ m : ℕ, ∀ t : ℝ, s < t → t < 1 → (birthsIn b s t).card ≤ m →
      ∀ a : ℕ → ℕ, Tendsto (fun n ↦ (a n : ℝ) / n) atTop (𝓝 t) →
      (∀ j, ∀ᶠ n in atTop, (a n ≤ Freezing1.birthTime n (u n j) ↔ t ≤ b j)) →
      Tendsto (fun n ↦ chainPower (companionSchedule (xa n)) n (a n) (u n) (a n - c n)) atTop
        (𝓝 (propagatorAux g b s m t)) := by
  classical
  intro m
  induction m with
  | zero =>
    intro t hst ht hcard a ha htop
    have hempty : birthsIn b s t = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hcard)
    exact tendsto_chainPower_noBirths hx hL1 hpos h2 hs hst ht ha hc hbs hB hempty htop
  | succ m ih =>
    intro t hst ht hcard a ha htop
    by_cases hne : (birthsIn b s t).Nonempty
    · rw [propagatorAux, dite_eq_left_of_eq_true (eq_true hne)]
      obtain ⟨jstar, hjmem, hjeq⟩ := Finset.exists_mem_eq_sup' hne b
      set cstar := (birthsIn b s t).sup' hne b with hcstar
      have hjb : s < b jstar ∧ b jstar < t := by simpa [birthsIn] using hjmem
      have hsc : s < cstar := hjeq ▸ hjb.1
      have hct : cstar < t := hjeq ▸ hjb.2
      set e : ℕ → ℕ := fun n ↦ Freezing1.birthTime n (u n jstar)
      have he : Tendsto (fun n ↦ (e n : ℝ) / n) atTop (𝓝 cstar) := hjeq ▸ hB jstar
      -- labels other than `jstar` and born below `t` are born below `cstar`
      have hbelow : ∀ j, j ≠ jstar → b j < t → b j < cstar := by
        intro j hj hjt
        by_cases hsj : s < b j
        · have hjmem' : j ∈ birthsIn b s t := by simp [birthsIn, hsj, hjt]
          have hle : b j ≤ cstar := Finset.le_sup' b hjmem'
          have hne' : b j ≠ cstar := fun h ↦ hj (hb (h.trans hjeq))
          exact lt_of_le_of_ne hle hne'
        · exact lt_of_le_of_lt (not_lt.mp hsj) hsc
      -- the top window
      have htopwin := tendsto_chainPower_block hx hL1 hpos h2 (hs.trans hsc) hct ht ha he u
        (bornAt b t) (eventually_bornSet_eq htop fun j hj ↦ by
          by_cases hjj : j = jstar
          · subst hjj
            exact Eventually.of_forall fun n ↦ le_rfl
          · exact (eventually_lt_of_tendsto_div (hB j) he (hbelow j hjj hj)).mono
              fun n h ↦ h.le)
      -- the remaining window, by induction
      have hcard' : (birthsIn b s cstar).card ≤ m := by
        have hsub : birthsIn b s cstar ⊆ (birthsIn b s t).erase jstar := by
          intro j hj
          have hj' : s < b j ∧ b j < cstar := by simpa [birthsIn] using hj
          refine Finset.mem_erase.mpr ⟨fun h ↦ ?_, ?_⟩
          · subst h
            exact lt_irrefl _ (hjeq ▸ hj'.2)
          · simp [birthsIn, hj'.1, hj'.2.trans hct]
        have := Finset.card_le_card hsub
        rw [Finset.card_erase_of_mem hjmem] at this
        omega
      have htop' : ∀ j, ∀ᶠ n in atTop,
          (e n ≤ Freezing1.birthTime n (u n j) ↔ cstar ≤ b j) := by
        intro j
        by_cases hjj : j = jstar
        · subst hjj
          exact Eventually.of_forall fun n ↦ by simp [e, hjeq]
        · have hne' : b j ≠ cstar := fun h ↦ hjj (hb (h.trans hjeq))
          rcases lt_or_gt_of_ne hne' with hlt | hgt
          · filter_upwards [eventually_lt_of_tendsto_div (hB j) he hlt] with n hn
            constructor
            · intro h
              omega
            · intro h
              exact absurd h (not_le.mpr hlt)
          · filter_upwards [eventually_lt_of_tendsto_div he (hB j) hgt] with n hn
            exact ⟨fun _ ↦ hgt.le, fun _ ↦ hn.le⟩
      have hrest := ih cstar hsc (hct.trans ht) hcard' e he htop'
      have hsplit : ∀ᶠ n in atTop,
          chainPower (companionSchedule (xa n)) n (a n) (u n) (a n - c n) =
            chainPower (companionSchedule (xa n)) n (a n) (u n) (a n - e n) *
              chainPower (companionSchedule (xa n)) n (e n) (u n) (e n - c n) := by
        filter_upwards [eventually_lt_of_tendsto_div hc he hsc,
          eventually_lt_of_tendsto_div he ha hct] with n h1 h2
        rw [show a n - c n = (a n - e n) + (e n - c n) by omega, chainPower_add,
          show a n - (a n - e n) = e n by omega]
      exact (htopwin.mul hrest).congr' (hsplit.mono fun n h ↦ h.symm)
    · rw [propagatorAux, dite_eq_right_of_eq_false (eq_false hne)]
      exact tendsto_chainPower_noBirths hx hL1 hpos h2 hs hst ht ha hc hbs hB
        (Finset.not_nonempty_iff_eq_empty.mp hne) htop

/-- **Continuous limit of the tracked chain.** For tracked labels whose scaled birth
phases converge to distinct limits `b`, none equal to `s`, the transition matrices of
the tracked connectivity chain from phases `a n ≈ tn` to `c n ≈ sn` converge to the
continuous propagator, provided the labels born at `a n` are eventually those born
at time `t`. -/
theorem tendsto_chainPower_propagator {xa : ℕ → ℕ → ℤ} {g : ℝ → ℝ}
    (hx : AdmissibleArray xa) (hL1 : HasL1ReciprocalProfile xa (1 / 2) g)
    (hpos : PositiveProfile g) (h2 : HasLocalSquareMomentProfile xa (1 / 2) g)
    {s t : ℝ} (hs : 0 < s) (hst : s < t) (ht : t < 1)
    {a c : ℕ → ℕ} (ha : Tendsto (fun n ↦ (a n : ℝ) / n) atTop (𝓝 t))
    (hc : Tendsto (fun n ↦ (c n : ℝ) / n) atTop (𝓝 s))
    {u : ℕ → Fin k → ℕ ⊕ ℕ} {b : Fin k → ℝ} (hb : Function.Injective b)
    (hbs : ∀ j, b j ≠ s)
    (hB : ∀ j, Tendsto (fun n ↦ (Freezing1.birthTime n (u n j) : ℝ) / n) atTop (𝓝 (b j)))
    (htop : ∀ j, ∀ᶠ n in atTop, (a n ≤ Freezing1.birthTime n (u n j) ↔ t ≤ b j)) :
    Tendsto (fun n ↦ chainPower (companionSchedule (xa n)) n (a n) (u n) (a n - c n)) atTop
      (𝓝 (propagator g b s t)) :=
  tendsto_chainPower_propagatorAux hx hL1 hpos h2 hs hc hb hbs hB k t hst ht
    ((Finset.card_le_univ _).trans (by simp)) a ha htop

end Freezing2.TrackedGenealogy
