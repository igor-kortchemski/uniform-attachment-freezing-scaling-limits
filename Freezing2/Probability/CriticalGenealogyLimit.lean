module

public import Freezing2.Probability.TrackedChainPath
public import Freezing2.Probability.VertexQuantileCoupling
public import Freezing2.Probability.ReverseLabelBridge

/-!
# Limits of coalescence-time events for tracked labels

For tracked labels with prescribed thresholds `γ j l`, the event that every scaled
coalescence time exceeds its threshold is an observation event of the tracked
connectivity chain: for `0 < γ < 1` the coalescence phase exceeds `γ n` exactly when
the two labels are connected at phase `⌊γ n⌋ + 1`, and negative thresholds impose no
constraint. Its probability is therefore the discrete observation recursion started
from the singleton state above all births.

For labels realized by the quantile coupling at distinct points `U j ∈ (0, 1)`
avoiding the thresholds, these probabilities converge, in the critical regime, to
the explicit limit `coalescenceLimit g U γ` built from the continuous propagators.
-/

@[expose] public section

open MeasureTheory Set Filter Topology

namespace Freezing2.CriticalGenealogy

open Freezing1 TrackedGenealogy ReverseCoalescence ReverseHistory

variable {k : ℕ}

/-- The off-diagonal thresholds lying strictly inside the unit interval. -/
noncomputable def obsTimes (γ : Fin k → Fin k → ℝ) : Finset ℝ :=
  open Classical in ((Finset.univ : Finset (Fin k × Fin k)).filter
    (fun p ↦ p.1 ≠ p.2 ∧ 0 < γ p.1 p.2 ∧ γ p.1 p.2 < 1)).image (fun p ↦ γ p.1 p.2)

/-- States in which every pair with threshold `τ` is connected. -/
noncomputable def obsSet (γ : Fin k → Fin k → ℝ) (τ : ℝ) : Set (Fin k → Fin k → Bool) :=
  {s | ∀ j l, j ≠ l → γ j l = τ → s j l = true}

/-- The state in which all tracked labels are singletons. -/
def diagState : Fin k → Fin k → Bool := fun j l ↦ decide (j = l)

/-- The point mass at the singleton state. -/
noncomputable def diagVec : (Fin k → Fin k → Bool) → ℝ :=
  open Classical in fun s ↦ if s = diagState then 1 else 0

/-- A time above all births and thresholds, below one when they are. -/
noncomputable def topTime (b : Fin k → ℝ) (T : Finset ℝ) : ℝ :=
  (1 + (Finset.univ.image b ∪ T).fold max 0 id) / 2

/-- The phase just above the scaled time `τ`. -/
noncomputable def phaseAbove (n : ℕ) (τ : ℝ) : ℕ := ⌊τ * n⌋₊ + 1

/-- The continuous limit of the probability that the coalescence times exceed the
off-diagonal thresholds `γ`, for births `b`. -/
noncomputable def coalescenceLimit (g : ℝ → ℝ) (b : Fin k → ℝ) (γ : Fin k → Fin k → ℝ) : ℝ :=
  ∑ s, contVec g b (obsSet γ) (obsTimes γ).card (obsTimes γ) (topTime b (obsTimes γ)) diagVec s

theorem mem_obsTimes {γ : Fin k → Fin k → ℝ} {τ : ℝ} :
    τ ∈ obsTimes γ ↔ ∃ j l, j ≠ l ∧ 0 < γ j l ∧ γ j l < 1 ∧ γ j l = τ := by
  classical
  simp only [obsTimes, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
    Prod.exists]
  constructor
  · rintro ⟨j, l, ⟨h1, h2, h3⟩, h4⟩
    exact ⟨j, l, h1, h2, h3, h4⟩
  · rintro ⟨j, l, h1, h2, h3, h4⟩
    exact ⟨j, l, ⟨h1, h2, h3⟩, h4⟩

theorem obsTimes_pos {γ : Fin k → Fin k → ℝ} {τ : ℝ} (h : τ ∈ obsTimes γ) : 0 < τ ∧ τ < 1 := by
  obtain ⟨j, l, _, h1, h2, rfl⟩ := mem_obsTimes.mp h
  exact ⟨h1, h2⟩

theorem le_topFold {b : Fin k → ℝ} {T : Finset ℝ} {y : ℝ}
    (hy : y ∈ Finset.univ.image b ∪ T) : y ≤ (Finset.univ.image b ∪ T).fold max 0 id :=
  (Finset.le_fold_max y).mpr (Or.inr ⟨y, hy, le_rfl⟩)

theorem topTime_lt_one {b : Fin k → ℝ} {T : Finset ℝ} (hb : ∀ j, b j < 1)
    (hT : ∀ τ ∈ T, τ < 1) : topTime b T < 1 := by
  have : (Finset.univ.image b ∪ T).fold max 0 id < 1 := by
    refine (Finset.fold_max_lt 1).mpr ⟨one_pos, fun y hy ↦ ?_⟩
    rcases Finset.mem_union.mp hy with h | h
    · obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp h
      exact hb j
    · exact hT y h
  unfold topTime
  linarith

theorem lt_topTime_of_mem {b : Fin k → ℝ} {T : Finset ℝ} {y : ℝ}
    (hy : y ∈ Finset.univ.image b ∪ T) (hy1 : y < 1) : y < topTime b T := by
  have := le_topFold hy
  unfold topTime
  linarith

theorem birth_lt_topTime {b : Fin k → ℝ} (T : Finset ℝ) (hb : ∀ j, b j < 1) (j : Fin k) :
    b j < topTime b T :=
  lt_topTime_of_mem (Finset.mem_union_left _ (Finset.mem_image_of_mem b (Finset.mem_univ j)))
    (hb j)

theorem obs_lt_topTime (b : Fin k → ℝ) {T : Finset ℝ} {τ : ℝ} (hτ : τ ∈ T) (hτ1 : τ < 1) :
    τ < topTime b T :=
  lt_topTime_of_mem (Finset.mem_union_right _ hτ) hτ1

theorem tendsto_phaseAbove_div {τ : ℝ} (hτ : 0 ≤ τ) :
    Tendsto (fun n : ℕ ↦ (phaseAbove n τ : ℝ) / n) atTop (𝓝 τ) := by
  have h1 : Tendsto (fun n : ℕ ↦ (⌊τ * n⌋₊ : ℝ) / n) atTop (𝓝 τ) := by
    simpa [Function.comp_def, mul_comm] using
      (tendsto_nat_floor_mul_div_atTop hτ).comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have h2 := h1.add (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))
  rw [add_zero] at h2
  apply h2.congr
  intro n
  simp only [phaseAbove, Nat.cast_add, Nat.cast_one, add_div]

/-- Thresholds in phases. -/
theorem lt_div_iff_phaseAbove {τ : ℝ} (hτ : 0 ≤ τ) {n : ℕ} (hn : 0 < n) (C : ℕ) :
    τ < (C : ℝ) / n ↔ phaseAbove n τ ≤ C := by
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  rw [lt_div_iff₀ hnr, phaseAbove, Nat.add_one_le_iff, Nat.floor_lt (by positivity)]

variable {x : SignSequence} {n : ℕ} {u : Fin k → ℕ ⊕ ℕ}

/-- On a history with the actual connectivity characterization, the tracked state
records the comparison of a phase with the coalescence phase. -/
theorem chainState_eq_true_iff {φ : ℕ} (hφ : φ ≤ n) {j l : Fin k} (hjl : j ≠ l)
    {ω : History}
    (hω : ∀ i ≤ commonBirth n (u j) (u l),
      connectedAt n (u j) (u l) i ω ↔ i ≤ coalescenceTime n (u j) (u l) ω) :
    chainState n u (n - φ) ω j l = true ↔ φ ≤ coalescenceTime n (u j) (u l) ω := by
  classical
  unfold chainState
  rw [show n - (n - φ) = φ by omega]
  by_cases hb : Born n φ u j ∧ Born n φ u l
  · have hcb : φ ≤ commonBirth n (u j) (u l) := le_min hb.1 hb.2
    simp only [trackedState, hb, and_self, ↓reduceIte, decide_eq_true_eq]
    rw [← hω φ hcb]
    rfl
  · simp only [trackedState, hb, ↓reduceIte, decide_eq_true_eq, hjl, false_iff, not_le]
    have hC := coalescenceTime_le_commonBirth n (u j) (u l) ω
    have : commonBirth n (u j) (u l) < φ := by
      simp only [Born, not_and_or, not_le] at hb
      unfold commonBirth
      rcases hb with h | h
      · exact lt_of_le_of_lt (min_le_left _ _) h
      · exact lt_of_le_of_lt (min_le_right _ _) h
    omega

theorem chainState_eq_diag {a : ℕ} (ha : a ≤ n)
    (hbirth : ∀ j, Freezing1.birthTime n (u j) < a) (ω : History) :
    chainState n u (n - a) ω = diagState := by
  classical
  funext j l
  unfold chainState
  rw [show n - (n - a) = a by omega]
  have hj : ¬ Born n a u j := by simp only [Born, not_le]; exact hbirth j
  simp [trackedState, hj, diagState]

/-- **Exact coalescence-threshold law.** -/
theorem jointLaw_coalescence_gt (hn : (n : ℕ∞) ≤ extinctionTime x)
    (hu : ∀ j, u j ∈ Freezing1.vertexLabels x n) (hinj : Function.Injective u)
    {γ : Fin k → Fin k → ℝ} (hγ0 : ∀ j l, j ≠ l → γ j l ≠ 0)
    (hγ1 : ∀ j l, j ≠ l → γ j l < 1)
    {a : ℕ} (ha : a ≤ n) (ha1 : 1 ≤ a)
    (hbirth : ∀ j, Freezing1.birthTime n (u j) < a)
    (hφa : ∀ τ ∈ obsTimes γ, phaseAbove n τ < a)
    (hmono : StrictMonoOn (phaseAbove n) (obsTimes γ)) :
    (jointLaw x n).real
        {ω | ∀ j l, j ≠ l → γ j l < (coalescenceTime n (u j) (u l) ω : ℝ) / n} =
      ∑ s, discVec x n u (obsSet γ) (phaseAbove n) (obsTimes γ).card (obsTimes γ) a
        diagVec s := by
  classical
  have hn0 : 0 < n := by omega
  have hpairs : ∀ᵐ ω ∂jointLaw x n, ∀ p : Fin k × Fin k,
      ∀ i ≤ commonBirth n (u p.1) (u p.2),
        connectedAt n (u p.1) (u p.2) i ω ↔ i ≤ coalescenceTime n (u p.1) (u p.2) ω :=
    ae_all_iff.mpr fun p ↦ jointLaw_connected_iff_le_coalescenceTime hn (hu p.1) (hu p.2)
  have hae : {ω | ∀ j l, j ≠ l → γ j l < (coalescenceTime n (u j) (u l) ω : ℝ) / n} =ᵐ[jointLaw x n]
      {ω | ∀ τ ∈ obsTimes γ, chainState n u (n - phaseAbove n τ) ω ∈ obsSet γ τ} := by
    filter_upwards [hpairs] with ω hω
    apply propext
    simp only [mem_ofPred_eq, obsSet]
    constructor
    · intro h τ hτ j l hjl hjτ
      have hτp := obsTimes_pos hτ
      rw [chainState_eq_true_iff ((hφa τ hτ).le.trans ha) hjl (hω (j, l))]
      rw [← lt_div_iff_phaseAbove hτp.1.le hn0, ← hjτ]
      exact h j l hjl
    · intro h j l hjl
      by_cases hneg : γ j l < 0
      · exact lt_of_lt_of_le hneg (by positivity)
      · have hpos : 0 < γ j l := lt_of_le_of_ne (not_lt.mp hneg) (hγ0 j l hjl).symm
        have hτ : γ j l ∈ obsTimes γ := mem_obsTimes.mpr ⟨j, l, hjl, hpos, hγ1 j l hjl, rfl⟩
        have := h (γ j l) hτ j l hjl rfl
        rw [chainState_eq_true_iff ((hφa _ hτ).le.trans ha) hjl (hω (j, l))] at this
        exact (lt_div_iff_phaseAbove hpos.le hn0 _).mpr this
  rw [measureReal_congr hae]
  have hobs := jointLaw_observe_eq_discVec hn hu hinj (obsSet γ) (phaseAbove n)
    (obsTimes γ).card (obsTimes γ) le_rfl a ha hφa hmono univ MeasurableSet.univ
  rw [univ_inter] at hobs
  rw [hobs]
  have hvec : (fun s ↦ (jointLaw x n).real (univ ∩ {ω | chainState n u (n - a) ω = s})) =
      diagVec := by
    funext s
    simp only [univ_inter, chainState_eq_diag ha hbirth, diagVec]
    by_cases hs : s = diagState
    · subst hs
      simp
    · have : {ω : History | diagState = s} = ∅ := by
        ext ω
        simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
        exact fun h ↦ hs h.symm
      simp [this, hs]
  rw [hvec]

theorem vertexQuantile_mem (x : ℕ → ℤ) (n : ℕ) (hN : 0 < vertexCount x n) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t < 1) : vertexQuantile x n t ∈ vertexLabels x n := by
  rw [← image_vertexAtIndex]
  apply Finset.mem_image_of_mem
  rw [Finset.mem_range, Nat.floor_lt (mul_nonneg ht0 (Nat.cast_nonneg _))]
  have hNr : (0 : ℝ) < vertexCount x n := by exact_mod_cast hN
  nlinarith

theorem vertexCount_pos {x : ℕ → ℤ} {n : ℕ} (hs : SurvivesThrough x n) : 0 < vertexCount x n := by
  rw [← card_vertexLabels]
  have h := hs n le_rfl
  exact Finset.card_pos.mpr ⟨.inr 1, Finset.inr_mem_disjSum.mpr
    (Finset.mem_Ioc.mpr ⟨zero_lt_one, by omega⟩)⟩

/-- Companion labels of the vertices selected by the quantile coupling at the points `U`. -/
noncomputable def coupledLabels (xa : ℕ → ℕ → ℤ) (n : ℕ) (U : Fin k → ℝ) : Fin k → ℕ ⊕ ℕ :=
  fun j ↦ toCompanionLabel (vertexQuantile (xa n) n (U j))

theorem topTime_nonneg (b : Fin k → ℝ) (T : Finset ℝ) : 0 ≤ topTime b T := by
  have : (0 : ℝ) ≤ (Finset.univ.image b ∪ T).fold max 0 id :=
    (Finset.le_fold_max 0).mpr (Or.inl le_rfl)
  unfold topTime
  linarith

/-- **Coalescence thresholds for coupled labels.** For distinct points `U j ∈ (0, 1)`
avoiding the thresholds, the probability that every scaled coalescence time of the
coupled labels exceeds its threshold converges to `coalescenceLimit g U γ`. -/
theorem tendsto_coalescence_gt {xa : ℕ → ℕ → ℤ} {g : ℝ → ℝ} (hx : AdmissibleArray xa)
    (hL1 : HasL1ReciprocalProfile xa (1 / 2) g) (hpos : PositiveProfile g)
    (h2 : HasLocalSquareMomentProfile xa (1 / 2) g)
    {γ : Fin k → Fin k → ℝ} (hγ0 : ∀ j l, j ≠ l → γ j l ≠ 0)
    (hγ1 : ∀ j l, j ≠ l → γ j l < 1)
    {U : Fin k → ℝ} (hU : ∀ j, 0 < U j ∧ U j < 1) (hUinj : Function.Injective U)
    (hUT : ∀ j, U j ∉ obsTimes γ) :
    Tendsto (fun n ↦ (jointLaw (companionSchedule (xa n)) n).real
        {ω | ∀ j l, j ≠ l → γ j l <
          (coalescenceTime n (coupledLabels xa n U j) (coupledLabels xa n U l) ω : ℝ) / n})
      atTop (𝓝 (coalescenceLimit g U γ)) := by
  classical
  set T := obsTimes γ with hTdef
  set t₀ := topTime U T with ht₀def
  set a : ℕ → ℕ := fun n ↦ phaseAbove n t₀
  set u : ℕ → Fin k → ℕ ⊕ ℕ := fun n ↦ coupledLabels xa n U
  have hT : ∀ τ ∈ T, 0 < τ ∧ τ < 1 := fun τ h ↦ obsTimes_pos h
  have ht₀1 : t₀ < 1 := topTime_lt_one (fun j ↦ (hU j).2) fun τ h ↦ (hT τ h).2
  have ht₀0 : 0 ≤ t₀ := topTime_nonneg U T
  have hUt₀ : ∀ j, U j < t₀ := birth_lt_topTime T (fun j ↦ (hU j).2)
  have hTt₀ : ∀ τ ∈ T, τ < t₀ := fun τ h ↦ obs_lt_topTime U h (hT τ h).2
  have hB : ∀ j, Tendsto (fun n ↦ (Freezing1.birthTime n (u n j) : ℝ) / n) atTop (𝓝 (U j)) := by
    intro j
    simp only [u, coupledLabels, companion_birthTime]
    exact (tendsto_birthTime_vertexQuantile hx (by norm_num) hL1 hpos (hU j).1 (hU j).2).2
  have ha : Tendsto (fun n ↦ (a n : ℝ) / n) atTop (𝓝 t₀) := tendsto_phaseAbove_div ht₀0
  -- eventual hypotheses of the exact formula
  have hinj : ∀ᶠ n in atTop, Function.Injective (u n) := by
    have hpair : ∀ p : Fin k × Fin k, ∀ᶠ n in atTop, p.1 ≠ p.2 → u n p.1 ≠ u n p.2 := by
      intro p
      by_cases hp : p.1 = p.2
      · exact Eventually.of_forall fun n h ↦ absurd hp h
      · have hne : U p.1 ≠ U p.2 := fun h ↦ hp (hUinj h)
        rcases lt_or_gt_of_ne hne with hlt | hgt
        · filter_upwards [eventually_lt_of_tendsto_div (hB p.1) (hB p.2) hlt] with n hn _ he
          rw [he] at hn
          exact lt_irrefl _ hn
        · filter_upwards [eventually_lt_of_tendsto_div (hB p.2) (hB p.1) hgt] with n hn _ he
          rw [he] at hn
          exact lt_irrefl _ hn
    filter_upwards [eventually_all.mpr hpair] with n hn j l hjl
    by_contra hne
    exact hn (j, l) hne hjl
  have hmem : ∀ n, ∀ j, u n j ∈ Freezing1.vertexLabels (companionSchedule (xa n)) n := by
    intro n j
    exact toCompanionLabel_mem (xa n) (hx n).1 (vertexQuantile_mem (xa n) n
      (vertexCount_pos (hx n).2) (hU j).1.le (hU j).2)
  have han : ∀ᶠ n in atTop, a n ≤ n := by
    filter_upwards [eventually_lt_mul_of_tendsto ha ht₀1, eventually_gt_atTop 0] with n hn hn0
    have : (a n : ℝ) < n := by simpa using hn
    exact_mod_cast this.le
  have hbirth : ∀ᶠ n in atTop, ∀ j, Freezing1.birthTime n (u n j) < a n :=
    eventually_all.mpr fun j ↦ eventually_lt_of_tendsto_div (hB j) ha (hUt₀ j)
  have hφa : ∀ᶠ n in atTop, ∀ τ ∈ T, phaseAbove n τ < a n :=
    (eventually_all_finset T).mpr fun τ hτ ↦
      eventually_lt_of_tendsto_div (tendsto_phaseAbove_div (hT τ hτ).1.le) ha (hTt₀ τ hτ)
  have hmono : ∀ᶠ n in atTop, StrictMonoOn (phaseAbove n) T := by
    have hp : ∀ᶠ n in atTop, ∀ p ∈ T ×ˢ T, p.1 < p.2 → phaseAbove n p.1 < phaseAbove n p.2 := by
      refine (eventually_all_finset _).mpr fun p hp ↦ ?_
      obtain ⟨h1, h2⟩ := Finset.mem_product.mp hp
      by_cases hlt : p.1 < p.2
      · exact (eventually_lt_of_tendsto_div (tendsto_phaseAbove_div (hT _ h1).1.le)
          (tendsto_phaseAbove_div (hT _ h2).1.le) hlt).mono fun n hn _ ↦ hn
      · exact Eventually.of_forall fun n h ↦ absurd h hlt
    filter_upwards [hp] with n hn τ hτ τ' hτ' hlt
    exact hn (τ, τ') (Finset.mem_product.mpr ⟨hτ, hτ'⟩) hlt
  have heq : ∀ᶠ n in atTop, (jointLaw (companionSchedule (xa n)) n).real
      {ω | ∀ j l, j ≠ l → γ j l < (coalescenceTime n (u n j) (u n l) ω : ℝ) / n} =
      ∑ s, discVec (companionSchedule (xa n)) n (u n) (obsSet γ) (phaseAbove n) T.card T (a n)
        diagVec s := by
    filter_upwards [hinj, han, hbirth, hφa, hmono] with n h1 h3 h4 h5 h6
    exact jointLaw_coalescence_gt (companion_before_extinction (xa n) (hx n).1 (hx n).2).le
      (hmem n) h1 hγ0 hγ1 h3 (Nat.succ_pos _) h4 h5 h6
  have hvec := tendsto_discVec_contVec hx hL1 hpos h2 hUinj hB (obsSet γ)
    (φ := fun n ↦ phaseAbove n) T.card T le_rfl
    (fun τ hτ ↦ ⟨(hT τ hτ).1, fun j h ↦ hUT j (h ▸ hτ),
      tendsto_phaseAbove_div (hT τ hτ).1.le⟩) t₀ ht₀1 hTt₀ a ha
    (fun j ↦ (eventually_lt_of_tendsto_div (hB j) ha (hUt₀ j)).mono fun n hn ↦
      ⟨fun h ↦ absurd (lt_of_le_of_lt h hn) (lt_irrefl _), fun h ↦ absurd h (not_le.mpr (hUt₀ j))⟩)
    (fun _ ↦ diagVec) diagVec tendsto_const_nhds
  have hsum : Tendsto (fun n ↦ ∑ s, discVec (companionSchedule (xa n)) n (u n) (obsSet γ)
      (phaseAbove n) T.card T (a n) diagVec s) atTop (𝓝 (coalescenceLimit g U γ)) :=
    tendsto_finsetSum _ fun s _ ↦ (continuous_apply s).continuousAt.tendsto.comp hvec
  exact hsum.congr' (heq.mono fun n h ↦ h.symm)

end Freezing2.CriticalGenealogy
