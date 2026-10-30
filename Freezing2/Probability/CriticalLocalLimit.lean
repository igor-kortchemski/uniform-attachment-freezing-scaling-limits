module

public import Freezing2.Probability.CoalescentForests
public import Freezing2.Probability.AuxiliaryAttachmentRate
public import Freezing2.Probability.CriticalSurvivalProduct

/-!
# The critical local limit `eq:cv locale` (inventory N12a), corrected

This file formalizes the local limit lemma containing the display `eq:cv locale` of
`attachement-uniforme-2-final.tex` (lines 1305–1470), in a corrected form that addresses the
defects S10 of the source inventory.

## The corrected statement

Fix `k > r ≥ 0`, set `m = k - 1 - r` (the number of merges above the cutoff), and fix a cutoff
`ε > 0`. For integer birth phases `b` and merge phases `c` (listed from the top), and a merge
history `xs : Fin m → ConnState k` (non-plane, leaf-labelled ranked forest, as in
`CoalescentDensity`), `scaledPatternProb xa n ε xs b c` is `(n/2)^m` times the conditional
probability, given that the sampled vertices are the distinct frozen vertices born at `b`, that
the genealogy of the sampled vertices consists, at the phases above `ε n`, of exactly the `m`
merges of `xs` at the phases `c`. Equivalently, `R^n(ε) = r` merges occur at phases `≤ ε n` and
the merges above `ε n` form `xs`. For a forest `F₀ ∈ 𝔉⁺_{r,k}` (`SourceForest r k`),
`scaledForestProb` sums this over the histories compatible with `F₀` for the order of the event
times: it is the rescaled probability that the merges above `ε n` form `F₀` up to the orders of
the children.

* `critical_local_limit_forest`: at the source's samples (iid uniform down-step births `B̃ⁿ`, iid
  uniform up-step merge phases `C̃ⁿ`, `sourceSampleLaw`), the law of `scaledForestProb`
  converges weakly as `n → ∞` (for each `ε > 0`), and then as `ε → 0⁺`, to the law of
  `2^(k-1-r) g_{r,k}(F₀, B, C)` at independent uniform times (`sourceDensity`, with `g = 1/f`).
* `critical_local_limit`: the same for a single merge history, with limit the non-plane density
  `historyDensity g B m xs C`.

The factor `2^(k-1-r)` is the number of child orders, which the discrete event does not
prescribe (see below).

## Corrections (S10)

* All `k` births are conditioned on (the statement's `r` conditioning variables at line 1327
  were a typo).
* Iid samples may collide: the corrected event requires distinct frozen vertices, and the
  probability is `0` otherwise. The conditional probability is taken given the sampled vertices
  (`sampledReverseVectorLaw_patternEvent`); their own probability `N^{-k}` differs from the
  source's normalization `(2/n)^k` by a factor tending to one (`sourceNormalization_eq`,
  `tendsto_vertexFactor`).
* `R^n(ε)` is the number of merges at phases `≤ ε n`, and the `m` prescribed merges lie strictly
  above `ε n`.
* The discrete quantities are functions of integer phases; the scaled inputs of the limit enter
  through `⌊n β⌋₊`, `⌊n γ⌋₊` (`floorBirths`, `floorMerges`).
* The merge factors `n / (S (S - 1))` at the sampled merge phases are not functions of the
  limiting locations (`g` is only measurable), so convergence of locations alone cannot give
  their limit `g(γ)²`. They enter as marks whose joint law with the locations converges
  (`tendsto_auxiliary_birth_and_rates`), and the local functional converges continuously in
  locations and marks (`tendsto_discFun`).

## Main results

* `jointLaw_chainPath`: the probability of a path of the tracked connectivity chain is the
  product of its one-step transition probabilities.
* `jointLaw_patternEvent`: **the exact discrete pattern probability**, the product of the merge
  hazards `1 / C(S, 2)` at the merge phases and of the survival factors `1 - C(a, 2) / C(S, 2)`
  at the other phases, `a` being the number of clusters (`stepWeight`).
* `scaledPatternProb_eq`: the rescaled probability is the product of the exact merge rates
  `n / (S (S - 1))` and of `survivalFactor`.
* `tendsto_survivalFactor`: for converging configurations the survival factor converges to
  `exp (-∫_ε^1 C(a(t), 2) g(t)² dt)`.
* `tendsto_discFun`: **pointwise (continuous) convergence** of the local functional `discFun`
  (with the merge rates as marks) to the limit functional `limitFun` at every configuration with
  distinct times in `(0, 1)` avoiding the cutoff.
* `tendsto_map_of_continuousConvergence`: an extended continuous mapping theorem.
* `tendsto_localLaw`, `eventually_map_discFun_eq`: **convergence in distribution** at a fixed
  cutoff, and the identification of the discrete law with the law of `scaledPatternProb` at the
  source's samples.
* `tendsto_limitLaw_zero`, `limitLocalLaw_map_limitFun0`: removal of the cutoff and
  identification of the limit with `historyDensity`.
* `sum_historyDensity_forest`: summing `historyDensity` over the histories compatible with
  `F₀` gives `2^(k-1-r) g_{r,k}(F₀, ·)`; the forest results `tendsto_localLawForest`,
  `tendsto_limitLawForest_zero`, `limitLocalLaw_map_limitFun0Forest`.

## Scope

The plane structure (the order of the children of a merge, given by which root survives it) is
not tracked by the connectivity chain here, so this file's forest statement carries the factor
`2^(k-1-r)`. The plane form, with `g_{r,k}(F₀, ·)` itself, is `critical_local_limit_plane` in
`CriticalLocalLimitPlane`: each orientation of a merge has probability `1 / (S (S - 1))`. The
finite decoding of the discrete event to the source's forest `𝓕ⁿ_r` and ordered times `Cⁿ_j` is
not formalized (`ae_patternEvent_iff_coalescenceTimes` identifies the event with truncated
pairwise coalescence times). The joint convergence `cv coalescent` (N12b) is proved elsewhere
by another route.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace Freezing2.CriticalLocalLimit

open Freezing1 TrackedGenealogy ReverseCoalescence ReverseHistory CriticalGenealogy
  CoalescentDensity

variable {k m : ℕ}

/-- The number of entries of `e` that are at least `i`. -/
noncomputable def countAbove {ι α : Type*} [Fintype ι] [LinearOrder α] (e : ι → α) (i : α) : ℕ :=
  open Classical in (Finset.univ.filter fun q ↦ i ≤ e q).card

theorem countAbove_le {ι α : Type*} [Fintype ι] [LinearOrder α] (e : ι → α) (i : α) :
    countAbove e i ≤ Fintype.card ι := by
  classical
  unfold countAbove
  convert Finset.card_filter_le (Finset.univ : Finset ι) _
  simp

/-- **States of a history listed by the number of merges above a time.** For strictly
decreasing merge times, the state of the history at time `u` is the state after the merges
at times `≥ u`. -/
theorem stateAt_eq_cons {m : ℕ} : ∀ {t : ℝ} {x : ConnState k} {xs : Fin m → ConnState k}
    {cs : Fin m → ℝ}, StrictAnti cs → ∀ (u : ℝ) (h : countAbove cs u < m + 1),
      stateAt m t x xs cs u = (Fin.cons x xs : Fin (m + 1) → ConnState k) ⟨_, h⟩ := by
  classical
  induction m with
  | zero =>
    intro t x xs cs _ u h
    have : (⟨countAbove cs u, h⟩ : Fin (0 + 1)) = 0 := Fin.ext (by simp [countAbove])
    rw [this, Fin.cons_zero]
    rfl
  | succ m ih =>
    intro t x xs cs hcs u h
    have hcount : countAbove cs u =
        (if u ≤ cs 0 then 1 else 0) + countAbove (Fin.tail cs) u := by
      unfold countAbove
      rw [Finset.card_filter, Finset.card_filter, Fin.sum_univ_succ]
      rfl
    have htail : StrictAnti (Fin.tail cs) := hcs.comp_strictMono (Fin.strictMono_succ)
    by_cases hu : cs 0 < u
    · have hzero : countAbove cs u = 0 := by
        unfold countAbove
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro i _ hi
        exact absurd (hi.trans (hcs.antitone (Fin.zero_le i))) (not_le.mpr hu)
      have : (⟨countAbove cs u, h⟩ : Fin (m + 1 + 1)) = 0 := Fin.ext hzero
      rw [this, Fin.cons_zero]
      simp only [stateAt, hu, ↓reduceIte]
    · have hle : u ≤ cs 0 := not_lt.mp hu
      simp only [hle, ↓reduceIte] at hcount
      have h' : countAbove (Fin.tail cs) u < m + 1 := by omega
      have hst : stateAt (m + 1) t x xs cs u =
          stateAt m (cs 0) (xs 0) (Fin.tail xs) (Fin.tail cs) u := by
        simp only [stateAt, hu, ↓reduceIte]
      rw [hst, ih htail u h']
      have : (⟨countAbove cs u, h⟩ : Fin (m + 1 + 1)) = Fin.succ ⟨_, h'⟩ :=
        Fin.ext (by simp [hcount, add_comm])
      rw [this, Fin.cons_succ, Fin.cons_self_tail]


/-- The prescribed tracked state at phase `p` of the merge history `xs` with integer merge
phases `c` listed from the top (`c 0` is the latest merge): the state after all merges at
phases `≥ p`. -/
noncomputable def patternState (xs : Fin m → ConnState k) (c : Fin m → ℕ) (p : ℕ) :
    ConnState k :=
  stateAt m 0 diagState xs (fun i ↦ (c i : ℝ)) p

theorem countAbove_natCast (c : Fin m → ℕ) (p : ℕ) :
    countAbove (fun i ↦ (c i : ℝ)) (p : ℝ) = countAbove c p := by
  classical
  unfold countAbove
  congr 1
  ext i
  simp

theorem patternState_eq_cons {xs : Fin m → ConnState k} {c : Fin m → ℕ} (hc : StrictAnti c)
    (p : ℕ) (h : countAbove c p < m + 1) :
    patternState xs c p = (Fin.cons diagState xs : Fin (m + 1) → ConnState k) ⟨_, h⟩ := by
  have hcs : StrictAnti (fun i ↦ (c i : ℝ)) := fun a b hab ↦ by
    simpa using hc hab
  rw [patternState, stateAt_eq_cons hcs (p : ℝ) (by rw [countAbove_natCast]; exact h)]
  congr 2
  exact countAbove_natCast c p

/-- Off the merge phases the prescribed state does not change. -/
theorem patternState_succ_of_notMem {xs : Fin m → ConnState k} {c : Fin m → ℕ}
    (hc : StrictAnti c) {p : ℕ} (hp : ∀ i, c i ≠ p) :
    patternState xs c (p + 1) = patternState xs c p := by
  classical
  have hcnt : countAbove c (p + 1) = countAbove c p := by
    unfold countAbove
    congr 1
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have := hp i
    omega
  have h1 : countAbove c p < m + 1 := Nat.lt_succ_of_le (by simpa using countAbove_le c p)
  rw [patternState_eq_cons hc (p + 1) (hcnt ▸ h1), patternState_eq_cons hc p h1]
  congr 2

/-- At the merge phase `c i`, the prescribed state passes from the state before the `i`-th
merge to the state after it. -/
theorem patternState_merge {xs : Fin m → ConnState k} {c : Fin m → ℕ} (hc : StrictAnti c)
    (i : Fin m) :
    patternState xs c (c i + 1) = (Fin.cons diagState xs : Fin (m + 1) → ConnState k) i.castSucc ∧
      patternState xs c (c i) = (Fin.cons diagState xs : Fin (m + 1) → ConnState k) i.succ := by
  classical
  have h1 : countAbove c (c i + 1) = i := by
    unfold countAbove
    have : (Finset.univ.filter fun l ↦ c i + 1 ≤ c l) = Finset.Iio i := by
      ext l
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Iio,
        Nat.add_one_le_iff]
      exact hc.lt_iff_gt
    rw [this, Fin.card_Iio]
  have h2 : countAbove c (c i) = i + 1 := by
    unfold countAbove
    have : (Finset.univ.filter fun l ↦ c i ≤ c l) = Finset.Iic i := by
      ext l
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Iic]
      exact hc.le_iff_ge
    rw [this, Fin.card_Iic]
  constructor
  · rw [patternState_eq_cons hc _ (by rw [h1]; omega)]
    congr 1
    exact Fin.ext h1
  · rw [patternState_eq_cons hc _ (by rw [h2]; omega)]
    congr 1
    exact Fin.ext h2


/-- The signed count `#{j : i ≤ b j} - #{l : i ≤ c l}`: on an admissible history, the
number of clusters of the labels born at time `i`. -/
noncomputable def clusterNum {α : Type*} [LinearOrder α] (b : Fin k → α) (c : Fin m → α)
    (i : α) : ℝ :=
  (countAbove b i : ℝ) - (countAbove c i : ℝ)

/-- `C(a, 2)` for the signed cluster count `a = clusterNum b c i`. -/
noncomputable def pairWeight {α : Type*} [LinearOrder α] (b : Fin k → α) (c : Fin m → α)
    (i : α) : ℝ :=
  clusterNum b c i * (clusterNum b c i - 1) / 2

/-- The tracked frozen labels born at the phases `b`. -/
def frozenLabels (b : Fin k → ℕ) : Fin k → ℕ ⊕ ℕ := fun j ↦ Sum.inr (b j)

open Classical in
/-- The exact one-step factor of the prescribed pattern at phase `p`: the merge hazard
`1 / C(S, 2)` at a merge phase, and the survival factor `1 - C(a, 2) / C(S, 2)` otherwise
(equal to `1` at freezing steps). -/
noncomputable def stepWeight (x : SignSequence) (b : Fin k → ℕ) (c : Fin m → ℕ) (p : ℕ) : ℝ :=
  if ∃ i, c i = p then coalescenceHazard x (p + 1)
  else 1 - pairWeight b c (p + 1) * coalescenceHazard x (p + 1)

theorem bornSet_frozenLabels (n p : ℕ) (b : Fin k → ℕ) :
    TrackedGenealogy.bornSet n p (frozenLabels b) = bornAt (fun j ↦ (b j : ℝ)) (p : ℝ) := by
  classical
  ext j
  unfold TrackedGenealogy.bornSet bornAt
  rw [Finset.mem_filter, Finset.mem_filter]
  simp [Born, frozenLabels, Freezing1.birthTime]

/-- On an admissible history, the number of clusters of the born labels is the signed
count. -/
theorem classesOn_patternState {n : ℕ} {b : Fin k → ℕ} {xs : Fin m → ConnState k}
    {c : Fin m → ℕ}
    (hadm : IsAdmissible (fun j ↦ (b j : ℝ)) m n diagState xs (fun i ↦ (c i : ℝ)))
    {i : ℕ} (hi : i ≤ n) :
    (classesOn (bornAt (fun j ↦ (b j : ℝ)) (i : ℝ)) (patternState xs c i) : ℝ) =
      clusterNum b c i := by
  classical
  have h := classesOn_stateAt m hadm (isValid_diagState _) (u := (i : ℝ)) (by exact_mod_cast hi)
  rw [classesOn_diagState] at h
  have hb : (bornAt (fun j ↦ (b j : ℝ)) (i : ℝ)).card = countAbove b i := by
    unfold bornAt countAbove
    congr 1
    ext j
    simp
  have hc : (Finset.univ.filter fun l ↦ (i : ℝ) ≤ (c l : ℝ)).card = countAbove c i := by
    unfold countAbove
    congr 1
    ext l
    simp
  -- `stateAt` does not depend on its starting time argument
  have hst : stateAt m (n : ℝ) diagState xs (fun l ↦ (c l : ℝ)) (i : ℝ) =
      stateAt m 0 diagState xs (fun l ↦ (c l : ℝ)) (i : ℝ) := by
    cases m with
    | zero => rfl
    | succ m => rfl
  rw [hb, hc, hst] at h
  unfold clusterNum
  rw [patternState]
  have h' : (countAbove b i : ℝ) = (classesOn (bornAt (fun j ↦ (b j : ℝ)) (i : ℝ))
      (stateAt m 0 diagState xs (fun l ↦ (c l : ℝ)) (i : ℝ)) : ℝ) + (countAbove c i : ℝ) := by
    exact_mod_cast h.symm
  linarith

/-- **The exact one-step factor along an admissible pattern.** -/
theorem chainStep_pattern {x : SignSequence} {n : ℕ} (hn : (n : ℕ∞) ≤ extinctionTime x)
    {b : Fin k → ℕ} {xs : Fin m → ConnState k} {c : Fin m → ℕ}
    (hbx : ∀ j, x (b j + 1) = false) (hcx : ∀ i, x (c i + 1) = true)
    (hadm : IsAdmissible (fun j ↦ (b j : ℝ)) m n diagState xs (fun i ↦ (c i : ℝ)))
    {p : ℕ} (hp : p < n) :
    chainStep x n p (frozenLabels b) (patternState xs c (p + 1)) (patternState xs c p) =
      stepWeight x b c p := by
  classical
  have hanti : StrictAnti c := fun a a' h ↦ by
    have := hadm.strictAnti h
    exact_mod_cast this
  by_cases hmerge : ∃ i, c i = p
  · obtain ⟨i, rfl⟩ := hmerge
    obtain ⟨h1, h2⟩ := patternState_merge (xs := xs) hanti i
    have hx := hcx i
    have hstep := (isAdmissible_iff_forall.mp hadm).2 i
    rw [← h1, ← h2] at hstep
    obtain ⟨hne, hmo⟩ := hstep
    have hborn : bornAt (fun j ↦ (b j : ℝ)) ((c i : ℕ) : ℝ) =
        TrackedGenealogy.bornSet n (c i + 1) (frozenLabels b) := by
      rw [bornSet_frozenLabels]
      ext j
      simp only [bornAt, Finset.mem_filter, Finset.mem_univ, true_and, Nat.cast_le]
      have hbj : b j ≠ c i := fun h ↦ by
        have := hbx j
        rw [h, hx] at this
        exact Bool.noConfusion this
      constructor
      · intro h
        have : c i ≤ b j := by exact_mod_cast h
        have : c i + 1 ≤ b j := by omega
        exact_mod_cast this
      · intro h
        have : c i + 1 ≤ b j := by exact_mod_cast h
        have : c i ≤ b j := by omega
        exact_mod_cast this
    rw [hborn, ← isMerge_iff_mergeOn] at hmo
    have hval : stepWeight x b c (c i) = coalescenceHazard x (c i + 1) := by
      simp [stepWeight]
    rw [hval, coalescenceHazard_eq_inv_choose hn (by omega) hx]
    simp [chainStep, hx, hne, hmo]
  · have hp' : ∀ i, c i ≠ p := fun i h ↦ hmerge ⟨i, h⟩
    rw [patternState_succ_of_notMem hanti hp']
    have hval : stepWeight x b c p = 1 - pairWeight b c (p + 1) * coalescenceHazard x (p + 1) := by
      simp [stepWeight, hmerge]
    rw [hval]
    by_cases hx : x (p + 1) = true
    · rw [coalescenceHazard_eq_inv_choose hn (by omega) hx]
      have hcl : (stateClasses n (p + 1) (frozenLabels b) (patternState xs c p) : ℝ) =
          clusterNum b c (p + 1) := by
        rw [stateClasses_eq_classesOn, bornSet_frozenLabels,
          ← patternState_succ_of_notMem hanti hp']
        exact_mod_cast classesOn_patternState hadm (i := p + 1) (by omega)
      simp only [chainStep, hx, ↓reduceIte]
      rw [Nat.cast_choose_two, hcl, pairWeight]
      ring
    · have hxf : x (p + 1) = false := by simpa using hx
      simp [chainStep, hxf, coalescenceHazard]


theorem trackedState_top {n : ℕ} {u : Fin k → ℕ ⊕ ℕ}
    (hbirth : ∀ j, Freezing1.birthTime n (u j) < n) (F : Reverse.Forest) :
    trackedState n n u F = diagState := by
  funext j l
  have hj : ¬ Born n n u j := by simp only [Born, not_le]; exact hbirth j
  simp [trackedState, hj, diagState]

/-- **Path law of the tracked chain.** The probability that the tracked connectivity
state follows a prescribed path for its first `D` reverse steps (phases `n, …, n - D`) is
the product of the one-step transition probabilities, the state at phase `n` being the
singleton state. -/
theorem jointLaw_chainPath {x : SignSequence} {n : ℕ} {u : Fin k → ℕ ⊕ ℕ}
    (hn : (n : ℕ∞) ≤ extinctionTime x) (hu : ∀ j, u j ∈ Freezing1.vertexLabels x n)
    (hinj : Function.Injective u) (hbirth : ∀ j, Freezing1.birthTime n (u j) < n)
    (π : ℕ → ConnState k) :
    ∀ D ≤ n, (jointLaw x n).real {ω | ∀ N ≤ D, chainState n u N ω = π N} =
      (open Classical in if π 0 = diagState then 1 else 0) *
        ∏ N ∈ Finset.range D, chainStep x n (n - (N + 1)) u (π N) (π (N + 1)) := by
  classical
  intro D
  induction D with
  | zero =>
    intro _
    have h0 : ∀ ω : History, chainState n u 0 ω = diagState := fun ω ↦ by
      simp only [chainState, Nat.sub_zero]
      exact trackedState_top hbirth _
    by_cases hπ : π 0 = diagState
    · have hset : {ω : History | ∀ N ≤ 0, chainState n u N ω = π N} = Set.univ := by
        ext ω
        simp only [mem_ofPred_eq, mem_univ, Nat.le_zero, forall_eq, h0, hπ]
      rw [hset]
      simp [hπ]
    · have hset : {ω : History | ∀ N ≤ 0, chainState n u N ω = π N} = ∅ := by
        ext ω
        simp only [mem_ofPred_eq, Nat.le_zero, forall_eq, h0, mem_empty_iff_false, iff_false]
        exact fun h ↦ hπ h.symm
      rw [hset]
      simp [hπ]
  | succ D ih =>
    intro hD
    set A : Set History := {ω | ∀ N < D, chainState n u N ω = π N} with hAdef
    have hA : MeasurableSet[Filtration.piLE (X := fun _ ↦ Reverse.Forest) D] A := by
      have : A = ⋂ N ∈ Finset.range D, {ω | chainState n u N ω = π N} := by
        ext ω
        simp [hAdef]
      rw [this]
      exact Finset.measurableSet_biInter _ fun N hN ↦
        measurableSet_chainState n u (Finset.mem_range.mp hN).le (π N)
    have h1 : {ω : History | ∀ N ≤ D + 1, chainState n u N ω = π N} =
        A ∩ {ω | chainState n u D ω = π D} ∩ {ω | chainState n u (D + 1) ω = π (D + 1)} := by
      ext ω
      simp only [hAdef, mem_ofPred_eq, mem_inter_iff]
      constructor
      · intro h
        exact ⟨⟨fun N hN ↦ h N (by omega), h D (by omega)⟩, h (D + 1) le_rfl⟩
      · rintro ⟨⟨h, hD'⟩, hD1⟩ N hN
        rcases Nat.lt_or_ge N D with hlt | hge
        · exact h N hlt
        · rcases Nat.eq_or_lt_of_le hge with heq | hgt
          · exact heq ▸ hD'
          · have : N = D + 1 := by omega
            exact this ▸ hD1
    have h2 : {ω : History | ∀ N ≤ D, chainState n u N ω = π N} =
        A ∩ {ω | chainState n u D ω = π D} := by
      ext ω
      simp only [hAdef, mem_ofPred_eq, mem_inter_iff]
      constructor
      · intro h
        exact ⟨fun N hN ↦ h N hN.le, h D le_rfl⟩
      · rintro ⟨h, hD'⟩ N hN
        rcases Nat.lt_or_ge N D with hlt | hge
        · exact h N hlt
        · exact (le_antisymm hN hge) ▸ hD'
    rw [h1, jointLaw_chainState_step hn hu hinj (by omega) hA, ← h2, ih (by omega),
      Finset.prod_range_succ]
    ring

/-- The event that the tracked chain of the frozen labels born at `b` follows the
prescribed pattern `(xs, c)` at every phase `≥ p₀`. -/
def patternEvent (n p₀ : ℕ) (b : Fin k → ℕ) (xs : Fin m → ConnState k) (c : Fin m → ℕ) :
    Set History :=
  {ω | ∀ N ≤ n - p₀, chainState n (frozenLabels b) N ω = patternState xs c (n - N)}

theorem measurableSet_patternEvent (n p₀ : ℕ) (b : Fin k → ℕ) (xs : Fin m → ConnState k)
    (c : Fin m → ℕ) : MeasurableSet (patternEvent n p₀ b xs c) := by
  have : patternEvent n p₀ b xs c =
      ⋂ N ∈ Finset.range (n - p₀ + 1), {ω | chainState n (frozenLabels b) N ω =
        patternState xs c (n - N)} := by
    ext ω
    simp [patternEvent]
  rw [this]
  exact Finset.measurableSet_biInter _ fun N _ ↦
    (Filtration.piLE (X := fun _ ↦ Reverse.Forest)).le N _
      (measurableSet_chainState n (frozenLabels b) le_rfl _)

theorem jointLaw_patternEvent_of_le {x : SignSequence} {n : ℕ}
    (hn : (n : ℕ∞) ≤ extinctionTime x)
    {b : Fin k → ℕ} {xs : Fin m → ConnState k} {c : Fin m → ℕ}
    (hb : ∀ j, b j < n ∧ x (b j + 1) = false) (hbinj : Function.Injective b)
    (hcx : ∀ i, x (c i + 1) = true)
    (hadm : IsAdmissible (fun j ↦ (b j : ℝ)) m n diagState xs (fun i ↦ (c i : ℝ)))
    {p₀ : ℕ} (hp₀ : p₀ ≤ n) :
    (jointLaw x n).real (patternEvent n p₀ b xs c) = ∏ p ∈ Finset.Ico p₀ n, stepWeight x b c p := by
  classical
  have hanti : StrictAnti c := fun a a' h ↦ by
    have := hadm.strictAnti h
    exact_mod_cast this
  have hcn : ∀ i, c i < n := fun i ↦ by
    have := (hadm.time_mem i).2
    exact_mod_cast this
  have hu : ∀ j, frozenLabels b j ∈ Freezing1.vertexLabels x n := by
    intro j
    simp only [frozenLabels, Freezing1.vertexLabels, Finset.inr_mem_disjSum,
      Freezing1.frozenIndices, Finset.mem_filter, Finset.mem_range]
    exact hb j
  have hinj : Function.Injective (frozenLabels b) := fun a a' h ↦ hbinj (Sum.inr_injective h)
  have hbirth : ∀ j, Freezing1.birthTime n (frozenLabels b j) < n := fun j ↦ (hb j).1
  have h := jointLaw_chainPath hn hu hinj hbirth (fun N ↦ patternState xs c (n - N))
    (n - p₀) (Nat.sub_le n p₀)
  have htop : patternState xs c (n - 0) = diagState := by
    have h0 : countAbove c n = 0 := by
      unfold countAbove
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro i _ hi
      exact absurd (hcn i) (not_lt.mpr hi)
    rw [Nat.sub_zero, patternState_eq_cons hanti n (by omega)]
    have : (⟨countAbove c n, by omega⟩ : Fin (m + 1)) = 0 := Fin.ext h0
    rw [this, Fin.cons_zero]
  rw [patternEvent, h, htop, ite_eq_left rfl, one_mul]
  -- reindex the steps by phases
  rw [← Finset.prod_range_reflect]
  rw [Finset.prod_Ico_eq_prod_range]
  refine Finset.prod_congr rfl fun N hN ↦ ?_
  have hN' := Finset.mem_range.mp hN
  have e1 : n - (n - p₀ - 1 - N + 1) = p₀ + N := by omega
  have e2 : n - (n - p₀ - 1 - N) = p₀ + N + 1 := by omega
  rw [e1, e2]
  exact chainStep_pattern hn (fun j ↦ (hb j).2) hcx hadm (by omega)

/-- **The exact discrete pattern probability.** For distinct frozen labels born at the
phases `b` (freezing steps), merge phases `c` at attachment steps, and an admissible
history, the probability that the tracked genealogy follows the pattern at every phase
`≥ p₀` is the product of the step factors `stepWeight` over the phases `p₀ ≤ p < n`. -/
theorem jointLaw_patternEvent {x : SignSequence} {n : ℕ} (hn : (n : ℕ∞) ≤ extinctionTime x)
    {b : Fin k → ℕ} {xs : Fin m → ConnState k} {c : Fin m → ℕ}
    (hb : ∀ j, b j < n ∧ x (b j + 1) = false) (hbinj : Function.Injective b)
    (hcx : ∀ i, x (c i + 1) = true)
    (hadm : IsAdmissible (fun j ↦ (b j : ℝ)) m n diagState xs (fun i ↦ (c i : ℝ)))
    (p₀ : ℕ) :
    (jointLaw x n).real (patternEvent n p₀ b xs c) = ∏ p ∈ Finset.Ico p₀ n, stepWeight x b c p := by
  rcases le_or_gt p₀ n with hp₀ | hp₀
  · exact jointLaw_patternEvent_of_le hn hb hbinj hcx hadm hp₀
  · have hev : patternEvent n p₀ b xs c = patternEvent n n b xs c := by
      unfold patternEvent
      rw [show n - p₀ = n - n by omega]
    rw [hev, jointLaw_patternEvent_of_le hn hb hbinj hcx hadm le_rfl, Finset.Ico_self,
      Finset.Ico_eq_empty (by omega), Finset.prod_empty]

/-! ### Algebra of the pair weight -/

/-- The events of a configuration: births then merges. -/
def eventTime {α : Type*} (b : Fin k → α) (c : Fin m → α) : Fin k ⊕ Fin m → α := Sum.elim b c

/-- Signs of the events: `+1` for a birth, `-1` for a merge. -/
def eventSign : Fin k ⊕ Fin m → ℝ := Sum.elim (fun _ ↦ 1) (fun _ ↦ -1)

/-- Indicator of `i ≤ e`. -/
noncomputable def leInd {α : Type*} [LinearOrder α] (i e : α) : ℝ :=
  open Classical in if i ≤ e then 1 else 0

theorem countAbove_eq_sum {ι α : Type*} [Fintype ι] [LinearOrder α] (e : ι → α) (i : α) :
    (countAbove e i : ℝ) = ∑ q, leInd i (e q) := by
  classical
  unfold countAbove leInd
  rw [Finset.card_filter]
  push_cast
  rfl

theorem clusterNum_eq_sum {α : Type*} [LinearOrder α] (b : Fin k → α) (c : Fin m → α) (i : α) :
    clusterNum b c i = ∑ q, eventSign q * leInd i (eventTime b c q) := by
  rw [clusterNum, countAbove_eq_sum, countAbove_eq_sum, Fintype.sum_sum_type]
  simp [eventSign, eventTime, sub_eq_add_neg, Finset.sum_neg_distrib]

theorem leInd_mul_leInd {α : Type*} [LinearOrder α] (i e e' : α) :
    leInd i e * leInd i e' = leInd i (min e e') := by
  classical
  unfold leInd
  by_cases h : i ≤ e <;> by_cases h' : i ≤ e' <;> simp [h, h']

/-- **Expansion of the pair weight** into indicators of the events. -/
theorem pairWeight_eq_sum {α : Type*} [LinearOrder α] (b : Fin k → α) (c : Fin m → α)
    (i : α) :
    pairWeight b c i = ((∑ q, ∑ q', eventSign q * eventSign q' *
      leInd i (min (eventTime b c q) (eventTime b c q'))) -
        ∑ q, eventSign q * leInd i (eventTime b c q)) / 2 := by
  rw [pairWeight, clusterNum_eq_sum]
  congr 1
  rw [mul_sub, mul_one, Finset.sum_mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun q _ ↦ Finset.sum_congr rfl fun q' _ ↦ ?_
  rw [← leInd_mul_leInd]
  ring

theorem pairWeight_nonneg {α : Type*} [LinearOrder α] (b : Fin k → α) (c : Fin m → α)
    (i : α) : 0 ≤ pairWeight b c i := by
  unfold pairWeight clusterNum
  rcases le_or_gt (countAbove b i) (countAbove c i) with h | h
  · have h' : (countAbove b i : ℝ) ≤ countAbove c i := by exact_mod_cast h
    have : 0 ≤ ((countAbove b i : ℝ) - countAbove c i) *
        ((countAbove b i : ℝ) - countAbove c i - 1) :=
      mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)
    linarith
  · have h' : (countAbove c i : ℝ) + 1 ≤ countAbove b i := by exact_mod_cast h
    have : 0 ≤ ((countAbove b i : ℝ) - countAbove c i) *
        ((countAbove b i : ℝ) - countAbove c i - 1) :=
      mul_nonneg (by linarith) (by linarith)
    linarith

theorem pairWeight_le {α : Type*} [LinearOrder α] (b : Fin k → α) (c : Fin m → α)
    (i : α) : pairWeight b c i ≤ ((k + m : ℕ) : ℝ) ^ 2 := by
  unfold pairWeight clusterNum
  have hb : (countAbove b i : ℝ) ≤ k := by
    have := countAbove_le b i
    rw [Fintype.card_fin] at this
    exact_mod_cast this
  have hc : (countAbove c i : ℝ) ≤ m := by
    have := countAbove_le c i
    rw [Fintype.card_fin] at this
    exact_mod_cast this
  have hb0 : (0 : ℝ) ≤ countAbove b i := Nat.cast_nonneg _
  have hc0 : (0 : ℝ) ≤ countAbove c i := Nat.cast_nonneg _
  have hkm : ((k + m : ℕ) : ℝ) ≤ ((k + m : ℕ) : ℝ) ^ 2 := by
    rcases Nat.eq_zero_or_pos (k + m) with h | h
    · rw [h]; norm_num
    · have : (1 : ℝ) ≤ ((k + m : ℕ) : ℝ) := by exact_mod_cast h
      nlinarith
  push_cast at hkm ⊢
  nlinarith [mul_nonneg hb0 hc0]

theorem pairWeight_eq_zero_of_lt {α : Type*} [LinearOrder α] {b : Fin k → α} {c : Fin m → α}
    {i : α} (hb : ∀ j, b j < i) (hc : ∀ l, c l < i) : pairWeight b c i = 0 := by
  classical
  have h1 : countAbove b i = 0 := by
    unfold countAbove
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    exact fun j _ hj ↦ absurd (hb j) (not_lt.mpr hj)
  have h2 : countAbove c i = 0 := by
    unfold countAbove
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    exact fun j _ hj ↦ absurd (hc j) (not_lt.mpr hj)
  simp [pairWeight, clusterNum, h1, h2]


/-! ### Hazard sums over cut windows -/

/-- The window sum of hazards: phases `p₀ ≤ p < n` with `p + 1 ≤ e`, reindexed by steps. -/
theorem sum_Ico_leInd_eq (h : ℕ → ℝ) {p₀ n e : ℕ} (hen : e ≤ n) :
    ∑ p ∈ Finset.Ico p₀ n, leInd (p + 1) e * h (p + 1) = ∑ i ∈ Finset.Icc (p₀ + 1) e, h i := by
  classical
  rw [Finset.sum_Ico_add' (fun i ↦ leInd i e * h i) p₀ n 1]
  unfold leInd
  simp only [boole_mul]
  rw [← Finset.sum_filter]
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_Icc]
  omega

theorem sum_Ico_leInd_eq_zero (h : ℕ → ℝ) {p₀ n e : ℕ} (he : e ≤ p₀) :
    ∑ p ∈ Finset.Ico p₀ n, leInd (p + 1) e * h (p + 1) = 0 := by
  classical
  refine Finset.sum_eq_zero fun p hp ↦ ?_
  have hp' := (Finset.mem_Ico.mp hp).1
  have : ¬ (p + 1 ≤ e) := by omega
  simp [leInd, this]

theorem setIntegral_leInd {g : ℝ → ℝ} {ε η : ℝ} (hη1 : η < 1) :
    ∫ t in Ioc ε 1, leInd t η * g t ^ 2 = ∫ t in Icc ε η, g t ^ 2 := by
  classical
  have hfun : (fun t ↦ leInd t η * g t ^ 2) = (Iic η).indicator (fun t ↦ g t ^ 2) := by
    funext t
    by_cases ht : t ≤ η <;> simp [leInd, ht, Set.indicator]
  have hset : Ioc ε 1 ∩ Iic η = Ioc ε η := by
    ext t
    simp only [mem_inter_iff, mem_Ioc, mem_Iic]
    constructor
    · rintro ⟨⟨h1, -⟩, h3⟩
      exact ⟨h1, h3⟩
    · rintro ⟨h1, h3⟩
      exact ⟨⟨h1, h3.trans hη1.le⟩, h3⟩
  rw [hfun, setIntegral_indicator measurableSet_Iic, integral_Icc_eq_integral_Ioc, hset]

theorem setIntegral_leInd_of_lt {g : ℝ → ℝ} {ε η : ℝ} (hηε : η < ε) :
    ∫ t in Ioc ε 1, leInd t η * g t ^ 2 = 0 := by
  classical
  refine setIntegral_eq_zero_of_forall_eq_zero fun t ht ↦ ?_
  have : ¬ t ≤ η := fun h ↦ absurd (lt_of_le_of_lt h hηε) (not_lt.mpr ht.1.le)
  simp [leInd, this]

/-- **Hazard sums over a cut window.** Summing the actual merge hazards of the steps
`p + 1 ≤ e n` over the phases `p` above the cutoff `ε n` converges to `∫_ε^η g²` (to `0` when
`η < ε`), for `e n / n → η < 1` with `η ≠ ε`. -/
theorem tendsto_cutHazard {xa : ℕ → ℕ → ℤ} {g : ℝ → ℝ} (hx : AdmissibleArray xa)
    (hL1 : HasL1ReciprocalProfile xa (1 / 2) g) (hpos : PositiveProfile g)
    (h2 : HasLocalSquareMomentProfile xa (1 / 2) g)
    {ε η : ℝ} (hε : 0 < ε) (hη1 : η < 1) (hηε : η ≠ ε)
    {e : ℕ → ℕ} (he : Tendsto (fun n ↦ (e n : ℝ) / n) atTop (𝓝 η)) :
    Tendsto (fun n ↦ ∑ p ∈ Finset.Ico (phaseAbove n ε) n,
        leInd (p + 1) (e n) * coalescenceHazard (companionSchedule (xa n)) (p + 1)) atTop
      (𝓝 (∫ t in Ioc ε 1, leInd t η * g t ^ 2)) := by
  have hp := tendsto_phaseAbove_div hε.le
  rcases lt_or_gt_of_ne hηε with hlt | hgt
  · rw [setIntegral_leInd_of_lt hlt]
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_lt_of_tendsto_div he hp hlt] with n hn
    exact (sum_Ico_leInd_eq_zero _ hn.le).symm
  · rw [setIntegral_leInd hη1]
    set ε' : ℝ := min ε (1 - η) / 2 with hε'
    have hε'0 : 0 < ε' := by
      have : 0 < min ε (1 - η) := lt_min hε (by linarith)
      linarith
    have hε'ε : ε' < ε := by
      have : min ε (1 - η) ≤ ε := min_le_left _ _
      linarith
    have hε'η : η < 1 - ε' := by
      have : min ε (1 - η) ≤ 1 - η := min_le_right _ _
      linarith
    have hε'half : ε' < 1 / 2 := by linarith
    have hu := tendsto_succ_div hp
    have hwin : ∀ᶠ n in atTop,
        CoalescenceInterval ε' n (phaseAbove n ε + 1) (e n) := by
      filter_upwards [eventually_lt_of_tendsto_div hu he hgt,
        eventually_lt_mul_of_tendsto he hε'η, eventually_gt_atTop 0] with n h1 h2' hn0
      have hnpos : (0 : ℝ) < n := by exact_mod_cast hn0
      have hεn : ε * n < (phaseAbove n ε : ℝ) := by
        unfold phaseAbove
        push_cast
        exact Nat.lt_floor_add_one _
      refine ⟨by omega, h1.le, ?_, ?_, h2'.le⟩
      · have : (e n : ℝ) < n := lt_of_lt_of_le h2' (by nlinarith)
        exact_mod_cast this.le
      · have : ε' * n ≤ ε * n := by nlinarith
        push_cast
        linarith
    have hlim := tendsto_critical_coalescence_hazard_sum hx hL1 hpos h2 hε'0 hε'half hu he hwin
    apply hlim.congr'
    filter_upwards [hwin] with n hn
    exact (sum_Ico_leInd_eq _ hn.2.2.1).symm


theorem integrableOn_leInd {xa : ℕ → ℕ → ℤ} {g : ℝ → ℝ}
    (h2 : HasLocalSquareMomentProfile xa (1 / 2) g) {ε η : ℝ} (hε : 0 < ε) (hη1 : η < 1) :
    IntegrableOn (fun t ↦ leInd t η * g t ^ 2) (Ioc ε 1) := by
  classical
  rcases le_or_gt η ε with hle | hgt
  · apply (integrableOn_zero).congr_fun _ measurableSet_Ioc
    intro t ht
    have : ¬ t ≤ η := fun h ↦ absurd (lt_of_le_of_lt (h.trans hle) ht.1) (lt_irrefl _)
    simp [leInd, this]
  · have hg := (h2 ε η hε hgt hη1).1
    have hfun : (fun t ↦ leInd t η * g t ^ 2) = (Iic η).indicator (fun t ↦ g t ^ 2) := by
      funext t
      by_cases ht : t ≤ η <;> simp [leInd, ht, Set.indicator]
    rw [hfun, IntegrableOn, integrable_indicator_iff measurableSet_Iic, IntegrableOn,
      Measure.restrict_restrict measurableSet_Iic]
    apply hg.mono_set
    intro t ht
    exact ⟨ht.2.1.le, ht.1⟩

/-- The integral of the pair weight, expanded along the events. -/
theorem integral_pairWeight_eq {xa : ℕ → ℕ → ℤ} {g : ℝ → ℝ}
    (h2 : HasLocalSquareMomentProfile xa (1 / 2) g) {ε : ℝ} (hε : 0 < ε)
    {β : Fin k → ℝ} {γ : Fin m → ℝ} (hβ1 : ∀ j, β j < 1) (hγ1 : ∀ l, γ l < 1) :
    ∫ t in Ioc ε 1, pairWeight β γ t * g t ^ 2 =
      ((∑ q, ∑ q', eventSign q * eventSign q' *
        ∫ t in Ioc ε 1, leInd t (min (eventTime β γ q) (eventTime β γ q')) * g t ^ 2) -
        ∑ q, eventSign q * ∫ t in Ioc ε 1, leInd t (eventTime β γ q) * g t ^ 2) / 2 := by
  have hη1 : ∀ q, eventTime β γ q < 1 := by
    intro q
    rcases q with j | l
    · exact hβ1 j
    · exact hγ1 l
  have hI : ∀ η, η < 1 → IntegrableOn (fun t ↦ leInd t η * g t ^ 2) (Ioc ε 1) :=
    fun η hη ↦ integrableOn_leInd h2 hε hη
  have hfun : (fun t ↦ pairWeight β γ t * g t ^ 2) = fun t ↦
      ((∑ q, ∑ q', eventSign q * eventSign q' *
        (leInd t (min (eventTime β γ q) (eventTime β γ q')) * g t ^ 2)) -
        ∑ q, eventSign q * (leInd t (eventTime β γ q) * g t ^ 2)) / 2 := by
    funext t
    rw [pairWeight_eq_sum, div_mul_eq_mul_div, sub_mul, Finset.sum_mul, Finset.sum_mul]
    congr 2
    · refine Finset.sum_congr rfl fun q _ ↦ ?_
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun q' _ ↦ ?_
      ring
    · refine Finset.sum_congr rfl fun q _ ↦ ?_
      ring
  rw [hfun, integral_div, integral_sub, integral_finsetSum, integral_finsetSum]
  · congr 2
    · refine Finset.sum_congr rfl fun q _ ↦ ?_
      rw [integral_finsetSum]
      · refine Finset.sum_congr rfl fun q' _ ↦ ?_
        rw [integral_const_mul]
      · intro q' _
        exact (hI _ (lt_of_le_of_lt (min_le_left _ _) (hη1 q))).const_mul _
    · refine Finset.sum_congr rfl fun q _ ↦ ?_
      rw [integral_const_mul]
  · intro q _
    exact (hI _ (hη1 q)).const_mul _
  · intro q _
    exact integrable_finsetSum _ fun q' _ ↦
      (hI _ (lt_of_le_of_lt (min_le_left _ _) (hη1 q))).const_mul _
  · exact integrable_finsetSum _ fun q _ ↦ integrable_finsetSum _ fun q' _ ↦
      (hI _ (lt_of_le_of_lt (min_le_left _ _) (hη1 q))).const_mul _
  · exact integrable_finsetSum _ fun q _ ↦ (hI _ (hη1 q)).const_mul _

/-- The discrete survival exponent, expanded along the events. -/
theorem sum_pairWeight_eq (h : ℕ → ℝ) (p₀ n : ℕ) (b : Fin k → ℕ) (c : Fin m → ℕ) :
    ∑ p ∈ Finset.Ico p₀ n, pairWeight b c (p + 1) * h (p + 1) =
      ((∑ q, ∑ q', eventSign q * eventSign q' *
        ∑ p ∈ Finset.Ico p₀ n, leInd (p + 1) (min (eventTime b c q) (eventTime b c q')) *
          h (p + 1)) -
        ∑ q, eventSign q * ∑ p ∈ Finset.Ico p₀ n, leInd (p + 1) (eventTime b c q) *
          h (p + 1)) / 2 := by
  have hterm : ∀ p, pairWeight b c (p + 1) * h (p + 1) =
      ((∑ q, ∑ q', eventSign q * eventSign q' *
        (leInd (p + 1) (min (eventTime b c q) (eventTime b c q')) * h (p + 1))) -
        ∑ q, eventSign q * (leInd (p + 1) (eventTime b c q) * h (p + 1))) / 2 := by
    intro p
    rw [pairWeight_eq_sum, div_mul_eq_mul_div, sub_mul, Finset.sum_mul, Finset.sum_mul]
    congr 2
    · refine Finset.sum_congr rfl fun q _ ↦ ?_
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun q' _ ↦ ?_
      ring
    · refine Finset.sum_congr rfl fun q _ ↦ ?_
      ring
  rw [Finset.sum_congr rfl fun p _ ↦ hterm p, ← Finset.sum_div, Finset.sum_sub_distrib]
  congr 2
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun q _ ↦ ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun q' _ ↦ ?_
    rw [Finset.mul_sum]
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun q _ ↦ ?_
    rw [Finset.mul_sum]

/-- **The survival exponent converges.** For configurations whose scaled event phases
converge to limits below `1` and different from the cutoff `ε`, the sum over the phases above
`ε n` of `C(a, 2)` times the actual merge hazard converges to `∫_ε^1 C(a(t), 2) g(t)² dt`. -/
theorem tendsto_sum_pairWeight_hazard {xa : ℕ → ℕ → ℤ} {g : ℝ → ℝ} (hx : AdmissibleArray xa)
    (hL1 : HasL1ReciprocalProfile xa (1 / 2) g) (hpos : PositiveProfile g)
    (h2 : HasLocalSquareMomentProfile xa (1 / 2) g) {ε : ℝ} (hε : 0 < ε)
    {b : ℕ → Fin k → ℕ} {c : ℕ → Fin m → ℕ} {β : Fin k → ℝ} {γ : Fin m → ℝ}
    (hb : ∀ j, Tendsto (fun n ↦ (b n j : ℝ) / n) atTop (𝓝 (β j)))
    (hc : ∀ l, Tendsto (fun n ↦ (c n l : ℝ) / n) atTop (𝓝 (γ l)))
    (hβ1 : ∀ j, β j < 1) (hγ1 : ∀ l, γ l < 1) (hβε : ∀ j, β j ≠ ε) (hγε : ∀ l, γ l ≠ ε) :
    Tendsto (fun n ↦ ∑ p ∈ Finset.Ico (phaseAbove n ε) n,
        pairWeight (b n) (c n) (p + 1) * coalescenceHazard (companionSchedule (xa n)) (p + 1))
      atTop (𝓝 (∫ t in Ioc ε 1, pairWeight β γ t * g t ^ 2)) := by
  have hev : ∀ q, Tendsto (fun n ↦ ((eventTime (b n) (c n) q : ℕ) : ℝ) / n) atTop
      (𝓝 (eventTime β γ q)) := by
    intro q
    rcases q with j | l
    · exact hb j
    · exact hc l
  have hη1 : ∀ q, eventTime β γ q < 1 := by
    intro q
    rcases q with j | l
    · exact hβ1 j
    · exact hγ1 l
  have hηε : ∀ q, eventTime β γ q ≠ ε := by
    intro q
    rcases q with j | l
    · exact hβε j
    · exact hγε l
  have hmin : ∀ q q', Tendsto (fun n ↦ ((min (eventTime (b n) (c n) q)
      (eventTime (b n) (c n) q') : ℕ) : ℝ) / n) atTop
      (𝓝 (min (eventTime β γ q) (eventTime β γ q'))) := by
    intro q q'
    have h := (hev q).min (hev q')
    refine h.congr fun n ↦ ?_
    rw [Nat.cast_min, min_div_div_right (Nat.cast_nonneg _)]
  have hminε : ∀ q q', min (eventTime β γ q) (eventTime β γ q') ≠ ε := by
    intro q q'
    rcases min_choice (eventTime β γ q) (eventTime β γ q') with h | h <;> rw [h]
    · exact hηε q
    · exact hηε q'
  rw [integral_pairWeight_eq h2 hε hβ1 hγ1]
  simp_rw [sum_pairWeight_eq]
  refine Tendsto.div_const (Tendsto.sub ?_ ?_) _
  · refine tendsto_finsetSum _ fun q _ ↦ tendsto_finsetSum _ fun q' _ ↦ ?_
    exact (tendsto_cutHazard hx hL1 hpos h2 hε (lt_of_le_of_lt (min_le_left _ _) (hη1 q))
      (hminε q q') (hmin q q')).const_mul _
  · refine tendsto_finsetSum _ fun q _ ↦ ?_
    exact (tendsto_cutHazard hx hL1 hpos h2 hε (hη1 q) (hηε q) (hev q)).const_mul _


theorem exists_bound_lt_one {ι : Type*} [Fintype ι] (f : ι → ℝ) (hf : ∀ i, f i < 1) :
    ∃ θ, θ < 1 ∧ ∀ i, f i < θ := by
  by_cases hι : Nonempty ι
  · obtain ⟨i0, -, hi0⟩ := Finset.exists_max_image Finset.univ f Finset.univ_nonempty
    refine ⟨(f i0 + 1) / 2, by linarith [hf i0], fun i ↦ ?_⟩
    have := hi0 i (Finset.mem_univ _)
    linarith [hf i0]
  · exact ⟨0, by norm_num, fun i ↦ (hι ⟨i⟩).elim⟩

open Classical in
/-- The product of the survival factors `1 - C(a, 2) / C(S, 2)` over the phases
`p₀ ≤ p < n` other than the merge phases `c`. -/
noncomputable def survivalFactor (x : SignSequence) (n p₀ : ℕ) (b : Fin k → ℕ)
    (c : Fin m → ℕ) : ℝ :=
  ∏ p ∈ (Finset.Ico p₀ n).filter (fun p ↦ ¬ ∃ i, c i = p),
    (1 - pairWeight b c (p + 1) * coalescenceHazard x (p + 1))

/-- **Convergence of the survival factor.** For configurations whose scaled birth and merge
phases converge to limits below `1` and different from the cutoff `ε`, the product of the
exact survival factors over the phases above `ε n` converges to
`exp (-∫_ε^1 C(a(t), 2) g(t)² dt)`. -/
theorem tendsto_survivalFactor {xa : ℕ → ℕ → ℤ} {g : ℝ → ℝ} (hx : AdmissibleArray xa)
    (hL1 : HasL1ReciprocalProfile xa (1 / 2) g) (hpos : PositiveProfile g)
    (h2 : HasLocalSquareMomentProfile xa (1 / 2) g) {ε : ℝ} (hε : 0 < ε)
    {b : ℕ → Fin k → ℕ} {c : ℕ → Fin m → ℕ} {β : Fin k → ℝ} {γ : Fin m → ℝ}
    (hb : ∀ j, Tendsto (fun n ↦ (b n j : ℝ) / n) atTop (𝓝 (β j)))
    (hc : ∀ l, Tendsto (fun n ↦ (c n l : ℝ) / n) atTop (𝓝 (γ l)))
    (hβ1 : ∀ j, β j < 1) (hγ1 : ∀ l, γ l < 1) (hβε : ∀ j, β j ≠ ε) (hγε : ∀ l, γ l ≠ ε) :
    Tendsto (fun n ↦ survivalFactor (companionSchedule (xa n)) n (phaseAbove n ε) (b n) (c n))
      atTop (𝓝 (Real.exp (-∫ t in Ioc ε 1, pairWeight β γ t * g t ^ 2))) := by
  classical
  set H : ℕ → ℕ → ℝ := fun n p ↦
    pairWeight (b n) (c n) (p + 1) * coalescenceHazard (companionSchedule (xa n)) (p + 1)
    with hHdef
  -- a common upper bound `θ < 1` of all limits
  obtain ⟨θ, hθ1, hθ⟩ := exists_bound_lt_one (eventTime β γ) (by
    intro q
    rcases q with j | l
    · exact hβ1 j
    · exact hγ1 l)
  set ε' : ℝ := min (min ε (1 - θ)) (1 / 2) / 2 with hε'def
  have hmin1 : min (min ε (1 - θ)) (1 / 2) ≤ min ε (1 - θ) := min_le_left _ _
  have hmin2 : min (min ε (1 - θ)) (1 / 2) ≤ 1 / 2 := min_le_right _ _
  have hmin3 : min ε (1 - θ) ≤ ε := min_le_left _ _
  have hmin4 : min ε (1 - θ) ≤ 1 - θ := min_le_right _ _
  have hε'0 : 0 < ε' := by
    have : 0 < min (min ε (1 - θ)) (1 / 2) := lt_min (lt_min hε (by linarith)) (by norm_num)
    linarith
  have hε'ε : ε' ≤ ε := by linarith
  have hε'θ : θ < 1 - ε' := by linarith
  have hε'q : ε' ≤ 1 / 4 := by linarith
  set M : ℕ → ℝ := fun n ↦ (activeCount (xa n) (interiorMinimizer xa n ε' (1 - ε')) : ℝ)
    with hMdef
  have hM : Tendsto M atTop atTop :=
    tendsto_interiorMinimum_atTop hx (by norm_num : (1 / 2 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1) hL1 hpos h2 hε'0 (by linarith) (by linarith)
  set δ : ℕ → ℝ := fun n ↦ ((k + m : ℕ) : ℝ) ^ 2 * (4 * ((M n)⁻¹) ^ 2) with hδdef
  have hδ : Tendsto δ atTop (𝓝 0) := by
    have hinv : Tendsto (fun n ↦ (M n)⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero.comp hM
    simpa [δ] using ((hinv.pow 2).const_mul 4).const_mul (((k + m : ℕ) : ℝ) ^ 2)
  have hδ0 : ∀ n, 0 ≤ δ n := fun n ↦ by positivity
  -- eventually every event phase lies below `(1 - ε') n`
  have hev : ∀ q, ∀ᶠ n in atTop,
      ((eventTime (b n) (c n) q : ℕ) : ℝ) < (1 - ε') * n := by
    intro q
    have hlim : Tendsto (fun n ↦ ((eventTime (b n) (c n) q : ℕ) : ℝ) / n) atTop
        (𝓝 (eventTime β γ q)) := by
      rcases q with j | l
      · exact hb j
      · exact hc l
    exact eventually_lt_mul_of_tendsto hlim ((hθ q).trans hε'θ)
  have hbound : ∀ᶠ n in atTop, ∀ p ∈ Finset.Ico (phaseAbove n ε) n, 0 ≤ H n p ∧ H n p ≤ δ n := by
    filter_upwards [eventually_all.mpr hev, hM.eventually (eventually_ge_atTop 2),
      eventually_gt_atTop 0] with n hn hMn hn0 p hp
    obtain ⟨hp1, hp2⟩ := Finset.mem_Ico.mp hp
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn0
    have hhaz0 : 0 ≤ coalescenceHazard (companionSchedule (xa n)) (p + 1) :=
      companion_coalescenceHazard_nonneg (xa n) (hx n).1 (hx n).2 (by omega)
    have hpw0 := pairWeight_nonneg (b n) (c n) (p + 1)
    refine ⟨mul_nonneg hpw0 hhaz0, ?_⟩
    by_cases hall : (∀ j, b n j < p + 1) ∧ ∀ l, c n l < p + 1
    · rw [hHdef]
      simp only
      rw [pairWeight_eq_zero_of_lt hall.1 hall.2, zero_mul]
      exact hδ0 n
    · -- some event lies at or above the step `p + 1`
      have hexists : ∃ q, p + 1 ≤ eventTime (b n) (c n) q := by
        by_contra hne
        push Not at hne
        exact hall ⟨fun j ↦ hne (Sum.inl j), fun l ↦ hne (Sum.inr l)⟩
      obtain ⟨q, hq⟩ := hexists
      have hup : ((p + 1 : ℕ) : ℝ) ≤ (1 - ε') * n :=
        le_trans (by exact_mod_cast hq) (hn q).le
      have hlow : ε' * n ≤ ((p + 1 : ℕ) : ℝ) := by
        have h1 : ε * n < (phaseAbove n ε : ℝ) := by
          unfold phaseAbove
          push_cast
          exact Nat.lt_floor_add_one _
        have h2' : (phaseAbove n ε : ℝ) ≤ p := by exact_mod_cast hp1
        have h3 : ε' * n ≤ ε * n := by nlinarith
        push_cast
        linarith
      have hmem : p + 1 ∈ interiorTimes n ε' (1 - ε') := by
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_range.mpr (by omega), hlow, hup⟩
      have hmin : M n ≤ (activeCount (xa n) (p + 1) : ℝ) := by
        simp only [hMdef]
        exact_mod_cast interiorMinimizer_min xa n ε' (1 - ε') hmem
      have hhaz := companion_coalescenceHazard_le_four_inv_sq (xa n) (hx n).1 (p + 1) hMn hmin
      have hpw := pairWeight_le (b n) (c n) (p + 1)
      simp only [hHdef, hδdef]
      exact mul_le_mul hpw hhaz hhaz0 (by positivity)
  -- the sum over the merge phases is negligible
  have hmerge : Tendsto (fun n ↦ ∑ p ∈ (Finset.Ico (phaseAbove n ε) n).filter
      (fun p ↦ ∃ i, c n i = p), H n p) atTop (𝓝 0) := by
    have hupper : Tendsto (fun n ↦ (m : ℝ) * δ n) atTop (𝓝 0) := by
      simpa using hδ.const_mul (m : ℝ)
    apply squeeze_zero' _ _ hupper
    · filter_upwards [hbound] with n hn
      exact Finset.sum_nonneg fun p hp ↦ (hn p (Finset.mem_filter.mp hp).1).1
    · filter_upwards [hbound] with n hn
      calc _ ≤ ∑ p ∈ (Finset.Ico (phaseAbove n ε) n).filter (fun p ↦ ∃ i, c n i = p), δ n :=
            Finset.sum_le_sum fun p hp ↦ (hn p (Finset.mem_filter.mp hp).1).2
        _ = (((Finset.Ico (phaseAbove n ε) n).filter (fun p ↦ ∃ i, c n i = p)).card : ℝ) *
            δ n := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (m : ℝ) * δ n := by
          apply mul_le_mul_of_nonneg_right _ (hδ0 n)
          have hsub : (Finset.Ico (phaseAbove n ε) n).filter (fun p ↦ ∃ i, c n i = p) ⊆
              Finset.univ.image (c n) := by
            intro p hp
            obtain ⟨i, hi⟩ := (Finset.mem_filter.mp hp).2
            exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hi⟩
          have := (Finset.card_le_card hsub).trans Finset.card_image_le
          rw [Finset.card_univ, Fintype.card_fin] at this
          exact_mod_cast this
  have hsum : Tendsto (fun n ↦ ∑ p ∈ (Finset.Ico (phaseAbove n ε) n).filter
      (fun p ↦ ¬ ∃ i, c n i = p), H n p) atTop
      (𝓝 (∫ t in Ioc ε 1, pairWeight β γ t * g t ^ 2)) := by
    have hall := tendsto_sum_pairWeight_hazard hx hL1 hpos h2 hε hb hc hβ1 hγ1 hβε hγε
    have := hall.sub hmerge
    rw [sub_zero] at this
    refine this.congr fun n ↦ ?_
    rw [← Finset.sum_filter_add_sum_filter_not (Finset.Ico (phaseAbove n ε) n)
      (fun p ↦ ∃ i, c n i = p)]
    ring
  have hbound' : ∀ᶠ n in atTop, ∀ p ∈ (Finset.Ico (phaseAbove n ε) n).filter
      (fun p ↦ ¬ ∃ i, c n i = p), 0 ≤ H n p ∧ H n p ≤ δ n := by
    filter_upwards [hbound] with n hn p hp
    exact hn p (Finset.mem_filter.mp hp).1
  exact tendsto_finite_survival_product hδ hbound' hsum


/-! ### The rescaled conditional local probability -/

/-- The product of the step factors splits into the merge hazards and the survival
factor. -/
theorem prod_stepWeight_eq {x : SignSequence} {n p₀ : ℕ} {b : Fin k → ℕ} {c : Fin m → ℕ}
    (hcinj : Function.Injective c) (hc : ∀ i, p₀ ≤ c i ∧ c i < n) :
    ∏ p ∈ Finset.Ico p₀ n, stepWeight x b c p =
      (∏ i, coalescenceHazard x (c i + 1)) * survivalFactor x n p₀ b c := by
  classical
  rw [← Finset.prod_filter_mul_prod_filter_not (Finset.Ico p₀ n) (fun p ↦ ∃ i, c i = p)]
  congr 1
  · have hset : (Finset.Ico p₀ n).filter (fun p ↦ ∃ i, c i = p) = Finset.univ.image c := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_image, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨-, h⟩
        exact h
      · rintro ⟨i, rfl⟩
        exact ⟨hc i, i, rfl⟩
    rw [hset, Finset.prod_image fun i _ i' _ h ↦ hcinj h]
    refine Finset.prod_congr rfl fun i _ ↦ ?_
    simp [stepWeight]
  · unfold survivalFactor
    refine Finset.prod_congr rfl fun p hp ↦ ?_
    have := (Finset.mem_filter.mp hp).2
    simp [stepWeight, this]

/-- The corrected local event is possible: distinct sampled frozen vertices born at the
down-step phases `b`, merge phases `c` at up-steps strictly above the cutoff `ε n`, and an
admissible merge history `xs` for these phases. -/
def LocalAdmissible (xa : ℕ → ℤ) (n : ℕ) (ε : ℝ) (xs : Fin m → ConnState k) (b : Fin k → ℕ)
    (c : Fin m → ℕ) : Prop :=
  Function.Injective b ∧ (∀ j, b j < n ∧ xa (b j + 1) = -1) ∧ (∀ i, xa (c i + 1) = 1) ∧
    (∀ i, phaseAbove n ε ≤ c i) ∧
    IsAdmissible (fun j ↦ (b j : ℝ)) m n diagState xs (fun i ↦ (c i : ℝ))

open Classical in
/-- **The rescaled conditional local probability** of the corrected statement `eq:cv locale`.
Given that the `k` sampled vertices are the distinct frozen vertices born at the phases `b`, it
is `(n/2)^m` times the probability that the genealogy of the sampled vertices, restricted to
the phases above `ε n`, consists of exactly the `m` merges of the history `xs` at the phases
`c` (`c 0 > ⋯ > c (m-1) > ε n`). Since the sampled vertices are all connected at phase `0`,
this says that `R^n(ε) = r := k - 1 - m` merges occur at phases `≤ ε n` and that the merges
above `ε n` form `xs`. It is `0` when the configuration is impossible (`LocalAdmissible`
fails), in particular for colliding samples. -/
noncomputable def scaledPatternProb (xa : ℕ → ℤ) (n : ℕ) (ε : ℝ) (xs : Fin m → ConnState k)
    (b : Fin k → ℕ) (c : Fin m → ℕ) : ℝ :=
  if LocalAdmissible xa n ε xs b c then
    ((n : ℝ) / 2) ^ m *
      (jointLaw (companionSchedule xa) n).real (patternEvent n (phaseAbove n ε) b xs c)
  else 0

theorem half_mul_coalescenceHazard {xa : ℕ → ℤ} (hx : IsSigned xa) (n : ℕ) {c : ℕ}
    (hc : xa (c + 1) = 1) :
    (n : ℝ) / 2 * coalescenceHazard (companionSchedule xa) (c + 1) =
      auxiliaryAttachmentRate xa n c := by
  have hcs : companionSchedule xa (c + 1) = true := by simp [companionSchedule, hc]
  rw [coalescenceHazard, ite_eq_left hcs, companion_activeCount xa hx, auxiliaryAttachmentRate]
  ring

/-- **Exact formula of the rescaled local probability**: the product of the exact merge
rates `n / (S (S - 1))` at the merge phases and of the exact survival factors. -/
theorem scaledPatternProb_eq {xa : ℕ → ℤ} (hx : IsSigned xa) {n : ℕ} (hs : SurvivesThrough xa n)
    {ε : ℝ} {xs : Fin m → ConnState k} {b : Fin k → ℕ} {c : Fin m → ℕ}
    (h : LocalAdmissible xa n ε xs b c) :
    scaledPatternProb xa n ε xs b c =
      (∏ i, auxiliaryAttachmentRate xa n (c i)) *
        survivalFactor (companionSchedule xa) n (phaseAbove n ε) b c := by
  classical
  obtain ⟨hbinj, hb, hc, hcp, hadm⟩ := h
  have hn : (n : ℕ∞) ≤ extinctionTime (companionSchedule xa) :=
    (companion_before_extinction xa hx hs).le
  have hb' : ∀ j, b j < n ∧ companionSchedule xa (b j + 1) = false := fun j ↦
    ⟨(hb j).1, by simp [companionSchedule, (hb j).2]⟩
  have hcx : ∀ i, companionSchedule xa (c i + 1) = true := fun i ↦ by
    simp [companionSchedule, hc i]
  have hanti : StrictAnti c := fun a a' h ↦ by
    have := hadm.strictAnti h
    exact_mod_cast this
  have hcn : ∀ i, c i < n := fun i ↦ by
    have := (hadm.time_mem i).2
    exact_mod_cast this
  rw [scaledPatternProb, ite_eq_left ⟨hbinj, hb, hc, hcp, hadm⟩,
    jointLaw_patternEvent hn hb' hbinj hcx hadm,
    prod_stepWeight_eq hanti.injective fun i ↦ ⟨hcp i, hcn i⟩, ← mul_assoc]
  congr 1
  rw [← Fin.prod_const m ((n : ℝ) / 2), ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun i _ ↦ half_mul_coalescenceHazard hx n (hc i)


/-! ### Continuous convergence of the local functional -/

theorem tendsto_floor_mul_div {w : ℕ → ℝ} {a : ℝ} (ha : 0 < a)
    (hw : Tendsto w atTop (𝓝 a)) :
    Tendsto (fun n : ℕ ↦ (⌊(n : ℝ) * w n⌋₊ : ℝ) / n) atTop (𝓝 a) := by
  have h1 : Tendsto (fun n : ℕ ↦ w n - 1 / (n : ℝ)) atTop (𝓝 a) := by
    simpa using hw.sub tendsto_one_div_atTop_nhds_zero_nat
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' h1 hw
  · filter_upwards [hw.eventually (lt_mem_nhds ha), eventually_gt_atTop 0] with n hwn hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
    have := Nat.lt_floor_add_one ((n : ℝ) * w n)
    have heq : w n - 1 / (n : ℝ) = ((n : ℝ) * w n - 1) / n := by
      field_simp
    rw [heq]
    exact div_le_div_of_nonneg_right (by linarith) hnpos.le
  · filter_upwards [hw.eventually (lt_mem_nhds ha), eventually_gt_atTop 0] with n hwn hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
    rw [div_le_iff₀ hnpos]
    have := Nat.floor_le (mul_nonneg hnpos.le hwn.le)
    linarith

/-- `IsAdmissible` only depends on the relative order of the times. -/
theorem isAdmissible_congr {b b' : Fin k → ℝ} : ∀ {m : ℕ} {t t' : ℝ} {x : ConnState k}
    {xs : Fin m → ConnState k} {cs cs' : Fin m → ℝ},
    (∀ i, 0 < cs i ↔ 0 < cs' i) → (∀ i, cs i < t ↔ cs' i < t') →
    (∀ i l, cs i < cs l ↔ cs' i < cs' l) → (∀ i j, cs i ≤ b j ↔ cs' i ≤ b' j) →
    (IsAdmissible b m t x xs cs ↔ IsAdmissible b' m t' x xs cs')
  | 0, _, _, _, _, _, _, _, _, _, _ => Iff.rfl
  | m + 1, t, t', x, xs, cs, cs', h0, ht, hcc, hcb => by
    have hborn : bornAt b (cs 0) = bornAt b' (cs' 0) := by
      ext j
      simp only [bornAt, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hcb 0 j
    have ih := isAdmissible_congr (b := b) (b' := b') (m := m) (t := cs 0) (t' := cs' 0)
      (x := xs 0) (xs := Fin.tail xs) (cs := Fin.tail cs) (cs' := Fin.tail cs')
      (fun i ↦ h0 i.succ) (fun i ↦ hcc i.succ 0) (fun i l ↦ hcc i.succ l.succ)
      (fun i j ↦ hcb i.succ j)
    simp only [IsAdmissible, hborn, h0 0, ht 0, ih]

/-- The order part of `LocalAdmissible`: distinct births, merges above the cutoff, and an
admissible history for the integer phases. -/
def OrderAdmissible (n : ℕ) (ε : ℝ) (xs : Fin m → ConnState k) (b : Fin k → ℕ)
    (c : Fin m → ℕ) : Prop :=
  Function.Injective b ∧ (∀ i, phaseAbove n ε ≤ c i) ∧
    IsAdmissible (fun j ↦ (b j : ℝ)) m n diagState xs (fun i ↦ (c i : ℝ))

/-- The continuous counterpart: distinct births, merge times above `ε`, and an admissible
history. -/
def ContAdmissible (ε : ℝ) (xs : Fin m → ConnState k) (β : Fin k → ℝ) (γ : Fin m → ℝ) : Prop :=
  Function.Injective β ∧ (∀ i, ε < γ i) ∧ IsAdmissible β m 1 diagState xs γ

theorem eventually_cast_lt_iff {u v : ℕ → ℕ} {a a' : ℝ}
    (hu : Tendsto (fun n ↦ (u n : ℝ) / n) atTop (𝓝 a))
    (hv : Tendsto (fun n ↦ (v n : ℝ) / n) atTop (𝓝 a')) (h : a ≠ a') :
    ∀ᶠ n in atTop, ((u n : ℝ) < v n ↔ a < a') := by
  rcases lt_or_gt_of_ne h with hlt | hgt
  · filter_upwards [eventually_lt_of_tendsto_div hu hv hlt] with n hn
    exact ⟨fun _ ↦ hlt, fun _ ↦ by exact_mod_cast hn⟩
  · filter_upwards [eventually_lt_of_tendsto_div hv hu hgt] with n hn
    have : ¬ ((u n : ℝ) < v n) := not_lt.mpr (by exact_mod_cast hn.le)
    exact ⟨fun h' ↦ absurd h' this, fun h' ↦ absurd h' (not_lt.mpr hgt.le)⟩

theorem eventually_cast_le_iff {u v : ℕ → ℕ} {a a' : ℝ}
    (hu : Tendsto (fun n ↦ (u n : ℝ) / n) atTop (𝓝 a))
    (hv : Tendsto (fun n ↦ (v n : ℝ) / n) atTop (𝓝 a')) (h : a ≠ a') :
    ∀ᶠ n in atTop, ((u n : ℝ) ≤ v n ↔ a ≤ a') := by
  filter_upwards [eventually_cast_lt_iff hv hu h.symm] with n hn
  rw [← not_lt, hn, not_lt]

/-- **Eventual agreement of the discrete and continuous admissibility** for configurations
converging to distinct limits in `(0, 1)` different from the cutoff. -/
theorem eventually_orderAdmissible_iff {ε : ℝ} (hε : 0 ≤ ε) (xs : Fin m → ConnState k)
    {b : ℕ → Fin k → ℕ} {c : ℕ → Fin m → ℕ} {β : Fin k → ℝ} {γ : Fin m → ℝ}
    (hb : ∀ j, Tendsto (fun n ↦ (b n j : ℝ) / n) atTop (𝓝 (β j)))
    (hc : ∀ l, Tendsto (fun n ↦ (c n l : ℝ) / n) atTop (𝓝 (γ l)))
    (hγ : ∀ i, 0 < γ i ∧ γ i < 1) (hinj : Function.Injective (Sum.elim β γ))
    (hγε : ∀ i, γ i ≠ ε) :
    ∀ᶠ n in atTop, (OrderAdmissible n ε xs (b n) (c n) ↔ ContAdmissible ε xs β γ) := by
  have hβinj : Function.Injective β := hinj.comp Sum.inl_injective
  have hγinj : Function.Injective γ := hinj.comp Sum.inr_injective
  have hp := tendsto_phaseAbove_div hε
  -- injectivity of the births
  have e1 : ∀ᶠ n in atTop, Function.Injective (b n) := by
    have : ∀ j j', ∀ᶠ n in atTop, j ≠ j' → b n j ≠ b n j' := by
      intro j j'
      by_cases hjj : j = j'
      · exact Eventually.of_forall fun _ h ↦ absurd hjj h
      · have hne : β j ≠ β j' := fun h ↦ hjj (hβinj h)
        filter_upwards [eventually_cast_lt_iff (hb j) (hb j') hne,
          eventually_cast_lt_iff (hb j') (hb j) hne.symm] with n h1 h2 _ heq
        rcases lt_or_gt_of_ne hne with hlt | hgt
        · have := h1.mpr hlt
          rw [heq] at this
          exact lt_irrefl _ this
        · have := h2.mpr hgt
          rw [heq] at this
          exact lt_irrefl _ this
    filter_upwards [eventually_all.mpr fun j ↦ eventually_all.mpr fun j' ↦ this j j'] with n hn
    intro j j' h
    by_contra hjj
    exact hn j j' hjj h
  -- the cutoff
  have e2 : ∀ i, ∀ᶠ n in atTop, (phaseAbove n ε ≤ c n i ↔ ε < γ i) := by
    intro i
    rcases lt_or_gt_of_ne (hγε i) with hlt | hgt
    · filter_upwards [eventually_lt_of_tendsto_div (hc i) hp hlt] with n hn
      exact ⟨fun h ↦ absurd (lt_of_le_of_lt h hn) (lt_irrefl _),
        fun h ↦ absurd h (not_lt.mpr hlt.le)⟩
    · filter_upwards [eventually_lt_of_tendsto_div hp (hc i) hgt] with n hn
      exact ⟨fun _ ↦ hgt, fun _ ↦ hn.le⟩
  have e3 : ∀ i, ∀ᶠ n in atTop, (0 < (c n i : ℝ) ↔ 0 < γ i) := by
    intro i
    filter_upwards [eventually_mul_lt_of_tendsto (hc i) (hγ i).1] with n hn
    simp only [zero_mul] at hn
    exact ⟨fun _ ↦ (hγ i).1, fun _ ↦ hn⟩
  have e4 : ∀ i, ∀ᶠ n in atTop, ((c n i : ℝ) < (n : ℝ) ↔ γ i < 1) := by
    intro i
    filter_upwards [eventually_lt_mul_of_tendsto (hc i) (hγ i).2] with n hn
    simp only [one_mul] at hn
    exact ⟨fun _ ↦ (hγ i).2, fun _ ↦ hn⟩
  have e5 : ∀ i l, ∀ᶠ n in atTop, ((c n i : ℝ) < c n l ↔ γ i < γ l) := by
    intro i l
    by_cases hil : i = l
    · subst hil
      exact Eventually.of_forall fun _ ↦ ⟨fun h ↦ absurd h (lt_irrefl _),
        fun h ↦ absurd h (lt_irrefl _)⟩
    · exact eventually_cast_lt_iff (hc i) (hc l) fun h ↦ hil (hγinj h)
  have e6 : ∀ i j, ∀ᶠ n in atTop, ((c n i : ℝ) ≤ b n j ↔ γ i ≤ β j) := by
    intro i j
    have hne : γ i ≠ β j := fun h ↦ by
      have := hinj (a₁ := Sum.inr i) (a₂ := Sum.inl j) (by simpa using h)
      exact Sum.inr_ne_inl this
    exact eventually_cast_le_iff (hc i) (hb j) hne
  filter_upwards [e1, eventually_all.mpr e2, eventually_all.mpr e3, eventually_all.mpr e4,
    eventually_all.mpr fun i ↦ eventually_all.mpr (e5 i),
    eventually_all.mpr fun i ↦ eventually_all.mpr (e6 i)] with n h1 h2 h3 h4 h5 h6
  have hadm : IsAdmissible (fun j ↦ (b n j : ℝ)) m n diagState xs (fun i ↦ (c n i : ℝ)) ↔
      IsAdmissible β m 1 diagState xs γ :=
    isAdmissible_congr (fun i ↦ h3 i) (fun i ↦ h4 i) (fun i l ↦ h5 i l) (fun i j ↦ h6 i j)
  unfold OrderAdmissible ContAdmissible
  rw [hadm]
  constructor
  · rintro ⟨-, hcut, ha⟩
    exact ⟨hβinj, fun i ↦ (h2 i).mp (hcut i), ha⟩
  · rintro ⟨-, hcut, ha⟩
    exact ⟨h1, fun i ↦ (h2 i).mpr (hcut i), ha⟩

/-- The space of local configurations: `k` birth times and `m` pairs (merge time, rate mark). -/
abbrev LocalSpace (k m : ℕ) := (Fin k → ℝ) × (Fin m → ℝ × ℝ)

/-- The merge times of a configuration. -/
def mergeTimes (z : LocalSpace k m) : Fin m → ℝ := fun i ↦ (z.2 i).1

/-- The integer birth phases `⌊n β⌋₊` of a configuration. -/
noncomputable def floorBirths (n : ℕ) (z : LocalSpace k m) : Fin k → ℕ :=
  fun j ↦ ⌊(n : ℝ) * z.1 j⌋₊

/-- The integer merge phases `⌊n γ⌋₊` of a configuration. -/
noncomputable def floorMerges (n : ℕ) (z : LocalSpace k m) : Fin m → ℕ :=
  fun i ↦ ⌊(n : ℝ) * (z.2 i).1⌋₊

open Classical in
/-- **The discrete local functional** at horizon `n`: the product of the rate marks and the
exact survival factor at the integer phases of the configuration, on order-admissible
configurations. At an actual sample whose marks are the exact merge rates, it is the
rescaled local probability `scaledPatternProb`. -/
noncomputable def discFun (xa : ℕ → ℤ) (n : ℕ) (ε : ℝ) (xs : Fin m → ConnState k)
    (z : LocalSpace k m) : ℝ :=
  if OrderAdmissible n ε xs (floorBirths n z) (floorMerges n z) then
    (∏ i, (z.2 i).2) *
      survivalFactor (companionSchedule xa) n (phaseAbove n ε) (floorBirths n z) (floorMerges n z)
  else 0

open Classical in
/-- **The limit local functional** at cutoff `ε`: on admissible configurations with merges above
`ε`, the product of the marks and `exp (-∫_ε^1 C(a(t), 2) g(t)² dt)`. At marks `g(γ)²` it is
the truncation of the density `g_{r,k}` (non-plane form) to the merges above `ε`. -/
noncomputable def limitFun (g : ℝ → ℝ) (ε : ℝ) (xs : Fin m → ConnState k)
    (z : LocalSpace k m) : ℝ :=
  if ContAdmissible ε xs z.1 (mergeTimes z) then
    (∏ i, (z.2 i).2) * Real.exp (-∫ t in Ioc ε 1, pairWeight z.1 (mergeTimes z) t * g t ^ 2)
  else 0

/-- Configurations with distinct times in `(0, 1)`, all different from the cutoff. -/
def goodSet (ε : ℝ) : Set (LocalSpace k m) :=
  {z | (∀ j, 0 < z.1 j ∧ z.1 j < 1) ∧ (∀ i, 0 < (z.2 i).1 ∧ (z.2 i).1 < 1) ∧
    Function.Injective (Sum.elim z.1 (mergeTimes z)) ∧ (∀ j, z.1 j ≠ ε) ∧
    ∀ i, (z.2 i).1 ≠ ε}

/-- **Continuous convergence of the local functional.** Along any sequence of configurations
converging to a good configuration, the discrete functionals converge to the limit
functional. This is the pointwise local limit at fixed admissible times, with the merge-rate
marks as separate inputs (S10: their convergence comes from the joint law of time and mark,
not from convergence of locations). -/
theorem tendsto_discFun {xa : ℕ → ℕ → ℤ} {g : ℝ → ℝ} (hx : AdmissibleArray xa)
    (hL1 : HasL1ReciprocalProfile xa (1 / 2) g) (hpos : PositiveProfile g)
    (h2 : HasLocalSquareMomentProfile xa (1 / 2) g) {ε : ℝ} (hε : 0 < ε)
    (xs : Fin m → ConnState k) {z : LocalSpace k m} (hz : z ∈ goodSet ε)
    {w : ℕ → LocalSpace k m} (hw : Tendsto w atTop (𝓝 z)) :
    Tendsto (fun n ↦ discFun (xa n) n ε xs (w n)) atTop (𝓝 (limitFun g ε xs z)) := by
  classical
  obtain ⟨hβ, hγ, hinj, hβε, hγε⟩ := hz
  have hwb : ∀ j, Tendsto (fun n ↦ (w n).1 j) atTop (𝓝 (z.1 j)) := fun j ↦
    ((show Continuous (fun z : LocalSpace k m ↦ z.1 j) by fun_prop).tendsto z).comp hw
  have hwc : ∀ i, Tendsto (fun n ↦ ((w n).2 i).1) atTop (𝓝 ((z.2 i).1)) := fun i ↦
    ((show Continuous (fun z : LocalSpace k m ↦ (z.2 i).1) by fun_prop).tendsto z).comp hw
  have hwr : ∀ i, Tendsto (fun n ↦ ((w n).2 i).2) atTop (𝓝 ((z.2 i).2)) := fun i ↦
    ((show Continuous (fun z : LocalSpace k m ↦ (z.2 i).2) by fun_prop).tendsto z).comp hw
  have hb : ∀ j, Tendsto (fun n ↦ (floorBirths n (w n) j : ℝ) / n) atTop (𝓝 (z.1 j)) :=
    fun j ↦ tendsto_floor_mul_div (hβ j).1 (hwb j)
  have hc : ∀ i, Tendsto (fun n ↦ (floorMerges n (w n) i : ℝ) / n) atTop
      (𝓝 (mergeTimes z i)) := fun i ↦ tendsto_floor_mul_div (hγ i).1 (hwc i)
  have hadm := eventually_orderAdmissible_iff hε.le xs hb hc hγ hinj hγε
  have hsurv := tendsto_survivalFactor hx hL1 hpos h2 hε hb hc (fun j ↦ (hβ j).2)
    (fun i ↦ (hγ i).2) hβε hγε
  have hprod : Tendsto (fun n ↦ ∏ i, ((w n).2 i).2) atTop (𝓝 (∏ i, (z.2 i).2)) :=
    tendsto_finsetProd _ fun i _ ↦ hwr i
  by_cases hA : ContAdmissible ε xs z.1 (mergeTimes z)
  · rw [limitFun, ite_eq_left hA]
    apply (hprod.mul hsurv).congr'
    filter_upwards [hadm] with n hn
    rw [discFun, ite_eq_left (hn.mpr hA)]
  · rw [limitFun, ite_eq_right hA]
    apply tendsto_const_nhds.congr'
    filter_upwards [hadm] with n hn
    rw [discFun, ite_eq_right fun h ↦ hA (hn.mp h)]


/-! ### An extended continuous mapping theorem -/

/-- **Sequential continuous convergence is uniform near the point.** If `F n (w n) → L` for
every sequence `w n → z`, then for every neighbourhood `V` of `L`, `F n x ∈ V` for all large
`n` and all `x` close to `z`. -/
theorem eventually_uniform_of_seq {X Y : Type*} [PseudoMetricSpace X] [TopologicalSpace Y]
    {F : ℕ → X → Y} {z : X} {L : Y}
    (h : ∀ w : ℕ → X, Tendsto w atTop (𝓝 z) → Tendsto (fun n ↦ F n (w n)) atTop (𝓝 L))
    {V : Set Y} (hV : V ∈ 𝓝 L) :
    ∃ N, ∃ δ > 0, ∀ n ≥ N, ∀ x, dist x z < δ → F n x ∈ V := by
  classical
  by_contra hne
  push Not at hne
  have hne' : ∀ j : ℕ, ∃ n, j ≤ n ∧ ∃ x, dist x z < 1 / ((j : ℝ) + 1) ∧ F n x ∉ V :=
    fun j ↦ by
      obtain ⟨n, hn, x, hx, hF⟩ := hne j (1 / ((j : ℝ) + 1)) (by positivity)
      exact ⟨n, hn, x, hx, hF⟩
  choose nn hnn ww hww hF using hne'
  let w' : ℕ → X := fun n ↦
    if ∃ j, nn j = n then ww (Nat.findGreatest (fun j ↦ nn j = n) n) else z
  have hspec : ∀ n, (∃ j, nn j = n) → nn (Nat.findGreatest (fun j ↦ nn j = n) n) = n := by
    rintro n ⟨j, hj⟩
    exact Nat.findGreatest_spec (P := fun j ↦ nn j = n) (hj ▸ hnn j) hj
  have hw' : Tendsto w' atTop (𝓝 z) := by
    rw [Metric.tendsto_atTop]
    intro δ hδ
    obtain ⟨J, hJ⟩ := exists_nat_one_div_lt hδ
    refine ⟨(Finset.range J).sup nn + 1, fun n hn ↦ ?_⟩
    by_cases hex : ∃ j, nn j = n
    · simp only [w', ite_eq_left hex]
      have hj := hspec n hex
      generalize Nat.findGreatest (fun j ↦ nn j = n) n = j at hj ⊢
      have hJj : J ≤ j := by
        by_contra hlt
        push Not at hlt
        have : nn j ≤ (Finset.range J).sup nn := Finset.le_sup (Finset.mem_range.mpr hlt)
        omega
      calc dist (ww j) z < 1 / ((j : ℝ) + 1) := hww j
        _ ≤ 1 / ((J : ℝ) + 1) := by
          apply one_div_le_one_div_of_le (by positivity)
          exact_mod_cast Nat.add_le_add_right hJj 1
        _ < δ := hJ
    · simp only [w', ite_eq_right hex, dist_self]
      exact hδ
  obtain ⟨N1, hN1⟩ := eventually_atTop.mp ((h w' hw').eventually hV)
  have hex : ∃ j, nn j = nn N1 := ⟨N1, rfl⟩
  have hmem := hN1 (nn N1) (hnn N1)
  simp only [w', ite_eq_left hex] at hmem
  have hj := hspec (nn N1) hex
  have := hF (Nat.findGreatest (fun j ↦ nn j = nn N1) (nn N1))
  rw [hj] at this
  exact this hmem

/-- **Extended continuous mapping theorem.** Let `μs n → μ` weakly, and let the measurable
maps `Φs n` converge continuously to `Φ` at every point of a set `G` of full `μ`-measure:
`Φs n (w n) → Φ z` whenever `w n → z ∈ G`. Then the image laws converge weakly. -/
theorem tendsto_map_of_continuousConvergence {Ω : Type*} [MeasurableSpace Ω]
    [PseudoMetricSpace Ω] [OpensMeasurableSpace Ω]
    {μs : ℕ → ProbabilityMeasure Ω} {μ : ProbabilityMeasure Ω} (hμ : Tendsto μs atTop (𝓝 μ))
    {Φs : ℕ → Ω → ℝ} {Φ : Ω → ℝ} (hΦs : ∀ n, Measurable (Φs n)) (hΦ : Measurable Φ)
    {G : Set Ω} (hG : (μ : Measure Ω) Gᶜ = 0)
    (hconv : ∀ z ∈ G, ∀ w : ℕ → Ω, Tendsto w atTop (𝓝 z) →
      Tendsto (fun n ↦ Φs n (w n)) atTop (𝓝 (Φ z))) :
    Tendsto (fun n ↦ (μs n).map (Φs n)) atTop (𝓝 (μ.map Φ)) := by
  apply tendsto_of_forall_isClosed_limsup_le'
  intro F hF
  simp only [ProbabilityMeasure.toMeasure_map]
  rw [Measure.map_apply hΦ hF.measurableSet]
  have hmap : ∀ n, (μs n : Measure Ω).map (Φs n) F = (μs n : Measure Ω) (Φs n ⁻¹' F) :=
    fun n ↦ Measure.map_apply (hΦs n) hF.measurableSet
  simp only [hmap]
  set A : ℕ → Set Ω := fun N ↦ closure (⋃ n, ⋃ (_ : N ≤ n), Φs n ⁻¹' F) with hAdef
  have hAclosed : ∀ N, IsClosed (A N) := fun N ↦ isClosed_closure
  have hstep : ∀ N, limsup (fun n ↦ (μs n : Measure Ω) (Φs n ⁻¹' F)) atTop ≤
      (μ : Measure Ω) (A N) := by
    intro N
    calc limsup (fun n ↦ (μs n : Measure Ω) (Φs n ⁻¹' F)) atTop
        ≤ limsup (fun n ↦ (μs n : Measure Ω) (A N)) atTop := by
          refine limsup_le_limsup ?_ (by isBoundedDefault) (by isBoundedDefault)
          filter_upwards [eventually_ge_atTop N] with n hn
          apply measure_mono
          intro x hx
          exact subset_closure (mem_iUnion₂.mpr ⟨n, hn, hx⟩)
      _ ≤ (μ : Measure Ω) (A N) :=
          ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hμ (hAclosed N)
  have hanti : Antitone A := by
    intro N N' hNN'
    apply closure_mono
    intro x hx
    obtain ⟨n, hn, hx⟩ := mem_iUnion₂.mp hx
    exact mem_iUnion₂.mpr ⟨n, hNN'.trans hn, hx⟩
  have hlim : Tendsto (fun N ↦ (μ : Measure Ω) (A N)) atTop
      (𝓝 ((μ : Measure Ω) (⋂ N, A N))) :=
    tendsto_measure_iInter_atTop (fun N ↦ (hAclosed N).measurableSet.nullMeasurableSet) hanti
      ⟨0, measure_ne_top _ _⟩
  have hle : limsup (fun n ↦ (μs n : Measure Ω) (Φs n ⁻¹' F)) atTop ≤
      (μ : Measure Ω) (⋂ N, A N) := ge_of_tendsto' hlim hstep
  refine hle.trans ?_
  have hsub : (⋂ N, A N) ⊆ Φ ⁻¹' F ∪ Gᶜ := by
    intro z hz
    by_cases hzG : z ∈ G
    · left
      by_contra hzF
      obtain ⟨N, δ, hδ, hgood⟩ := eventually_uniform_of_seq (hconv z hzG)
        (hF.isOpen_compl.mem_nhds hzF)
      have hzA := mem_iInter.mp hz N
      obtain ⟨x, hx, hdist⟩ := Metric.mem_closure_iff.mp hzA δ hδ
      obtain ⟨n, hn, hxF⟩ := mem_iUnion₂.mp hx
      exact hgood n hn x (by rwa [dist_comm]) hxF
    · exact Or.inr hzG
  calc (μ : Measure Ω) (⋂ N, A N) ≤ (μ : Measure Ω) (Φ ⁻¹' F ∪ Gᶜ) := measure_mono hsub
    _ ≤ (μ : Measure Ω) (Φ ⁻¹' F) + (μ : Measure Ω) Gᶜ := measure_union_le _ _
    _ = (μ : Measure Ω) (Φ ⁻¹' F) := by rw [hG, add_zero]

/-! ### Measurability of the local functionals -/

theorem measurable_floorBirths (n : ℕ) :
    Measurable (fun z : LocalSpace k m ↦ floorBirths n z) :=
  measurable_pi_iff.mpr fun j ↦
    (measurable_const.mul ((measurable_pi_apply j).comp measurable_fst)).nat_floor

theorem measurable_floorMerges (n : ℕ) :
    Measurable (fun z : LocalSpace k m ↦ floorMerges n z) :=
  measurable_pi_iff.mpr fun i ↦ (measurable_const.mul
    (measurable_fst.comp ((measurable_pi_apply i).comp measurable_snd))).nat_floor

theorem measurable_prod_marks :
    Measurable (fun z : LocalSpace k m ↦ ∏ i, (z.2 i).2) :=
  Finset.measurable_prod _ fun i _ ↦
    measurable_snd.comp ((measurable_pi_apply i).comp measurable_snd)

theorem measurable_discFun (xa : ℕ → ℤ) (n : ℕ) (ε : ℝ) (xs : Fin m → ConnState k) :
    Measurable (discFun xa n ε xs) := by
  classical
  let Ψ : (Fin k → ℕ) × (Fin m → ℕ) → ℝ := fun q ↦
    if OrderAdmissible n ε xs q.1 q.2 then
      survivalFactor (companionSchedule xa) n (phaseAbove n ε) q.1 q.2 else 0
  have hΨ : Measurable Ψ := measurable_of_countable Ψ
  have heq : discFun xa n ε xs =
      fun z ↦ Ψ (floorBirths n z, floorMerges n z) * ∏ i, (z.2 i).2 := by
    funext z
    simp only [discFun, Ψ]
    split_ifs <;> ring
  rw [heq]
  exact (hΨ.comp ((measurable_floorBirths n).prodMk (measurable_floorMerges n))).mul
    measurable_prod_marks

/-- The relative order of the coordinates of a configuration and of the cutoff. -/
noncomputable def orderData (ε : ℝ) (z : LocalSpace k m) :
    (Fin k → Fin k → Bool) × (Fin m → Bool) × (Fin m → Bool) × (Fin m → Bool) ×
      (Fin m → Fin m → Bool) × (Fin m → Fin k → Bool) :=
  (fun j j' ↦ decide (z.1 j < z.1 j'), fun i ↦ decide (ε < (z.2 i).1),
    fun i ↦ decide (0 < (z.2 i).1), fun i ↦ decide ((z.2 i).1 < 1),
    fun i l ↦ decide ((z.2 i).1 < (z.2 l).1), fun i j ↦ decide ((z.2 i).1 ≤ z.1 j))

theorem measurable_decide {X : Type*} [MeasurableSpace X] {p : X → Prop} [DecidablePred p]
    (hp : MeasurableSet {x | p x}) : Measurable (fun x ↦ decide (p x)) := by
  apply measurable_to_bool
  convert hp using 1
  ext x
  simp

theorem measurable_orderData (ε : ℝ) : Measurable (orderData (k := k) (m := m) ε) := by
  have hβ : ∀ j, Measurable (fun z : LocalSpace k m ↦ z.1 j) := fun j ↦
    (measurable_pi_apply j).comp measurable_fst
  have hγ : ∀ i, Measurable (fun z : LocalSpace k m ↦ (z.2 i).1) := fun i ↦
    measurable_fst.comp ((measurable_pi_apply i).comp measurable_snd)
  refine Measurable.prodMk ?_ (Measurable.prodMk ?_ (Measurable.prodMk ?_
    (Measurable.prodMk ?_ (Measurable.prodMk ?_ ?_))))
  · exact measurable_pi_iff.mpr fun j ↦ measurable_pi_iff.mpr fun j' ↦
      measurable_decide (measurableSet_lt (hβ j) (hβ j'))
  · exact measurable_pi_iff.mpr fun i ↦ measurable_decide (measurableSet_lt measurable_const (hγ i))
  · exact measurable_pi_iff.mpr fun i ↦ measurable_decide (measurableSet_lt measurable_const (hγ i))
  · exact measurable_pi_iff.mpr fun i ↦ measurable_decide (measurableSet_lt (hγ i) measurable_const)
  · exact measurable_pi_iff.mpr fun i ↦ measurable_pi_iff.mpr fun l ↦
      measurable_decide (measurableSet_lt (hγ i) (hγ l))
  · exact measurable_pi_iff.mpr fun i ↦ measurable_pi_iff.mpr fun j ↦
      measurable_decide (measurableSet_le (hγ i) (hβ j))

/-- Configurations with the same order data have the same distinctness of births, position
of the merges relative to the cutoff, and admissibility. -/
theorem orderData_congr {ε : ℝ} (xs : Fin m → ConnState k) {z z' : LocalSpace k m}
    (h : orderData ε z = orderData ε z') :
    (Function.Injective z.1 ↔ Function.Injective z'.1) ∧
      ((∀ i, ε < mergeTimes z i) ↔ ∀ i, ε < mergeTimes z' i) ∧
      (IsAdmissible z.1 m 1 diagState xs (mergeTimes z) ↔
        IsAdmissible z'.1 m 1 diagState xs (mergeTimes z')) := by
  simp only [orderData, Prod.mk.injEq] at h
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  have e1 : ∀ j j', (z.1 j < z.1 j' ↔ z'.1 j < z'.1 j') := fun j j' ↦
    decide_eq_decide.mp (congrFun (congrFun h1 j) j')
  have e2 : ∀ i, (ε < (z.2 i).1 ↔ ε < (z'.2 i).1) := fun i ↦
    decide_eq_decide.mp (congrFun h2 i)
  have e3 : ∀ i, (0 < (z.2 i).1 ↔ 0 < (z'.2 i).1) := fun i ↦
    decide_eq_decide.mp (congrFun h3 i)
  have e4 : ∀ i, ((z.2 i).1 < 1 ↔ (z'.2 i).1 < 1) := fun i ↦
    decide_eq_decide.mp (congrFun h4 i)
  have e5 : ∀ i l, ((z.2 i).1 < (z.2 l).1 ↔ (z'.2 i).1 < (z'.2 l).1) := fun i l ↦
    decide_eq_decide.mp (congrFun (congrFun h5 i) l)
  have e6 : ∀ i j, ((z.2 i).1 ≤ z.1 j ↔ (z'.2 i).1 ≤ z'.1 j) := fun i j ↦
    decide_eq_decide.mp (congrFun (congrFun h6 i) j)
  have hinj : Function.Injective z.1 ↔ Function.Injective z'.1 := by
    have key : ∀ β : Fin k → ℝ, Function.Injective β ↔
        ∀ j j', j ≠ j' → β j < β j' ∨ β j' < β j := by
      intro β
      constructor
      · intro hβ j j' hjj
        exact lt_or_gt_of_ne fun h ↦ hjj (hβ h)
      · intro hβ j j' h
        by_contra hjj
        rcases hβ j j' hjj with hlt | hlt <;> rw [h] at hlt <;> exact lt_irrefl _ hlt
    rw [key, key]
    exact forall_congr' fun j ↦ forall_congr' fun j' ↦ imp_congr_right fun _ ↦
      or_congr (e1 j j') (e1 j' j)
  exact ⟨hinj, forall_congr' e2, isAdmissible_congr (b := z.1) (b' := z'.1) (t := 1) (t' := 1)
    (x := diagState) (xs := xs) (cs := mergeTimes z) (cs' := mergeTimes z') e3 e4 e5 e6⟩

theorem contAdmissible_congr {ε : ℝ} (xs : Fin m → ConnState k) {z z' : LocalSpace k m}
    (h : orderData ε z = orderData ε z') :
    ContAdmissible ε xs z.1 (mergeTimes z) ↔ ContAdmissible ε xs z'.1 (mergeTimes z') := by
  obtain ⟨h1, h2, h3⟩ := orderData_congr xs h
  unfold ContAdmissible
  rw [h1, h2, h3]

/-- A set of configurations determined by the order data is measurable. -/
theorem measurableSet_of_orderData (ε : ℝ) {P : LocalSpace k m → Prop}
    (hP : ∀ z z', orderData ε z = orderData ε z' → (P z ↔ P z')) :
    MeasurableSet {z : LocalSpace k m | P z} := by
  have : {z : LocalSpace k m | P z} = orderData ε ⁻¹' (orderData ε '' {z | P z}) := by
    ext z
    constructor
    · intro hz
      exact ⟨z, hz, rfl⟩
    · rintro ⟨z', hz', he⟩
      exact (hP z' z he).mp hz'
  rw [this]
  exact measurable_orderData ε (Set.to_countable _).measurableSet

theorem measurableSet_contAdmissible (ε : ℝ) (xs : Fin m → ConnState k) :
    MeasurableSet {z : LocalSpace k m | ContAdmissible ε xs z.1 (mergeTimes z)} :=
  measurableSet_of_orderData ε fun _ _ h ↦ contAdmissible_congr xs h

theorem measurable_countAbove_pair {ι : Type*} [Fintype ι] {X : Type*} [MeasurableSpace X]
    {e : X → ι → ℝ} (he : ∀ q, Measurable fun x ↦ e x q) {t : X → ℝ} (ht : Measurable t) :
    Measurable (fun x ↦ (countAbove (e x) (t x) : ℝ)) := by
  classical
  simp_rw [countAbove_eq_sum]
  refine Finset.measurable_sum _ fun q _ ↦ ?_
  unfold leInd
  exact Measurable.ite (measurableSet_le ht (he q)) measurable_const measurable_const

theorem measurable_survivalExponent {g : ℝ → ℝ} (hg : Measurable g) (ε : ℝ) :
    Measurable (fun z : LocalSpace k m ↦
      ∫ t in Ioc ε 1, pairWeight z.1 (mergeTimes z) t * g t ^ 2) := by
  have hβ : ∀ j, Measurable (fun p : LocalSpace k m × ℝ ↦ p.1.1 j) := fun j ↦
    (measurable_pi_apply j).comp (measurable_fst.comp measurable_fst)
  have hγ : ∀ i, Measurable (fun p : LocalSpace k m × ℝ ↦ mergeTimes p.1 i) := fun i ↦
    measurable_fst.comp ((measurable_pi_apply i).comp (measurable_snd.comp measurable_fst))
  have hb := measurable_countAbove_pair (e := fun p : LocalSpace k m × ℝ ↦ p.1.1) hβ measurable_snd
  have hc := measurable_countAbove_pair (e := fun p : LocalSpace k m × ℝ ↦ mergeTimes p.1) hγ
    measurable_snd
  have hF : Measurable (fun p : LocalSpace k m × ℝ ↦
      pairWeight p.1.1 (mergeTimes p.1) p.2 * g p.2 ^ 2) := by
    unfold pairWeight clusterNum
    exact (((hb.sub hc).mul ((hb.sub hc).sub measurable_const)).div_const 2).mul
      ((hg.comp measurable_snd).pow_const 2)
  exact (hF.stronglyMeasurable.integral_prod_right' (ν := volume.restrict (Ioc ε 1))).measurable

theorem measurable_limitFun {g : ℝ → ℝ} (hg : Measurable g) (ε : ℝ) (xs : Fin m → ConnState k) :
    Measurable (limitFun g ε xs) := by
  classical
  unfold limitFun
  exact Measurable.ite (measurableSet_contAdmissible ε xs)
    (measurable_prod_marks.mul (Real.measurable_exp.comp
      (measurable_survivalExponent hg ε).neg)) measurable_const


/-! ### The local limit in distribution at a fixed cutoff -/

/-- The joint law of the auxiliary samples: `k` independent uniform frozen birth phases and `m`
independent uniform attachment phases with their exact merge rates `n / (S (S - 1))`, all
scaled by `n`. At every horizon with both sign sets nonempty it is the source's sampler. -/
noncomputable def auxLocalLaw (xa : ℕ → ℤ) (n k m : ℕ) : ProbabilityMeasure (LocalSpace k m) :=
  (auxiliarySignVectorLaw xa (fun _ : Fin k ↦ (-1 : ℤ)) n).prod
    (ProbabilityMeasure.pi fun _ : Fin m ↦ auxiliaryAttachmentMarkedLaw xa n)

/-- The limit law: independent uniform births on `[0, 1]`, and independent uniform merge times
marked by `g² = f⁻²`. -/
noncomputable def limitLocalLaw (g : ℝ → ℝ) (k m : ℕ) : ProbabilityMeasure (LocalSpace k m) :=
  (ProbabilityMeasure.pi fun _ : Fin k ↦ profileProbabilityMeasure).prod
    (ProbabilityMeasure.pi fun _ : Fin m ↦
      profileProbabilityMeasure.map (fun t ↦ (t, g t ^ 2)))

/-- The births and merge times of the limit law are independent uniform variables. -/
theorem map_times_limitLocalLaw {g : ℝ → ℝ} (hg : Measurable g) :
    (limitLocalLaw g k m : Measure (LocalSpace k m)).map (fun z ↦ (z.1, mergeTimes z)) =
      (cubeMeasure k).prod (cubeMeasure m) := by
  have hh : Measurable (fun t : ℝ ↦ (t, g t ^ 2)) := measurable_id.prodMk (hg.pow_const 2)
  have hf : Measurable (fun v : Fin m → ℝ × ℝ ↦ fun i ↦ (v i).1) :=
    measurable_pi_iff.mpr fun i ↦ measurable_fst.comp (measurable_pi_apply i)
  have hπ : (fun z : LocalSpace k m ↦ (z.1, mergeTimes z)) =
      Prod.map id (fun v : Fin m → ℝ × ℝ ↦ fun i ↦ (v i).1) := rfl
  rw [hπ]
  change ((Measure.pi fun _ : Fin k ↦ (profileMeasure : Measure ℝ)).prod
    (Measure.pi fun _ : Fin m ↦ (profileMeasure : Measure ℝ).map (fun t ↦ (t, g t ^ 2)))).map
      (Prod.map id (fun v : Fin m → ℝ × ℝ ↦ fun i ↦ (v i).1)) = _
  rw [← Measure.map_prod_map _ _ measurable_id hf, Measure.map_id]
  congr 1
  rw [Measure.pi_map_pi (fun _ ↦ measurable_fst.aemeasurable)]
  have h1 : ((profileMeasure : Measure ℝ).map (fun t ↦ (t, g t ^ 2))).map Prod.fst =
      profileMeasure := by
    rw [Measure.map_map measurable_fst hh]
    exact Measure.map_id
  simp only [h1]
  rfl

theorem ae_cubeProd_good (ε : ℝ) :
    ∀ᵐ q ∂((cubeMeasure k).prod (cubeMeasure m)),
      (∀ j, 0 < q.1 j ∧ q.1 j < 1) ∧ (∀ i, 0 < q.2 i ∧ q.2 i < 1) ∧
        Function.Injective (Sum.elim q.1 q.2) ∧ (∀ j, q.1 j ≠ ε) ∧ ∀ i, q.2 i ≠ ε := by
  have ha : ∀ᵐ q ∂((cubeMeasure k).prod (cubeMeasure m)),
      (∀ j, 0 < q.1 j ∧ q.1 j < 1 ∧ q.1 j ∉ ({ε} : Finset ℝ)) ∧ Function.Injective q.1 := by
    have h := ae_cube_good (k := k) {ε}
    have h' : ∀ᵐ U ∂((cubeMeasure k).prod (cubeMeasure m)).map Prod.fst,
        (∀ j, 0 < U j ∧ U j < 1 ∧ U j ∉ ({ε} : Finset ℝ)) ∧ Function.Injective U := by
      rw [Measure.map_fst_prod, measure_univ, one_smul]
      exact h
    exact ae_of_ae_map measurable_fst.aemeasurable h'
  have hb : ∀ᵐ q ∂((cubeMeasure k).prod (cubeMeasure m)),
      (∀ i, 0 < q.2 i ∧ q.2 i < 1 ∧ q.2 i ∉ ({ε} : Finset ℝ)) ∧ Function.Injective q.2 := by
    have h := ae_cube_good (k := m) {ε}
    have h' : ∀ᵐ U ∂((cubeMeasure k).prod (cubeMeasure m)).map Prod.snd,
        (∀ i, 0 < U i ∧ U i < 1 ∧ U i ∉ ({ε} : Finset ℝ)) ∧ Function.Injective U := by
      rw [Measure.map_snd_prod, measure_univ, one_smul]
      exact h
    exact ae_of_ae_map measurable_snd.aemeasurable h'
  have hc : ∀ᵐ q ∂((cubeMeasure k).prod (cubeMeasure m)), ∀ j i, q.1 j ≠ q.2 i := by
    refine ae_all_iff.mpr fun j ↦ ae_all_iff.mpr fun i ↦ ?_
    rw [ae_iff]
    have hmeas : MeasurableSet {q : (Fin k → ℝ) × (Fin m → ℝ) | ¬ q.1 j ≠ q.2 i} := by
      simp only [ne_eq, not_not]
      exact measurableSet_eq_fun ((measurable_pi_apply j).comp measurable_fst)
        ((measurable_pi_apply i).comp measurable_snd)
    rw [Measure.prod_apply_symm hmeas]
    have hzero : ∀ y : Fin m → ℝ, cubeMeasure k ((fun x ↦ (x, y)) ⁻¹'
        {q : (Fin k → ℝ) × (Fin m → ℝ) | ¬ q.1 j ≠ q.2 i}) = 0 := by
      intro y
      have h := ae_cube_good (k := k) {y i}
      rw [ae_iff] at h
      refine measure_mono_null (fun x hx ↦ ?_) h
      simp only [Set.mem_preimage, ne_eq, not_not, Set.mem_ofPred_eq] at hx ⊢
      intro hgood
      exact (hgood.1 j).2.2 (by simp [hx])
    exact (lintegral_congr fun y ↦ hzero y).trans lintegral_zero
  filter_upwards [ha, hb, hc] with q hqa hqb hqc
  refine ⟨fun j ↦ ⟨(hqa.1 j).1, (hqa.1 j).2.1⟩, fun i ↦ ⟨(hqb.1 i).1, (hqb.1 i).2.1⟩, ?_,
    fun j h ↦ (hqa.1 j).2.2 (by simp [h]), fun i h ↦ (hqb.1 i).2.2 (by simp [h])⟩
  intro a a' h
  rcases a with j | i <;> rcases a' with j' | i'
  · exact congrArg Sum.inl (hqa.2 h)
  · exact absurd h (hqc j i')
  · exact absurd h.symm (hqc j' i)
  · exact congrArg Sum.inr (hqb.2 h)

/-- Under the limit law, the configuration is almost surely good. -/
theorem limitLocalLaw_goodSet_compl {g : ℝ → ℝ} (hg : Measurable g) (ε : ℝ) :
    (limitLocalLaw g k m : Measure (LocalSpace k m)) (goodSet ε)ᶜ = 0 := by
  have hπ : Measurable (fun z : LocalSpace k m ↦ (z.1, mergeTimes z)) :=
    measurable_fst.prodMk (measurable_pi_iff.mpr fun i ↦
      measurable_fst.comp ((measurable_pi_apply i).comp measurable_snd))
  have h := ae_cubeProd_good (k := k) (m := m) ε
  rw [← map_times_limitLocalLaw hg] at h
  have h' := ae_of_ae_map hπ.aemeasurable h
  exact ae_iff.mp h'

/-- **The corrected local limit `eq:cv locale` at a fixed cutoff `ε > 0`**, in distribution.
The law of the discrete local functional under the auxiliary samples (scaled births, scaled
merge phases, exact merge rates) converges weakly to the law of the limit functional under
independent uniform times with marks `g²`. -/
theorem tendsto_localLaw {xa : ℕ → ℕ → ℤ} {g : ℝ → ℝ} (hx : AdmissibleArray xa)
    (hL1 : HasL1ReciprocalProfile xa (1 / 2) g) (hpos : PositiveProfile g)
    (h2 : HasLocalSquareMomentProfile xa (1 / 2) g) (hg : Measurable g) {ε : ℝ} (hε : 0 < ε)
    (xs : Fin m → ConnState k) :
    Tendsto (fun n ↦ (auxLocalLaw (xa n) n k m).map (discFun (xa n) n ε xs)) atTop
      (𝓝 ((limitLocalLaw g k m).map (limitFun g ε xs))) :=
  tendsto_map_of_continuousConvergence (tendsto_auxiliary_birth_and_rates hx hL1 hpos h2 k m)
    (fun n ↦ measurable_discFun (xa n) n ε xs) (measurable_limitFun hg ε xs)
    (limitLocalLaw_goodSet_compl hg ε)
    (fun _ hz _ hw ↦ tendsto_discFun hx hL1 hpos h2 hε xs hz hw)


/-! ### Identification with the source's sampler -/

instance isFiniteMeasure_uniformOfFinset {A : Type*} [MeasurableSpace A]
    [MeasurableSingletonClass A] {s : Finset A} : IsFiniteMeasure (Measure.uniformOfFinset s) :=
  uniformOfFinset_finite s

/-- The source's sampler of `eq:cv locale`: `k` iid uniform down-step phases `0 ≤ i < n` with
`x_{i+1} = -1` (the births `B̃ⁿ`) and, independently, `m` iid uniform up-step phases with
`x_{i+1} = 1` (the merge phases `C̃ⁿ`). -/
noncomputable def sourceSampleLaw (xa : ℕ → ℤ) (n k m : ℕ) :
    Measure ((Fin k → ℕ) × (Fin m → ℕ)) :=
  (Measure.pi fun _ : Fin k ↦ Measure.uniformOfFinset (auxiliarySignTimes xa (-1) n)).prod
    (Measure.pi fun _ : Fin m ↦ Measure.uniformOfFinset (auxiliarySignTimes xa 1 n))

theorem ae_mem_uniformOfFinset {A : Type*} [MeasurableSpace A] [MeasurableSingletonClass A]
    (s : Finset A) : ∀ᵐ a ∂Measure.uniformOfFinset s, a ∈ s := by
  classical
  rw [ae_iff, Measure.uniformOfFinset_apply]
  simp

theorem ae_sourceSampleLaw (xa : ℕ → ℤ) (n : ℕ) :
    ∀ᵐ q ∂sourceSampleLaw xa n k m,
      (∀ j, q.1 j ∈ auxiliarySignTimes xa (-1) n) ∧ ∀ i, q.2 i ∈ auxiliarySignTimes xa 1 n := by
  have h1 : ∀ᵐ b ∂(Measure.pi fun _ : Fin k ↦
      Measure.uniformOfFinset (auxiliarySignTimes xa (-1) n)),
      ∀ j, b j ∈ auxiliarySignTimes xa (-1) n :=
    ae_all_iff.mpr fun j ↦ Measure.tendsto_eval_ae_ae.eventually (ae_mem_uniformOfFinset _)
  have h2 : ∀ᵐ c ∂(Measure.pi fun _ : Fin m ↦
      Measure.uniformOfFinset (auxiliarySignTimes xa 1 n)),
      ∀ i, c i ∈ auxiliarySignTimes xa 1 n :=
    ae_all_iff.mpr fun i ↦ Measure.tendsto_eval_ae_ae.eventually (ae_mem_uniformOfFinset _)
  have h1' := ae_of_ae_map (μ := sourceSampleLaw xa n k m) measurable_fst.aemeasurable
    (p := fun b : Fin k → ℕ ↦ ∀ j, b j ∈ auxiliarySignTimes xa (-1) n) (by
      rw [sourceSampleLaw, Measure.map_fst_prod]
      exact Measure.ae_smul_measure h1 _)
  have h2' := ae_of_ae_map (μ := sourceSampleLaw xa n k m) measurable_snd.aemeasurable
    (p := fun c : Fin m → ℕ ↦ ∀ i, c i ∈ auxiliarySignTimes xa 1 n) (by
      rw [sourceSampleLaw, Measure.map_snd_prod]
      exact Measure.ae_smul_measure h2 _)
  filter_upwards [h1', h2'] with q hq1 hq2
  exact ⟨hq1, hq2⟩

/-- The embedding of integer samples into configurations: scaled phases and exact merge
rates. -/
noncomputable def sampleEmbed (xa : ℕ → ℤ) (n : ℕ) (q : (Fin k → ℕ) × (Fin m → ℕ)) :
    LocalSpace k m :=
  (fun j ↦ (q.1 j : ℝ) / n, fun i ↦ ((q.2 i : ℝ) / n, auxiliaryAttachmentRate xa n (q.2 i)))

theorem floorBirths_sampleEmbed (xa : ℕ → ℤ) {n : ℕ} (hn : 0 < n)
    (q : (Fin k → ℕ) × (Fin m → ℕ)) : floorBirths n (sampleEmbed xa n q) = q.1 := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  funext j
  simp only [floorBirths, sampleEmbed]
  rw [mul_div_cancel₀ _ hn0, Nat.floor_natCast]

theorem floorMerges_sampleEmbed (xa : ℕ → ℤ) {n : ℕ} (hn : 0 < n)
    (q : (Fin k → ℕ) × (Fin m → ℕ)) : floorMerges n (sampleEmbed xa n q) = q.2 := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  funext i
  simp only [floorMerges, sampleEmbed]
  rw [mul_div_cancel₀ _ hn0, Nat.floor_natCast]

/-- At a source sample, the discrete local functional is the rescaled local probability. -/
theorem discFun_sampleEmbed {xa : ℕ → ℤ} (hx : IsSigned xa) {n : ℕ}
    (hs : SurvivesThrough xa n) (hn : 0 < n) (ε : ℝ) (xs : Fin m → ConnState k)
    {q : (Fin k → ℕ) × (Fin m → ℕ)}
    (hq : (∀ j, q.1 j ∈ auxiliarySignTimes xa (-1) n) ∧ ∀ i, q.2 i ∈ auxiliarySignTimes xa 1 n) :
    discFun xa n ε xs (sampleEmbed xa n q) = scaledPatternProb xa n ε xs q.1 q.2 := by
  classical
  have hsb : ∀ j, q.1 j < n ∧ xa (q.1 j + 1) = -1 := fun j ↦ by
    have := hq.1 j
    simp only [auxiliarySignTimes, Finset.mem_filter, Finset.mem_range] at this
    exact this
  have hsc : ∀ i, xa (q.2 i + 1) = 1 := fun i ↦ by
    have := hq.2 i
    simp only [auxiliarySignTimes, Finset.mem_filter, Finset.mem_range] at this
    exact this.2
  simp only [discFun, floorBirths_sampleEmbed xa hn, floorMerges_sampleEmbed xa hn]
  by_cases hO : OrderAdmissible n ε xs q.1 q.2
  · have hL : LocalAdmissible xa n ε xs q.1 q.2 := ⟨hO.1, hsb, hsc, hO.2.1, hO.2.2⟩
    rw [ite_eq_left hO, scaledPatternProb_eq hx hs hL]
    rfl
  · have hL : ¬ LocalAdmissible xa n ε xs q.1 q.2 := fun h ↦
      hO ⟨h.1, h.2.2.2.1, h.2.2.2.2⟩
    rw [ite_eq_right hO, scaledPatternProb, ite_eq_right hL]

/-- Eventually, the auxiliary law is the image of the source's sampler. -/
theorem eventually_auxLocalLaw_eq {xa : ℕ → ℕ → ℤ} {g : ℝ → ℝ} (hx : AdmissibleArray xa)
    (hL1 : HasL1ReciprocalProfile xa (1 / 2) g) (hpos : PositiveProfile g) :
    ∀ᶠ n in atTop, (auxLocalLaw (xa n) n k m : Measure (LocalSpace k m)) =
      (sourceSampleLaw (xa n) n k m).map (sampleEmbed (xa n) n) := by
  filter_upwards [eventually_auxiliarySignTimeLaw_eq_uniform hx (by norm_num : (1 / 2 : ℝ) < 1)
      hL1 hpos (σ := -1) (Or.inr rfl),
    eventually_auxiliaryAttachmentMarkedLaw_eq_uniform hx hL1 hpos] with n hB hC
  change (Measure.pi fun _ : Fin k ↦ (auxiliarySignTimeLaw (xa n) (-1) n : Measure ℝ)).prod
    (Measure.pi fun _ : Fin m ↦ (auxiliaryAttachmentMarkedLaw (xa n) n : Measure (ℝ × ℝ))) = _
  rw [hB, hC, ← Measure.pi_map_pi (fun _ ↦ (measurable_of_countable _).aemeasurable),
    ← Measure.pi_map_pi (fun _ ↦ (measurable_of_countable _).aemeasurable),
    Measure.map_prod_map _ _ (measurable_of_countable _) (measurable_of_countable _)]
  rfl

/-- **The discrete law is the law of the rescaled conditional probability at the source's
samples.** Eventually, the image of the auxiliary law by the discrete local functional is the
law of `scaledPatternProb` evaluated at iid uniform down-step births and iid uniform up-step
merge phases. -/
theorem eventually_map_discFun_eq {xa : ℕ → ℕ → ℤ} {g : ℝ → ℝ} (hx : AdmissibleArray xa)
    (hL1 : HasL1ReciprocalProfile xa (1 / 2) g) (hpos : PositiveProfile g) (ε : ℝ)
    (xs : Fin m → ConnState k) :
    ∀ᶠ n in atTop, ((auxLocalLaw (xa n) n k m).map (discFun (xa n) n ε xs) : Measure ℝ) =
      (sourceSampleLaw (xa n) n k m).map
        (fun q ↦ scaledPatternProb (xa n) n ε xs q.1 q.2) := by
  filter_upwards [eventually_auxLocalLaw_eq (k := k) (m := m) hx hL1 hpos,
    eventually_gt_atTop 0] with n hlaw hn
  rw [ProbabilityMeasure.toMeasure_map, hlaw,
    Measure.map_map (measurable_discFun (xa n) n ε xs) (measurable_of_countable _)]
  apply Measure.map_congr
  filter_upwards [ae_sourceSampleLaw (k := k) (m := m) (xa n) n] with q hq
  exact discFun_sampleEmbed (hx n).1 (hx n).2 hn ε xs hq

/-! ### Removing the cutoff: `ε → 0` -/

theorem pairWeight_mul_eq {α : Type*} [LinearOrder α] (b : Fin k → α) (c : Fin m → α) (i : α)
    (G : ℝ) :
    pairWeight b c i * G = ((∑ q, ∑ q', eventSign q * eventSign q' *
        (leInd i (min (eventTime b c q) (eventTime b c q')) * G)) -
        ∑ q, eventSign q * (leInd i (eventTime b c q) * G)) / 2 := by
  rw [pairWeight_eq_sum, div_mul_eq_mul_div, sub_mul, Finset.sum_mul, Finset.sum_mul]
  congr 2
  · refine Finset.sum_congr rfl fun q _ ↦ ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun q' _ ↦ ?_
    ring
  · refine Finset.sum_congr rfl fun q _ ↦ ?_
    ring

theorem integrableOn_pairWeight {xa : ℕ → ℕ → ℤ} {g : ℝ → ℝ}
    (h2 : HasLocalSquareMomentProfile xa (1 / 2) g) {ε : ℝ} (hε : 0 < ε)
    {β : Fin k → ℝ} {γ : Fin m → ℝ} (hβ1 : ∀ j, β j < 1) (hγ1 : ∀ l, γ l < 1) :
    IntegrableOn (fun t ↦ pairWeight β γ t * g t ^ 2) (Ioc ε 1) := by
  have hη1 : ∀ q, eventTime β γ q < 1 := by
    intro q
    rcases q with j | l
    · exact hβ1 j
    · exact hγ1 l
  have hI : ∀ η, η < 1 → IntegrableOn (fun t ↦ leInd t η * g t ^ 2) (Ioc ε 1) :=
    fun η hη ↦ integrableOn_leInd h2 hε hη
  simp_rw [pairWeight_mul_eq]
  refine ((integrable_finsetSum _ fun q _ ↦ integrable_finsetSum _ fun q' _ ↦
    (hI _ (lt_of_le_of_lt (min_le_left _ _) (hη1 q))).const_mul _).sub
    (integrable_finsetSum _ fun q _ ↦ (hI _ (hη1 q)).const_mul _)).div_const _

theorem measurable_pairWeight_sq {g : ℝ → ℝ} (hg : Measurable g) :
    Measurable (fun p : LocalSpace k m × ℝ ↦
      pairWeight p.1.1 (mergeTimes p.1) p.2 * g p.2 ^ 2) := by
  have hβ : ∀ j, Measurable (fun p : LocalSpace k m × ℝ ↦ p.1.1 j) := fun j ↦
    (measurable_pi_apply j).comp (measurable_fst.comp measurable_fst)
  have hγ : ∀ i, Measurable (fun p : LocalSpace k m × ℝ ↦ mergeTimes p.1 i) := fun i ↦
    measurable_fst.comp ((measurable_pi_apply i).comp (measurable_snd.comp measurable_fst))
  have hb := measurable_countAbove_pair (e := fun p : LocalSpace k m × ℝ ↦ p.1.1) hβ measurable_snd
  have hc := measurable_countAbove_pair (e := fun p : LocalSpace k m × ℝ ↦ mergeTimes p.1) hγ
    measurable_snd
  unfold pairWeight clusterNum
  exact (((hb.sub hc).mul ((hb.sub hc).sub measurable_const)).div_const 2).mul
    ((hg.comp measurable_snd).pow_const 2)

/-- The survival exponent `∫_{(ε, 1]} C(a(t), 2) g(t)² dt`, possibly infinite at `ε = 0`. -/
noncomputable def survLIntegral (g : ℝ → ℝ) (β : Fin k → ℝ) (γ : Fin m → ℝ) (ε : ℝ) : ℝ≥0∞ :=
  ∫⁻ t in Ioc ε 1, ENNReal.ofReal (pairWeight β γ t * g t ^ 2)

theorem measurable_pairWeight_sq_slice {g : ℝ → ℝ} (hg : Measurable g) (z : LocalSpace k m) :
    Measurable (fun t ↦ pairWeight z.1 (mergeTimes z) t * g t ^ 2) := by
  have hb := measurable_countAbove_pair (e := fun _ : ℝ ↦ z.1) (fun _ ↦ measurable_const)
    measurable_id
  have hc := measurable_countAbove_pair (e := fun _ : ℝ ↦ mergeTimes z) (fun _ ↦ measurable_const)
    measurable_id
  unfold pairWeight clusterNum
  exact (((hb.sub hc).mul ((hb.sub hc).sub measurable_const)).div_const 2).mul (hg.pow_const 2)

theorem tendsto_survLIntegral {g : ℝ → ℝ} (hg : Measurable g) (z : LocalSpace k m) :
    Tendsto (fun ε ↦ survLIntegral g z.1 (mergeTimes z) ε) (𝓝[>] 0)
      (𝓝 (survLIntegral g z.1 (mergeTimes z) 0)) := by
  classical
  set F : ℝ → ℝ≥0∞ := fun t ↦ ENNReal.ofReal (pairWeight z.1 (mergeTimes z) t * g t ^ 2)
    with hFdef
  have hF : Measurable F := ENNReal.measurable_ofReal.comp (measurable_pairWeight_sq_slice hg z)
  have hanti : Antitone (fun ε ↦ survLIntegral g z.1 (mergeTimes z) ε) := by
    intro a b hab
    exact lintegral_mono_set (Ioc_subset_Ioc_left hab)
  have hlim := hanti.tendsto_nhdsGT 0
  convert hlim using 2
  apply le_antisymm
  · -- monotone convergence along `1 / (n + 1)`
    have hseq : survLIntegral g z.1 (mergeTimes z) 0 =
        ⨆ n : ℕ, survLIntegral g z.1 (mergeTimes z) (1 / ((n : ℝ) + 1)) := by
      unfold survLIntegral
      rw [← lintegral_indicator measurableSet_Ioc]
      simp_rw [← lintegral_indicator measurableSet_Ioc]
      rw [← lintegral_iSup (fun n ↦ hF.indicator measurableSet_Ioc)]
      · congr 1
        funext t
        by_cases ht : t ∈ Ioc (0 : ℝ) 1
        · rw [indicator_of_mem ht]
          apply le_antisymm
          · obtain ⟨N, hN⟩ := exists_nat_one_div_lt ht.1
            refine le_iSup_of_le N (le_of_eq ?_)
            rw [indicator_of_mem (show t ∈ Ioc (1 / ((N : ℝ) + 1)) 1 from ⟨hN, ht.2⟩)]
          · exact iSup_le fun n ↦ indicator_le_self _ _ t
        · rw [indicator_of_notMem ht]
          symm
          refine le_antisymm (iSup_le fun n ↦ ?_) bot_le
          rw [indicator_of_notMem]
          intro h
          exact ht ⟨lt_trans (by positivity) h.1, h.2⟩
      · intro a b hab t
        apply indicator_le_indicator_of_subset _ (fun _ ↦ bot_le)
        apply Ioc_subset_Ioc_left
        apply one_div_le_one_div_of_le (by positivity)
        exact_mod_cast Nat.add_le_add_right hab 1
    rw [hseq]
    refine iSup_le fun n ↦ le_sSup ⟨1 / ((n : ℝ) + 1), ?_, rfl⟩
    exact mem_Ioi.mpr (by positivity)
  · refine sSup_le ?_
    rintro _ ⟨ε, hε, rfl⟩
    exact lintegral_mono_set (Ioc_subset_Ioc_left (le_of_lt hε))

theorem integral_eq_survLIntegral {g : ℝ → ℝ} (hg : Measurable g) (z : LocalSpace k m) (ε : ℝ) :
    ∫ t in Ioc ε 1, pairWeight z.1 (mergeTimes z) t * g t ^ 2 =
      (survLIntegral g z.1 (mergeTimes z) ε).toReal := by
  apply integral_eq_lintegral_of_nonneg_ae
  · exact Eventually.of_forall fun t ↦ mul_nonneg (pairWeight_nonneg _ _ _) (sq_nonneg _)
  · exact (measurable_pairWeight_sq_slice hg z).aestronglyMeasurable

theorem survLIntegral_lt_top {xa : ℕ → ℕ → ℤ} {g : ℝ → ℝ}
    (h2 : HasLocalSquareMomentProfile xa (1 / 2) g) {ε : ℝ} (hε : 0 < ε)
    {β : Fin k → ℝ} {γ : Fin m → ℝ} (hβ1 : ∀ j, β j < 1) (hγ1 : ∀ l, γ l < 1) :
    survLIntegral g β γ ε < ∞ :=
  (integrableOn_pairWeight h2 hε hβ1 hγ1).lintegral_lt_top

/-- The survival factor at cutoff `ε` converges, as `ε → 0⁺`, to `exp (-∫₀¹ C(a, 2) g²)`, with
`exp (-∞) = 0`. -/
theorem tendsto_exp_survival {xa : ℕ → ℕ → ℤ} {g : ℝ → ℝ} (hg : Measurable g)
    (h2 : HasLocalSquareMomentProfile xa (1 / 2) g) {z : LocalSpace k m}
    (hβ1 : ∀ j, z.1 j < 1) (hγ1 : ∀ l, mergeTimes z l < 1) :
    Tendsto (fun ε ↦ Real.exp (-∫ t in Ioc ε 1, pairWeight z.1 (mergeTimes z) t * g t ^ 2))
      (𝓝[>] 0) (𝓝 (expNeg (survLIntegral g z.1 (mergeTimes z) 0)).toReal) := by
  have hL := tendsto_survLIntegral hg z
  simp_rw [integral_eq_survLIntegral hg z]
  have hfin : ∀ᶠ ε in 𝓝[>] (0 : ℝ), survLIntegral g z.1 (mergeTimes z) ε ≠ ∞ :=
    eventually_nhdsWithin_of_forall fun ε hε ↦
      (survLIntegral_lt_top h2 (mem_Ioi.mp hε) hβ1 hγ1).ne
  by_cases h0 : survLIntegral g z.1 (mergeTimes z) 0 = ∞
  · rw [h0]
    simp only [expNeg, ↓reduceIte, ENNReal.toReal_zero]
    have hat : Tendsto (fun ε ↦ (survLIntegral g z.1 (mergeTimes z) ε).toReal) (𝓝[>] 0)
        atTop := by
      rw [h0] at hL
      refine tendsto_atTop.mpr fun M ↦ ?_
      filter_upwards [hL.eventually (lt_mem_nhds (ENNReal.ofReal_lt_top (r := max M 0))), hfin]
        with ε hε hεfin
      have := (ENNReal.ofReal_lt_iff_lt_toReal (le_max_right M 0) hεfin).mp hε
      exact (le_max_left M 0).trans this.le
    exact Real.tendsto_exp_neg_atTop_nhds_zero.comp hat
  · have hval : (expNeg (survLIntegral g z.1 (mergeTimes z) 0)).toReal =
        Real.exp (-(survLIntegral g z.1 (mergeTimes z) 0).toReal) := by
      simp only [expNeg, h0, ↓reduceIte]
      exact ENNReal.toReal_ofReal (Real.exp_pos _).le
    rw [hval]
    exact (Real.continuous_exp.comp continuous_neg).continuousAt.tendsto.comp
      ((ENNReal.tendsto_toReal h0).comp hL)


open Classical in
/-- **The limit functional without cutoff**: on admissible configurations with distinct births,
the product of the marks and `exp (-∫₀¹ C(a(t), 2) g(t)² dt)` (`0` if the integral diverges).
At marks `g(γ)²` it is the non-plane density `historyDensity` of Proposition
`loi du coalescent généralisé`. -/
noncomputable def limitFun0 (g : ℝ → ℝ) (xs : Fin m → ConnState k) (z : LocalSpace k m) : ℝ :=
  if Function.Injective z.1 ∧ IsAdmissible z.1 m 1 diagState xs (mergeTimes z) then
    (∏ i, (z.2 i).2) * (expNeg (survLIntegral g z.1 (mergeTimes z) 0)).toReal
  else 0

theorem tendsto_limitFun_zero {xa : ℕ → ℕ → ℤ} {g : ℝ → ℝ} (hg : Measurable g)
    (h2 : HasLocalSquareMomentProfile xa (1 / 2) g) (xs : Fin m → ConnState k)
    {z : LocalSpace k m} (hβ1 : ∀ j, z.1 j < 1)
    (hγ : ∀ i, 0 < mergeTimes z i ∧ mergeTimes z i < 1) :
    Tendsto (fun ε ↦ limitFun g ε xs z) (𝓝[>] 0) (𝓝 (limitFun0 g xs z)) := by
  classical
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ i, ε < mergeTimes z i :=
    eventually_all.mpr fun i ↦ eventually_nhdsWithin_of_eventually_nhds
      (eventually_lt_nhds (hγ i).1)
  by_cases hA : Function.Injective z.1 ∧ IsAdmissible z.1 m 1 diagState xs (mergeTimes z)
  · rw [limitFun0, ite_eq_left hA]
    apply (tendsto_const_nhds.mul (tendsto_exp_survival hg h2 hβ1 fun i ↦ (hγ i).2)).congr'
    filter_upwards [hev] with ε hε
    rw [limitFun, ite_eq_left ⟨hA.1, hε, hA.2⟩]
  · rw [limitFun0, ite_eq_right hA]
    apply tendsto_const_nhds.congr'
    filter_upwards [hev] with ε hε
    rw [limitFun, ite_eq_right fun h ↦ hA ⟨h.1, h.2.2⟩]

theorem measurable_limitFun0 {g : ℝ → ℝ} (hg : Measurable g) (xs : Fin m → ConnState k) :
    Measurable (limitFun0 (k := k) g xs) := by
  classical
  have hset : MeasurableSet {z : LocalSpace k m |
      Function.Injective z.1 ∧ IsAdmissible z.1 m 1 diagState xs (mergeTimes z)} :=
    measurableSet_of_orderData 0 fun _ _ h ↦ by
      obtain ⟨h1, -, h3⟩ := orderData_congr xs h
      rw [h1, h3]
  have hL : Measurable (fun z : LocalSpace k m ↦ survLIntegral g z.1 (mergeTimes z) 0) :=
    (ENNReal.measurable_ofReal.comp (measurable_pairWeight_sq hg)).lintegral_prod_right'
  unfold limitFun0
  exact Measurable.ite hset (measurable_prod_marks.mul
    (ENNReal.measurable_toReal.comp (measurable_expNeg.comp hL))) measurable_const

/-- Almost-everywhere convergence of real functions gives weak convergence of their image
laws. -/
theorem tendsto_map_of_ae_tendsto {Ω ι : Type*} [MeasurableSpace Ω] (μ : ProbabilityMeasure Ω)
    {l : Filter ι} [l.IsCountablyGenerated] {Φ : ι → Ω → ℝ} {Φ0 : Ω → ℝ}
    (hΦ : ∀ i, Measurable (Φ i)) (hΦ0 : Measurable Φ0)
    (h : ∀ᵐ z ∂(μ : Measure Ω), Tendsto (fun i ↦ Φ i z) l (𝓝 (Φ0 z))) :
    Tendsto (fun i ↦ μ.map (Φ i)) l (𝓝 (μ.map Φ0)) := by
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
  intro f
  simp only [ProbabilityMeasure.toMeasure_map]
  rw [integral_map hΦ0.aemeasurable f.continuous.aestronglyMeasurable]
  have heq : (fun i ↦ ∫ ω, f ω ∂(μ : Measure Ω).map (Φ i)) =
      fun i ↦ ∫ ω, f (Φ i ω) ∂(μ : Measure Ω) := by
    funext i
    rw [integral_map (hΦ i).aemeasurable f.continuous.aestronglyMeasurable]
  rw [heq]
  refine tendsto_integral_filter_of_dominated_convergence (fun _ ↦ ‖f‖) ?_ ?_
    (integrable_const _) ?_
  · exact Eventually.of_forall fun i ↦ (f.continuous.measurable.comp (hΦ i)).aestronglyMeasurable
  · exact Eventually.of_forall fun i ↦ Eventually.of_forall fun ω ↦ f.norm_coe_le_norm _
  · filter_upwards [h] with ω hω
    exact (f.continuous.tendsto _).comp hω

/-- **Removing the cutoff.** As `ε → 0⁺`, the limit laws at cutoff `ε` converge weakly to the
law of the limit functional without cutoff. -/
theorem tendsto_limitLaw_zero {xa : ℕ → ℕ → ℤ} {g : ℝ → ℝ} (hg : Measurable g)
    (h2 : HasLocalSquareMomentProfile xa (1 / 2) g) (xs : Fin m → ConnState k) :
    Tendsto (fun ε ↦ (limitLocalLaw g k m).map (limitFun g ε xs)) (𝓝[>] 0)
      (𝓝 ((limitLocalLaw g k m).map (limitFun0 g xs))) := by
  apply tendsto_map_of_ae_tendsto _ (fun ε ↦ measurable_limitFun hg ε xs)
    (measurable_limitFun0 hg xs)
  have hgood := limitLocalLaw_goodSet_compl (k := k) (m := m) hg 0
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp hgood] with z hz
  have hz' : z ∈ goodSet 0 := by simpa using hz
  exact tendsto_limitFun_zero hg h2 xs (fun j ↦ (hz'.1 j).2) hz'.2.1

/-- The limit law is the image of independent uniform births and merge times, marked by
`g²`. -/
theorem limitLocalLaw_eq_map {g : ℝ → ℝ} (hg : Measurable g) :
    (limitLocalLaw g k m : Measure (LocalSpace k m)) =
      ((cubeMeasure k).prod (cubeMeasure m)).map
        (fun q ↦ (q.1, fun i ↦ (q.2 i, g (q.2 i) ^ 2))) := by
  have hh : Measurable (fun t : ℝ ↦ (t, g t ^ 2)) := measurable_id.prodMk (hg.pow_const 2)
  have hf : Measurable (fun v : Fin m → ℝ ↦ fun i ↦ (v i, g (v i) ^ 2)) :=
    measurable_pi_iff.mpr fun i ↦ hh.comp (measurable_pi_apply i)
  change (Measure.pi fun _ : Fin k ↦ (profileMeasure : Measure ℝ)).prod
    (Measure.pi fun _ : Fin m ↦ (profileMeasure : Measure ℝ).map (fun t ↦ (t, g t ^ 2))) = _
  rw [← Measure.pi_map_pi (fun _ ↦ hh.aemeasurable)]
  have := Measure.map_prod_map (Measure.pi fun _ : Fin k ↦ (profileMeasure : Measure ℝ))
    (Measure.pi fun _ : Fin m ↦ (profileMeasure : Measure ℝ)) measurable_id hf
  rw [Measure.map_id] at this
  exact this

/-- On admissible histories the cluster count is the signed count, so the integrand of the
density is the pair weight. -/
theorem choose_clusterCount_eq {β : Fin k → ℝ} {xs : Fin m → ConnState k} {γ : Fin m → ℝ}
    (hadm : IsAdmissible β m 1 diagState xs γ) {u : ℝ} (hu : u ≤ 1) :
    (((clusterCount β m xs γ u).choose 2 : ℕ) : ℝ) = pairWeight β γ u := by
  classical
  have h := classesOn_stateAt m hadm (isValid_diagState _) hu
  rw [classesOn_diagState] at h
  have hb : (bornAt β u).card = countAbove β u := by
    unfold bornAt countAbove
    congr 1
  have hc : (Finset.univ.filter fun i ↦ u ≤ γ i).card = countAbove γ u := by
    unfold countAbove
    congr 1
  rw [hb, hc] at h
  have hcc : (clusterCount β m xs γ u : ℝ) = clusterNum β γ u := by
    unfold clusterCount clusterNum
    have h' : (countAbove β u : ℝ) =
        (classesOn (bornAt β u) (stateAt m 1 diagState xs γ u) : ℝ) + (countAbove γ u : ℝ) := by
      exact_mod_cast h.symm
    linarith
  rw [Nat.cast_choose_two, hcc, pairWeight]

/-- The marks of the limit law. -/
noncomputable def markEmbed (g : ℝ → ℝ) (q : (Fin k → ℝ) × (Fin m → ℝ)) : LocalSpace k m :=
  (q.1, fun i ↦ (q.2 i, g (q.2 i) ^ 2))

theorem measurable_markEmbed {g : ℝ → ℝ} (hg : Measurable g) :
    Measurable (markEmbed (k := k) (m := m) g) :=
  measurable_fst.prodMk (measurable_pi_iff.mpr fun i ↦
    ((measurable_pi_apply i).comp measurable_snd).prodMk
      ((hg.comp ((measurable_pi_apply i).comp measurable_snd)).pow_const 2))

/-- At marks `g²` and distinct births, the limit functional without cutoff is the non-plane
density. -/
theorem limitFun0_markEmbed (g : ℝ → ℝ) (xs : Fin m → ConnState k)
    {q : (Fin k → ℝ) × (Fin m → ℝ)} (hinj : Function.Injective q.1) :
    limitFun0 g xs (markEmbed g q) = (historyDensity g q.1 m xs q.2).toReal := by
  classical
  simp only [limitFun0]
  rw [show mergeTimes (markEmbed g q) = q.2 from rfl, show (markEmbed g q).1 = q.1 from rfl]
  by_cases hadm : IsAdmissible q.1 m 1 diagState xs q.2
  · rw [ite_eq_left ⟨hinj, hadm⟩, historyDensity, ite_eq_left hadm, one_mul,
      ENNReal.toReal_mul, ENNReal.toReal_prod]
    congr 1
    · refine Finset.prod_congr rfl fun i _ ↦ ?_
      rw [ENNReal.toReal_ofReal (sq_nonneg _)]
      rfl
    · congr 2
      unfold survLIntegral
      refine setLIntegral_congr_fun measurableSet_Ioc fun u hu ↦ ?_
      rw [ENNReal.ofReal_mul (pairWeight_nonneg _ _ _), ← choose_clusterCount_eq hadm hu.2,
        ENNReal.ofReal_natCast]
  · rw [ite_eq_right fun h ↦ hadm h.2, historyDensity, ite_eq_right hadm, zero_mul, zero_mul,
      ENNReal.toReal_zero]

/-- **Identification of the limit law.** The law of the limit functional without cutoff under
the limit law is the law of the non-plane density `historyDensity g B m xs C` of Proposition
`loi du coalescent généralisé` at independent uniform births `B` and merge times `C`. -/
theorem limitLocalLaw_map_limitFun0 {g : ℝ → ℝ} (hg : Measurable g) (xs : Fin m → ConnState k) :
    ((limitLocalLaw g k m).map (limitFun0 g xs) : Measure ℝ) =
      ((cubeMeasure k).prod (cubeMeasure m)).map
        (fun q ↦ (historyDensity g q.1 m xs q.2).toReal) := by
  rw [ProbabilityMeasure.toMeasure_map, limitLocalLaw_eq_map hg,
    show (fun q : (Fin k → ℝ) × (Fin m → ℝ) ↦ (q.1, fun i ↦ (q.2 i, g (q.2 i) ^ 2))) =
      markEmbed g from rfl,
    Measure.map_map (measurable_limitFun0 hg xs) (measurable_markEmbed hg)]
  apply Measure.map_congr
  filter_upwards [ae_cubeProd_good (k := k) (m := m) 0] with q hq
  exact limitFun0_markEmbed g xs ((hq.2.2.1).comp Sum.inl_injective)

/-! ### The source's normalization and the sampled vertices -/

/-- The sampled vertices that are the frozen vertices born at the phases `b`: the vertex with
paper label `b j + 1`, frozen at step `b j + 1`. -/
def frozenVertex (b : Fin k → ℕ) : Fin k → VertexLabel := fun j ↦ Sum.inl (b j + 1)

/-- **Conditioning on the sampled vertices.** Under one actual reverse history and `k` iid
uniform vertices, the probability that the sampled vertices are the frozen vertices born at
`b` and that the tracked genealogy follows the pattern is `N⁻ᵏ` times the pattern probability,
`N` being the number of vertices: the conditional probability given the sample is the pattern
probability of the tracked frozen labels. -/
theorem sampledReverseVectorLaw_patternEvent {xa : ℕ → ℤ} {n p₀ : ℕ} {b : Fin k → ℕ}
    (hb : ∀ j, b j < n ∧ xa (b j + 1) = -1) (xs : Fin m → ConnState k) (c : Fin m → ℕ) :
    (sampledReverseVectorLaw xa n k).real (patternEvent n p₀ b xs c ×ˢ {frozenVertex b}) =
      ((vertexCount xa n : ℝ)⁻¹) ^ k *
        (jointLaw (companionSchedule xa) n).real (patternEvent n p₀ b xs c) := by
  classical
  have hmem : ∀ j, frozenVertex b j ∈ vertexLabels xa n := by
    intro j
    simp only [frozenVertex, vertexLabels, Finset.inl_mem_disjSum, downSteps, Finset.mem_filter,
      Finset.mem_Ioc]
    exact ⟨⟨by omega, by have := (hb j).1; omega⟩, (hb j).2⟩
  have : IsFiniteMeasure (uniformVertex xa n) := uniformOfFinset_finite _
  have hpt : (Measure.pi fun _ : Fin k ↦ uniformVertex xa n) {frozenVertex b} =
      ((vertexCount xa n : ℝ≥0∞)⁻¹) ^ k := by
    rw [← Set.univ_pi_singleton, Measure.pi_pi]
    simp only [uniformVertex]
    rw [Finset.prod_congr rfl fun j _ ↦ Measure.uniformOfFinset_apply_singleton_of_mem (hmem j),
      Finset.prod_const, Finset.card_univ, Fintype.card_fin, card_vertexLabels]
  rw [measureReal_def, sampledReverseVectorLaw, Measure.prod_prod, hpt, ENNReal.toReal_mul,
    mul_comm, ENNReal.toReal_pow, ENNReal.toReal_inv, ENNReal.toReal_natCast, measureReal_def]

/-- The source's normalization `(n/2)^(2k-1-r)` of the joint probability (including the choice
of the sampled vertices) differs from `scaledPatternProb` by the deterministic factor
`((n/2)/N)^k`. -/
theorem sourceNormalization_eq {xa : ℕ → ℤ} {n : ℕ} {ε : ℝ} {xs : Fin m → ConnState k}
    {b : Fin k → ℕ} {c : Fin m → ℕ} (h : LocalAdmissible xa n ε xs b c) :
    ((n : ℝ) / 2) ^ (k + m) * (sampledReverseVectorLaw xa n k).real
        (patternEvent n (phaseAbove n ε) b xs c ×ˢ {frozenVertex b}) =
      (((n : ℝ) / 2) / vertexCount xa n) ^ k * scaledPatternProb xa n ε xs b c := by
  classical
  rw [sampledReverseVectorLaw_patternEvent h.2.1, scaledPatternProb, ite_eq_left h,
    div_pow ((n : ℝ) / 2), inv_pow, pow_add]
  ring

/-- The normalization factor `((n/2)/N)^k` tends to one in the critical regime. -/
theorem tendsto_vertexFactor {xa : ℕ → ℕ → ℤ} {g : ℝ → ℝ} (hx : AdmissibleArray xa)
    (hL1 : HasL1ReciprocalProfile xa (1 / 2) g) (hpos : PositiveProfile g) (k : ℕ) :
    Tendsto (fun n : ℕ ↦ (((n : ℝ) / 2) / vertexCount (xa n) n) ^ k) atTop (𝓝 1) := by
  have hV := tendsto_vertexCount_div hx (by norm_num : (1 / 2 : ℝ) < 1) hL1 hpos
  have hinv := hV.inv₀ one_ne_zero
  rw [inv_one] at hinv
  have h := hinv.pow k
  rw [one_pow] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  congr 1
  rw [mul_inv, inv_div, div_div, div_mul_eq_mul_div, mul_comm, ← div_div]
  ring

/-! ### The corrected local limit -/

/-- **The corrected local limit `eq:cv locale` (inventory N12a), non-plane form.**
Under the critical hypotheses, with `g = 1/f` measurable, fix `k`, a number `m ≤ k - 1` of
merges above the cutoff (`r = k - 1 - m` merges below it) and a merge history `xs`.
1. For every cutoff `ε > 0`, the law of the rescaled conditional probability
   `scaledPatternProb` at the source's samples (iid uniform down-step births, iid uniform
   up-step merge phases) is eventually the image of the auxiliary law by the discrete local
   functional, and these laws converge weakly, as `n → ∞`, to the law of the limit functional
   at cutoff `ε` under independent uniform times marked by `g²`.
2. As `ε → 0⁺`, these limit laws converge weakly to the law of the limit functional without
   cutoff.
3. The latter is the law of the non-plane density `historyDensity g B m xs C`
   (`= 2^m g_{r,k}`) at independent uniform births `B` and merge times `C`. -/
theorem critical_local_limit {xa : ℕ → ℕ → ℤ} {g : ℝ → ℝ} (hx : AdmissibleArray xa)
    (hL1 : HasL1ReciprocalProfile xa (1 / 2) g) (hpos : PositiveProfile g)
    (h2 : HasLocalSquareMomentProfile xa (1 / 2) g) (hg : Measurable g)
    (xs : Fin m → ConnState k) :
    (∀ ε, 0 < ε →
      (∀ᶠ n in atTop, ((auxLocalLaw (xa n) n k m).map (discFun (xa n) n ε xs) : Measure ℝ) =
        (sourceSampleLaw (xa n) n k m).map
          (fun q ↦ scaledPatternProb (xa n) n ε xs q.1 q.2)) ∧
      Tendsto (fun n ↦ (auxLocalLaw (xa n) n k m).map (discFun (xa n) n ε xs)) atTop
        (𝓝 ((limitLocalLaw g k m).map (limitFun g ε xs)))) ∧
    Tendsto (fun ε ↦ (limitLocalLaw g k m).map (limitFun g ε xs)) (𝓝[>] 0)
      (𝓝 ((limitLocalLaw g k m).map (limitFun0 g xs))) ∧
    ((limitLocalLaw g k m).map (limitFun0 g xs) : Measure ℝ) =
      ((cubeMeasure k).prod (cubeMeasure m)).map
        (fun q ↦ (historyDensity g q.1 m xs q.2).toReal) :=
  ⟨fun _ hε ↦ ⟨eventually_map_discFun_eq hx hL1 hpos _ xs,
      tendsto_localLaw hx hL1 hpos h2 hg hε xs⟩,
    tendsto_limitLaw_zero hg h2 xs, limitLocalLaw_map_limitFun0 hg xs⟩

/-! ### The source's forests `𝔉⁺_{r,k}` -/

section Forest

variable {r : ℕ}

/-- The plane forest `F₀ ∈ 𝔉⁺_{r,k}` is compatible with the merge history `xs` for the event
times `(b, cs)`: for some child orders, the plane history has forest `F₀`. -/
def ForestCompatible (r : ℕ) (F₀ : SourceForest r k) (xs : Fin (k - 1 - r) → ConnState k)
    (b : Fin k → ℝ) (cs : Fin (k - 1 - r) → ℝ) : Prop :=
  ∃ σ, patternForest r xs σ (cmpOf (Sum.elim b cs)) (unitPattern cs) = some F₀

/-- The child orders of a plane history with a given forest are unique. -/
theorem eq_of_patternForest_eq_some (hr : r < k) {F₀ : SourceForest r k}
    {xs : Fin (k - 1 - r) → ConnState k} {b : Fin k → ℝ} {cs : Fin (k - 1 - r) → ℝ}
    {σ σ' : Fin (k - 1 - r) → Bool}
    (h : patternForest r xs σ (cmpOf (Sum.elim b cs)) (unitPattern cs) = some F₀)
    (h' : patternForest r xs σ' (cmpOf (Sum.elim b cs)) (unitPattern cs) = some F₀) :
    σ = σ' := by
  obtain ⟨hinj, hadm, hF⟩ := (patternForest_eq_some_iff hr xs σ b cs F₀).mp h
  obtain ⟨hinj2, -, hF2⟩ := (patternForest_eq_some_iff hr xs σ' b cs F₀).mp h'
  have hN : k + (k - 1 - r) = 2 * k - 1 - r := by omega
  have hD := ((isAdmissible_iff_dAdm hinj (labelEquiv_lt_iff_times hinj hN) xs).mp hadm).2
  rw [← hD.forestOrders_histForest σ, ← hD.forestOrders_histForest σ', hF, hF2]

theorem sum_ite_patternForest {M : Type*} [AddCommMonoid M] (hr : r < k) (F₀ : SourceForest r k)
    (xs : Fin (k - 1 - r) → ConnState k) (b : Fin k → ℝ) (cs : Fin (k - 1 - r) → ℝ) (a : M) :
    (∑ σ : Fin (k - 1 - r) → Bool,
      open Classical in
      if patternForest r xs σ (cmpOf (Sum.elim b cs)) (unitPattern cs) = some F₀ then a
        else 0) =
      open Classical in if ForestCompatible r F₀ xs b cs then a else 0 := by
  classical
  by_cases hex : ForestCompatible r F₀ xs b cs
  · obtain ⟨σ₀, h₀⟩ := hex
    rw [ite_eq_left ⟨σ₀, h₀⟩, Finset.sum_eq_single σ₀]
    · rw [ite_eq_left h₀]
    · intro σ _ hσ
      rw [ite_eq_right]
      intro h
      exact hσ (eq_of_patternForest_eq_some hr h h₀)
    · intro h
      exact absurd (Finset.mem_univ _) h
  · rw [ite_eq_right hex]
    refine Finset.sum_eq_zero fun σ _ ↦ ?_
    rw [ite_eq_right]
    intro h
    exact hex ⟨σ, h⟩

open Classical in
/-- **The non-plane density of a forest.** Summing the non-plane density over the merge
histories compatible with `F₀ ∈ 𝔉⁺_{r,k}` gives `2^(k-1-r) g_{r,k}(F₀, b, c)`, the factor
accounting for the `2^(k-1-r)` child orders. -/
theorem sum_historyDensity_forest (g : ℝ → ℝ) (hr : r < k) (F₀ : SourceForest r k)
    (b : Fin k → ℝ) (cs : Fin (k - 1 - r) → ℝ) :
    ∑ xs : Fin (k - 1 - r) → ConnState k,
      (if ForestCompatible r F₀ xs b cs then historyDensity g b (k - 1 - r) xs cs else 0) =
      2 ^ (k - 1 - r) * sourceDensity g F₀ b (cs ∘ Fin.rev) := by
  have h := sum_planeDensity_patternForest g hr F₀ b cs
  simp_rw [sum_ite_patternForest hr F₀ _ b cs, planeDensity] at h
  rw [← h, Finset.mul_sum]
  refine Finset.sum_congr rfl fun xs _ ↦ ?_
  have h2 : (2 : ℝ≥0∞) ^ (k - 1 - r) * 2⁻¹ ^ (k - 1 - r) = 1 := by
    rw [← mul_pow, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_pow]
  split_ifs
  · rw [← mul_assoc, h2, one_mul]
  · rw [mul_zero]

/-- Scaled integer phases. -/
noncomputable def scaledPhases {ι : Type*} (n : ℕ) (b : ι → ℕ) : ι → ℝ := fun j ↦ (b j : ℝ) / n

open Classical in
/-- **The rescaled conditional probability of a forest.** `(n/2)^(k-1-r)` times the
probability, given that the sampled vertices are the frozen vertices born at `b`, that the
merges above `ε n` are `k - 1 - r` merges at the phases `c` forming the forest `F₀ ∈ 𝔉⁺_{r,k}`
up to the order of the children (the merge histories compatible with `F₀` for the order of the
event times give disjoint events). -/
noncomputable def scaledForestProb (xa : ℕ → ℤ) (n : ℕ) (ε : ℝ) (F₀ : SourceForest r k)
    (b : Fin k → ℕ) (c : Fin (k - 1 - r) → ℕ) : ℝ :=
  ∑ xs : Fin (k - 1 - r) → ConnState k,
    if ForestCompatible r F₀ xs (scaledPhases n b) (scaledPhases n c) then
      scaledPatternProb xa n ε xs b c else 0

open Classical in
/-- The discrete forest functional. -/
noncomputable def discFunForest (xa : ℕ → ℤ) (n : ℕ) (ε : ℝ) (F₀ : SourceForest r k)
    (z : LocalSpace k (k - 1 - r)) : ℝ :=
  ∑ xs : Fin (k - 1 - r) → ConnState k,
    if ForestCompatible r F₀ xs (scaledPhases n (floorBirths n z))
        (scaledPhases n (floorMerges n z)) then discFun xa n ε xs z else 0

open Classical in
/-- The limit forest functional at cutoff `ε`. -/
noncomputable def limitFunForest (g : ℝ → ℝ) (ε : ℝ) (F₀ : SourceForest r k)
    (z : LocalSpace k (k - 1 - r)) : ℝ :=
  ∑ xs : Fin (k - 1 - r) → ConnState k,
    if ForestCompatible r F₀ xs z.1 (mergeTimes z) then limitFun g ε xs z else 0

open Classical in
/-- The limit forest functional without cutoff. -/
noncomputable def limitFun0Forest (g : ℝ → ℝ) (F₀ : SourceForest r k)
    (z : LocalSpace k (k - 1 - r)) : ℝ :=
  ∑ xs : Fin (k - 1 - r) → ConnState k,
    if ForestCompatible r F₀ xs z.1 (mergeTimes z) then limitFun0 g xs z else 0

theorem forestCompatible_congr {F₀ : SourceForest r k} {xs : Fin (k - 1 - r) → ConnState k}
    {b b' : Fin k → ℝ} {cs cs' : Fin (k - 1 - r) → ℝ}
    (h1 : cmpOf (Sum.elim b cs) = cmpOf (Sum.elim b' cs')) (h2 : unitPattern cs = unitPattern cs') :
    ForestCompatible r F₀ xs b cs ↔ ForestCompatible r F₀ xs b' cs' := by
  unfold ForestCompatible
  rw [h1, h2]

/-- Along converging configurations with distinct limits in `(0, 1)`, the comparison pattern
and the unit pattern are eventually those of the limit. -/
theorem eventually_forestCompatible_iff {F₀ : SourceForest r k} {β : ℕ → Fin k → ℝ}
    {γ : ℕ → Fin (k - 1 - r) → ℝ} {β₀ : Fin k → ℝ} {γ₀ : Fin (k - 1 - r) → ℝ}
    (hβ : ∀ j, Tendsto (fun n ↦ β n j) atTop (𝓝 (β₀ j)))
    (hγ : ∀ i, Tendsto (fun n ↦ γ n i) atTop (𝓝 (γ₀ i)))
    (hinj : Function.Injective (Sum.elim β₀ γ₀)) (hγ01 : ∀ i, 0 < γ₀ i ∧ γ₀ i < 1) :
    ∀ᶠ n in atTop, ∀ xs, (ForestCompatible r F₀ xs (β n) (γ n) ↔
      ForestCompatible r F₀ xs β₀ γ₀) := by
  have ht : ∀ a, Tendsto (fun n ↦ Sum.elim (β n) (γ n) a) atTop (𝓝 (Sum.elim β₀ γ₀ a)) := by
    intro a
    rcases a with j | i
    · exact hβ j
    · exact hγ i
  have hcmp : ∀ a a', ∀ᶠ n in atTop,
      cmpOf (Sum.elim (β n) (γ n)) a a' = cmpOf (Sum.elim β₀ γ₀) a a' := by
    intro a a'
    by_cases haa : a = a'
    · subst haa
      exact Eventually.of_forall fun n ↦ by simp [cmpOf]
    · rcases lt_or_gt_of_ne (fun h ↦ haa (hinj h)) with hlt | hgt
      · filter_upwards [(ht a).eventually_lt (ht a') hlt] with n hn
        simp [cmpOf, hn, hlt]
      · filter_upwards [(ht a').eventually_lt (ht a) hgt] with n hn
        simp [cmpOf, not_lt.mpr hn.le, not_lt.mpr hgt.le]
  have hunit : ∀ i, ∀ᶠ n in atTop, unitPattern (γ n) i = unitPattern γ₀ i := by
    intro i
    filter_upwards [(hγ i).eventually (lt_mem_nhds (hγ01 i).1),
      (hγ i).eventually (gt_mem_nhds (hγ01 i).2)] with n h1 h2
    simp [unitPattern, h1, h2, hγ01 i]
  filter_upwards [eventually_all.mpr fun a ↦ eventually_all.mpr (hcmp a),
    eventually_all.mpr hunit] with n h1 h2 xs
  exact forestCompatible_congr (funext fun a ↦ funext fun a' ↦ h1 a a') (funext h2)

theorem tendsto_discFunForest {xa : ℕ → ℕ → ℤ} {g : ℝ → ℝ} (hx : AdmissibleArray xa)
    (hL1 : HasL1ReciprocalProfile xa (1 / 2) g) (hpos : PositiveProfile g)
    (h2 : HasLocalSquareMomentProfile xa (1 / 2) g) {ε : ℝ} (hε : 0 < ε)
    (F₀ : SourceForest r k) {z : LocalSpace k (k - 1 - r)} (hz : z ∈ goodSet ε)
    {w : ℕ → LocalSpace k (k - 1 - r)} (hw : Tendsto w atTop (𝓝 z)) :
    Tendsto (fun n ↦ discFunForest (xa n) n ε F₀ (w n)) atTop
      (𝓝 (limitFunForest g ε F₀ z)) := by
  classical
  have hwb : ∀ j, Tendsto (fun n ↦ (w n).1 j) atTop (𝓝 (z.1 j)) := fun j ↦
    ((show Continuous (fun z : LocalSpace k (k - 1 - r) ↦ z.1 j) by fun_prop).tendsto z).comp hw
  have hwc : ∀ i, Tendsto (fun n ↦ ((w n).2 i).1) atTop (𝓝 ((z.2 i).1)) := fun i ↦
    ((show Continuous (fun z : LocalSpace k (k - 1 - r) ↦ (z.2 i).1) by fun_prop).tendsto
      z).comp hw
  have hb : ∀ j, Tendsto (fun n ↦ scaledPhases n (floorBirths n (w n)) j) atTop (𝓝 (z.1 j)) :=
    fun j ↦ tendsto_floor_mul_div (hz.1 j).1 (hwb j)
  have hc : ∀ i, Tendsto (fun n ↦ scaledPhases n (floorMerges n (w n)) i) atTop
      (𝓝 (mergeTimes z i)) := fun i ↦ tendsto_floor_mul_div (hz.2.1 i).1 (hwc i)
  have hev := eventually_forestCompatible_iff (F₀ := F₀) hb hc hz.2.2.1 hz.2.1
  unfold discFunForest limitFunForest
  refine tendsto_finsetSum _ fun xs _ ↦ ?_
  by_cases hF : ForestCompatible r F₀ xs z.1 (mergeTimes z)
  · rw [ite_eq_left hF]
    apply (tendsto_discFun hx hL1 hpos h2 hε xs hz hw).congr'
    filter_upwards [hev] with n hn
    rw [ite_eq_left ((hn xs).mpr hF)]
  · rw [ite_eq_right hF]
    apply tendsto_const_nhds.congr'
    filter_upwards [hev] with n hn
    rw [ite_eq_right fun h ↦ hF ((hn xs).mp h)]

theorem measurable_discFunForest (xa : ℕ → ℤ) (n : ℕ) (ε : ℝ) (F₀ : SourceForest r k) :
    Measurable (discFunForest xa n ε F₀) := by
  classical
  unfold discFunForest
  refine Finset.measurable_sum _ fun xs _ ↦ Measurable.ite ?_ (measurable_discFun xa n ε xs)
    measurable_const
  have : {z : LocalSpace k (k - 1 - r) | ForestCompatible r F₀ xs
      (scaledPhases n (floorBirths n z)) (scaledPhases n (floorMerges n z))} =
      (fun z ↦ (floorBirths n z, floorMerges n z)) ⁻¹'
        {q | ForestCompatible r F₀ xs (scaledPhases n q.1) (scaledPhases n q.2)} := rfl
  rw [this]
  exact ((measurable_floorBirths n).prodMk (measurable_floorMerges n))
    (Set.to_countable _).measurableSet

theorem measurableSet_forestCompatible (F₀ : SourceForest r k)
    (xs : Fin (k - 1 - r) → ConnState k) :
    MeasurableSet {z : LocalSpace k (k - 1 - r) | ForestCompatible r F₀ xs z.1 (mergeTimes z)} := by
  have ht : ∀ a, Measurable (fun z : LocalSpace k (k - 1 - r) ↦ Sum.elim z.1 (mergeTimes z) a) := by
    intro a
    rcases a with j | i
    · exact (measurable_pi_apply j).comp measurable_fst
    · exact measurable_fst.comp ((measurable_pi_apply i).comp measurable_snd)
  have hD : Measurable (fun z : LocalSpace k (k - 1 - r) ↦
      (cmpOf (Sum.elim z.1 (mergeTimes z)), unitPattern (mergeTimes z))) := by
    refine Measurable.prodMk ?_ ?_
    · exact measurable_pi_iff.mpr fun a ↦ measurable_pi_iff.mpr fun a' ↦
        measurable_decide_lt (ht a) (ht a')
    · exact measurable_pi_iff.mpr fun i ↦ measurable_decide
        ((measurableSet_lt measurable_const (ht (Sum.inr i))).inter
          (measurableSet_lt (ht (Sum.inr i)) measurable_const))
  have : {z : LocalSpace k (k - 1 - r) | ForestCompatible r F₀ xs z.1 (mergeTimes z)} =
      (fun z : LocalSpace k (k - 1 - r) ↦
        (cmpOf (Sum.elim z.1 (mergeTimes z)), unitPattern (mergeTimes z))) ⁻¹'
        {d | ∃ σ, patternForest r xs σ d.1 d.2 = some F₀} := rfl
  rw [this]
  exact hD (Set.to_countable _).measurableSet

theorem measurable_limitFunForest {g : ℝ → ℝ} (hg : Measurable g) (ε : ℝ)
    (F₀ : SourceForest r k) : Measurable (limitFunForest g ε F₀) := by
  classical
  unfold limitFunForest
  exact Finset.measurable_sum _ fun xs _ ↦ Measurable.ite (measurableSet_forestCompatible F₀ xs)
    (measurable_limitFun hg ε xs) measurable_const

theorem measurable_limitFun0Forest {g : ℝ → ℝ} (hg : Measurable g) (F₀ : SourceForest r k) :
    Measurable (limitFun0Forest g F₀) := by
  classical
  unfold limitFun0Forest
  exact Finset.measurable_sum _ fun xs _ ↦ Measurable.ite (measurableSet_forestCompatible F₀ xs)
    (measurable_limitFun0 hg xs) measurable_const

/-- **The corrected local limit for a forest at a fixed cutoff**, in distribution. -/
theorem tendsto_localLawForest {xa : ℕ → ℕ → ℤ} {g : ℝ → ℝ} (hx : AdmissibleArray xa)
    (hL1 : HasL1ReciprocalProfile xa (1 / 2) g) (hpos : PositiveProfile g)
    (h2 : HasLocalSquareMomentProfile xa (1 / 2) g) (hg : Measurable g) {ε : ℝ} (hε : 0 < ε)
    (F₀ : SourceForest r k) :
    Tendsto (fun n ↦ (auxLocalLaw (xa n) n k (k - 1 - r)).map (discFunForest (xa n) n ε F₀))
      atTop (𝓝 ((limitLocalLaw g k (k - 1 - r)).map (limitFunForest g ε F₀))) :=
  tendsto_map_of_continuousConvergence (tendsto_auxiliary_birth_and_rates hx hL1 hpos h2 k _)
    (fun n ↦ measurable_discFunForest (xa n) n ε F₀) (measurable_limitFunForest hg ε F₀)
    (limitLocalLaw_goodSet_compl hg ε)
    (fun _ hz _ hw ↦ tendsto_discFunForest hx hL1 hpos h2 hε F₀ hz hw)

theorem eventually_map_discFunForest_eq {xa : ℕ → ℕ → ℤ} {g : ℝ → ℝ} (hx : AdmissibleArray xa)
    (hL1 : HasL1ReciprocalProfile xa (1 / 2) g) (hpos : PositiveProfile g) (ε : ℝ)
    (F₀ : SourceForest r k) :
    ∀ᶠ n in atTop,
      ((auxLocalLaw (xa n) n k (k - 1 - r)).map (discFunForest (xa n) n ε F₀) : Measure ℝ) =
        (sourceSampleLaw (xa n) n k (k - 1 - r)).map
          (fun q ↦ scaledForestProb (xa n) n ε F₀ q.1 q.2) := by
  classical
  filter_upwards [eventually_auxLocalLaw_eq (k := k) (m := k - 1 - r) hx hL1 hpos,
    eventually_gt_atTop 0] with n hlaw hn
  rw [ProbabilityMeasure.toMeasure_map, hlaw,
    Measure.map_map (measurable_discFunForest (xa n) n ε F₀) (measurable_of_countable _)]
  apply Measure.map_congr
  filter_upwards [ae_sourceSampleLaw (k := k) (m := k - 1 - r) (xa n) n] with q hq
  simp only [Function.comp_apply, discFunForest, scaledForestProb,
    floorBirths_sampleEmbed (xa n) hn, floorMerges_sampleEmbed (xa n) hn,
    discFun_sampleEmbed (hx n).1 (hx n).2 hn ε _ hq]

/-- Removing the cutoff for a forest. -/
theorem tendsto_limitLawForest_zero {xa : ℕ → ℕ → ℤ} {g : ℝ → ℝ} (hg : Measurable g)
    (h2 : HasLocalSquareMomentProfile xa (1 / 2) g) (F₀ : SourceForest r k) :
    Tendsto (fun ε ↦ (limitLocalLaw g k (k - 1 - r)).map (limitFunForest g ε F₀)) (𝓝[>] 0)
      (𝓝 ((limitLocalLaw g k (k - 1 - r)).map (limitFun0Forest g F₀))) := by
  classical
  apply tendsto_map_of_ae_tendsto _ (fun ε ↦ measurable_limitFunForest hg ε F₀)
    (measurable_limitFun0Forest hg F₀)
  have hgood := limitLocalLaw_goodSet_compl (k := k) (m := k - 1 - r) hg 0
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp hgood] with z hz
  have hz' : z ∈ goodSet 0 := by simpa using hz
  unfold limitFunForest limitFun0Forest
  refine tendsto_finsetSum _ fun xs _ ↦ ?_
  by_cases hF : ForestCompatible r F₀ xs z.1 (mergeTimes z)
  · simp only [ite_eq_left hF]
    exact tendsto_limitFun_zero hg h2 xs (fun j ↦ (hz'.1 j).2) hz'.2.1
  · simp only [ite_eq_right hF]
    exact tendsto_const_nhds

theorem historyDensity_ne_top (g : ℝ → ℝ) (b : Fin k → ℝ) (xs : Fin m → ConnState k)
    (cs : Fin m → ℝ) : historyDensity g b m xs cs ≠ ∞ := by
  classical
  unfold historyDensity
  refine ENNReal.mul_ne_top (ENNReal.mul_ne_top ?_ ?_) (expNeg_ne_top _)
  · split_ifs <;> simp
  · exact ENNReal.prod_ne_top fun i _ ↦ ENNReal.ofReal_ne_top

/-- **Identification of the forest limit law** with the source's density: the law of the limit
forest functional without cutoff is the law of `2^(k-1-r) g_{r,k}(F₀, B, C)` at independent
uniform births `B` and merge times (listed increasingly, `C = cs ∘ rev`). -/
theorem limitLocalLaw_map_limitFun0Forest {g : ℝ → ℝ} (hg : Measurable g) (hr : r < k)
    (F₀ : SourceForest r k) :
    ((limitLocalLaw g k (k - 1 - r)).map (limitFun0Forest g F₀) : Measure ℝ) =
      ((cubeMeasure k).prod (cubeMeasure (k - 1 - r))).map
        (fun q ↦ (2 ^ (k - 1 - r) * sourceDensity g F₀ q.1 (q.2 ∘ Fin.rev)).toReal) := by
  classical
  rw [ProbabilityMeasure.toMeasure_map, limitLocalLaw_eq_map hg,
    show (fun q : (Fin k → ℝ) × (Fin (k - 1 - r) → ℝ) ↦ (q.1, fun i ↦ (q.2 i, g (q.2 i) ^ 2))) =
      markEmbed g from rfl,
    Measure.map_map (measurable_limitFun0Forest hg F₀) (measurable_markEmbed hg)]
  apply Measure.map_congr
  filter_upwards [ae_cubeProd_good (k := k) (m := k - 1 - r) 0] with q hq
  have hinj : Function.Injective q.1 := (hq.2.2.1).comp Sum.inl_injective
  simp only [Function.comp_apply, limitFun0Forest]
  rw [show mergeTimes (markEmbed g q) = q.2 from rfl, show (markEmbed g q).1 = q.1 from rfl,
    ← sum_historyDensity_forest g hr F₀ q.1 q.2, ENNReal.toReal_sum]
  · refine Finset.sum_congr rfl fun xs _ ↦ ?_
    split_ifs
    · exact limitFun0_markEmbed g xs hinj
    · rfl
  · intro xs _
    split_ifs
    · exact historyDensity_ne_top g q.1 xs q.2
    · simp

/-- **The corrected local limit `eq:cv locale` (inventory N12a), forest form.**
Under the critical hypotheses, with `g = 1/f` measurable, let `k > r ≥ 0` and
`F₀ ∈ 𝔉⁺_{r,k}`.
1. For every cutoff `ε > 0`, the law of `scaledForestProb` (the rescaled conditional
   probability that the merges above `ε n` form the forest `F₀` up to child orders, at the
   source's samples) is eventually the image of the auxiliary law by the discrete forest
   functional, and these laws converge weakly as `n → ∞`;
2. as `ε → 0⁺` the limits converge weakly;
3. the final limit is the law of `2^(k-1-r) g_{r,k}(F₀, B, C)` at independent uniform times
   (`sourceDensity`). The factor `2^(k-1-r)` is the number of child orders: the discrete
   event does not prescribe them. -/
theorem critical_local_limit_forest {xa : ℕ → ℕ → ℤ} {g : ℝ → ℝ} (hx : AdmissibleArray xa)
    (hL1 : HasL1ReciprocalProfile xa (1 / 2) g) (hpos : PositiveProfile g)
    (h2 : HasLocalSquareMomentProfile xa (1 / 2) g) (hg : Measurable g) (hr : r < k)
    (F₀ : SourceForest r k) :
    (∀ ε, 0 < ε →
      (∀ᶠ n in atTop,
        ((auxLocalLaw (xa n) n k (k - 1 - r)).map (discFunForest (xa n) n ε F₀) : Measure ℝ) =
          (sourceSampleLaw (xa n) n k (k - 1 - r)).map
            (fun q ↦ scaledForestProb (xa n) n ε F₀ q.1 q.2)) ∧
      Tendsto (fun n ↦ (auxLocalLaw (xa n) n k (k - 1 - r)).map (discFunForest (xa n) n ε F₀))
        atTop (𝓝 ((limitLocalLaw g k (k - 1 - r)).map (limitFunForest g ε F₀)))) ∧
    Tendsto (fun ε ↦ (limitLocalLaw g k (k - 1 - r)).map (limitFunForest g ε F₀)) (𝓝[>] 0)
      (𝓝 ((limitLocalLaw g k (k - 1 - r)).map (limitFun0Forest g F₀))) ∧
    ((limitLocalLaw g k (k - 1 - r)).map (limitFun0Forest g F₀) : Measure ℝ) =
      ((cubeMeasure k).prod (cubeMeasure (k - 1 - r))).map
        (fun q ↦ (2 ^ (k - 1 - r) * sourceDensity g F₀ q.1 (q.2 ∘ Fin.rev)).toReal) :=
  ⟨fun _ hε ↦ ⟨eventually_map_discFunForest_eq hx hL1 hpos _ F₀,
      tendsto_localLawForest hx hL1 hpos h2 hg hε F₀⟩,
    tendsto_limitLawForest_zero hg h2 F₀, limitLocalLaw_map_limitFun0Forest hg hr F₀⟩

end Forest

end Freezing2.CriticalLocalLimit
