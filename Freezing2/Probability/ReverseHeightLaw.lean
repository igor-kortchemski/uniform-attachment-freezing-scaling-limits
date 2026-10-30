module

public import Freezing2.Probability.ReverseHeightIncrements
public import Freezing2.Probability.ConditionalBernoulli
public import Mathlib.Probability.Distributions.Bernoulli
public import Mathlib.Probability.IdentDistrib

/-!
# Bernoulli representation of actual reverse-forest heights

All random variables below live on the constructed joint history. Independence
comes from the proved conditional increment probabilities given the entire
past. The height identity is obtained from kernel support, zero depth at birth,
and telescoping, including time zero and the extinction horizon.
Freezing steps are encoded as Bernoulli variables of parameter zero, equivalently
the source's Bernoulli variables multiplied by the deterministic up-step indicator.
-/

@[expose] public section

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators ProbabilityTheory

namespace Freezing2.ReverseHistory

/-- A transition property holding under the actual kernel at every valid state
holds almost surely for the corresponding two coordinates of the joint law. -/
theorem jointLaw_transition_support {x : Freezing1.SignSequence} {n k : ℕ}
    (hn : (n : ℕ∞) ≤ Freezing1.extinctionTime x) (hk : k ≤ n)
    {E : Set (Forest × Forest)} (hE : MeasurableSet E)
    (hker : ∀ F, Freezing1.Reverse.ValidAt x n (n - k) F →
      ∀ᵐ F' ∂stepKernel x n k F, (F, F') ∈ E) :
    ∀ᵐ ω ∂jointLaw x n, (ω k, ω (k + 1)) ∈ E := by
  apply jointLaw_ae_transition x n k hE
  filter_upwards [jointLaw_valid x n hn] with ω hv
  exact (ae_iff_prob_eq_one measurable_from_top).mp (hker (ω k) (hv k hk))

/-- Heights of an existing vertex change by zero or one at a reverse step. -/
theorem jointLaw_depth_step_support {x : Freezing1.SignSequence} {n i : ℕ}
    (hn : (n : ℕ∞) ≤ Freezing1.extinctionTime x) (hi : 1 ≤ i)
    {v : ℕ ⊕ ℕ} (hv : v ∈ Freezing1.vertexLabels x n)
    (hib : i ≤ Freezing1.birthTime n v) :
    ∀ᵐ ω ∂jointLaw x n,
      (ω (n - i + 1)).depth v = (ω (n - i)).depth v ∨
      (ω (n - i + 1)).depth v = (ω (n - i)).depth v + 1 := by
  have hin := hib.trans (birthTime_le_horizon hv)
  have hk : n - i < n := by omega
  have ht : n - (n - i) = i := by omega
  have ht' : n - ((n - i) + 1) + 1 = i := by omega
  let E : Set (Forest × Forest) :=
    {p | p.2.depth v = p.1.depth v ∨ p.2.depth v = p.1.depth v + 1}
  have hE : MeasurableSet E := by
    have hd : Measurable (fun F : Forest ↦ F.depth v) := measurable_from_top
    exact (measurableSet_eq_fun (hd.comp measurable_snd) (hd.comp measurable_fst)).union
      (measurableSet_eq_fun (hd.comp measurable_snd) ((hd.comp measurable_fst).add_const 1))
  apply jointLaw_transition_support hn (Nat.sub_le n i) hE
  intro F hF
  rw [ht] at hF
  have hvF : v ∈ F.vertices := by
    rw [hF.vertices_eq]
    exact (Freezing1.Reverse.mem_phaseLabels_iff_birthTime hin hv).mpr hib
  simp only [stepKernel, Kernel.coe_mk, hk, ite_true, Freezing1.Reverse.transitionLaw, ht']
  cases hxi : x i
  · have hfresh : Sum.inr (n - ((n - i) + 1)) ∉ F.vertices := by
      rw [hF.vertices_eq]
      simpa only [ht'] using
        Freezing1.Reverse.fresh_freezing_label x n (n - ((n - i) + 1))
    simp only [Bool.false_eq_true, ite_false]
    apply (ae_dirac_iff (by trivial)).mpr
    apply Or.inl
    simp only [Freezing1.Reverse.insertLabel, dite_eq_right hfresh,
      Freezing1.RootedForest.adjoin_depth_old F hfresh hvF]
  · have hiτ : ((n - ((n - i) + 1) + 1 : ℕ) : ℕ∞) ≤ Freezing1.extinctionTime x := by
      rw [ht']
      exact le_trans (by exact_mod_cast hin) hn
    have htwo : 2 ≤ F.roots.card := by
      rw [hF.roots_card]
      simpa only [ht'] using
        Freezing1.two_le_activeCount_toNat_succ_of_attachment hiτ (by simpa only [ht'] using hxi)
    simp only [ite_true]
    exact F.joinLaw_depth_support htwo v

/-- The actual depth at a vertex's prescribed birth time is zero. -/
theorem jointLaw_depth_at_birth_zero {x : Freezing1.SignSequence} {n : ℕ}
    (hn : (n : ℕ∞) ≤ Freezing1.extinctionTime x)
    {v : ℕ ⊕ ℕ} (hv : v ∈ Freezing1.vertexLabels x n) :
    ∀ᵐ ω ∂jointLaw x n, (forestAt n (Freezing1.birthTime n v) ω).depth v = 0 := by
  cases v with
  | inl j =>
    have hinit : (fun ω : History ↦ ω 0) =ᵐ[jointLaw x n]
        fun _ ↦ Freezing1.Reverse.initial x n :=
      HasLaw.ae_eq_of_dirac ⟨(measurable_pi_apply 0).aemeasurable, jointLaw_map_zero x n⟩
    filter_upwards [hinit] with ω hω
    simp only [Freezing1.birthTime, forestAt, Nat.sub_self, hω,
      Freezing1.Reverse.initial, Freezing1.RootedForest.isolated]
  | inr j =>
    have hj : j < n ∧ x (j + 1) = false := by
      simpa only [Freezing1.vertexLabels, Freezing1.frozenIndices, Finset.inr_mem_disjSum,
        Finset.mem_filter, Finset.mem_range] using hv
    have hk : n - (j + 1) < n := by omega
    have ht : n - (n - (j + 1)) = j + 1 := by omega
    have ht' : n - ((n - (j + 1)) + 1) = j := by omega
    let E : Set (Forest × Forest) := {p | p.2.depth (.inr j) = 0}
    have hE : MeasurableSet E := by
      have hd : Measurable (fun F : Forest ↦ F.depth (.inr j)) := measurable_from_top
      exact measurableSet_eq_fun (hd.comp measurable_snd) measurable_const
    have hs := jointLaw_transition_support hn (Nat.sub_le n (j + 1)) hE (fun F hF ↦ ?_)
    · filter_upwards [hs] with ω hω
      simpa only [E, Set.mem_ofPred_eq, Freezing1.birthTime, forestAt,
        show n - (j + 1) + 1 = n - j by omega] using hω
    · rw [ht] at hF
      have hfresh : Sum.inr j ∉ F.vertices := by
        rw [hF.vertices_eq]
        exact Freezing1.Reverse.fresh_freezing_label x n j
      simp only [stepKernel, Kernel.coe_mk, hk, ite_true, ht',
        Freezing1.Reverse.transitionLaw, hj.2, Bool.false_eq_true, ite_false]
      apply (ae_dirac_iff (by trivial)).mpr
      simp [E, Freezing1.Reverse.insertLabel, hfresh]

/-- The genuine increment event, set to the empty event outside the period
when this vertex is present and reverse steps are performed. -/
def heightIncrementEvent (n : ℕ) (v : ℕ ⊕ ℕ) (k : ℕ) : Set History :=
  if n - Freezing1.birthTime n v ≤ k ∧ k < n then
    transitionEvent (heightIncrementPair v) k else ∅

theorem measurableSet_heightIncrementEvent_piLE (n : ℕ) (v : ℕ ⊕ ℕ) (k : ℕ) :
    MeasurableSet[Filtration.piLE (X := fun _ ↦ Forest) (k + 1)]
      (heightIncrementEvent n v k) := by
  unfold heightIncrementEvent
  split_ifs
  · exact measurableSet_transitionEvent_piLE (measurableSet_heightIncrementPair v) k
  · exact @MeasurableSet.empty History (Filtration.piLE (X := fun _ ↦ Forest) (k + 1))

theorem measurableSet_heightIncrementEvent (n : ℕ) (v : ℕ ⊕ ℕ) (k : ℕ) :
    MeasurableSet (heightIncrementEvent n v k) :=
  (Filtration.piLE (X := fun _ ↦ Forest)).le (k + 1) _
    (measurableSet_heightIncrementEvent_piLE n v k)

/-- The deterministic increment probability in construction time. -/
noncomputable def heightIncrementRate (x : Freezing1.SignSequence) (n : ℕ)
    (v : ℕ ⊕ ℕ) (k : ℕ) : ℝ :=
  if n - Freezing1.birthTime n v ≤ k ∧ k < n then
    if x (n - k) then 1 / (Freezing1.activeCount x (n - k) : ℝ) else 0
  else 0

theorem conditional_heightIncrementEvent {x : Freezing1.SignSequence} {n : ℕ}
    (hn : (n : ℕ∞) ≤ Freezing1.extinctionTime x)
    {v : ℕ ⊕ ℕ} (hv : v ∈ Freezing1.vertexLabels x n) (k : ℕ) :
    (jointLaw x n)[(heightIncrementEvent n v k).indicator (fun _ ↦ (1 : ℝ)) |
      Filtration.piLE (X := fun _ ↦ Forest) k] =ᵐ[jointLaw x n]
      fun _ ↦ heightIncrementRate x n v k := by
  by_cases hk : n - Freezing1.birthTime n v ≤ k ∧ k < n
  · have hi : 1 ≤ n - k := by omega
    have hib : n - k ≤ Freezing1.birthTime n v := by omega
    have h := conditional_height_increment hn hi hv hib
    rw [heightIncrementEvent, ite_eq_left hk, heightIncrementRate, ite_eq_left hk]
    simpa only [incrementIndicator, transitionIndicator, Nat.sub_sub_self hk.2.le] using h
  · rw [heightIncrementEvent, ite_eq_right hk, heightIncrementRate, ite_eq_right hk]
    simp

/-- Independent increment events are a consequence of the actual full-history
conditional laws, rather than an independent-increments model premise. -/
theorem iIndepSet_heightIncrementEvent {x : Freezing1.SignSequence} {n : ℕ}
    (hn : (n : ℕ∞) ≤ Freezing1.extinctionTime x)
    {v : ℕ ⊕ ℕ} (hv : v ∈ Freezing1.vertexLabels x n) :
    iIndepSet (heightIncrementEvent n v) (jointLaw x n) :=
  iIndepSet_of_condExp_indicator (Filtration.piLE (X := fun _ ↦ Forest))
    (heightIncrementEvent n v) (measurableSet_heightIncrementEvent_piLE n v)
    (heightIncrementRate x n v) (conditional_heightIncrementEvent hn hv)

/-- Bernoulli variables realized by the actual height-increment events. -/
noncomputable def heightIncrementVariable (n : ℕ) (v : ℕ ⊕ ℕ) (k : ℕ) : History → ℝ :=
  (heightIncrementEvent n v k).indicator (fun _ ↦ 1)

/-- The probability parameter is intrinsically in `[0,1]`; its explicit source
formula is established below from the conditional increment theorem. -/
noncomputable def heightIncrementParameter (x : Freezing1.SignSequence) (n : ℕ)
    (v : ℕ ⊕ ℕ) (k : ℕ) : unitInterval :=
  ⟨(jointLaw x n).real (heightIncrementEvent n v k), by simp⟩

theorem heightIncrementParameter_val {x : Freezing1.SignSequence} {n : ℕ}
    (hn : (n : ℕ∞) ≤ Freezing1.extinctionTime x)
    {v : ℕ ⊕ ℕ} (hv : v ∈ Freezing1.vertexLabels x n) (k : ℕ) :
    (heightIncrementParameter x n v k : ℝ) = heightIncrementRate x n v k :=
  measureReal_of_condExp_indicator ((Filtration.piLE (X := fun _ ↦ Forest)).le k)
    (measurableSet_heightIncrementEvent n v k) (conditional_heightIncrementEvent hn hv k)

theorem hasLaw_heightIncrementVariable (x : Freezing1.SignSequence) (n : ℕ)
    (v : ℕ ⊕ ℕ) (k : ℕ) :
    HasLaw (heightIncrementVariable n v k)
      (bernoulliMeasure (1 : ℝ) 0 (heightIncrementParameter x n v k)) (jointLaw x n) :=
  hasLaw_indicator_bernoulliMeasure 1 (measurableSet_heightIncrementEvent n v k).nullMeasurableSet

theorem iIndepFun_heightIncrementVariable {x : Freezing1.SignSequence} {n : ℕ}
    (hn : (n : ℕ∞) ≤ Freezing1.extinctionTime x)
    {v : ℕ ⊕ ℕ} (hv : v ∈ Freezing1.vertexLabels x n) :
    iIndepFun (heightIncrementVariable n v) (jointLaw x n) :=
  (iIndepSet_heightIncrementEvent hn hv).iIndepFun_indicator

/-- Reindex the actual increments in the source order `a+1,…,birth(v)`. -/
noncomputable def heightBernoulli (n a : ℕ) (v : ℕ ⊕ ℕ)
    (i : Fin (Freezing1.birthTime n v - a)) : History → ℝ :=
  heightIncrementVariable n v (n - (a + i.val + 1))

noncomputable def heightBernoulliParameter (x : Freezing1.SignSequence) (n a : ℕ)
    (v : ℕ ⊕ ℕ) (i : Fin (Freezing1.birthTime n v - a)) : unitInterval :=
  heightIncrementParameter x n v (n - (a + i.val + 1))

theorem heightBernoulliParameter_val {x : Freezing1.SignSequence} {n a : ℕ}
    (hn : (n : ℕ∞) ≤ Freezing1.extinctionTime x)
    {v : ℕ ⊕ ℕ} (hv : v ∈ Freezing1.vertexLabels x n)
    (i : Fin (Freezing1.birthTime n v - a)) :
    (heightBernoulliParameter x n a v i : ℝ) =
      if x (a + i.val + 1) then 1 / (Freezing1.activeCount x (a + i.val + 1) : ℝ) else 0 := by
  unfold heightBernoulliParameter
  rw [heightIncrementParameter_val hn hv]
  have hib := i.isLt
  have hb := birthTime_le_horizon hv
  have hk : n - Freezing1.birthTime n v ≤ n - (a + i.val + 1) ∧
      n - (a + i.val + 1) < n := by omega
  rw [heightIncrementRate, ite_eq_left hk,
    Nat.sub_sub_self (show a + i.val + 1 ≤ n by omega)]

/-- Exact Bernoulli mean, in the source interval `(a,birth(v)]`. -/
theorem sum_heightBernoulliParameter {x : Freezing1.SignSequence} {n a : ℕ}
    (hn : (n : ℕ∞) ≤ Freezing1.extinctionTime x)
    {v : ℕ ⊕ ℕ} (hv : v ∈ Freezing1.vertexLabels x n) :
    (∑ i, (heightBernoulliParameter x n a v i : ℝ)) =
      ∑ i ∈ Finset.range (Freezing1.birthTime n v - a),
        if x (a + i + 1) then 1 / (Freezing1.activeCount x (a + i + 1) : ℝ) else 0 := by
  simp_rw [heightBernoulliParameter_val hn hv]
  exact Fin.sum_univ_eq_sum_range
    (fun i : ℕ ↦ if x (a + i + 1) then 1 / (Freezing1.activeCount x (a + i + 1) : ℝ) else 0)
    (Freezing1.birthTime n v - a)

theorem iIndepFun_heightBernoulli {x : Freezing1.SignSequence} {n a : ℕ}
    (hn : (n : ℕ∞) ≤ Freezing1.extinctionTime x)
    {v : ℕ ⊕ ℕ} (hv : v ∈ Freezing1.vertexLabels x n) :
    iIndepFun (heightBernoulli n a v) (jointLaw x n) := by
  apply (iIndepFun_heightIncrementVariable hn hv).precomp
  intro i j hij
  apply Fin.ext
  have hi := i.isLt
  have hj := j.isLt
  have hb := birthTime_le_horizon hv
  change n - (a + i.val + 1) = n - (a + j.val + 1) at hij
  omega

theorem hasLaw_heightBernoulli (x : Freezing1.SignSequence) (n a : ℕ)
    (v : ℕ ⊕ ℕ) (i : Fin (Freezing1.birthTime n v - a)) :
    HasLaw (heightBernoulli n a v i)
      (bernoulliMeasure (1 : ℝ) 0 (heightBernoulliParameter x n a v i)) (jointLaw x n) :=
  hasLaw_heightIncrementVariable x n v _

/-- Actual height in the source forest at time `i`, viewed as a real random
variable for the concentration theorem. The stored natural depth is already
proved equal to the graph distance from its component root. -/
def heightAt (n i : ℕ) (v : ℕ ⊕ ℕ) (ω : History) : ℝ :=
  ((forestAt n i ω).depth v : ℝ)

theorem measurable_heightAt (n i : ℕ) (v : ℕ ⊕ ℕ) : Measurable (heightAt n i v) := by
  exact (measurable_from_top : Measurable (fun F : Forest ↦ (F.depth v : ℝ))).comp
    (measurable_pi_apply (n - i))

/-- The indicator is the actual height difference, almost surely; the support
lemma rules out other increments. -/
theorem heightIncrementVariable_eq_sub {x : Freezing1.SignSequence} {n i : ℕ}
    (hn : (n : ℕ∞) ≤ Freezing1.extinctionTime x) (hi : 1 ≤ i)
    {v : ℕ ⊕ ℕ} (hv : v ∈ Freezing1.vertexLabels x n)
    (hib : i ≤ Freezing1.birthTime n v) :
    heightIncrementVariable n v (n - i) =ᵐ[jointLaw x n]
      fun ω ↦ heightAt n (i - 1) v ω - heightAt n i v ω := by
  have hin := hib.trans (birthTime_le_horizon hv)
  have hk : n - Freezing1.birthTime n v ≤ n - i ∧ n - i < n := by omega
  have ht : n - (i - 1) = n - i + 1 := by omega
  filter_upwards [jointLaw_depth_step_support hn hi hv hib] with ω hω
  simp only [heightIncrementVariable, heightIncrementEvent, ite_eq_left hk,
    heightAt, forestAt, ht]
  rcases hω with h0 | h1
  · simp [transitionEvent, heightIncrementPair, h0]
  · simp [transitionEvent, heightIncrementPair, h1, Nat.cast_add, Nat.cast_one]

/-- The actual forest height is the sum of its actual Bernoulli increments.
The proof also covers the empty sum at birth, including birth time zero. -/
theorem heightAt_eq_sum_heightBernoulli {x : Freezing1.SignSequence} {n a : ℕ}
    (hn : (n : ℕ∞) ≤ Freezing1.extinctionTime x)
    {v : ℕ ⊕ ℕ} (hv : v ∈ Freezing1.vertexLabels x n)
    (ha : a ≤ Freezing1.birthTime n v) :
    heightAt n a v =ᵐ[jointLaw x n] fun ω ↦ ∑ i, heightBernoulli n a v i ω := by
  have hstep (i : Fin (Freezing1.birthTime n v - a)) :
      heightBernoulli n a v i =ᵐ[jointLaw x n] fun ω ↦
        heightAt n (a + i.val) v ω - heightAt n (a + i.val + 1) v ω := by
    have hi := i.isLt
    simpa only [heightBernoulli, Nat.add_sub_cancel] using
      heightIncrementVariable_eq_sub hn (show 1 ≤ a + i.val + 1 by omega) hv (by omega)
  filter_upwards [ae_all_iff.mpr hstep, jointLaw_depth_at_birth_zero hn hv] with ω hω hb
  symm
  calc
    _ = ∑ i : Fin (Freezing1.birthTime n v - a),
        (heightAt n (a + i.val) v ω - heightAt n (a + i.val + 1) v ω) :=
      Finset.sum_congr rfl fun i _ ↦ hω i
    _ = ∑ i ∈ Finset.range (Freezing1.birthTime n v - a),
        (heightAt n (a + i) v ω - heightAt n (a + i + 1) v ω) :=
      Fin.sum_univ_eq_sum_range
        (fun i : ℕ ↦ heightAt n (a + i) v ω - heightAt n (a + i + 1) v ω)
        (Freezing1.birthTime n v - a)
    _ = heightAt n a v ω - heightAt n (Freezing1.birthTime n v) v ω := by
      simpa only [Nat.add_zero, Nat.add_assoc, Nat.add_sub_of_le ha] using
        Finset.sum_range_sub' (fun i ↦ heightAt n (a + i) v ω)
          (Freezing1.birthTime n v - a)
    _ = heightAt n a v ω := by simp only [heightAt, hb, Nat.cast_zero, sub_zero]

/-- The Bernoulli-sum marginal law of the actual reverse height. Independence
and the exact source probabilities are the preceding proved exports. -/
theorem identDistrib_heightAt_sum_heightBernoulli {x : Freezing1.SignSequence} {n a : ℕ}
    (hn : (n : ℕ∞) ≤ Freezing1.extinctionTime x)
    {v : ℕ ⊕ ℕ} (hv : v ∈ Freezing1.vertexLabels x n)
    (ha : a ≤ Freezing1.birthTime n v) :
    IdentDistrib (heightAt n a v) (fun ω ↦ ∑ i, heightBernoulli n a v i ω)
      (jointLaw x n) (jointLaw x n) :=
  IdentDistrib.of_ae_eq (measurable_heightAt n a v).aemeasurable
    (heightAt_eq_sum_heightBernoulli hn hv ha)

end Freezing2.ReverseHistory
