module

/-
Vendored from the freezing1 companion project. Local imports are relocated;
namespace, statements, and proofs are preserved. See docs/companion-provenance.md.
-/

public import Freezing2.Companion.ForwardTree
public import Mathlib.Probability.Distributions.Uniform
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# Uniform random choices in the forward construction

The transition law is the pushforward of the uniform distribution on the
current active vertices. An empty active set is absorbing. Iterated measure
binds give the law of the tree at each time, with fresh uniform choices
conditional on the whole current state. These definitions do not assume the
reverse construction or any height-distribution identity.
-/

@[expose] public section

namespace Freezing1.Forward

open MeasureTheory
open scoped ENNReal Classical

instance : MeasurableSpace State := ⊤
instance : DiscreteMeasurableSpace State := ⟨fun _ => trivial⟩

theorem uniform_active_probability (s : State) (h : s.active.Nonempty) :
    IsProbabilityMeasure (Measure.uniformOfFinset s.active) := by
  constructor
  rw [Measure.uniformOfFinset_apply]
  simp only [Set.mem_univ, Finset.filter_true]
  exact ENNReal.div_self (by exact_mod_cast h.card_pos.ne') (by simp)

/-- One uniform choice, followed by the deterministic Algorithm 1 transition. -/
noncomputable def transitionLaw (s : State) (t : ℕ) (sign : Bool) : Measure State :=
  if s.active.Nonempty then
    (Measure.uniformOfFinset s.active).map (fun v => step s t sign v)
  else Measure.dirac s

instance transitionLaw_probability (s : State) (t : ℕ) (sign : Bool) :
    IsProbabilityMeasure (transitionLaw s t sign) := by
  unfold transitionLaw
  split_ifs with h
  · have := uniform_active_probability s h
    exact Measure.isProbabilityMeasure_map_iff (by fun_prop) |>.mpr inferInstance
  · infer_instance

/-- Exact finite transition probabilities, expressed as uniform counts. -/
theorem transitionLaw_apply (s : State) (t : ℕ) (sign : Bool)
    (h : s.active.Nonempty) (A : Set State) :
    transitionLaw s t sign A =
      ((s.active.filter (fun v => step s t sign v ∈ A)).card : ℝ≥0∞) / s.active.card := by
  classical
  rw [transitionLaw, ite_eq_left h, Measure.map_apply (by fun_prop) (by trivial),
    Measure.uniformOfFinset_apply]
  rfl

theorem transitionLaw_eq_dirac_of_empty (s : State) (t : ℕ) (sign : Bool)
    (h : s.active = ∅) : transitionLaw s t sign = Measure.dirac s := by
  simp [transitionLaw, h]

/-- An invariant is preserved almost surely when every admissible choice preserves it. -/
theorem transitionLaw_ae (s : State) (t : ℕ) (sign : Bool) (P : State → Prop)
    (hempty : s.active = ∅ → P s)
    (hstep : ∀ v ∈ s.active, P (step s t sign v)) :
    ∀ᵐ s' ∂transitionLaw s t sign, P s' := by
  classical
  apply (ae_iff_prob_eq_one measurable_from_top).mpr
  by_cases h : s.active.Nonempty
  · rw [transitionLaw_apply s t sign h]
    have hf : s.active.filter (fun v => step s t sign v ∈ {s' | P s'}) = s.active := by
      exact Finset.filter_eq_self.mpr hstep
    rw [hf]
    exact ENNReal.div_self (by exact_mod_cast h.card_pos.ne') (by simp)
  · have he : s.active = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    rw [transitionLaw_eq_dirac_of_empty s t sign he]
    simp [hempty he]

/-- The law of the forward random tree at time `n`. -/
noncomputable def treeLaw (x : SignSequence) : ℕ → Measure State
  | 0 => Measure.dirac initial
  | n + 1 => (treeLaw x n).bind (fun s => transitionLaw s (n + 1) (x (n + 1)))

instance treeLaw_probability (x : SignSequence) (n : ℕ) : IsProbabilityMeasure (treeLaw x n) := by
  induction n with
  | zero => change IsProbabilityMeasure (Measure.dirac initial); infer_instance
  | succ n ih =>
    exact isProbabilityMeasure_bind measurable_from_top.aemeasurable
      (Filter.Eventually.of_forall (fun s => transitionLaw_probability s _ _))

/-- Induction on the actual random construction, including absorption. -/
theorem treeLaw_ae_induction (x : SignSequence) (P : ℕ → State → Prop)
    (hinit : P 0 initial)
    (habsorb : ∀ n s, P n s → s.active = ∅ → P (n + 1) s)
    (hstep : ∀ n s, P n s → ∀ v ∈ s.active, P (n + 1) (step s (n + 1) (x (n + 1)) v))
    (n : ℕ) : ∀ᵐ s ∂treeLaw x n, P n s := by
  induction n with
  | zero => simp [treeLaw, hinit]
  | succ n ih =>
    apply (ae_iff_prob_eq_one measurable_from_top).mpr
    rw [treeLaw, Measure.bind_apply (by trivial) measurable_from_top.aemeasurable]
    calc
      _ = ∫⁻ _s, (1 : ℝ≥0∞) ∂treeLaw x n := by
        apply lintegral_congr_ae
        filter_upwards [ih] with s hs
        exact (ae_iff_prob_eq_one measurable_from_top).mp
          (transitionLaw_ae s _ _ (P (n + 1)) (habsorb n s hs) (hstep n s hs))
      _ = 1 := by simp

/-- Every state sampled from the forward law is a rooted finite tree with its verified heights. -/
theorem treeLaw_valid (x : SignSequence) (n : ℕ) :
    ∀ᵐ s ∂treeLaw x n, ValidAt n s := by
  apply treeLaw_ae_induction x ValidAt initial_valid
  · intro n s hs _; exact hs.mono (Nat.le_succ n)
  · intro n s hs v _; exact hs.step _ _

theorem treeLaw_isTree (x : SignSequence) (n : ℕ) :
    ∀ᵐ s ∂treeLaw x n, s.tree.IsTree :=
  (treeLaw_valid x n).mono (fun _ hs => hs.isTree)

/-- Active and total vertex counts for the genuine random forward tree. -/
theorem treeLaw_counts (x : SignSequence) (n : ℕ) (hτ : (n : ℕ∞) ≤ extinctionTime x) :
    ∀ᵐ s ∂treeLaw x n, (s.active.card : ℤ) = activeCount x n ∧
      s.vertices.card = plusCount x n + 1 := by
  have h := treeLaw_ae_induction x
    (fun n s => ValidAt n s ∧ ((n : ℕ∞) ≤ extinctionTime x →
      (s.active.card : ℤ) = activeCount x n ∧ s.vertices.card = plusCount x n + 1))
    (by exact ⟨initial_valid, by simp [initial]⟩)
    (by
      intro k s hs he
      refine ⟨hs.1.mono (Nat.le_succ k), ?_⟩
      intro hkτ
      have hk : (k : ℕ∞) < extinctionTime x :=
        lt_of_lt_of_le (by exact_mod_cast Nat.lt_succ_self k) hkτ
      have hcount := (hs.2 hk.le).1
      have hpos := ((lt_extinctionTime_iff x k).mp hk) k le_rfl
      simp only [he, Finset.card_empty, Nat.cast_zero] at hcount
      omega)
    (by
      intro k s hs v hv
      refine ⟨hs.1.step _ _, ?_⟩
      intro hkτ
      have hk : (k : ℕ∞) < extinctionTime x :=
        lt_of_lt_of_le (by exact_mod_cast Nat.lt_succ_self k) hkτ
      obtain ⟨ha, hverts⟩ := hs.2 hk.le
      have hfresh : k + 1 ∉ s.vertices := by
        intro hm; have := hs.1.vertices_le _ hm; omega
      have hafresh : k + 1 ∉ s.active := fun hm => hfresh (hs.1.active_subset hm)
      have hcard : 0 < s.active.card := Finset.card_pos.mpr ⟨v, hv⟩
      rw [Forward.step, ite_eq_left hv, activeCount_succ, plusCount_succ]
      cases hx : x (k + 1)
      · simp only [Bool.false_eq_true, ↓reduceIte, Forward.freeze]
        rw [Finset.card_erase_of_mem hv]
        constructor
        · rw [Nat.cast_sub (by omega), Nat.cast_one, ha]; omega
        · simpa using hverts
      · simp only [↓reduceIte, Forward.attach]
        rw [Finset.card_insert_of_notMem hafresh, Finset.card_insert_of_notMem hfresh]
        constructor
        · simp [ha]
        · omega)
    n
  exact h.mono (fun s hs => hs.2 hτ)

theorem treeLaw_vertices_card_real (x : SignSequence) (n : ℕ)
    (hτ : (n : ℕ∞) ≤ extinctionTime x) :
    ∀ᵐ s ∂treeLaw x n, (s.vertices.card : ℝ) = ((n : ℝ) + 1 + activeCount x n) / 2 := by
  filter_upwards [treeLaw_counts x n hτ] with s hs
  rw [hs.2, activeCount_eq]
  push_cast
  ring

theorem treeLaw_active_nonempty (x : SignSequence) (n : ℕ)
    (hτ : (n : ℕ∞) < extinctionTime x) :
    ∀ᵐ s ∂treeLaw x n, s.active.Nonempty := by
  filter_upwards [treeLaw_counts x n hτ.le] with s hs
  apply Finset.card_pos.mp
  have hp := ((lt_extinctionTime_iff x n).mp hτ) n le_rfl
  have := hs.1
  omega

end Freezing1.Forward
