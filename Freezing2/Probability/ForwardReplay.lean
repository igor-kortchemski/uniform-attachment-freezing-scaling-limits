module

public import Freezing2.Probability.ForwardHistoryUnique

/-!
# Replaying a schedule from its parent and freezing records

A prescribed attachment parent must already be born and not yet frozen. A
prescribed freezing vertex must already be born, and distinct freezing times
must name distinct vertices. These concrete record conditions suffice to
reconstruct a legal forward history; no equality-in-law assumption is used.
-/

@[expose] public section

namespace Freezing2.ForwardReplay

abbrev History := Freezing2.ForwardHistory.History

/-- Birth identifiers present by the indicated time, including the initial root. -/
def Born (x : Freezing1.SignSequence) (k v : ℕ) : Prop :=
  v = 0 ∨ (1 ≤ v ∧ v ≤ k ∧ x v = true)

/-- The vertex has not occurred among the prescribed freezing records yet. -/
def NotFrozen (x : Freezing1.SignSequence) (frozenVertex : ℕ → ℕ) (k v : ℕ) : Prop :=
  ∀ s, 1 ≤ s → s ≤ k → x s = false → frozenVertex s ≠ v

def choice (x : Freezing1.SignSequence) (parent frozenVertex : ℕ → ℕ) (t : ℕ) : ℕ :=
  if x t then parent t else frozenVertex t

def history (x : Freezing1.SignSequence) (parent frozenVertex : ℕ → ℕ) : ℕ → History
  | 0 => []
  | k + 1 => choice x parent frozenVertex (k + 1) :: history x parent frozenVertex k

@[simp] theorem history_length (x : Freezing1.SignSequence) (parent frozenVertex : ℕ → ℕ)
    (k : ℕ) : (history x parent frozenVertex k).length = k := by
  induction k <;> simp [history, *]

theorem Born.le {x : Freezing1.SignSequence} {k v : ℕ} (hv : Born x k v) : v ≤ k := by
  rcases hv with rfl | ⟨_, hv, _⟩
  · omega
  · exact hv

theorem born_succ (x : Freezing1.SignSequence) (k v : ℕ) :
    Born x (k + 1) v ↔ (v = k + 1 ∧ x (k + 1) = true) ∨ Born x k v := by
  unfold Born
  constructor
  · rintro (rfl | ⟨hv0, hv, hx⟩)
    · exact Or.inr (Or.inl rfl)
    · by_cases he : v = k + 1
      · exact Or.inl ⟨he, he ▸ hx⟩
      · exact Or.inr (Or.inr ⟨hv0, by omega, hx⟩)
  · rintro (⟨rfl, hx⟩ | h)
    · exact Or.inr ⟨by omega, le_rfl, hx⟩
    · rcases h with rfl | ⟨hv0, hv, hx⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨hv0, by omega, hx⟩

theorem notFrozen_succ (x : Freezing1.SignSequence) (fv : ℕ → ℕ) (k v : ℕ) :
    NotFrozen x fv (k + 1) v ↔
      (x (k + 1) = false → fv (k + 1) ≠ v) ∧ NotFrozen x fv k v := by
  constructor
  · intro h
    exact ⟨h _ (by omega) le_rfl, fun s hs hsk hx ↦ h s hs (by omega) hx⟩
  · rintro ⟨hlast, hprev⟩ s hs hsk hx
    by_cases he : s = k + 1
    · subst s
      exact hlast hx
    · exact hprev s hs (by omega) hx

/-- Legal replay and the precise active-vertex set are proved together.
All premises refer to the proposed finite records, not to a stochastic model. -/
theorem legal_and_active (x : Freezing1.SignSequence) (n : ℕ) (parent fv : ℕ → ℕ)
    (hparent : ∀ t, 1 ≤ t → t ≤ n → x t = true → Born x (t - 1) (parent t))
    (hfrozen : ∀ t, 1 ≤ t → t ≤ n → x t = false → Born x (t - 1) (fv t))
    (hparent_free : ∀ t, 1 ≤ t → t ≤ n → x t = true →
      ∀ s, 1 ≤ s → s < t → x s = false → fv s ≠ parent t)
    (hfrozen_inj : Set.InjOn fv {s | 1 ≤ s ∧ s ≤ n ∧ x s = false})
    (k : ℕ) (hk : k ≤ n) :
    Freezing2.ForwardHistory.Legal x (history x parent fv k) ∧
      ∀ v, v ∈ (Freezing2.ForwardHistory.state x (history x parent fv k)).active ↔
        Born x k v ∧ NotFrozen x fv k v := by
  induction k with
  | zero =>
    refine ⟨trivial, ?_⟩
    intro v
    have hnf : NotFrozen x fv 0 v := by intro s hs hsk; omega
    simp [history, Freezing2.ForwardHistory.state, Freezing1.Forward.initial, Born, hnf]
    omega
  | succ k ih =>
    obtain ⟨hlegal, hactive⟩ := ih (by omega)
    have hborn : Born x k (choice x parent fv (k + 1)) := by
      cases hx : x (k + 1) with
      | true => simpa [choice, hx] using hparent (k + 1) (by omega) hk hx
      | false => simpa [choice, hx] using hfrozen (k + 1) (by omega) hk hx
    have hfree : NotFrozen x fv k (choice x parent fv (k + 1)) := by
      intro s hs hsk hxs
      cases hx : x (k + 1) with
      | true => simpa [choice, hx] using
          hparent_free (k + 1) (by omega) hk hx s hs (by omega) hxs
      | false =>
        simp only [choice, hx, Bool.false_eq_true, ite_false]
        intro he
        have := hfrozen_inj ⟨hs, by omega, hxs⟩ ⟨by omega, hk, hx⟩ he
        omega
    have hchosen := (hactive _).mpr ⟨hborn, hfree⟩
    refine ⟨⟨hlegal, hchosen⟩, ?_⟩
    intro v
    cases hx : x (k + 1) with
    | false =>
      have hchosen' : fv (k + 1) ∈
          (Freezing2.ForwardHistory.state x (history x parent fv k)).active := by
        simpa [choice, hx] using hchosen
      simp only [history, Freezing2.ForwardHistory.state, history_length,
        Freezing1.Forward.step, ite_eq_left hchosen', hx, Bool.false_eq_true,
        ite_false, Freezing1.Forward.freeze, Finset.mem_erase, hactive,
        choice, born_succ, notFrozen_succ]
      simp only [and_false, false_or, true_implies]
      tauto
    | true =>
      have hnfnew : NotFrozen x fv k (k + 1) := by
        intro s hs hsk hxs he
        have hb := (hfrozen s hs (by omega) hxs).le
        omega
      simp only [history, Freezing2.ForwardHistory.state, history_length,
        Freezing1.Forward.step, ite_eq_left hchosen, hx, ite_true,
        Freezing1.Forward.attach, Finset.mem_insert, hactive, born_succ, notFrozen_succ]
      simp only [Bool.true_eq_false, false_implies, true_and, and_true]
      constructor
      · rintro (rfl | ⟨hb, hf⟩)
        · exact ⟨Or.inl rfl, hnfnew⟩
        · exact ⟨Or.inr hb, hf⟩
      · rintro ⟨hv | hb, hf⟩
        · exact Or.inl hv
        · exact Or.inr ⟨hb, hf⟩

/-- Reading a replayed history returns its prescribed record at every
performed time. -/
theorem choiceAt_history (x : Freezing1.SignSequence) (parent fv : ℕ → ℕ)
    (k : ℕ) {t : ℕ} (ht0 : 1 ≤ t) (ht : t ≤ k) :
    Freezing2.ForwardHistory.choiceAt (history x parent fv k) t =
      choice x parent fv t := by
  induction k with
  | zero => omega
  | succ k ih =>
    by_cases he : t = k + 1
    · subst t
      simp [history, Freezing2.ForwardHistory.choiceAt]
    · simp only [history, Freezing2.ForwardHistory.choiceAt, history_length, ite_eq_right he]
      exact ih (by omega)

end Freezing2.ForwardReplay
