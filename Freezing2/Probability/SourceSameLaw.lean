module

public import Freezing2.Probability.ForwardReverseLaw
public import Freezing2.Probability.ReversePaper

/-!
# Forward/reverse equality for the source's integer sign schedule

The finite no-zero-before-horizon condition is exactly `n ≤ τ`; zero at the
horizon is permitted. The Boolean companion schedule is the already checked
encoding of the manuscript's `±1` increments.
-/

@[expose] public section

namespace Freezing2

/-- N01 in the manuscript's original integer sign convention, retaining
both zero time and a terminal freezing step at extinction. -/
theorem source_forward_reverse_same_law (x : ℕ → ℤ) (hx : IsSigned x) (n : ℕ)
    (hzero : ∀ k < n, activeCount x k ≠ 0) :
    (Freezing1.ReverseStamped.treeLaw (companionSchedule x) n).map
        (ReverseStamped.canonicalForwardState (companionSchedule x) n) =
      Freezing1.Forward.treeLaw (companionSchedule x) n :=
  ReverseStamped.forward_reverse_same_law (companionSchedule x) n
    ((companion_le_extinctionTime_iff_no_zero_before x hx n).mpr hzero)

end Freezing2
