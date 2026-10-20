module

public import PottsContinuity.BD12.FiniteRevealKernel

/-! The actual stopping predicate for a finite decision tree: the revealed
coordinates determine the observable on their entire configuration fiber. -/

@[expose] public section

namespace PottsContinuity.BD12
variable {E : Type*} [Fintype E] [DecidableEq E]

/-- All completions of the revealed pattern give the same observable value. -/
def finiteDetermines (f : Finset E → ℝ) (R H : Finset E) : Prop :=
  ∀ A, A ∩ R = H ∩ R → f A = f H

end PottsContinuity.BD12
