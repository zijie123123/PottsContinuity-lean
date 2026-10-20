module

public import PottsContinuity.BD12.FiniteRevealKernel

/-! Adaptive finite reveal trees and their exact output law. Each node chooses
a fresh coordinate, and its two continuation trees may choose different orders. -/

@[expose] public section

namespace PottsContinuity.BD12

/-- A complete finite decision tree. The index records the already revealed
coordinates, so freshness is enforced at every node and leaves reveal all E. -/
inductive FiniteRevealTree (E : Type*) [Fintype E] [DecidableEq E] : Finset E → Type _
  | done : FiniteRevealTree E Finset.univ
  | query {R : Finset E} (e : E) (he : e ∉ R)
      (next : Bool → FiniteRevealTree E (insert e R)) : FiniteRevealTree E R

noncomputable section
variable {E : Type*} [Fintype E] [DecidableEq E]

end
end PottsContinuity.BD12
