module

public import PottsContinuity.BD12.RadiusOneArmComparison
public import PottsContinuity.BD12.PositiveMean

/-! One-arm comparisons for arbitrary positive finite laws, in particular
true marginals of larger-domain random-cluster laws. -/

@[expose] public section

namespace PottsContinuity.BD12
open FKC.FiniteFK
open scoped Classical
noncomputable section
variable {V : Type*} [Fintype V] (G : SimpleGraph V)
local instance positiveOneArmEdgeFintype : Fintype G.edgeSet := Fintype.ofFinite _
local instance positiveOneArmEdgeDecidableEq : DecidableEq G.edgeSet := Classical.decEq _

/-- Positive-weight one-arm probabilities decrease with the radius. -/
theorem positive_radius_one_arm_antitone (w : Configuration G → Set.Ioi (0 : ℝ))
    (r : V → ℕ) (o : V) (ho : r o = 0) (hstep : ∀ {x y}, G.Adj x y → r y ≤ r x + 1) :
    Antitone (fun n => finitePositiveMean w (radiusOneArmIndicator G r o n)) := by
  intro m n hmn
  exact finitePositiveMean_mono w _ _ (fun A => radiusOneArmIndicator_antitone G r o ho hstep A hmn)

/-- Positive-weight shell probabilities are bounded by the corresponding centred
one-arm probabilities at the radius difference. -/
theorem positive_seed_shell_connection_le_one_arm
    (w : Configuration G → Set.Ioi (0 : ℝ))
    (r d : V → ℕ) (u : V) (k : ℕ) (hdu : d u = 0)
    (hstep : ∀ {x y}, G.Adj x y → d y ≤ d x + 1) (hdom : ∀ v, Nat.dist (r v) (r u) ≤ d v) :
    finitePositiveMean w (fun A => if actualMultiClusterConnected G (finiteRadiusShell r k) A u then 1 else 0) ≤
      finitePositiveMean w (radiusOneArmIndicator G d u (Nat.dist k (r u))) :=
  finitePositiveMean_mono w _ _ (fun A => seedShell_indicator_le_radiusOneArm G r d u k hdu hstep hdom A)

end
end PottsContinuity.BD12
