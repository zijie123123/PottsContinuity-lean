module

public import PottsContinuity.Thm3.RSW.BottomCollarDualBoundary
public import PottsContinuity.Thm3.RSW.Lemma4SideRectangleLaw

@[expose] public section

namespace PottsContinuity.RSW
open PD.FK PD.Duality
noncomputable section

/-- Complement the genuine side sample through its explicit coordinate
rectangle and bottom collar, keeping the entire residual dual carrier. -/
def lemma4SideInducedDualEquiv (n : ℕ) (σ : ℤ) (hσ : σ = 1 ∨ σ = -1) :
    Configuration (lemma4SideFullGraph n σ) ≃
      Configuration (bottomCollarInducedDualGraph (-56*(n:ℤ),0) (112*n) (54*n)) :=
  (configurationIso (lemma4SideFullRectangleIso n σ hσ)).trans
    (bottomCollarInducedDualEquiv (-56*(n:ℤ),0) (112*n) (54*n))

/-- Both actual original side laws map to the same exact complementary dual
law with its explicit host exterior wiring. No partition or dual-law premise
remains, and all scales and all real q>=1 are included. -/
theorem lemma4SideFull_law_map_inducedDual (q : Set.Ici (1:ℝ)) (n : ℕ) (σ : ℤ)
    (hσ : σ = 1 ∨ σ = -1) :
    (law (lemma4SideFullGraph n σ) (selfDualParameters q)
      (BoundaryCondition.wired (lemma4SideBase n σ))).map
      (lemma4SideInducedDualEquiv n σ hσ) =
    law (bottomCollarInducedDualGraph (-56*(n:ℤ),0) (112*n) (54*n)) (selfDualParameters q)
      (rectangleDualBoundaryCondition (-56*(n:ℤ),-1) (112*n) (54*n+1)) := by
  change (law _ _ _).map
    ((bottomCollarInducedDualEquiv _ _ _) ∘
      (configurationIso (lemma4SideFullRectangleIso n σ hσ))) = _
  rw [← PMF.map_comp,lemma4SideFull_law_map_rectangle,bottomCollar_dual_law_at_selfDual]
  rfl

end
end PottsContinuity.RSW
