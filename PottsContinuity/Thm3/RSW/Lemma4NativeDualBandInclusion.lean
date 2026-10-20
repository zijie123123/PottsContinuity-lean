module

public import PottsContinuity.Thm3.RSW.Lemma4SideAffineWalk
public import PottsContinuity.Thm3.RSW.Lemma4NativeDualBandReplay
public import PottsContinuity.Thm3.RSW.Lemma4SideDualBandProbability

@[expose] public section

namespace PottsContinuity.RSW
open PD.FK PD.Duality
noncomputable section

/-- Every native sampled residual-dual band crossing replays in either exact
source side band. The complementary state and both coordinate transfers are
proved, with no event-inclusion or probability premise. -/
theorem lemma4_nativeDualBand_subset_sourceDualBand (n : ℕ) (i : Fin 2) :
    lemma4NativeDualBandEvent n ⊆ lemma4SideInducedDualBandEvent n i := by
  intro D hD
  have hA := lemma4_nativeDualBand_normalized_inverse_replay n D hD
  exact lemma4_normalizedBand_to_originalSide n i
    ((bottomCollarInducedDualEquiv (-56*(n:ℤ),0) (112*n) (54*n)).symm D) hA

end
end PottsContinuity.RSW
