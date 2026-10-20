module

public import PottsContinuity.Thm3.Prop4.MarkedBoxFrontierTrace
public import PottsContinuity.Thm3.Push.IsoStoppingReveal

/-! # The actual raw lower-arc stopping record on the original box -/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4
open PD.FK PD.RCInfinite
noncomputable section
local instance markedBoxRawSourceEdgeEq (n : ℕ) :
    DecidableEq (finiteLatticeGraph (box n)).edgeSet := Classical.decEq _
local instance markedBoxRawTargetEdgeEq (n : ℕ) :
    DecidableEq (rectangleGraph (-(n : ℤ),-(n : ℤ)) (2*n) (2*n)).edgeSet := Classical.decEq _

/-- Pull back the actual lower-arc raw queried bonds to the original box. -/
def markedLowerBoxRawReveal (n : ℕ) (u v : (box n : Set LatticeVertex))
    (A : Configuration (finiteLatticeGraph (box n))) :
    Configuration (finiteLatticeGraph (box n)) :=
  (configurationIso (boxTubeRectangleIso n)).symm
    (markedLowerDualReveal (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) u.val v.val
      (configurationIso (boxTubeRectangleIso n) A))

/-- Agreement on the actual box query set gives agreement on the original
sampled rectangle raw record. -/
theorem markedLowerBoxRawReveal_agreement (n : ℕ) (u v : (box n : Set LatticeVertex))
    (A C : Configuration (finiteLatticeGraph (box n)))
    (hagree : C ∩ markedLowerBoxRawReveal n u v A = A ∩ markedLowerBoxRawReveal n u v A) :
    configurationIso (boxTubeRectangleIso n) C ∩
      markedLowerDualReveal (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) u.val v.val
        (configurationIso (boxTubeRectangleIso n) A) =
    configurationIso (boxTubeRectangleIso n) A ∩
      markedLowerDualReveal (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) u.val v.val
        (configurationIso (boxTubeRectangleIso n) A) := by
  have hh := congrArg (configurationIso (boxTubeRectangleIso n)) hagree
  erw [Push.configurationIso_inter,Push.configurationIso_inter] at hh
  simpa only [markedLowerBoxRawReveal,Equiv.apply_symm_apply] using hh

/-- The concrete original-box lower raw reveal is a stopping set. -/
theorem markedLowerBoxRawReveal_stable (n : ℕ) (u v : (box n : Set LatticeVertex))
    (A C : Configuration (finiteLatticeGraph (box n)))
    (hagree : C ∩ markedLowerBoxRawReveal n u v A = A ∩ markedLowerBoxRawReveal n u v A) :
    markedLowerBoxRawReveal n u v C = markedLowerBoxRawReveal n u v A := by
  exact congrArg (configurationIso (boxTubeRectangleIso n)).symm
    (markedLowerDualReveal_stable _ _ _ _ _ _ _
      (markedLowerBoxRawReveal_agreement n u v A C hagree))

/-- The WHOLE concrete connecting trace is observed on the same box raw record. -/
theorem markedLowerBoxTrace_observed (n : ℕ) (u v : (box n : Set LatticeVertex))
    (A C : Configuration (finiteLatticeGraph (box n)))
    (hobs : RSW.stoppingObservationMap (markedLowerBoxRawReveal n u v) A =
      RSW.stoppingObservationMap (markedLowerBoxRawReveal n u v) C) :
    markedLowerBoxTrace n u v A = markedLowerBoxTrace n u v C := by
  have hR := congrArg (configurationIso (boxTubeRectangleIso n))
    (congrArg Prod.fst (congrArg Subtype.val hobs))
  have hB := congrArg (configurationIso (boxTubeRectangleIso n))
    (congrArg Prod.snd (congrArg Subtype.val hobs))
  change configurationIso (boxTubeRectangleIso n) (markedLowerBoxRawReveal n u v A) =
    configurationIso (boxTubeRectangleIso n) (markedLowerBoxRawReveal n u v C) at hR
  simp only [markedLowerBoxRawReveal,Equiv.apply_symm_apply] at hR
  dsimp only [RSW.stoppingObservationMap,RSW.stoppingObservation] at hB
  erw [Push.configurationIso_inter,Push.configurationIso_inter] at hB
  simp only [markedLowerBoxRawReveal,Equiv.apply_symm_apply] at hB
  unfold markedLowerBoxTrace
  erw [hB,hR]

end
end PottsContinuity.Thm3.Prop4
