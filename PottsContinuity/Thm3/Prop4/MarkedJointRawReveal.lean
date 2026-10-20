module

public import PottsContinuity.Thm3.Prop4.MarkedBoxRawReveal
public import PottsContinuity.Thm3.Prop4.MarkedUpperBoxTrace
public import PottsContinuity.Thm3.Prop4.ObservedSourceCompletion

/-! # The common actual raw record for the two marked traces -/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4
open PD.FK PD.RCInfinite
noncomputable section
local instance markedJointRawEdgeEq (n : ℕ) :
    DecidableEq (finiteLatticeGraph (box n)).edgeSet := Classical.decEq _

/-- Return the rotated lower raw queries to the original sampled box. -/
def markedUpperBoxRawReveal (n : ℕ) (u v : (box n : Set LatticeVertex))
    (A : Configuration (finiteLatticeGraph (box n))) :
    Configuration (finiteLatticeGraph (box n)) :=
  (configurationIso (boxHalfTurnIso n)).symm
    (markedLowerBoxRawReveal n (boxHalfTurnIso n v) (boxHalfTurnIso n u)
      (configurationIso (boxHalfTurnIso n) A))

/-- The upper raw reveal has the original-state stopping property. -/
theorem markedUpperBoxRawReveal_stable (n : ℕ) (u v : (box n : Set LatticeVertex))
    (A C : Configuration (finiteLatticeGraph (box n)))
    (hagree : C ∩ markedUpperBoxRawReveal n u v A = A ∩ markedUpperBoxRawReveal n u v A) :
    markedUpperBoxRawReveal n u v C = markedUpperBoxRawReveal n u v A := by
  have hh := congrArg (configurationIso (boxHalfTurnIso n)) hagree
  erw [Push.configurationIso_inter,Push.configurationIso_inter] at hh
  dsimp only [markedUpperBoxRawReveal] at hh
  erw [Equiv.apply_symm_apply] at hh
  exact congrArg (configurationIso (boxHalfTurnIso n)).symm
    (markedLowerBoxRawReveal_stable n _ _ _ _ hh)

/-- The concrete upper trace is observed by its actual upper raw reveal. -/
theorem markedUpperBoxTrace_observed (n : ℕ) (u v : (box n : Set LatticeVertex))
    (A C : Configuration (finiteLatticeGraph (box n)))
    (hobs : RSW.stoppingObservationMap (markedUpperBoxRawReveal n u v) A =
      RSW.stoppingObservationMap (markedUpperBoxRawReveal n u v) C) :
    markedUpperBoxTrace n u v A = markedUpperBoxTrace n u v C := by
  have hR := congrArg (configurationIso (boxHalfTurnIso n))
    (congrArg Prod.fst (congrArg Subtype.val hobs))
  have hB := congrArg (configurationIso (boxHalfTurnIso n))
    (congrArg Prod.snd (congrArg Subtype.val hobs))
  dsimp only [RSW.stoppingObservationMap,RSW.stoppingObservation] at hR hB
  dsimp only [markedUpperBoxRawReveal] at hR
  erw [Equiv.apply_symm_apply,Equiv.apply_symm_apply] at hR
  erw [Push.configurationIso_inter,Push.configurationIso_inter] at hB
  dsimp only [markedUpperBoxRawReveal] at hB
  erw [Equiv.apply_symm_apply,Equiv.apply_symm_apply] at hB
  have ht := markedLowerBoxTrace_observed n (boxHalfTurnIso n v) (boxHalfTurnIso n u)
    (configurationIso (boxHalfTurnIso n) A) (configurationIso (boxHalfTurnIso n) C) (by
      apply Subtype.ext
      change (_,_) = (_,_) 
      exact Prod.ext hR hB)
  exact congrArg (Finset.map (boxHalfTurnIso n).symm.toEquiv.toEmbedding) ht

/-- Retain both actual raw explorations on the same original sample. -/
def markedJointBoxRawReveal (n : ℕ) (u v : (box n : Set LatticeVertex))
    (A : Configuration (finiteLatticeGraph (box n))) :
    Configuration (finiteLatticeGraph (box n)) :=
  markedLowerBoxRawReveal n u v A ∪ markedUpperBoxRawReveal n u v A

/-- The joint actual record is stable, including samples with empty traces. -/
theorem markedJointBoxRawReveal_stable (n : ℕ) (u v : (box n : Set LatticeVertex))
    (A C : Configuration (finiteLatticeGraph (box n)))
    (hagree : C ∩ markedJointBoxRawReveal n u v A = A ∩ markedJointBoxRawReveal n u v A) :
    markedJointBoxRawReveal n u v C = markedJointBoxRawReveal n u v A :=
  sourceRevealUnion_stable _ _ _ (markedLowerBoxRawReveal_stable n u v)
    (markedUpperBoxRawReveal_stable n u v) A C hagree

/-- BOTH concrete traces are observed by the same actual joint raw record. -/
theorem markedJointBoxRawReveal_observes_traces (n : ℕ) (u v : (box n : Set LatticeVertex))
    (A C : Configuration (finiteLatticeGraph (box n)))
    (hobs : RSW.stoppingObservationMap (markedJointBoxRawReveal n u v) A =
      RSW.stoppingObservationMap (markedJointBoxRawReveal n u v) C) :
    markedLowerBoxTrace n u v A = markedLowerBoxTrace n u v C ∧
      markedUpperBoxTrace n u v A = markedUpperBoxTrace n u v C := by
  exact sourceTraces_observed_of_retained_union _ _ _ _ _ _
    (markedLowerBoxRawReveal_stable n u v) (markedUpperBoxRawReveal_stable n u v)
    (fun _ => Finset.Subset.refl _) (markedLowerBoxTrace_observed n u v)
    (markedUpperBoxTrace_observed n u v) A C hobs

end
end PottsContinuity.Thm3.Prop4
