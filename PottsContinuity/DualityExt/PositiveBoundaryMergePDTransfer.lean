module

public import PottsContinuity.DualityExt.PositiveBoundaryMergeDualTransfer
public import PottsContinuity.DualityExt.PositivePDLawBridge
public import PottsContinuity.DualityExt.PositiveSubgraphCrossingTransfer
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# PD-measure consumer for the two-block dual transfer

This module exposes the positive-probability two-block transfer in the
`PD.FK.measure` API used by the source graph. The dual partition, law map, and
event identity remain explicit premises; no annulus geometry is inferred.
-/

@[expose] public section

namespace PottsContinuity.DualityExt

open PottsContinuity.PD.FK
open PottsContinuity.PD.Duality

noncomputable section

/-- At the explicit self-dual parameter, a dual event contained in the exact
dual image of the source disconnection event transfers to that event's
pullback under joint wiring. The conclusion keeps the smaller dual event
itself instead of replacing it by the whole disconnection event. -/
theorem positive_twoBlock_dual_transfer_measure_ge_div_at_selfDualParameter_of_law_and_subEvent
    {V W : Type*} [Finite V] [Finite W]
    {G : SimpleGraph V} {H : SimpleGraph W}
    (q : Set.Ici (1 : ℝ)) (c : ℝ)
    (I O : Set V) (hIO : Disjoint I O) {u v : V}
    (hu : u ∈ I) (hv : v ∈ O)
    (η : BoundaryCondition W)
    (d : Configuration G ≃ Configuration H)
    (S T : Set (Configuration H))
    (hlaw :
      (law G (criticalParameters q) (positiveTwoBlockBoundary I O hIO)).map d =
        law H (criticalParameters q) η)
    (hevent : positiveBoundaryDisconnectedEvent (G := G)
        (positiveTwoBlockBoundary I O hIO) u v = d ⁻¹' S)
    (hTsubset : T ⊆ S)
    (hdual : c ≤
      (measure H (criticalParameters q) η T).toReal) :
    c / (q : ℝ) ≤
      (measure G (criticalParameters q) (BoundaryCondition.wired (I ∪ O))
        (d ⁻¹' T)).toReal := by
  have hq : (1 : ℝ) ≤ (q : ℝ) := q.property
  have hqpos : 0 < (q : ℝ) := lt_of_lt_of_le zero_lt_one hq
  have hp : 0 < squareRootDualityParameter (q : ℝ) :=
    (squareRootDualityParameter_mem_Ioo hqpos).1
  have hp1 : squareRootDualityParameter (q : ℝ) < 1 :=
    (squareRootDualityParameter_mem_Ioo hqpos).2
  let ξ := positiveTwoBlockBoundary I O hIO
  let Ssrc := d ⁻¹' T
  let E := positiveBoundaryDisconnectedEvent (G := G) ξ u v
  have hlawPos :
      (positiveFKLaw G (q : ℝ) (squareRootDualityParameter (q : ℝ))
          hqpos hp hp1 ξ).map d =
        positiveFKLaw H (q : ℝ) (squareRootDualityParameter (q : ℝ))
          hqpos hp hp1 η := by
    have hlaw' := hlaw
    rw [← positiveFKLaw_eq_PD_law (θ := criticalParameters q) (ξ := ξ)] at hlaw'
    rw [← positiveFKLaw_eq_PD_law (G := H) (θ := criticalParameters q)
      (ξ := η)] at hlaw'
    simpa only [criticalParameters, edgeParameter, PD.rcCriticalParameter,
      squareRootDualityParameter] using hlaw'
  have hdualPos : c ≤ positiveFKEventProbability
      (q := (q : ℝ)) (p := squareRootDualityParameter (q : ℝ)) η T := by
    have hbridge := positiveFKEventProbability_eq_measure_toReal
      (θ := criticalParameters q) (ξ := η) (S := T)
    have hbridge' : positiveFKEventProbability
        (q := (q : ℝ)) (p := squareRootDualityParameter (q : ℝ)) η T =
          (measure H (criticalParameters q) η T).toReal := by
      simpa only [criticalParameters, edgeParameter, PD.rcCriticalParameter,
        squareRootDualityParameter] using hbridge
    rw [hbridge']
    exact hdual
  have hprob := positiveFKEventProbability_eq_of_law_map_equiv
    hqpos hp hp1 ξ η d T hlawPos
  have hsourcePos : c ≤ positiveFKEventProbability
      (q := (q : ℝ)) (p := squareRootDualityParameter (q : ℝ)) ξ Ssrc := by
    calc
      c ≤ positiveFKEventProbability
          (q := (q : ℝ)) (p := squareRootDualityParameter (q : ℝ)) η T := hdualPos
      _ = positiveFKEventProbability
          (q := (q : ℝ)) (p := squareRootDualityParameter (q : ℝ)) ξ Ssrc := hprob.symm
  have hsubset : Ssrc ⊆ E := by
    have hevent' : E = d ⁻¹' S := by simpa [E, ξ] using hevent
    intro A hA
    rw [hevent']
    exact hTsubset hA
  have hmerge := positiveFKEventProbability_boundaryMerge_subset_disconnected_ge_div
    (G := G) hq hp hp1 ξ u v Ssrc hsubset
  have hmergeBound : c / (q : ℝ) ≤ positiveFKEventProbability
      (q := (q : ℝ)) (p := squareRootDualityParameter (q : ℝ))
      (positiveBoundaryMerge ξ u v) Ssrc := by
    exact le_trans (div_le_div_of_nonneg_right hsourcePos hqpos.le) hmerge
  have hpartition := positiveTwoBlockBoundary_merge_partition I O hIO hu hv
  have hrename := positiveFKEventProbability_eq_of_partition_eq
    (G := G) hqpos hp hp1 (positiveBoundaryMerge ξ u v)
    (BoundaryCondition.wired (I ∪ O)) hpartition Ssrc
  have hjointPos : c / (q : ℝ) ≤ positiveFKEventProbability
      (q := (q : ℝ)) (p := squareRootDualityParameter (q : ℝ))
      (BoundaryCondition.wired (I ∪ O)) Ssrc := by
    rw [← hrename]
    exact hmergeBound
  have hbridge := positiveFKEventProbability_eq_measure_toReal
    (θ := criticalParameters q) (ξ := BoundaryCondition.wired (I ∪ O))
    (S := Ssrc)
  have hbridge' : positiveFKEventProbability
      (q := (q : ℝ)) (p := squareRootDualityParameter (q : ℝ))
      (BoundaryCondition.wired (I ∪ O)) Ssrc =
        (measure G (criticalParameters q) (BoundaryCondition.wired (I ∪ O))
          Ssrc).toReal := by
    simpa only [criticalParameters, edgeParameter, PD.rcCriticalParameter,
      squareRootDualityParameter] using hbridge
  simpa only [Ssrc] using hbridge'.symm ▸ hjointPos

end
end PottsContinuity.DualityExt
