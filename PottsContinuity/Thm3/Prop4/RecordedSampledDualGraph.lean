module

public import PottsContinuity.Thm3.Prop4.SampledArmCorrelation
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Walk.Maps

/-!
# Actual sampled dual bonds fixed closed by a source record

Every edge crosses an original sampled bond in the reveal but outside its
recorded open state. No exterior completion bond is added to this graph.
-/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4
open PD.FK PD.FK.Medial
noncomputable section

/-- The literal sampled dual graph of recorded closed original bonds. -/
def recordedSampledClosedDualGraph (a : LatticeVertex) (w h : ℕ)
    (R B : Configuration (rectangleGraph a w h)) : SimpleGraph LatticeVertex where
  Adj s t := ∃ e : RectangleDualEdgeCarrier a w h, e.primalEdge ∈ R ∧ e.primalEdge ∉ B ∧
    ((s = e.crossingBond.source ∧ t = e.crossingBond.target) ∨
      (s = e.crossingBond.target ∧ t = e.crossingBond.source))
  symm := ⟨by
    rintro s t ⟨e,he,hB,⟨hs,ht⟩ | ⟨hs,ht⟩⟩
    · exact ⟨e,he,hB,Or.inr ⟨ht,hs⟩⟩
    · exact ⟨e,he,hB,Or.inl ⟨ht,hs⟩⟩⟩
  loopless := ⟨by
    rintro s ⟨e,_,_,⟨hs,ht⟩ | ⟨hs,ht⟩⟩
    · exact e.crossingBond.source_ne_target (hs.symm.trans ht)
    · exact e.crossingBond.source_ne_target (ht.symm.trans hs)⟩

/-- Every sample agreeing with the complete record retains all its recorded
closed sampled dual bonds. -/
theorem recordedSampledClosedDualGraph_le_state (a : LatticeVertex) (w h : ℕ)
    (R B C : Configuration (rectangleGraph a w h)) (hC : C ∩ R = B) :
    recordedSampledClosedDualGraph a w h R B ≤ PlanarTopology.rectangleSampledClosedDualGraph a w h C := by
  classical
  rintro s t ⟨e,he,hB,hst⟩
  refine ⟨e,?_,hst⟩
  intro hmem
  apply hB
  rw [← hC]
  exact Finset.mem_inter.mpr ⟨hmem,he⟩

/-- A recorded sampled dual witness is an actual arm in every compatible
source sample, with precisely the same endpoints and support. -/
theorem sampled_dual_arm_of_recorded_walk (a : LatticeVertex) (w h : ℕ)
    (R B C : Configuration (rectangleGraph a w h)) (hC : C ∩ R = B)
    (F L : Set LatticeVertex) (P : LatticeVertex → Prop)
    {f s : LatticeVertex} (hf : f ∈ F) (hs : s ∈ L)
    (p : (recordedSampledClosedDualGraph a w h R B).Walk s f)
    (hp : ∀ z ∈ p.support, P z) : C ∈ sampledRectangleDualArmEvent a w h F L P := by
  refine ⟨f,hf,s,hs,p.mapLe (recordedSampledClosedDualGraph_le_state a w h R B C hC),?_⟩
  simpa only [SimpleGraph.Walk.support_mapLe_eq_support] using hp

end
end PottsContinuity.Thm3.Prop4
