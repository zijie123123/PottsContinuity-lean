module

public import PottsContinuity.Thm3.Push.StripSourceCylinder

@[expose] public section

namespace PottsContinuity.Push
open PD.FK MeasureTheory
noncomputable section
attribute [local instance] configurationMeasurableSpace
local instance stripSourceWindowStatesEdgeEq {V : Type*} (G : SimpleGraph V) :
    DecidableEq G.edgeSet := Classical.decEq _

/-- Restriction of the literal closed window extension is EXACTLY the sampled
source restriction. Every original open and closed source bond is retained. -/
theorem stripSourceSquareRestriction_window_eq (n m : ℕ) (x : ℤ)
    (hlo : -(m:ℤ) ≤ x) (hhi : x+2*(n:ℤ) ≤ (m:ℤ))
    (C : Configuration (PottsContinuity.squareLattice.induce
      (RSW.stripWindow n m : Set LatticeVertex))) :
    stripSourceSquareRestriction n x (RSW.stripPlaneRestriction n
      (RSW.stripWindowPlaneConfiguration n m C)) =
      embeddedConfigurationRestriction _ _ (intervalArmStripWindowEmbedding n m x hlo hhi)
        (intervalArmStripWindow_map_le n m x hlo hhi) C := by
  classical
  ext e
  rw [mem_stripSourceSquareRestriction,mem_embeddedConfigurationRestriction]
  let ew := embeddedEdgeEmbedding _ _ (intervalArmStripWindowEmbedding n m x hlo hhi)
    (intervalArmStripWindow_map_le n m x hlo hhi) e
  have hplane : (RSW.stripPlaneEmbedding n).mapEdgeSet
      ((intervalArmStripGraphEmbedding n x).mapEdgeSet e) =
      (RSW.stripWindowPlaneEmbedding n m).mapEdgeSet ew := by
    apply Subtype.ext
    change Sym2.map Subtype.val (Sym2.map (intervalArmStripVertex n x) e.val) =
      Sym2.map Subtype.val (Sym2.map (intervalArmStripWindowEmbedding n m x hlo hhi) e.val)
    rw [Sym2.map_map,Sym2.map_map]
    rfl
  simp only [RSW.stripPlaneRestriction,RSW.stripWindowPlaneConfiguration,decide_eq_true_eq]
  rw [hplane]
  exact Finset.mem_map' _

/-- Any actual source event has the identical finite-window probability when
read as its strip cylinder or as its embedded finite source restriction. -/
theorem stripSourceSquareEvent_window_probability_eq
    (θ : Parameters) (n m : ℕ) (x : ℤ)
    (hlo : -(m:ℤ) ≤ x) (hhi : x+2*(n:ℤ) ≤ (m:ℤ))
    (E : Set (Configuration (rectangleGraph (0,0) (2*n) (2*n)))) :
    RSW.stripWindowEventProbability θ n m (stripSourceSquareEvent n x E) =
      (measure (PottsContinuity.squareLattice.induce (RSW.stripWindow n m : Set LatticeVertex))
        θ (RSW.stripWindowBoundary n m 0)
        {C | embeddedConfigurationRestriction _ _ (intervalArmStripWindowEmbedding n m x hlo hhi)
          (intervalArmStripWindow_map_le n m x hlo hhi) C ∈ E}).toReal := by
  have hevent : {C | RSW.stripPlaneRestriction n (RSW.stripWindowPlaneConfiguration n m C) ∈
      stripSourceSquareEvent n x E} =
      {C | embeddedConfigurationRestriction _ _ (intervalArmStripWindowEmbedding n m x hlo hhi)
        (intervalArmStripWindow_map_le n m x hlo hhi) C ∈ E} := by
    ext C
    change stripSourceSquareRestriction n x _ ∈ E ↔ _
    rw [stripSourceSquareRestriction_window_eq n m x hlo hhi C]
    rfl
  unfold RSW.stripWindowEventProbability
  rw [hevent]

end
end PottsContinuity.Push
