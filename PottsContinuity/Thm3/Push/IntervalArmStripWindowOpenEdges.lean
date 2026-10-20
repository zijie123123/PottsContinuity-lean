module

public import PottsContinuity.Thm3.Push.IntervalArmStripWindowEmbedding

@[expose] public section

namespace PottsContinuity.Push
open PottsContinuity.PD.FK
noncomputable section

/-- Every actual sampled source bond is open on its literal translated strip
bond in the specified finite-window closed extension. -/
theorem intervalArmStripWindow_open_adj (n m : ℕ) (x : ℤ)
    (hlo : -(m : ℤ) ≤ x) (hhi : x+2*(n : ℤ) ≤ (m : ℤ))
    (C : Configuration (PottsContinuity.squareLattice.induce (RSW.stripWindow n m : Set LatticeVertex)))
    (u v : RectangleVertex (0,0) (2*n) (2*n))
    (huv : (openGraph (rectangleGraph (0,0) (2*n) (2*n))
      (embeddedConfigurationRestriction _ _ (intervalArmStripWindowEmbedding n m x hlo hhi)
        (intervalArmStripWindow_map_le n m x hlo hhi) C)).Adj u v) :
    (RSW.stripOpenGraph n (RSW.stripPlaneRestriction n (RSW.stripWindowPlaneConfiguration n m C))).Adj
      (intervalArmStripVertex n x u) (intervalArmStripVertex n x v) := by
  classical
  let f := intervalArmStripWindowEmbedding n m x hlo hhi
  let hGH := intervalArmStripWindow_map_le n m x hlo hhi
  obtain ⟨e,he,hpair⟩ := (openGraph_adj _ _ u v).mp huv
  let ew := embeddedEdgeEmbedding _ _ f hGH e
  have hew : ew ∈ C := (mem_embeddedConfigurationRestriction _ _ f hGH C e).mp he
  let es := (intervalArmStripGraphEmbedding n x).mapEdgeSet e
  have hplane : (RSW.stripPlaneEmbedding n).mapEdgeSet es =
      (RSW.stripWindowPlaneEmbedding n m).mapEdgeSet ew := by
    apply Subtype.ext
    change Sym2.map Subtype.val (Sym2.map (intervalArmStripVertex n x) e.val) =
      Sym2.map Subtype.val (Sym2.map f e.val)
    rw [Sym2.map_map,Sym2.map_map]
    rfl
  have hopen : RSW.stripPlaneRestriction n (RSW.stripWindowPlaneConfiguration n m C) es=true := by
    simp only [RSW.stripPlaneRestriction,RSW.stripWindowPlaneConfiguration,decide_eq_true_eq]
    rw [hplane]
    exact Finset.mem_map.mpr ⟨ew,hew,rfl⟩
  have heopen : es.val ∈ (RSW.stripOpenGraph n
      (RSW.stripPlaneRestriction n (RSW.stripWindowPlaneConfiguration n m C))).edgeSet := by
    rw [RSW.stripOpenGraph,SimpleGraph.edgeSet_fromEdgeSet]
    exact ⟨⟨es.property,hopen⟩,(RSW.stripGraph n).not_isDiag_of_mem_edgeSet es.property⟩
  have hes : es.val=s(intervalArmStripVertex n x u,intervalArmStripVertex n x v) := by
    change Sym2.map (intervalArmStripVertex n x) e.val=_
    rw [hpair]
    rfl
  apply (RSW.stripOpenGraph n _).mem_edgeSet.mp
  rwa [hes] at heopen

end
end PottsContinuity.Push
