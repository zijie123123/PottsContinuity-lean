module

public import PottsContinuity.Thm3.Push.IntervalArmStripWindowOpenEdges

@[expose] public section

namespace PottsContinuity.Push
open PottsContinuity.PD.FK PottsContinuity.BD12 MeasureTheory
noncomputable section
attribute [local instance] configurationMeasurableSpace remainingConfigurationMeasurableSpace

/-- An actual sampled source-square connection maps to the literal
`RSW.stripLocalConnection` on the specified finite-window extension. -/
theorem intervalArmStripWindow_connection_mem_local (n m s : ℕ) (x : ℤ)
    (hlo : -(m : ℤ) ≤ x) (hhi : x+2*(n : ℤ) ≤ (m : ℤ))
    (C : Configuration (PottsContinuity.squareLattice.induce (RSW.stripWindow n m : Set LatticeVertex)))
    (hC : embeddedConfigurationRestriction _ _ (intervalArmStripWindowEmbedding n m x hlo hhi)
      (intervalArmStripWindow_map_le n m x hlo hhi) C ∈
      arcsConnectionEvent (rectangleGraph (0,0) (2*n) (2*n))
        (intervalArmBottomArc (2*n) (4*(s : ℤ)) (5*(s : ℤ)))
        (intervalArmBottomArc (2*n) (6*(s : ℤ)) (7*(s : ℤ)))) :
    RSW.stripPlaneRestriction n (RSW.stripWindowPlaneConfiguration n m C) ∈ RSW.stripLocalConnection n s x := by
  obtain ⟨u,hu,v,hv,⟨p⟩⟩ := hC
  let ω := RSW.stripPlaneRestriction n (RSW.stripWindowPlaneConfiguration n m C)
  let j : openGraph (rectangleGraph (0,0) (2*n) (2*n))
      (embeddedConfigurationRestriction _ _ (intervalArmStripWindowEmbedding n m x hlo hhi)
        (intervalArmStripWindow_map_le n m x hlo hhi) C) →g RSW.stripOpenGraph n ω :=
    {toFun := intervalArmStripVertex n x,
     map_rel' := fun h => intervalArmStripWindow_open_adj n m x hlo hhi C _ _ h}
  refine ⟨intervalArmStripVertex n x u,intervalArmStripVertex n x v,p.map j,?_,?_,?_⟩
  · change (x+u.val.1,u.val.2) ∈ Set.Icc (x+4*(s : ℤ)) (x+5*(s : ℤ)) ×ˢ ({0} : Set ℤ)
    exact ⟨⟨by have h:=hu.2.1; omega,by have h:=hu.2.2; omega⟩,hu.1⟩
  · change (x+v.val.1,v.val.2) ∈ Set.Icc (x+6*(s : ℤ)) (x+7*(s : ℤ)) ×ˢ ({0} : Set ℤ)
    exact ⟨⟨by have h:=hv.2.1; omega,by have h:=hv.2.2; omega⟩,hv.1⟩
  · intro z hz
    rw [SimpleGraph.Walk.support_map] at hz
    obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hz
    rw [RSW.stripRectangleVertices,Finset.mem_preimage]
    change (x+w.val.1,w.val.2) ∈ PottsContinuity.latticeRectangle x (x+2*(n : ℤ)) 0 (2*(n : ℤ))
    simp only [PottsContinuity.latticeRectangle,Finset.mem_product,Finset.mem_Icc]
    have hwbox := (PD.FK.mem_latticeRectangle (0,0) w.val (2*n) (2*n)).mp w.property
    constructor <;> constructor <;> dsimp at hwbox <;> omega

/-- The finite-host source connection probability is bounded by the EXACT
finite-window probability `RSW.stripWindowEventProbability` used by the strip
local-event limit theorem. -/
theorem intervalArmStripWindow_connection_probability_le_local
    (θ : Parameters) (n m s : ℕ) (x : ℤ)
    (hlo : -(m : ℤ) ≤ x) (hhi : x+2*(n : ℤ) ≤ (m : ℤ)) :
    (measure (PottsContinuity.squareLattice.induce (RSW.stripWindow n m : Set LatticeVertex)) θ
      (RSW.stripWindowBoundary n m 0)
      {C | embeddedConfigurationRestriction _ _ (intervalArmStripWindowEmbedding n m x hlo hhi)
        (intervalArmStripWindow_map_le n m x hlo hhi) C ∈
        arcsConnectionEvent (rectangleGraph (0,0) (2*n) (2*n))
          (intervalArmBottomArc (2*n) (4*(s : ℤ)) (5*(s : ℤ)))
          (intervalArmBottomArc (2*n) (6*(s : ℤ)) (7*(s : ℤ)))}).toReal ≤
      RSW.stripWindowEventProbability θ n m (RSW.stripLocalConnection n s x) := by
  apply measureReal_mono (h₂ := measure_ne_top _ _)
  intro C hC
  exact intervalArmStripWindow_connection_mem_local n m s x hlo hhi C hC

end
end PottsContinuity.Push
