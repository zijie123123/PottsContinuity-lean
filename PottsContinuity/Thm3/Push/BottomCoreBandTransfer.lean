module

public import PottsContinuity.Thm3.Push.BottomCoreErasedPathLift
public import PottsContinuity.Thm3.Push.RectangleBandSideErasure
public import PottsContinuity.Thm3.Push.EmbeddedOpenGraph

@[expose] public section

namespace PottsContinuity.Push
open PD.FK PD.FK.Medial PD.Duality PlanarMixed.Square
noncomputable section
local instance coreBandTransferEdgeEq (a : LatticeVertex) (w h : ℕ) :
    DecidableEq (rectangleGraph a w h).edgeSet := Classical.decEq _

/-- An actual sampled walk across the retained core with every support
vertex in the stated bottom band. The two entire endpoint sides are used. -/
def bottomCoreBandEvent (a : LatticeVertex) (w h b : ℕ) :
    Set (Configuration (generalRectangleDualBottomCoreGraph a w h)) :=
  {C | ∃ u v, ∃ p : (openGraph (generalRectangleDualBottomCoreGraph a w h) C).Walk u v,
    u.val.val.1 = a.1-1 ∧ v.val.val.1 = a.1+(w:ℤ) ∧
    ∀ z ∈ p.support, a.2 ≤ z.val.val.2 ∧ z.val.val.2 ≤ a.2+(b:ℤ)}

/-- Every actual ordinary-rectangle band crossing supplies an actual core
band crossing in its original restricted sample. Removed side-bond runs are
first eliminated using actual arc connectivity, then every step is lifted. -/
theorem bottomCoreBandEvent_of_rectangle_band
    (a : LatticeVertex) (w h b : ℕ) (hw : 1 ≤ w) (hbh : b < h)
    (C : Configuration (rectangleGraph (a.1-1,a.2) (w+1) h))
    (hC : C ∈ rectangleBandConnectionEvent (a.1-1,a.2) (w+1) b h hbh.le) :
    embeddedConfigurationRestriction (generalRectangleDualBottomCoreGraph a w h)
      (rectangleGraph (a.1-1,a.2) (w+1) h)
      (generalRectangleDualBottomCoreVertexEquiv a w h).toEmbedding
      (bottomCoreAmbient_map_le a w h) C ∈ bottomCoreBandEvent a w h b := by
  classical
  let H := rectangleGraph (a.1-1,a.2) (w+1) h
  let G := rectangleGraph (a.1-1,a.2) (w+1) b
  let f := rectangleBandEmbedding (a.1-1,a.2) (w+1) b h hbh.le
  let R := rectangleThreeSideBonds (a.1-1,a.2) (w+1) h
  let e := generalRectangleDualBottomCoreVertexEquiv a w h
  have her := (rectangleBandConnectionEvent_sdiff_threeSideBonds
    (a.1-1,a.2) (w+1) b h hbh C).mpr hC
  obtain ⟨u,hu,v,hv,⟨q⟩⟩ := her
  let j := embeddedRestrictionOpenEmbedding G H f
    (rectangleBandEmbedding_map_le (a.1-1,a.2) (w+1) b h hbh.le)
    (fun _ _ => Iff.rfl) (C \ R)
  let qH := q.map j.toHom
  let p := qH.map (bottomCoreErasedOpenHom a w h hw C)
  refine ⟨e.symm (f u),e.symm (f v),p,?_,?_,?_⟩
  · exact hu
  · change v.val.1 = a.1+(w:ℤ)
    change v.val.1 = a.1-1+((w+1:ℕ):ℤ) at hv
    push_cast at hv
    omega
  · intro z hz
    change z ∈ (qH.map (bottomCoreErasedOpenHom a w h hw C)).support at hz
    rw [SimpleGraph.Walk.support_map] at hz
    obtain ⟨zH,hzH,rfl⟩ := List.mem_map.mp hz
    change zH ∈ (q.map j.toHom).support at hzH
    rw [SimpleGraph.Walk.support_map] at hzH
    obtain ⟨zG,_,rfl⟩ := List.mem_map.mp hzH
    change a.2 ≤ zG.val.2 ∧ zG.val.2 ≤ a.2+(b:ℤ)
    exact ((mem_latticeRectangle _ zG.val _ _).mp zG.property).2

end
end PottsContinuity.Push
