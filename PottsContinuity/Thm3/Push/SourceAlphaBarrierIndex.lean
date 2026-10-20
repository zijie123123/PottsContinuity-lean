module

public import PottsContinuity.PlanarMixed.FiniteSlit.SourceExteriorReveals
public import PottsContinuity.Thm3.Push.HorizontalBarrierTranslation

@[expose] public section

namespace PottsContinuity.Push
open PD.FK PD.Duality PlanarMixed PlanarMixed.FiniteSlit
noncomputable section

/-- The literal source alpha cut component has index zero for a genuine
slit barrier whose source trace is confined to the original source rectangle.
The exact source/reference projection handles both exterior vertices. -/
theorem sourceAlpha_cutReach_index_zero_of_slitBarrier
    (M : ℕ) (x y b : ℤ) (w h : ℕ)
    (hM : 2 ≤ M) (hx : 1 ≤ x) (hxw : x ≤ (w:ℤ))
    (hleft : x-(M:ℤ) < 0) (hright : (w:ℤ) < x+(M:ℤ)-1)
    (hh : h < M) (hyh : y ≤ (h:ℤ)) {t z : LatticeVertex}
    (q : squareLattice.Walk (b,0) t)
    (hsource : ∀ v ∈ q.support, v ∈ PD.FK.latticeRectangle (0,0) w h)
    (p : squareLattice.Walk z z)
    (hallowed : ∀ e ∈ p.edges, e ∈ slitBarrierEdges M x y b q)
    (hα : ∀ v : Vertex M x, v ∈ alpha M x → rayIndex v.val p = 0)
    (u : RectangleVertex (0,0) w h)
    (hu : Sum.inl u ∈ cutReachRegion (sourceExteriorGraph w h x y)
      (Sum.inl '' sourceCoordinateTrace w h {v | v ∈ q.support}) (sourceAlpha w h x)) :
    rayIndex u.val p = 0 := by
  classical
  let f := rectangleIntoReference M x w h (by omega) hleft.le hright.le hh.le
  have hcut : f '' sourceCoordinateTrace w h {v | v ∈ q.support} =
      {v : Vertex M x | v.val ∈ q.support} := by
    ext v
    constructor
    · rintro ⟨a,ha,rfl⟩
      exact ha
    · intro hv
      exact ⟨⟨v.val,hsource v.val hv⟩,hv,Subtype.ext rfl⟩
  have ht := source_cutReachRegion_iff M x y w h hM hx hxw hleft hright hh hyh
    (sourceCoordinateTrace w h {v | v ∈ q.support}) (alpha M x) u
  rw [exteriorProjection_image_alpha M x w h hM hx hxw hleft hright hh] at ht
  have href := ht.mp hu
  change f u ∈ cutReachRegion (graph M x y)
    (f '' sourceCoordinateTrace w h {v | v ∈ q.support}) (alpha M x) at href
  rw [hcut] at href
  obtain ⟨a,ha,r,hr⟩ := href
  have hi := rayIndex_eq_of_slitBarrier M x y b hM q p hallowed r hr
  exact hi.symm.trans (hα a ha)

end
end PottsContinuity.Push
