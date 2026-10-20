module

public import PottsContinuity.PlanarMixed.FiniteSlit.ExteriorSeeds
public import PottsContinuity.PlanarMixed.CutExteriorReveals

@[expose] public section

namespace PottsContinuity.PlanarMixed.FiniteSlit
open PD.FK
noncomputable section

/-- Closed left exterior of an arbitrary source cut, entirely in the
source-only deterministic graph. -/
def sourceLeftExterior (w h : ℕ) (x y : ℤ)
    (cut : Set (RectangleVertex (0,0) w h)) : Set (RectangleVertex (0,0) w h) :=
  {u | Sum.inl u ∈ closedCutExterior (sourceExteriorGraph w h x y)
    (Sum.inl '' cut) (sourceAlpha w h x)}

/-- Closed right exterior of an arbitrary source cut. -/
def sourceRightExterior (w h : ℕ) (x y : ℤ)
    (cut : Set (RectangleVertex (0,0) w h)) : Set (RectangleVertex (0,0) w h) :=
  {u | Sum.inl u ∈ closedCutExterior (sourceExteriorGraph w h x y)
    (Sum.inl '' cut) (sourceBeta w h x y)}

/-- The actual reference and explicit source graph have identical cut-reach
regions at every original source vertex. The seed set is projected exactly. -/
theorem source_cutReachRegion_iff (M : ℕ) (x y : ℤ) (w h : ℕ)
    (hM : 2 ≤ M) (hx : 1 ≤ x) (hxw : x ≤ (w:ℤ))
    (hleft : x-(M:ℤ) < 0) (hright : (w:ℤ) < x+(M:ℤ)-1) (hh : h < M)
    (hyh : y ≤ (h:ℤ)) (cut : Set (RectangleVertex (0,0) w h))
    (seeds : Set (Vertex M x)) (u : RectangleVertex (0,0) w h) :
    Sum.inl u ∈ cutReachRegion (sourceExteriorGraph w h x y) (Sum.inl '' cut)
      (exteriorProjection M x w h '' seeds) ↔
    rectangleIntoReference M x w h (by omega) (by omega) (by omega) (by omega) u ∈
      cutReachRegion (graph M x y)
        (rectangleIntoReference M x w h (by omega) (by omega) (by omega) (by omega) '' cut) seeds := by
  have hc := cutReachRegion_map_iff_of_connected_fibres (graph M x y)
    (exteriorProjection M x w h) (exteriorProjection_connected_fibres M x y w h hM hh)
    (Sum.inl '' cut) seeds
    (rectangleIntoReference M x w h (by omega) (by omega) (by omega) (by omega) u)
  rw [exteriorProjection_map_eq_sourceExteriorGraph M x y w h hM hx hxw hleft hright hh hyh,
    exteriorProjection_rectangleIntoReference,exteriorProjection_preimage_cut] at hc
  exact hc

/-- Closed exterior identity for every source cut and either original
reference seed set. Cut vertices, including both endpoints, are preserved. -/
theorem source_closedCutExterior_iff (M : ℕ) (x y : ℤ) (w h : ℕ)
    (hM : 2 ≤ M) (hx : 1 ≤ x) (hxw : x ≤ (w:ℤ))
    (hleft : x-(M:ℤ) < 0) (hright : (w:ℤ) < x+(M:ℤ)-1) (hh : h < M)
    (hyh : y ≤ (h:ℤ)) (cut : Set (RectangleVertex (0,0) w h))
    (seeds : Set (Vertex M x)) (u : RectangleVertex (0,0) w h) :
    Sum.inl u ∈ closedCutExterior (sourceExteriorGraph w h x y) (Sum.inl '' cut)
      (exteriorProjection M x w h '' seeds) ↔
    rectangleIntoReference M x w h (by omega) (by omega) (by omega) (by omega) u ∈
      closedCutExterior (graph M x y)
        (rectangleIntoReference M x w h (by omega) (by omega) (by omega) (by omega) '' cut) seeds := by
  let f := rectangleIntoReference M x w h (by omega) (by omega) (by omega) (by omega)
  change (_ ∨ Sum.inl u ∈ Sum.inl '' cut) ↔ (_ ∨ f u ∈ f '' cut)
  rw [source_cutReachRegion_iff M x y w h hM hx hxw hleft hright hh hyh cut seeds u]
  simp only [Set.mem_image,Sum.inl.injEq,f.injective.eq_iff]

/-- The source-only left exterior is exactly the clipped reference exterior,
with no walk outside the original source remaining in its definition. -/
theorem sourceLeftExterior_iff (M : ℕ) (x y : ℤ) (w h : ℕ)
    (hM : 2 ≤ M) (hx : 1 ≤ x) (hxw : x ≤ (w:ℤ))
    (hleft : x-(M:ℤ) < 0) (hright : (w:ℤ) < x+(M:ℤ)-1) (hh : h < M)
    (hyh : y ≤ (h:ℤ)) (cut : Set (RectangleVertex (0,0) w h))
    (u : RectangleVertex (0,0) w h) :
    u ∈ sourceLeftExterior w h x y cut ↔
    rectangleIntoReference M x w h (by omega) (by omega) (by omega) (by omega) u ∈
      closedCutExterior (graph M x y)
        (rectangleIntoReference M x w h (by omega) (by omega) (by omega) (by omega) '' cut) (alpha M x) := by
  have hc := source_closedCutExterior_iff M x y w h hM hx hxw hleft hright hh hyh cut (alpha M x) u
  rw [exteriorProjection_image_alpha M x w h hM hx hxw hleft hright hh] at hc
  exact hc

/-- The corresponding exact right exterior identity uses the ray starting
at y, rather than the reflected-dual ray starting at y+1. -/
theorem sourceRightExterior_iff (M : ℕ) (x y : ℤ) (w h : ℕ)
    (hM : 2 ≤ M) (hx : 1 ≤ x) (hxw : x ≤ (w:ℤ))
    (hleft : x-(M:ℤ) < 0) (hright : (w:ℤ) < x+(M:ℤ)-1) (hh : h < M)
    (hyh : y ≤ (h:ℤ)) (cut : Set (RectangleVertex (0,0) w h))
    (u : RectangleVertex (0,0) w h) :
    u ∈ sourceRightExterior w h x y cut ↔
    rectangleIntoReference M x w h (by omega) (by omega) (by omega) (by omega) u ∈
      closedCutExterior (graph M x y)
        (rectangleIntoReference M x w h (by omega) (by omega) (by omega) (by omega) '' cut) (beta M x y) := by
  have hc := source_closedCutExterior_iff M x y w h hM hx hxw hleft hright hh hyh cut (beta M x y) u
  rw [exteriorProjection_image_beta M x y w h hM hx hxw hleft hright hh] at hc
  exact hc

end
end PottsContinuity.PlanarMixed.FiniteSlit
