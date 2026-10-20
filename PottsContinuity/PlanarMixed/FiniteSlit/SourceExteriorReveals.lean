module

public import PottsContinuity.PlanarMixed.FiniteSlit.SourceExteriorRegions
public import PottsContinuity.PlanarMixed.FiniteSlit.ClippedReveals

@[expose] public section

namespace PottsContinuity.PlanarMixed.FiniteSlit
open PD.FK
noncomputable section
local instance sourceExteriorRevealsEdgeDecidableEq {U : Type*} (G : SimpleGraph U) :
    DecidableEq G.edgeSet := Classical.decEq _

/-- Read an actual lattice-coordinate trace on the original source carrier. -/
def sourceCoordinateTrace (w h : ℕ) (trace : Set LatticeVertex) :
    Set (RectangleVertex (0,0) w h) := Subtype.val ⁻¹' trace

/-- Coordinate traces lying in the source rectangle retain every original
reference vertex under the canonical inclusion. -/
theorem sourceCoordinateTrace_image_eq (M : ℕ) (x : ℤ) (w h : ℕ)
    (hM : 1 ≤ M) (hleft : x-(M:ℤ) ≤ 0) (hright : (w:ℤ) ≤ x+(M:ℤ)-1)
    (hheight : h ≤ M) (trace : Set (Vertex M x))
    (hs : ∀ v ∈ trace, v.val ∈ PD.FK.latticeRectangle (0,0) w h) :
    rectangleIntoReference M x w h hM hleft hright hheight ''
      sourceCoordinateTrace w h (Subtype.val '' trace) = trace := by
  ext v
  constructor
  · rintro ⟨u,⟨a,ha,he⟩,rfl⟩
    have heu : rectangleIntoReference M x w h hM hleft hright hheight u = a :=
      Subtype.ext he.symm
    simpa only [heu] using ha
  · intro hv
    exact ⟨⟨v.val,hs v hv⟩,⟨v,hv,rfl⟩,Subtype.ext rfl⟩

/-- Entire source reveal, defined without any reference truncation:
strict-above-tip slit bonds and the two closed one-sided source exteriors. -/
def sourceExteriorReveal (w h : ℕ) (x y : ℤ) (first second : Set LatticeVertex) :
    Configuration (rectangleGraph (0,0) w h) :=
  rectangleSlitBonds w h x y ∪
    (internalBonds (rectangleGraph (0,0) w h)
      (sourceLeftExterior w h x y (sourceCoordinateTrace w h first)) ∪
     internalBonds (rectangleGraph (0,0) w h)
      (sourceRightExterior w h x y (sourceCoordinateTrace w h second)))

/-- The corresponding literal host reveal adds exactly the bonds outside
the sampled source rectangle. All sampled bonds are original host bonds. -/
def sourceExteriorHostReveal {U : Type*} [Finite U] (H : SimpleGraph U)
    (w h : ℕ) (x y : ℤ) (first second : Set LatticeVertex)
    (j : RectangleVertex (0,0) w h ↪ U)
    (hSH : (rectangleGraph (0,0) w h).map j ≤ H) : Configuration H :=
  subgraphRemovedEdges ((rectangleGraph (0,0) w h).map j) H ∪
    embeddedConfigurationEmbedding _ H j hSH (sourceExteriorReveal w h x y first second)

namespace CrosscutData
variable {M : ℕ} {x y : ℤ} (D : CrosscutData M x y)
  (w h : ℕ) (hM : 2 ≤ M) (hx : 1 ≤ x) (hxw : x ≤ (w:ℤ))
  (hleft : x-(M:ℤ) < 0) (hright : (w:ℤ) < x+(M:ℤ)-1) (hh : h < M)
  (hyh : y ≤ (h:ℤ))
local notation "f" => rectangleIntoReference M x w h (by omega) (by omega) (by omega) (by omega)
include hx hxw hyh

/-- The first clipped reveal is intrinsic to the source-coordinate first trace. -/
theorem clippedFirstReveal_eq_sourceExterior
    (hp : ∀ v ∈ D.first.support, v.val ∈ PD.FK.latticeRectangle (0,0) w h) :
    D.clippedFirstReveal (rectangleGraph (0,0) w h) f =
      internalBonds (rectangleGraph (0,0) w h) (sourceLeftExterior w h x y
        (sourceCoordinateTrace w h (Subtype.val '' {v | v ∈ D.first.support}))) := by
  have hi := sourceCoordinateTrace_image_eq M x w h (by omega) (by omega) (by omega)
    (by omega) {v | v ∈ D.first.support} hp
  have he : {u | f u ∈ closedCutExterior (graph M x y) {v | v ∈ D.first.support} (alpha M x)} =
      sourceLeftExterior w h x y (sourceCoordinateTrace w h (Subtype.val '' {v | v ∈ D.first.support})) := by
    ext u
    have hc := sourceLeftExterior_iff M x y w h hM hx hxw hleft hright hh hyh
      (sourceCoordinateTrace w h (Subtype.val '' {v | v ∈ D.first.support})) u
    rw [hi] at hc
    exact hc.symm
  unfold clippedFirstReveal
  rw [he]

/-- The second clipped reveal is intrinsic to the source-coordinate second trace. -/
theorem clippedSecondReveal_eq_sourceExterior
    (hq : ∀ v ∈ D.second.support, v.val ∈ PD.FK.latticeRectangle (0,0) w h) :
    D.clippedSecondReveal (rectangleGraph (0,0) w h) f =
      internalBonds (rectangleGraph (0,0) w h) (sourceRightExterior w h x y
        (sourceCoordinateTrace w h (Subtype.val '' {v | v ∈ D.second.support}))) := by
  have hi := sourceCoordinateTrace_image_eq M x w h (by omega) (by omega) (by omega)
    (by omega) {v | v ∈ D.second.support} hq
  have he : {u | f u ∈ closedCutExterior (graph M x y) {v | v ∈ D.second.support} (beta M x y)} =
      sourceRightExterior w h x y (sourceCoordinateTrace w h (Subtype.val '' {v | v ∈ D.second.support})) := by
    ext u
    have hc := sourceRightExterior_iff M x y w h hM hx hxw hleft hright hh hyh
      (sourceCoordinateTrace w h (Subtype.val '' {v | v ∈ D.second.support})) u
    rw [hi] at hc
    exact hc.symm
  unfold clippedSecondReveal
  rw [he]

end CrosscutData
end
end PottsContinuity.PlanarMixed.FiniteSlit
