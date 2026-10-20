module

public import PottsContinuity.PlanarMixed.FiniteSlit.SourceExteriorReveals
public import PottsContinuity.PlanarMixed.FiniteSlit.SourcePaths

@[expose] public section

namespace PottsContinuity.PlanarMixed.FiniteSlit
open PD.FK
noncomputable section
local instance sourceActiveCarrierEdgeEq {U : Type*} (G : SimpleGraph U) :
    DecidableEq G.edgeSet := Classical.decEq _

namespace CrosscutData
variable {M : ℕ} {x y : ℤ} (D : CrosscutData M x y) (hM : 2 ≤ M) (hy : 0 < y)
  (w h : ℕ) (hx : 1 ≤ x) (hxw : x ≤ (w:ℤ))
  (hp : ∀ v ∈ D.first.support, 0 ≤ v.val.1 ∧ v.val.1 ≤ (w:ℤ) ∧ v.val.2 ≤ (h:ℤ))
  (hq : ∀ v ∈ D.second.support, 0 ≤ v.val.1 ∧ v.val.1 ≤ (w:ℤ) ∧ v.val.2 ≤ (h:ℤ))
  (hleft : x-(M:ℤ) < 0) (hright : (w:ℤ) < x+(M:ℤ)-1) (hh : h < M)
  (hyh : y ≤ (h:ℤ))
include hleft hright hh hyh
local notation "r" => D.rank hM hy
local notation "k" => D.sourceRectangleEmbedding hM hy w h hx hxw hp hq

/-- The source graph after deleting the literal slit and two closed exterior
reveals is EXACTLY the embedded active band, on the original source vertices.
No reference edges, exterior excursions or path bonds remain to be sampled. -/
theorem sourceRectangle_active_graph_eq :
    edgeRestriction (rectangleGraph (0,0) w h)
      (sourceExteriorReveal w h x y
        (Subtype.val '' {v | v ∈ D.first.support})
        (Subtype.val '' {v | v ∈ D.second.support})) =
    (edgeRestriction (rankedBandGraph (graph M x y) r)
      (bandArcBonds (graph M x y) r)).map k := by
  have hp' : ∀ v ∈ D.first.support, v.val ∈ PD.FK.latticeRectangle (0,0) w h := by
    intro v hv
    have hb := hp v hv
    have hr := (mem_rectangle_iff M x (by omega) v.val).mp v.property
    rw [PD.FK.mem_latticeRectangle]
    dsimp
    omega
  have hq' : ∀ v ∈ D.second.support, v.val ∈ PD.FK.latticeRectangle (0,0) w h := by
    intro v hv
    have hb := hq v hv
    have hr := (mem_rectangle_iff M x (by omega) v.val).mp v.property
    rw [PD.FK.mem_latticeRectangle]
    dsimp
    omega
  have hc := D.sourceRectangle_active_complement hM hy w h hx hxw hp hq
    (by omega) (by omega) (by omega)
  rw [D.clipped_outer_reveal_eq hM hy,
    D.clippedFirstReveal_eq_sourceExterior w h hM hx hxw hleft hright hh hyh hp',
    D.clippedSecondReveal_eq_sourceExterior w h hM hx hxw hleft hright hh hyh hq'] at hc
  change subgraphRemovedEdges _ (rectangleGraph (0,0) w h) =
    sourceExteriorReveal w h x y _ _ at hc
  rw [← hc]
  exact edgeRestriction_subgraphRemovedEdges
    (active_map_le _ _ _ k (D.sourceRectangleEmbedding_map_le hM hy w h hx hxw hp hq))

end CrosscutData
end
end PottsContinuity.PlanarMixed.FiniteSlit
