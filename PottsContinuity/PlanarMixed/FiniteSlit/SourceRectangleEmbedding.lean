module

public import PottsContinuity.PlanarMixed.FiniteSlit.CrosscutBand
public import PottsContinuity.Thm3.RSW.FiniteSlitBandLocalization

@[expose] public section

namespace PottsContinuity.PlanarMixed.FiniteSlit
open PD.FK
noncomputable section

namespace CrosscutData
variable {M : ℕ} {x y : ℤ} (D : CrosscutData M x y) (hM : 2 ≤ M) (hy : 0 < y)
  (w h : ℕ) (hx : 1 ≤ x) (hxw : x ≤ (w:ℤ))
  (hp : ∀ v ∈ D.first.support, 0 ≤ v.val.1 ∧ v.val.1 ≤ (w:ℤ) ∧ v.val.2 ≤ (h:ℤ))
  (hq : ∀ v ∈ D.second.support, 0 ≤ v.val.1 ∧ v.val.1 ≤ (w:ℤ) ∧ v.val.2 ≤ (h:ℤ))
include hx hxw hp hq

/-- The sharper localization `RSW.finiteSlit_orderedBand_in_box` confines this
actual band to the source rectangle of width w and height h, including the rectangle R
of equation (5). -/
theorem band_subset_sourceRectangle (v : rankedBandVertices (D.rank hM hy)) :
    v.val.val ∈ PD.FK.latticeRectangle (0,0) w h := by
  have hb := RSW.finiteSlit_orderedBand_in_box M x y (w:ℤ) (h:ℤ) hM hx hxw
    {z | z ∈ D.first.support} {z | z ∈ D.second.support}
    (D.orderedCuts hM hy) hp hq v
  apply (PD.FK.mem_latticeRectangle _ _ _ _).mpr
  dsimp
  simpa only [zero_add] using And.intro (And.intro hb.1 hb.2.1) hb.2.2

/-- Literal coordinate inclusion into the precise source rectangle. -/
def sourceRectangleEmbedding :
    rankedBandVertices (D.rank hM hy) ↪ RectangleVertex (0,0) w h where
  toFun v := ⟨v.val.val,D.band_subset_sourceRectangle hM hy w h hx hxw hp hq v⟩
  inj' := fun _u _v huv => Subtype.ext (Subtype.ext
    (congrArg (fun z : RectangleVertex (0,0) w h => z.val) huv))

/-- Every sampled band bond is an original source-rectangle bond. -/
theorem sourceRectangleEmbedding_map_le :
    (rankedBandGraph (graph M x y) (D.rank hM hy)).map
      (D.sourceRectangleEmbedding hM hy w h hx hxw hp hq) ≤ rectangleGraph (0,0) w h := by
  intro u v huv
  obtain ⟨a,b,hab,rfl,rfl⟩ := (SimpleGraph.map_adj _ _ _ _).mp huv
  exact hab.1

end CrosscutData
end
end PottsContinuity.PlanarMixed.FiniteSlit
