module

public import PottsContinuity.Thm3.Push.RectangleBandEmbedding

@[expose] public section

namespace PottsContinuity.Push
open PD.FK PlanarMixed
noncomputable section
local instance threeSideBondsEdgeEq (a : LatticeVertex) (w h : ℕ) :
    DecidableEq (rectangleGraph a w h).edgeSet := Classical.decEq _

/-- Original bonds internal to each of the three sides separately. Bonds
joining different sides are not added to this removed set. -/
def rectangleThreeSideBonds (a : LatticeVertex) (w h : ℕ) :
    Configuration (rectangleGraph a w h) :=
  (internalBonds (rectangleGraph a w h) {u | u.val.1 = a.1} ∪
   internalBonds (rectangleGraph a w h) {u | u.val.1 = a.1+(w:ℤ)}) ∪
   internalBonds (rectangleGraph a w h) {u | u.val.2 = a.2+(h:ℤ)}

/-- Literal membership criterion, keeping the three separate side tests. -/
theorem mem_rectangleThreeSideBonds_pair (a : LatticeVertex) (w h : ℕ)
    (u v : RectangleVertex a w h) (huv : (rectangleGraph a w h).Adj u v) :
    (⟨s(u,v),(rectangleGraph a w h).mem_edgeSet.mpr huv⟩ : (rectangleGraph a w h).edgeSet) ∈
      rectangleThreeSideBonds a w h ↔
      ((u.val.1 = a.1 ∧ v.val.1 = a.1) ∨
       (u.val.1 = a.1+(w:ℤ) ∧ v.val.1 = a.1+(w:ℤ))) ∨
       (u.val.2 = a.2+(h:ℤ) ∧ v.val.2 = a.2+(h:ℤ)) := by
  unfold rectangleThreeSideBonds
  rw [Finset.mem_union,Finset.mem_union,
    mem_internalBonds_pair _ _ u v huv,mem_internalBonds_pair _ _ u v huv,
    mem_internalBonds_pair _ _ u v huv]
  rfl

/-- In a strictly shorter bottom band, removed top bonds are absent and
all remaining removed bonds are internal to one horizontal endpoint arc. -/
theorem rectangleThreeSideBonds_band_internal (a : LatticeVertex) (w b h : ℕ)
    (hbh : b < h) (u v : RectangleVertex a w b) (huv : (rectangleGraph a w b).Adj u v)
    (he : embeddedEdgeEmbedding (rectangleGraph a w b) (rectangleGraph a w h)
      (rectangleBandEmbedding a w b h hbh.le) (rectangleBandEmbedding_map_le a w b h hbh.le)
        ⟨s(u,v),(rectangleGraph a w b).mem_edgeSet.mpr huv⟩ ∈ rectangleThreeSideBonds a w h) :
    (u.val.1 = a.1 ∧ v.val.1 = a.1) ∨
      (u.val.1 = a.1+(w:ℤ) ∧ v.val.1 = a.1+(w:ℤ)) := by
  let f := rectangleBandEmbedding a w b h hbh.le
  have hmap : (rectangleGraph a w h).Adj (f u) (f v) := huv
  have hhe : (⟨s(f u,f v),(rectangleGraph a w h).mem_edgeSet.mpr hmap⟩ :
      (rectangleGraph a w h).edgeSet) ∈ rectangleThreeSideBonds a w h := he
  have hm := (mem_rectangleThreeSideBonds_pair a w h (f u) (f v) hmap).mp hhe
  change ((u.val.1 = a.1 ∧ v.val.1 = a.1) ∨
       (u.val.1 = a.1+(w:ℤ) ∧ v.val.1 = a.1+(w:ℤ))) ∨
       (u.val.2 = a.2+(h:ℤ) ∧ v.val.2 = a.2+(h:ℤ)) at hm
  rcases hm with hside | htop
  · exact hside
  · have hu := (mem_latticeRectangle a u.val w b).mp u.property
    omega

end
end PottsContinuity.Push
