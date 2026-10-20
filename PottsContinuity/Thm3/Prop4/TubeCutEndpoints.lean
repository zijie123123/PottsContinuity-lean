module

public import PottsContinuity.Thm3.Prop4.TubeCutNonempty

/-!
# Exact exterior contacts of the central dual cut

At each extremal row of the cut, its outside face is incident to a vertex
outside the literal finite tube. These are digital boundary contacts, with
no identification of the induced boundary partition or explored side arms.
-/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4

open PD.FK.Medial

noncomputable section
local instance tubeCutEndpointsEdgeDecidableEq (n : ℕ) :
    DecidableEq (squareLattice.induce (box n : Set (ℤ × ℤ))).edgeSet := Classical.decEq _

/-- The cut rows are exactly the common integer heights of its two tube columns. -/
theorem mem_radiusTubeCutRows_iff (n : ℕ) (r : ℝ) (u v : ℤ × ℤ) (k y : ℤ) :
    y ∈ radiusTubeCutRows n r u v k ↔
      (k,y) ∈ radiusTube n r u v ∧ (k+1,y) ∈ radiusTube n r u v := by
  classical
  constructor
  · exact fun h => (Finset.mem_filter.mp h).2
  · intro h
    have hbox := ((mem_radiusTube n r u v _).mp h.1).1
    have hy := (Finset.mem_Icc.mp (Finset.mem_product.mp hbox).2)
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr hy,h⟩

end
end PottsContinuity.Thm3.Prop4
