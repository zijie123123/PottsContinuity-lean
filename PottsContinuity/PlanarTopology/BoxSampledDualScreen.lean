module

public import PottsContinuity.PlanarTopology.SampledDualScreenSeparation
public import PottsContinuity.PD.FK.Isomorphism
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Maps

@[expose] public section

namespace PottsContinuity.PlanarTopology
open PD.FK PD.FK.Medial
noncomputable section

/-- The literal source box and the rectangle used by the dual toolkit have
exactly the same retained vertices. -/
theorem latticeRectangle_neg_eq_box (n : ℕ) :
    latticeRectangle (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) = PD.box n := by
  ext z
  rw [mem_latticeRectangle]
  simp only [PD.box,Finset.mem_product,Finset.mem_Icc]
  push_cast
  omega

/-- Exact coordinate-preserving change from the source box graph to the
rectangle graph; isolated vertices and all original edges are retained. -/
def boxRectangleGraphIso (n : ℕ) :
    PD.squareLattice.induce (PD.box n : Set LatticeVertex) ≃g
      rectangleGraph (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) where
  toFun u := ⟨u.val,by rw [latticeRectangle_neg_eq_box]; exact u.property⟩
  invFun v := ⟨v.val,by rw [← latticeRectangle_neg_eq_box]; exact v.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

@[simp] theorem boxRectangleGraphIso_val (n : ℕ)
    (u : (PD.box n : Set LatticeVertex)) : (boxRectangleGraphIso n u).val = u.val := rfl

end
end PottsContinuity.PlanarTopology
