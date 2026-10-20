/- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
accessible (see `related_formalizations` in formalization.yaml): file
`Medial/PortPrimalVertexCoordinates.lean`.
Adaptation: namespace/import relocation only.
-/
module

public import PottsContinuity.Thm4.LatticePorts
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.Thm4.Medial

open PottsContinuity.PD.FK
open LatticeAxis

 def portBaseFromPrimalVertex (v : LatticeVertex) (axis : LatticeAxis)
    (tip : Bool) : LatticeVertex :=
  if tip then
    match axis with
    | horizontal => (v.1 - 1, v.2)
    | vertical => (v.1, v.2 - 1)
  else v

theorem endpoint_portBaseFromPrimalVertex (v : LatticeVertex)
    (axis : LatticeAxis) (tip : Bool) :
    (⟨portBaseFromPrimalVertex v axis tip, axis⟩ : LatticeBond).endpoint tip = v := by
  cases axis <;> cases tip <;>
    simp [portBaseFromPrimalVertex, LatticeBond.endpoint, LatticeBond.source,
      LatticeBond.target]

/-- Every port is determined by its actual primal endpoint and its axis/tip/side
flags. The bond base is recovered by shifting back one unit exactly when the
tip is the target endpoint. -/
def latticePortPrimalVertexCoordinatesEquiv :
    LatticePort ≃ LatticeVertex × (LatticeAxis × (Bool × Bool)) where
  toFun p := (p.primalVertex, (p.bond.axis, (p.tip, p.side)))
  invFun x :=
    ⟨⟨portBaseFromPrimalVertex x.1 x.2.1 x.2.2.1, x.2.1⟩,
      x.2.2.1, x.2.2.2⟩
  left_inv := by
    rintro ⟨⟨base, axis⟩, tip, side⟩
    cases axis <;> cases tip <;>
      simp [LatticePort.primalVertex, LatticeBond.endpoint, LatticeBond.source,
        LatticeBond.target, portBaseFromPrimalVertex]
  right_inv := by
    rintro ⟨v, ⟨axis, ⟨tip, side⟩⟩⟩
    simp only
    congr 1
    exact endpoint_portBaseFromPrimalVertex v axis tip

end PottsContinuity.Thm4.Medial
