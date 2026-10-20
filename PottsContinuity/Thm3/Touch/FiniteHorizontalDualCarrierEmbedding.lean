module

public import PottsContinuity.Thm3.Touch.FiniteHorizontalFullRestriction
public import PottsContinuity.FKC.FiniteFK.CrossingComponentRemoval
public import PottsContinuity.PlanarTopology.DobrushinDualProjection
public import Schoenflies.GeneralCrosscut
public import Schoenflies.FaceCyclesProof
public import PottsContinuity.PlanarTopology.OccurrenceDualHalfSegments
public import Mathlib.Combinatorics.SimpleGraph.Walk.Decomp
public import Mathlib.Topology.Connected.LocallyConnected
public import Schoenflies.AccessibleJoin
public import Schoenflies.JordanClosed
public import PottsContinuity.PlanarTopology.PolygonFourArcExistence
public import PottsContinuity.PlanarTopology.DobrushinExteriorExtraction
public import PottsContinuity.PlanarTopology.RotatedPolygon
public import PottsContinuity.PlanarTopology.RectangleGraphBridge
public import PottsContinuity.PlanarTopology.RectangleDualGraphBridge
public import PottsContinuity.Thm3.Touch.FiniteRectangleEmbedding

@[expose] public section

namespace PottsContinuity.Thm3.Touch

open PottsContinuity.PD.FK

noncomputable section

/-- Every face-base vertex of the left rectangle lies in the dual carrier of
the common host rectangle. -/
def horizontalLeftRectangleDualVertexToHost (n L : ℕ) :
    RectangleDualVertex (-(L : ℤ), 0) L (2*n) →
      RectangleDualVertex (-(L + 2*n + 2 : ℕ), -(L + 2*n + 2 : ℕ))
        (2*(L+2*n+2)) (2*(L+2*n+2)) := fun z => ⟨z.val, by
  have hz : z.val ∈ PD.FK.latticeRectangle ((-(L : ℤ)-1), -1) (L+1) (2*n+1) := by
    simpa [PD.FK.rectangleDualExpanded] using z.property
  rcases (PD.FK.mem_latticeRectangle ((-(L : ℤ)-1), -1) z.val (L+1) (2*n+1)).mp hz
      with ⟨hx,hy⟩
  have hMLNat : L ≤ L + 2*n + 2 := by omega
  have hMNNat : 2*n ≤ L + 2*n + 2 := by omega
  have hML : (L : ℤ) ≤ (L + 2*n + 2 : ℕ) := by exact_mod_cast hMLNat
  have hMN : 2*(n : ℤ) ≤ (L + 2*n + 2 : ℤ) := by exact_mod_cast hMNNat
  have hM0 : 0 ≤ (L + 2*n + 2 : ℤ) := by positivity
  have hrect := (PD.FK.mem_latticeRectangle
    (-(L + 2*n + 2 : ℤ)-1, -(L + 2*n + 2 : ℤ)-1) z.val
    (2*(L+2*n+2)+1) (2*(L+2*n+2)+1)).mpr (by
      constructor
      · constructor <;> omega
      · constructor <;> omega)
  simpa [PD.FK.rectangleDualExpanded, Nat.cast_add, Nat.cast_mul] using hrect⟩

@[simp] theorem horizontalLeftRectangleDualVertexToHost_val (n L : ℕ)
    (z : RectangleDualVertex (-(L : ℤ), 0) L (2*n)) :
    (horizontalLeftRectangleDualVertexToHost n L z).val = z.val := by rfl

end

end PottsContinuity.Thm3.Touch
