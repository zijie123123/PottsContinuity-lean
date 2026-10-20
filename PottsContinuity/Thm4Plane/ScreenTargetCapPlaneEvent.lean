module

public import PottsContinuity.Thm4Plane.ScreenTargetCap
public import PottsContinuity.Thm4Plane.ScreenConnector
public import PottsContinuity.Infinite.FiniteGraphComparison
public import PottsContinuity.Thm4Plane.PlaneTranslation
public import PottsContinuity.Foundations.BoxBoundary

@[expose] public section

namespace PottsContinuity.Thm4Plane

open PottsContinuity
open PottsContinuity.PD.FK
open PottsContinuity.PD.RCInfinite
open PottsContinuity.FKC
open PottsContinuity.FKC.FiniteFK
open PottsContinuity.Infinite

/-- The retained slit-box vertices embedded by their lattice coordinates. -/
def screenSlitVertexEmbedding (n : ℕ) :
    SlitBoxVertex n ↪ PottsContinuity.PD.FK.LatticeVertex where
  toFun := fun v => v.val
  inj' := Subtype.val_injective

/-- The slit-box graph maps into the actual square lattice under the coordinate
embedding, since deleting slit edges only removes adjacencies. -/
theorem screenSlitGraph_map_to_PD (n : ℕ) :
    (slitBoxGraph n).map (screenSlitVertexEmbedding n) ≤
      PottsContinuity.PD.FK.squareLattice := by
  have hlat : PottsContinuity.FKC.squareLattice =
      PottsContinuity.PD.FK.squareLattice := by
    ext u v
    rw [PottsContinuity.FKC.squareLattice_adj_iff,
      PottsContinuity.PD.FK.squareLattice_adj_iff]
  intro x y hxy
  obtain ⟨u, v, hadj, rfl, rfl⟩ :=
    (SimpleGraph.map_adj _ _ _ _).mp hxy
  rw [← hlat]
  exact (slitBoxGraph_adj_iff n u v).mp hadj |>.1

end PottsContinuity.Thm4Plane
