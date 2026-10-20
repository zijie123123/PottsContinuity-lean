-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `Medial/ParafermionicCoverVertexNeighbors.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.Medial.ParafermionicCoverGraph
public import Mathlib.Data.Set.Card
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.Medial

open PottsContinuity.FKC
open SimpleGraph

/-- Projection from actual cover neighbors is exactly the four-neighbor base
lattice projection; each projected neighbor has its unique sheet-shifted lift. -/
theorem parafermionicCoverGraph_neighborSet_eq_neighborLift_image
    (u : ParafermionicCoverVertex) :
    parafermionicCoverGraph.neighborSet u =
      (parafermionicCoverNeighborLift u) '' squareLattice.neighborSet u.1 := by
  ext w
  constructor
  · intro hw
    have hadj : parafermionicCoverGraph.Adj u w :=
      (by simpa only [SimpleGraph.mem_neighborSet] using hw)
    have hbase : w.1 ∈ squareLattice.neighborSet u.1 :=
      (by simpa only [SimpleGraph.mem_neighborSet] using hadj.1)
    have hlift := parafermionicCoverNeighborLift_unique u w.1 w rfl hadj
    exact ⟨w.1, hbase, hlift.symm⟩
  · rintro ⟨v, hv, rfl⟩
    rw [SimpleGraph.mem_neighborSet]
    exact parafermionicCoverNeighborLift_adj u v
      (by simpa only [SimpleGraph.mem_neighborSet] using hv)

end PottsContinuity.FKC.Medial
