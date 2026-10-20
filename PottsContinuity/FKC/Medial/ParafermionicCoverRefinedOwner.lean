-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `Medial/ParafermionicCoverRefinedOwner.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.Medial.ParafermionicCoverRefinedPortEmbedding
public import PottsContinuity.FKC.Medial.ParafermionicCoverRefinedClosedCap
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.Medial

/-- The coarse cover vertex owning a refined-grid vertex. The floor convention
is chosen so the coarse cell is centered at `(9*x-4, 9*y+4)`. -/
def parafermionicCoverRefinedCoarseOwner (z : ParafermionicCoverVertex) :
    ParafermionicCoverVertex :=
  (((z.1.1 + 8) / 9, z.1.2 / 9), z.2)

/-- The center of the refined `9`-by-`9` cell associated to a coarse vertex. -/
def parafermionicCoverRefinedCoarseCenter (v : ParafermionicCoverVertex) :
    ParafermionicCoverVertex :=
  ((9 * v.1.1 - 4, 9 * v.1.2 + 4), v.2)

theorem parafermionicCoverRefinedCoarseOwner_portEmbedding
    (c : ParafermionicCoverPort) (layer : Bool) :
    parafermionicCoverRefinedCoarseOwner
      (parafermionicCoverRefinedPortEmbedding (c, layer)) =
        parafermionicCoverPortVertex c := by
  rcases c with ⟨⟨⟨⟨x, y⟩, ax⟩, tip, side⟩, k⟩
  cases ax <;> cases tip <;> cases side <;> cases layer <;>
    simp [parafermionicCoverRefinedCoarseOwner,
      parafermionicCoverRefinedPortEmbedding_horizontal,
      parafermionicCoverRefinedPortEmbedding_vertical,
      parafermionicCoverPortVertex, LatticePort.primalVertex,
      LatticeBond.endpoint, LatticeBond.source, LatticeBond.target] <;> omega

theorem parafermionicCoverRefinedCoarseOwner_closedCapMiddle
    (c : ParafermionicCoverPort) :
    parafermionicCoverRefinedCoarseOwner
      (parafermionicCoverRefinedClosedCapMiddle c) =
        parafermionicCoverPortVertex c := by
  rcases c with ⟨⟨⟨⟨x, y⟩, ax⟩, tip, side⟩, k⟩
  cases ax <;> cases tip <;> cases side <;>
    simp [parafermionicCoverRefinedCoarseOwner,
      parafermionicCoverRefinedClosedCapMiddle_horizontal,
      parafermionicCoverRefinedClosedCapMiddle_vertical,
      parafermionicCoverPortVertex, LatticePort.primalVertex,
      LatticeBond.endpoint, LatticeBond.source, LatticeBond.target] <;> omega

end PottsContinuity.FKC.Medial
