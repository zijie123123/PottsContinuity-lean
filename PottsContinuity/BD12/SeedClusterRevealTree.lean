module

public import PottsContinuity.BD12.ClusterFrontier

/-! Literal adaptive boundary-seed cluster exploration. Every branch updates
the known open pattern by its observed answer, then recomputes the seed cluster
in those known edges. An open frontier bond therefore discovers its outside
endpoint, correcting the printed DRT endpoint-update typo. -/

@[expose] public section

namespace PottsContinuity.BD12
open FKC.FiniteFK
noncomputable section
variable {V : Type*} [Finite V] (G : SimpleGraph V)
local instance seedTreeEdgeFintype : Fintype G.edgeSet := Fintype.ofFinite _
local instance seedTreeEdgeDecidableEq : DecidableEq G.edgeSet := Classical.decEq _

/-- Explore the known seed clusters before completing the remaining edge order.
The supplied rank fixes the edge order uniquely. Each query is fresh, and each
branch is computed only from the answers already observed. -/
def seedClusterRevealTree (rank : G.edgeSet ≃ Fin (Fintype.card G.edgeSet)) (S : Finset V)
    (R H : Configuration G) : FiniteRevealTree G.edgeSet R :=
  if hR : R = Finset.univ then hR.symm ▸ FiniteRevealTree.done else
    let e := seedClusterSelect G rank S R H hR
    FiniteRevealTree.query e.val e.property (fun b =>
      seedClusterRevealTree rank S (insert e.val R) (finiteRevealPattern H e.val b))
termination_by Fintype.card G.edgeSet - R.card
decreasing_by exact remaining_card_insert_lt _ _ (seedClusterSelect G rank S R H hR).property

end
end PottsContinuity.BD12
