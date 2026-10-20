module

public import PottsContinuity.PlanarMixed.ClippedCutCarrier
public import PottsContinuity.PlanarMixed.CutExteriorReveals
public import PottsContinuity.PlanarMixed.FiniteSlit.RectangleClipping

/-! Literal one-sided source reveals, with the missing slit bonds and the
host exterior included separately. -/

@[expose] public section

namespace PottsContinuity.PlanarMixed.FiniteSlit
open PD.FK
noncomputable section
local instance clippedRevealsEdgeDecidableEq {U : Type*} (G : SimpleGraph U) :
    DecidableEq G.edgeSet := Classical.decEq _

namespace CrosscutData
variable {M : ℕ} {x y : ℤ} (D : CrosscutData M x y)
  {W U : Type*} [Finite W] [Finite U]

/-- The clipped left exterior depends only on the first original trace. -/
def clippedFirstReveal (S : SimpleGraph W) (f : W ↪ Vertex M x) : Configuration S :=
  internalBonds S {u | f u ∈ closedCutExterior (graph M x y)
    {w | w ∈ D.first.support} (alpha M x)}

/-- The clipped right exterior depends only on the second original trace. -/
def clippedSecondReveal (S : SimpleGraph W) (f : W ↪ Vertex M x) : Configuration S :=
  internalBonds S {u | f u ∈ closedCutExterior (graph M x y)
    {w | w ∈ D.second.support} (beta M x y)}

/-- The two closed exteriors are precisely the reference rank reveal read
on source vertices; source bonds need not belong to the reference graph. -/
theorem clipped_outer_reveal_eq (hM : 2 ≤ M) (hy : 0 < y)
    (S : SimpleGraph W) (f : W ↪ Vertex M x) :
    outerCutReveal S (D.rank hM hy ∘ f) =
      D.clippedFirstReveal S f ∪ D.clippedSecondReveal S f := by
  classical
  have hL : {u | D.rank hM hy (f u) ≤ 1} =
      {u | f u ∈ closedCutExterior (graph M x y) {w | w ∈ D.first.support} (alpha M x)} :=
    Set.ext (fun u => orderedCutRank_le_one_iff_exterior (D.orderedCuts hM hy) (f u))
  have hR : {u | 3 ≤ D.rank hM hy (f u)} =
      {u | f u ∈ closedCutExterior (graph M x y) {w | w ∈ D.second.support} (beta M x y)} :=
    Set.ext (fun u => orderedCutRank_three_le_iff_exterior (D.orderedCuts hM hy) (f u))
  unfold outerCutReveal
  simp only [Function.comp_apply]
  rw [hL,hR]
  apply Finset.ext
  intro e
  simp only [clippedFirstReveal,clippedSecondReveal,Finset.mem_union]

/-- Prescribed source exploration carrier: outside the source, missing
reference bonds inside the source, and the two independent closed exteriors. -/
def clippedHostReveal (S : SimpleGraph W) (H : SimpleGraph U)
    (j : W ↪ U) (hSH : S.map j ≤ H) (f : W ↪ Vertex M x) : Configuration H :=
  subgraphRemovedEdges (S.map j) H ∪ embeddedConfigurationEmbedding S H j hSH
    (subgraphRemovedEdges ((graph M x y).comap f) S ∪
      (D.clippedFirstReveal S f ∪ D.clippedSecondReveal S f))

end CrosscutData
end
end PottsContinuity.PlanarMixed.FiniteSlit
