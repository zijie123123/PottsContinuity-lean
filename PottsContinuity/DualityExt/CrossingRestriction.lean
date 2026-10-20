module

public import PottsContinuity.DualityExt.RectangleResults
public import PottsContinuity.PD.FK.SubgraphComparison
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Maps

/-!
# Local crossing duality inside a larger rectangular volume

The crossing event uses only the edges of its test rectangle. This module
transports the deterministic complement identity to configurations on any
larger rectangular host graph containing that rectangle. The ambient boundary
condition is not part of this event identity.
-/

@[expose] public section

namespace PottsContinuity.DualityExt

open PottsContinuity.PD.FK
open PottsContinuity.PD.FK.Medial

/-- The vertex inclusion induced by containment of lattice rectangles. -/
def rectangleVertexEmbedding {a b : LatticeVertex} {w h w' h' : ℕ}
    (hrect : latticeRectangle a w h ⊆ latticeRectangle b w' h') :
    RectangleVertex a w h ↪ RectangleVertex b w' h' where
  toFun v := ⟨v.1, hrect v.2⟩
  inj' := by
    intro x y hxy
    apply Subtype.ext
    change x.1 = y.1
    exact congrArg (fun z : RectangleVertex b w' h' => z.1) hxy

/-- The induced inner graph embeds as an actual subgraph of the host rectangle. -/
theorem rectangleGraph_map_rectangleVertexEmbedding
    {a b : LatticeVertex} {w h w' h' : ℕ}
    (hrect : latticeRectangle a w h ⊆ latticeRectangle b w' h') :
    (rectangleGraph a w h).map (rectangleVertexEmbedding hrect) ≤
      rectangleGraph b w' h' := by
  intro x y hxy
  rw [SimpleGraph.map_adj] at hxy
  rcases hxy with ⟨u, v, huv, rfl, rfl⟩
  exact (rectangleGraph_adj_iff b w' h' _ _).2
    ((rectangleGraph_adj_iff a w h _ _).1 huv)

/-- Restrict a host configuration to the actual edges of its contained test
rectangle. -/
noncomputable def rectangleConfigurationRestriction {a b : LatticeVertex} {w h w' h' : ℕ}
    (hrect : latticeRectangle a w h ⊆ latticeRectangle b w' h') :
    Configuration (rectangleGraph b w' h') → Configuration (rectangleGraph a w h) :=
  embeddedConfigurationRestriction (rectangleGraph a w h) (rectangleGraph b w' h')
    (rectangleVertexEmbedding hrect) (rectangleGraph_map_rectangleVertexEmbedding hrect)

/-- The host event that the restricted configuration has an actual horizontal
crossing of the inner rectangle. -/
def rectangleInnerHorizontalCrossingEvent {a b : LatticeVertex}
    {w h w' h' : ℕ}
    (hrect : latticeRectangle a w h ⊆ latticeRectangle b w' h') :
    Set (Configuration (rectangleGraph b w' h')) :=
  {A | rectangleConfigurationRestriction hrect A ∈
    PottsContinuity.PD.FK.rectangleHorizontalCrossingEvent a w h}

end PottsContinuity.DualityExt
