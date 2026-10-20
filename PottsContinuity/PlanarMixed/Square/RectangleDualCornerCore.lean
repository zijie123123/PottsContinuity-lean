/- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
accessible (see `related_formalizations` in formalization.yaml): file
`FiniteFK/RectangleDualCornerCore.lean`.
Adaptation: namespace/import relocation; reuse existing PD/BD12 carriers.
Independent interior edge probability and every real q>=1 (PD.FK.Parameters).
No upper bound q<4 is used in this finite proof. -/
module

public import PottsContinuity.PD.Duality.RectangleDualAmbient
public import PottsContinuity.PD.FK.SubgraphComparison
public import PottsContinuity.PlanarMixed.Square.Extras
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Maps

@[expose] public section

namespace PottsContinuity.PlanarMixed.Square
open PD.FK PD.FK.Medial PD.Duality BD12
open scoped PottsContinuity.PlanarMixed.Square

open PD.FK PD.FK.Medial
noncomputable section

def rectangleDualCornerCoreEmbedding (a : LatticeVertex) (w h : ℕ) :
    RectangleVertex a w h ↪ RectangleDualVertex a w h where
  toFun v := ⟨v.1, by
    have hv := v.2
    rw [mem_latticeRectangle] at hv
    change v.1 ∈ rectangleDualExpanded a w h
    rw [rectangleDualExpanded, mem_latticeRectangle]
    rcases hv with ⟨hx, hy⟩
    constructor
    · constructor <;> omega
    · constructor <;> omega⟩
  inj' := by
    intro u v huv
    apply Subtype.ext
    exact congrArg (fun z : RectangleDualVertex a w h => z.1) huv

def rectangleDualCornerCoreGraph (a : LatticeVertex) (w h : ℕ) :
    SimpleGraph (RectangleVertex a w h) :=
  SimpleGraph.comap (rectangleDualCornerCoreEmbedding a w h)
    (rectangleDualGraph a w h)

theorem rectangleDualCornerCoreGraph_map_le_dual (a : LatticeVertex) (w h : ℕ) :
    (rectangleDualCornerCoreGraph a w h).map
      (rectangleDualCornerCoreEmbedding a w h) ≤ rectangleDualGraph a w h := by
  intro u v huv
  obtain ⟨x, y, hxy, rfl, rfl⟩ := (SimpleGraph.map_adj _ _ _ _).mp huv
  change (rectangleDualGraph a w h).Adj
    (rectangleDualCornerCoreEmbedding a w h x)
    (rectangleDualCornerCoreEmbedding a w h y) at hxy
  exact hxy

theorem rectangleDualCornerCoreGraph_le_rectangle (a : LatticeVertex) (w h : ℕ) :
    rectangleDualCornerCoreGraph a w h ≤ rectangleGraph a w h := by
  intro u v huv
  change (rectangleDualGraph a w h).Adj
    (rectangleDualCornerCoreEmbedding a w h u)
    (rectangleDualCornerCoreEmbedding a w h v) at huv
  have hd : (rectangleDualGraph a w h).Adj
      (rectangleDualCornerCoreEmbedding a w h u)
      (rectangleDualCornerCoreEmbedding a w h v) := huv
  have hamb := (rectangleDualGraph_le_ambient a w h) hd
  have hsq0 : squareLattice.Adj
      (rectangleDualCornerCoreEmbedding a w h u).1
      (rectangleDualCornerCoreEmbedding a w h v).1 :=
    (rectangleDualAmbientGraph_adj_iff a w h _ _).mp hamb
  have hsq : squareLattice.Adj u.1 v.1 := by
    change squareLattice.Adj u.1 v.1 at hsq0
    exact hsq0
  exact (rectangleGraph_adj_iff a w h u v).2 hsq

def rectangleDualCornerCoreConfigurationRestriction (a : LatticeVertex) (w h : ℕ)
    (A : Configuration (rectangleDualGraph a w h)) :
    Configuration (rectangleDualCornerCoreGraph a w h) :=
  embeddedConfigurationRestriction
    (rectangleDualCornerCoreGraph a w h) (rectangleDualGraph a w h)
    (rectangleDualCornerCoreEmbedding a w h)
    (rectangleDualCornerCoreGraph_map_le_dual a w h) A

@[simp] theorem mem_rectangleDualCornerCoreConfigurationRestriction
    (a : LatticeVertex) (w h : ℕ)
    (A : Configuration (rectangleDualGraph a w h))
    (e : (rectangleDualCornerCoreGraph a w h).edgeSet) :
    e ∈ rectangleDualCornerCoreConfigurationRestriction a w h A ↔
      embeddedEdgeEmbedding (rectangleDualCornerCoreGraph a w h)
        (rectangleDualGraph a w h) (rectangleDualCornerCoreEmbedding a w h)
        (rectangleDualCornerCoreGraph_map_le_dual a w h) e ∈ A := by
  exact mem_embeddedConfigurationRestriction
    (rectangleDualCornerCoreGraph a w h) (rectangleDualGraph a w h)
    (rectangleDualCornerCoreEmbedding a w h)
    (rectangleDualCornerCoreGraph_map_le_dual a w h) A e

end
end PottsContinuity.PlanarMixed.Square
