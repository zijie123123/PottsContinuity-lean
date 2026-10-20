/- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
accessible (see `related_formalizations` in formalization.yaml): file
`FiniteFK/GeneralRectangleDualBottomCollarConfiguration.lean`.
Adaptation: namespace/import relocation; reuse existing PD/BD12 carriers.
Independent interior edge probability and every real q>=1 (PD.FK.Parameters).
No upper bound q<4 is used in this finite proof. -/
module

public import PottsContinuity.PlanarMixed.Square.GeneralRectangleDualBottomCollarRestriction
public import PottsContinuity.PD.Duality.FiniteDuality
public import PottsContinuity.PlanarMixed.Square.PMFConditioningEquiv
public import PottsContinuity.PD.FK.ConditionalEmbeddedLaw
public import PottsContinuity.PlanarMixed.Square.Extras
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Maps

@[expose] public section

namespace PottsContinuity.PlanarMixed.Square
open PD.FK PD.FK.Medial PD.Duality BD12
open scoped PottsContinuity.PlanarMixed.Square

open PD.FK PD.FK.Medial

noncomputable section

local instance genDualCollarConfigPrimalOuterEdgeDecidableEq
    (a : LatticeVertex) (w h : ℕ) :
    DecidableEq (rectangleArbitraryBottomCollarOuterGraph a w h).edgeSet := Classical.decEq _
local instance genDualCollarConfigDualOuterEdgeDecidableEq
    (a : LatticeVertex) (w h : ℕ) :
    DecidableEq (generalRectangleDualBottomCollarOuterGraph a w h).edgeSet := Classical.decEq _
local instance genDualCollarConfigPrimalInnerEdgeDecidableEq
    (a : LatticeVertex) (w h : ℕ) :
    DecidableEq (rectangleArbitraryBottomCollarInnerGraph a w h).edgeSet := Classical.decEq _
local instance genDualCollarConfigDualInnerEdgeDecidableEq
    (a : LatticeVertex) (w h : ℕ) :
    DecidableEq (generalRectangleDualBottomCollarInnerGraph a w h).edgeSet := Classical.decEq _

 def generalRectangleDualBottomCollarInnerPrimalCarrier
    (a : LatticeVertex) (w h : ℕ)
    (A : Configuration (rectangleArbitraryBottomCollarInnerGraph a w h)) :
    Finset (rectanglePrimalEdgeCarrier a w h) := by
  change Finset (rectangleArbitraryBottomCollarInnerGraph a w h).edgeSet
  exact A

theorem generalRectangleDualBottomCollar_primalMap_le
    (a : LatticeVertex) (w h : ℕ) :
    (rectangleArbitraryBottomCollarInnerGraph a w h).map
      (rectangleArbitraryBottomCollarEmbedding a w h) ≤
      rectangleArbitraryBottomCollarOuterGraph a w h := by
  intro u v huv
  rcases (SimpleGraph.map_adj _ _ _ _).mp huv with ⟨x, y, hxy, hxu, hyv⟩
  have hsquare : squareLattice.Adj x.val y.val :=
    (rectangleGraph_adj_iff _ _ _ _ _).mp hxy
  have hx : x.val = u.val := congrArg Subtype.val hxu
  have hy : y.val = v.val := congrArg Subtype.val hyv
  exact (rectangleGraph_adj_iff _ _ _ _ _).mpr (by simpa [hx, hy] using hsquare)

theorem generalRectangleDualBottomCollar_dualMap_le
    (a : LatticeVertex) (w h : ℕ) :
    (generalRectangleDualBottomCollarInnerGraph a w h).map
      (generalRectangleDualBottomCollar_vertexEmbedding a w h) ≤
      generalRectangleDualBottomCollarOuterGraph a w h := by
  rw [← generalRectangleDualBottomCollar_remainingGraph_eq_map_inner]
  exact edgeRestriction_le _ _

private theorem generalRectanglePrimalDualConfiguration_eq_carrier
    (a : LatticeVertex) (w h : ℕ)
    (A : Configuration (rectangleGraph a w h)) :
    rectanglePrimalDualConfigurationEquiv a w h A = rectangleDualConfiguration a w h A := by
  rw [rectanglePrimalDualConfigurationEquiv_apply]
  rfl

/-- Restricting the true outer dual configuration to the mapped inner dual
graph agrees exactly with dualizing the actual restricted primal state. -/
theorem generalRectangleDualBottomCollar_primalDual_restriction_square
    (a : LatticeVertex) (w h : ℕ)
    (A : Configuration (rectangleArbitraryBottomCollarOuterGraph a w h)) :
    embeddedConfigurationRestriction
        (generalRectangleDualBottomCollarInnerGraph a w h)
        (generalRectangleDualBottomCollarOuterGraph a w h)
        (generalRectangleDualBottomCollar_vertexEmbedding a w h)
        (generalRectangleDualBottomCollar_dualMap_le a w h)
        (rectanglePrimalDualConfigurationEquiv (a.1, a.2 - 1) w (h + 1) A) =
      rectanglePrimalDualConfigurationEquiv a w h
        (embeddedConfigurationRestriction
          (rectangleArbitraryBottomCollarInnerGraph a w h)
          (rectangleArbitraryBottomCollarOuterGraph a w h)
          (rectangleArbitraryBottomCollarEmbedding a w h)
          (generalRectangleDualBottomCollar_primalMap_le a w h) A) := by
  classical
  ext d
  rw [generalRectanglePrimalDualConfiguration_eq_carrier,
      generalRectanglePrimalDualConfiguration_eq_carrier]
  have hdualEdge (d : (generalRectangleDualBottomCollarInnerGraph a w h).edgeSet) :
      rectangleDualGraphEdgeEquiv (a.1, a.2 - 1) w (h + 1)
          (generalRectangleDualBottomCollar_dualEdgeEmbedding a w h
            ((rectangleDualGraphEdgeEquiv a w h).symm d)) =
        embeddedEdgeEmbedding (generalRectangleDualBottomCollarInnerGraph a w h)
          (generalRectangleDualBottomCollarOuterGraph a w h)
          (generalRectangleDualBottomCollar_vertexEmbedding a w h)
          (generalRectangleDualBottomCollar_dualMap_le a w h) d := by
    apply Subtype.ext
    change rectangleDualCarrierPair _ _ _ _ = _
    rw [generalRectangleDualBottomCollar_dualEdgeEmbedding_pair,
      embeddedEdgeEmbedding_coe]
    have hpair : rectangleDualCarrierPair a w h
        ((rectangleDualGraphEdgeEquiv a w h).symm d) = d.val := by
      exact congrArg Subtype.val (Equiv.apply_symm_apply (rectangleDualGraphEdgeEquiv a w h) d)
    rw [hpair]
    rfl
  have hprimalEdge (e : (rectangleArbitraryBottomCollarInnerGraph a w h).edgeSet) :
      generalRectangleDualBottomCollar_primalEdgeEmbedding a w h e =
        embeddedEdgeEmbedding (rectangleArbitraryBottomCollarInnerGraph a w h)
          (rectangleArbitraryBottomCollarOuterGraph a w h)
          (rectangleArbitraryBottomCollarEmbedding a w h)
          (generalRectangleDualBottomCollar_primalMap_le a w h) e := by
    apply Subtype.ext
    rfl
  rw [mem_embeddedConfigurationRestriction, ← hdualEdge d]
  rw [mem_rectangleDualConfiguration (a.1, a.2 - 1) w (h + 1) A
    (generalRectangleDualBottomCollar_dualEdgeEmbedding a w h
      ((rectangleDualGraphEdgeEquiv a w h).symm d))]
  have hrhs : d ∈ rectangleDualConfiguration a w h
      (embeddedConfigurationRestriction
        (rectangleArbitraryBottomCollarInnerGraph a w h)
        (rectangleArbitraryBottomCollarOuterGraph a w h)
        (rectangleArbitraryBottomCollarEmbedding a w h)
        (generalRectangleDualBottomCollar_primalMap_le a w h) A) ↔
      ((rectangleDualGraphEdgeEquiv a w h).symm d).primalEdge ∉
        generalRectangleDualBottomCollarInnerPrimalCarrier a w h
          (embeddedConfigurationRestriction
            (rectangleArbitraryBottomCollarInnerGraph a w h)
            (rectangleArbitraryBottomCollarOuterGraph a w h)
            (rectangleArbitraryBottomCollarEmbedding a w h)
            (generalRectangleDualBottomCollar_primalMap_le a w h) A) := by
    rw [← Equiv.apply_symm_apply (rectangleDualGraphEdgeEquiv a w h) d]
    simpa only [Equiv.symm_apply_apply, generalRectangleDualBottomCollarInnerPrimalCarrier,
      Function.id_def] using
      (mem_rectangleDualConfiguration a w h
        (generalRectangleDualBottomCollarInnerPrimalCarrier a w h
          (embeddedConfigurationRestriction
            (rectangleArbitraryBottomCollarInnerGraph a w h)
            (rectangleArbitraryBottomCollarOuterGraph a w h)
            (rectangleArbitraryBottomCollarEmbedding a w h)
            (generalRectangleDualBottomCollar_primalMap_le a w h) A))
        ((rectangleDualGraphEdgeEquiv a w h).symm d))
  rw [hrhs]
  simp only [generalRectangleDualBottomCollar_dualEdgeEmbedding_primalEdge]
  rw [hprimalEdge ((rectangleDualGraphEdgeEquiv a w h).symm d).primalEdge]
  exact (not_congr (mem_embeddedConfigurationRestriction
    (rectangleArbitraryBottomCollarInnerGraph a w h)
    (rectangleArbitraryBottomCollarOuterGraph a w h)
    (rectangleArbitraryBottomCollarEmbedding a w h)
    (generalRectangleDualBottomCollar_primalMap_le a w h) A
    ((rectangleDualGraphEdgeEquiv a w h).symm d).primalEdge)).symm

 def generalRectangleDualBottomCollarOuterConfigurationCarrier
    (a : LatticeVertex) (w h : ℕ)
    (A : Configuration (rectangleArbitraryBottomCollarOuterGraph a w h)) :
    Finset (rectanglePrimalEdgeCarrier (a.1, a.2 - 1) w (h + 1)) := by
  change Finset (rectangleArbitraryBottomCollarOuterGraph a w h).edgeSet
  exact A

def generalRectangleDualBottomCollarClosedState (a : LatticeVertex) (w h : ℕ) :
    RemovedConfiguration (generalRectangleDualBottomCollarOuterGraph a w h)
      (generalRectangleDualBottomCollarRemovedDualEdges a w h) :=
  ⟨∅, Finset.empty_subset _⟩

/-- The original primal collar state is frozen exactly when the true outer
dual configuration is frozen to the all-closed dual collar state. -/
theorem generalRectangleDualBottomCollar_collar_event
    (a : LatticeVertex) (w h : ℕ)
    (A : Configuration (rectangleArbitraryBottomCollarOuterGraph a w h)) :
    A ∈ frozenStateEvent (rectangleArbitraryBottomCollarRemoved a w h)
        (rectangleArbitraryBottomCollarState a w h) ↔
      rectanglePrimalDualConfigurationEquiv (a.1, a.2 - 1) w (h + 1) A ∈
        frozenStateEvent (generalRectangleDualBottomCollarRemovedDualEdges a w h)
          (generalRectangleDualBottomCollarClosedState a w h) := by
  classical
  simp only [frozenStateEvent, rectangleArbitraryBottomCollarState,
    generalRectangleDualBottomCollarClosedState, Set.mem_ofPred_eq]
  rw [generalRectanglePrimalDualConfiguration_eq_carrier]
  change A ∩ rectangleArbitraryBottomCollarRemoved a w h =
      rectangleArbitraryBottomCollarRemoved a w h ↔
    rectangleDualConfiguration (a.1, a.2 - 1) w (h + 1)
      (generalRectangleDualBottomCollarOuterConfigurationCarrier a w h A) ∩
        generalRectangleDualBottomCollarRemovedDualEdges a w h = ∅
  constructor
  · intro hA
    apply Finset.ext
    intro g
    simp only [Finset.mem_inter, Finset.notMem_empty]
    constructor
    · rintro ⟨hgA, hgD⟩
      let e := (rectangleDualGraphEdgeEquiv (a.1, a.2 - 1) w (h + 1)).symm g
      have hgEq : rectangleDualGraphEdgeEquiv (a.1, a.2 - 1) w (h + 1) e = g :=
        Equiv.apply_symm_apply _ _
      have hremoved : generalRectangleDualBottomCollarPrimalEdgeAsGraphEdge a w h
          e.primalEdge ∈ rectangleArbitraryBottomCollarRemoved a w h := by
        apply (generalRectangleDualBottomCollar_removedDual_mem_iff a w h e).mp
        rw [hgEq]
        exact hgD
      have hA' : generalRectangleDualBottomCollarPrimalEdgeAsGraphEdge a w h
          e.primalEdge ∈ A := by
        have hsub : rectangleArbitraryBottomCollarRemoved a w h ⊆ A := by
          intro x hx
          have hx' : x ∈ A ∩ rectangleArbitraryBottomCollarRemoved a w h := by
            rw [hA]
            exact hx
          exact (Finset.mem_inter.mp hx').1
        exact hsub hremoved
      have hdualA : rectangleDualGraphEdgeEquiv (a.1, a.2 - 1) w (h + 1) e ∈
          rectangleDualConfiguration (a.1, a.2 - 1) w (h + 1)
            (generalRectangleDualBottomCollarOuterConfigurationCarrier a w h A) := by
        rw [hgEq]
        exact hgA
      have hclosed := (mem_rectangleDualConfiguration _ _ _ _ e).mp hdualA
      have hA'' : e.primalEdge ∈
          generalRectangleDualBottomCollarOuterConfigurationCarrier a w h A := by
        change e.primalEdge ∈ A
        exact hA'
      exact hclosed hA''
    · intro hfalse
      exact False.elim hfalse
  · intro hD
    have hsub : rectangleArbitraryBottomCollarRemoved a w h ⊆ A := by
      intro x hx
      by_contra hnot
      let e : rectanglePrimalEdgeCarrier (a.1, a.2 - 1) w (h + 1) := x
      let d := rectanglePrimalDualEdgeEquiv (a.1, a.2 - 1) w (h + 1) e
      have hremoved : generalRectangleDualBottomCollarPrimalEdgeAsGraphEdge a w h e ∈
          rectangleArbitraryBottomCollarRemoved a w h := by
        change x ∈ rectangleArbitraryBottomCollarRemoved a w h
        exact hx
      have hdualD : rectangleDualGraphEdgeEquiv (a.1, a.2 - 1) w (h + 1) d ∈
          generalRectangleDualBottomCollarRemovedDualEdges a w h :=
        (generalRectangleDualBottomCollar_removedDual_mem_iff a w h d).mpr hremoved
      have hdualA : rectangleDualGraphEdgeEquiv (a.1, a.2 - 1) w (h + 1) d ∈
          rectangleDualConfiguration (a.1, a.2 - 1) w (h + 1)
            (generalRectangleDualBottomCollarOuterConfigurationCarrier a w h A) := by
        apply (mem_rectangleDualConfiguration _ _ _ _ d).2
        change e ∉ A
        exact hnot
      have hcontra : rectangleDualGraphEdgeEquiv (a.1, a.2 - 1) w (h + 1) d ∈
          rectangleDualConfiguration (a.1, a.2 - 1) w (h + 1)
            (generalRectangleDualBottomCollarOuterConfigurationCarrier a w h A) ∩
          generalRectangleDualBottomCollarRemovedDualEdges a w h :=
        Finset.mem_inter.mpr ⟨hdualA, hdualD⟩
      rw [hD] at hcontra
      exact Finset.notMem_empty _ hcontra
    exact Finset.ext_iff.mpr (fun x => by
      simp only [Finset.mem_inter]
      constructor
      · rintro ⟨hxA, hxR⟩
        exact hxR
      · intro hxR
        exact ⟨hsub hxR, hxR⟩)

end
end PottsContinuity.PlanarMixed.Square
