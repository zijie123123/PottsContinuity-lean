/- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
accessible (see `related_formalizations` in formalization.yaml): file
`FiniteFK/RectangleDoubleCollarDualConfiguration.lean`.
Adaptation: namespace/import relocation; reuse existing PD/BD12 carriers.
Independent interior edge probability and every real q>=1 (PD.FK.Parameters).
No upper bound q<4 is used in this finite proof. -/
module

public import PottsContinuity.PlanarMixed.Square.RectangleDoubleCollarDualRemaining
public import PottsContinuity.PD.Duality.FiniteDuality
public import PottsContinuity.PD.FK.DomainMarkov
public import PottsContinuity.PlanarMixed.Square.Extras
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Maps

@[expose] public section

namespace PottsContinuity.PlanarMixed.Square
open PD.FK PD.FK.Medial PD.Duality BD12
open scoped PottsContinuity.PlanarMixed.Square

open PD.FK PD.FK.Medial

noncomputable section

local instance rectangleDoubleCollarDualConfigurationOuterPrimalEdgeDecidableEq
    (a : LatticeVertex) (w h : ℕ) :
    DecidableEq (rectangleDoubleCollarOuterGraph a w h).edgeSet := Classical.decEq _

local instance rectangleDoubleCollarDualConfigurationOuterDualEdgeDecidableEq
    (a : LatticeVertex) (w h : ℕ) :
    DecidableEq (rectangleDoubleCollarDualOuterGraph a w h).edgeSet := Classical.decEq _

local instance rectangleDoubleCollarDualConfigurationInnerPrimalEdgeDecidableEq
    (a : LatticeVertex) (w h : ℕ) :
    DecidableEq (rectangleDoubleCollarInnerGraph a w h).edgeSet := Classical.decEq _

local instance rectangleDoubleCollarDualConfigurationInnerDualEdgeDecidableEq
    (a : LatticeVertex) (w h : ℕ) :
    DecidableEq (rectangleDoubleCollarDualInnerGraph a w h).edgeSet := Classical.decEq _

def rectangleDoubleCollarInnerPrimalConfigurationCarrier
    (a : LatticeVertex) (w h : ℕ)
    (A : Configuration (rectangleDoubleCollarInnerGraph a w h)) :
    Finset (rectanglePrimalEdgeCarrier a w h) := by
  change Finset (rectangleDoubleCollarInnerGraph a w h).edgeSet
  exact A

theorem rectangleDoubleCollarPrimalDualConfiguration_eq_carrier
    (a : LatticeVertex) (w h : ℕ)
    (A : Configuration (rectangleGraph a w h)) :
    rectanglePrimalDualConfigurationEquiv a w h A =
      rectangleDualConfiguration a w h A := by
  rw [rectanglePrimalDualConfigurationEquiv_apply]
  rfl

theorem rectangleDoubleCollarInnerPrimalEdges_mem_iff_graph
    (a : LatticeVertex) (w h : ℕ)
    (e : rectanglePrimalEdgeCarrier (a.1, a.2 - 1) w (h + 2)) :
    e ∈ rectangleDoubleCollarInnerPrimalEdges a w h ↔
      e.val ∈ ((rectangleDoubleCollarInnerGraph a w h).map
        (rectangleDoubleCollarEmbedding a w h)).edgeSet := by
  rw [SimpleGraph.edgeSet_map]
  change e ∈ rectangleDoubleCollarInnerPrimalEdges a w h ↔
    e.val ∈ (rectangleDoubleCollarEmbedding a w h).sym2Map ''
      (rectangleDoubleCollarInnerGraph a w h).edgeSet
  constructor
  · intro he
    rcases (rectangleDoubleCollarInnerPrimalEdges_mem_iff_embedding a w h e).mp he
      with ⟨f, hf⟩
    refine ⟨f.val, f.property, ?_⟩
    exact congrArg Subtype.val hf
  · rintro ⟨f, hf, hpair⟩
    let fI : rectanglePrimalEdgeCarrier a w h := ⟨f, hf⟩
    have hEdge : rectangleDoubleCollarPrimalEdgeEmbedding a w h fI = e := by
      apply Subtype.ext
      change (rectangleDoubleCollarEmbedding a w h).sym2Map f = e.val
      exact hpair
    exact (rectangleDoubleCollarInnerPrimalEdges_mem_iff_embedding a w h e).mpr
      ⟨fI, hEdge⟩

theorem rectangleDoubleCollar_primalDual_restriction_square
    (a : LatticeVertex) (w h : ℕ)
    (A : Configuration (rectangleDoubleCollarOuterGraph a w h)) :
    embeddedConfigurationRestriction
        (rectangleDoubleCollarDualInnerGraph a w h)
        (rectangleDoubleCollarDualOuterGraph a w h)
        (rectangleDoubleCollarDual_vertexEmbedding a w h)
        (rectangleDoubleCollarDual_map_le a w h)
        (rectanglePrimalDualConfigurationEquiv (a.1, a.2 - 1) w (h + 2) A) =
      rectanglePrimalDualConfigurationEquiv a w h
        (embeddedConfigurationRestriction
          (rectangleDoubleCollarInnerGraph a w h)
          (rectangleDoubleCollarOuterGraph a w h)
          (rectangleDoubleCollarEmbedding a w h)
          (rectangleDoubleCollar_map_le a w h) A) := by
  classical
  ext d
  rw [rectangleDoubleCollarPrimalDualConfiguration_eq_carrier,
      rectangleDoubleCollarPrimalDualConfiguration_eq_carrier]
  have hdualEdge (d : (rectangleDoubleCollarDualInnerGraph a w h).edgeSet) :
      rectangleDualGraphEdgeEquiv (a.1, a.2 - 1) w (h + 2)
          (rectangleDoubleCollarDualEdgeEmbedding a w h
            ((rectangleDualGraphEdgeEquiv a w h).symm d)) =
        embeddedEdgeEmbedding (rectangleDoubleCollarDualInnerGraph a w h)
          (rectangleDoubleCollarDualOuterGraph a w h)
          (rectangleDoubleCollarDual_vertexEmbedding a w h)
          (rectangleDoubleCollarDual_map_le a w h) d := by
    apply Subtype.ext
    change rectangleDualCarrierPair _ _ _ _ = _
    rw [rectangleDoubleCollarDualEdgeEmbedding_pair, embeddedEdgeEmbedding_coe]
    have hpair : rectangleDualCarrierPair a w h
        ((rectangleDualGraphEdgeEquiv a w h).symm d) = d.val := by
      exact congrArg Subtype.val (Equiv.apply_symm_apply (rectangleDualGraphEdgeEquiv a w h) d)
    rw [hpair]
    rfl
  have hprimalEdge (e : (rectangleDoubleCollarInnerGraph a w h).edgeSet) :
      rectangleDoubleCollarPrimalEdgeEmbedding a w h e =
        embeddedEdgeEmbedding (rectangleDoubleCollarInnerGraph a w h)
          (rectangleDoubleCollarOuterGraph a w h)
          (rectangleDoubleCollarEmbedding a w h)
          (rectangleDoubleCollar_map_le a w h) e := by
    apply Subtype.ext
    rfl
  rw [mem_embeddedConfigurationRestriction, ← hdualEdge d]
  rw [mem_rectangleDualConfiguration (a.1, a.2 - 1) w (h + 2) A
    (rectangleDoubleCollarDualEdgeEmbedding a w h
      ((rectangleDualGraphEdgeEquiv a w h).symm d))]
  have hrhs : d ∈ rectangleDualConfiguration a w h
      (embeddedConfigurationRestriction
        (rectangleDoubleCollarInnerGraph a w h)
        (rectangleDoubleCollarOuterGraph a w h)
        (rectangleDoubleCollarEmbedding a w h)
        (rectangleDoubleCollar_map_le a w h) A) ↔
      ((rectangleDualGraphEdgeEquiv a w h).symm d).primalEdge ∉
        rectangleDoubleCollarInnerPrimalConfigurationCarrier a w h
          (embeddedConfigurationRestriction
          (rectangleDoubleCollarInnerGraph a w h)
          (rectangleDoubleCollarOuterGraph a w h)
          (rectangleDoubleCollarEmbedding a w h)
          (rectangleDoubleCollar_map_le a w h) A) := by
    rw [← Equiv.apply_symm_apply (rectangleDualGraphEdgeEquiv a w h) d]
    simpa only [Equiv.apply_symm_apply,
      rectangleDoubleCollarInnerPrimalConfigurationCarrier, Function.id_def] using
      (mem_rectangleDualConfiguration a w h
        (rectangleDoubleCollarInnerPrimalConfigurationCarrier a w h
          (embeddedConfigurationRestriction
            (rectangleDoubleCollarInnerGraph a w h)
            (rectangleDoubleCollarOuterGraph a w h)
            (rectangleDoubleCollarEmbedding a w h)
            (rectangleDoubleCollar_map_le a w h) A))
        ((rectangleDualGraphEdgeEquiv a w h).symm d))
  rw [hrhs]
  rw [rectangleDoubleCollarDualEdgeEmbedding_primalEdge]
  rw [hprimalEdge ((rectangleDualGraphEdgeEquiv a w h).symm d).primalEdge]
  exact (not_congr (mem_embeddedConfigurationRestriction
    (rectangleDoubleCollarInnerGraph a w h)
    (rectangleDoubleCollarOuterGraph a w h)
    (rectangleDoubleCollarEmbedding a w h)
    (rectangleDoubleCollar_map_le a w h) A
    ((rectangleDualGraphEdgeEquiv a w h).symm d).primalEdge)).symm

def rectangleDoubleCollarPrimalEdgeAsGraphEdge (a : LatticeVertex) (w h : ℕ)
    (e : rectanglePrimalEdgeCarrier (a.1, a.2 - 1) w (h + 2)) :
    (rectangleDoubleCollarOuterGraph a w h).edgeSet := ⟨e.val, e.property⟩

theorem rectangleDoubleCollar_dual_pair_open_iff_primalRemoved
    (a : LatticeVertex) (w h : ℕ)
    (e : RectangleDualEdgeCarrier (a.1, a.2 - 1) w (h + 2)) :
    rectangleDualCarrierPair (a.1, a.2 - 1) w (h + 2) e ∈
      openEdges (rectangleDoubleCollarDualOuterGraph a w h)
        (rectangleDoubleCollarRemovedDualEdges a w h) ↔
      rectangleDoubleCollarPrimalEdgeAsGraphEdge a w h e.primalEdge ∈
        rectangleDoubleCollarRemoved a w h := by
  rw [rectangleDoubleCollar_pair_mem_open_iff]
  rw [rectangleDoubleCollarRemoved_mem_iff a w h
    (rectangleDoubleCollarPrimalEdgeAsGraphEdge a w h e.primalEdge)]
  change e.primalEdge ∉ rectangleDoubleCollarInnerPrimalEdges a w h ↔
    e.primalEdge.val ∉ ((rectangleDoubleCollarInnerGraph a w h).map
      (rectangleDoubleCollarEmbedding a w h)).edgeSet
  exact not_congr (rectangleDoubleCollarInnerPrimalEdges_mem_iff_graph a w h e.primalEdge)

theorem rectangleDoubleCollar_dualSelector_mem_iff_primalRemoved
    (a : LatticeVertex) (w h : ℕ)
    (e : RectangleDualEdgeCarrier (a.1, a.2 - 1) w (h + 2)) :
    rectangleDualGraphEdgeEquiv (a.1, a.2 - 1) w (h + 2) e ∈
      rectangleDoubleCollarRemovedDualEdges a w h ↔
      rectangleDoubleCollarPrimalEdgeAsGraphEdge a w h e.primalEdge ∈
        rectangleDoubleCollarRemoved a w h := by
  calc
    rectangleDualGraphEdgeEquiv (a.1, a.2 - 1) w (h + 2) e ∈
        rectangleDoubleCollarRemovedDualEdges a w h ↔
      (rectangleDualGraphEdgeEquiv (a.1, a.2 - 1) w (h + 2) e).val ∈
        openEdges (rectangleDoubleCollarDualOuterGraph a w h)
          (rectangleDoubleCollarRemovedDualEdges a w h) :=
      (coe_mem_openEdges_iff _ _ _).symm
    _ ↔ rectangleDualCarrierPair (a.1, a.2 - 1) w (h + 2) e ∈
        openEdges (rectangleDoubleCollarDualOuterGraph a w h)
          (rectangleDoubleCollarRemovedDualEdges a w h) := Iff.rfl
    _ ↔ rectangleDoubleCollarPrimalEdgeAsGraphEdge a w h e.primalEdge ∈
        rectangleDoubleCollarRemoved a w h :=
      rectangleDoubleCollar_dual_pair_open_iff_primalRemoved a w h e

def rectangleDoubleCollarDualClosedState (a : LatticeVertex) (w h : ℕ) :
    RemovedConfiguration (rectangleDoubleCollarDualOuterGraph a w h)
      (rectangleDoubleCollarRemovedDualEdges a w h) :=
  ⟨∅, Finset.empty_subset _⟩

theorem rectangleDoubleCollar_collar_event
    (a : LatticeVertex) (w h : ℕ)
    (A : Configuration (rectangleDoubleCollarOuterGraph a w h)) :
    A ∈ frozenStateEvent (rectangleDoubleCollarRemoved a w h)
        (rectangleDoubleCollarState a w h) ↔
      rectanglePrimalDualConfigurationEquiv (a.1, a.2 - 1) w (h + 2) A ∈
        frozenStateEvent (rectangleDoubleCollarRemovedDualEdges a w h)
          (rectangleDoubleCollarDualClosedState a w h) := by
  classical
  simp only [frozenStateEvent, rectangleDoubleCollarState,
    rectangleDoubleCollarDualClosedState, Set.mem_ofPred_eq]
  rw [rectangleDoubleCollarPrimalDualConfiguration_eq_carrier]
  change A ∩ rectangleDoubleCollarRemoved a w h =
      rectangleDoubleCollarRemoved a w h ↔
    rectangleDualConfiguration (a.1, a.2 - 1) w (h + 2) A ∩
      rectangleDoubleCollarRemovedDualEdges a w h = ∅
  constructor
  · intro hA
    apply Finset.ext
    intro g
    simp only [Finset.mem_inter, Finset.notMem_empty]
    constructor
    · rintro ⟨hgA, hgD⟩
      let e := (rectangleDualGraphEdgeEquiv (a.1, a.2 - 1) w (h + 2)).symm g
      have hgEq : rectangleDualGraphEdgeEquiv (a.1, a.2 - 1) w (h + 2) e = g :=
        Equiv.apply_symm_apply _ _
      have hprimalRemoved : e.primalEdge ∈ rectangleDoubleCollarRemoved a w h := by
        apply (rectangleDoubleCollar_dualSelector_mem_iff_primalRemoved a w h e).mp
        rw [hgEq]
        exact hgD
      have hprimalA : e.primalEdge ∈ A := by
        have hsub : rectangleDoubleCollarRemoved a w h ⊆ A := by
          intro x hx
          have hx' : x ∈ A ∩ rectangleDoubleCollarRemoved a w h := by
            rw [hA]
            exact hx
          exact (Finset.mem_inter.mp hx').1
        exact hsub hprimalRemoved
      have hdualA : rectangleDualGraphEdgeEquiv (a.1, a.2 - 1) w (h + 2) e ∈
          rectangleDualConfiguration (a.1, a.2 - 1) w (h + 2) A := by
        rw [hgEq]
        exact hgA
      exact (mem_rectangleDualConfiguration _ _ _ _ e).mp hdualA hprimalA
    · intro hfalse
      exact False.elim hfalse
  · intro hD
    have hsub : rectangleDoubleCollarRemoved a w h ⊆ A := by
      intro x hx
      by_contra hnot
      let e : rectanglePrimalEdgeCarrier (a.1, a.2 - 1) w (h + 2) := x
      let d := rectanglePrimalDualEdgeEquiv (a.1, a.2 - 1) w (h + 2) e
      have hdualSelector : rectangleDualGraphEdgeEquiv (a.1, a.2 - 1) w (h + 2) d ∈
          rectangleDoubleCollarRemovedDualEdges a w h := by
        exact (rectangleDoubleCollar_dualSelector_mem_iff_primalRemoved a w h d).2 hx
      have hdualA : rectangleDualGraphEdgeEquiv (a.1, a.2 - 1) w (h + 2) d ∈
          rectangleDualConfiguration (a.1, a.2 - 1) w (h + 2) A := by
        apply (mem_rectangleDualConfiguration _ _ _ _ d).2
        change e ∉ A
        exact hnot
      have hcontra := Finset.mem_inter.mpr ⟨hdualA, hdualSelector⟩
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
