/-
Extracted from the following files of FKconvergence, an earlier formalization by the same
author that is not publicly accessible (see `related_formalizations` in formalization.yaml):
`Rectangle.lean`, `FiniteFK/RectangleEvents.lean`, `FiniteFK/SubgraphComparison.lean` and
`FiniteFK/EmbeddedMarginalLaw.lean`.
Adaptation: reuse PD.FK carriers, namespace relocation, independent Parameters
for the generic finite facts. Only declarations absent from the existing PD
ports are copied. The scoped coercion below selects the explicit self-dual
parameter and makes no threshold identification.
-/
module

public import PottsContinuity.PD.Duality.FiniteDuality
public import PottsContinuity.PD.Duality.RectangleEvents
public import PottsContinuity.PD.FK.EmbeddedMarginalLaw
public import PottsContinuity.PD.FK.BoundaryPartitionLaw
public import PottsContinuity.BD12.TwoBlockBoundaryMerge
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Probability.ProbabilityMassFunction.Constructions

@[expose] public section

namespace PottsContinuity.PlanarMixed.Square
open PD.FK PD.FK.Medial PD.Duality BD12
noncomputable section

/-- In this scope only, a real q>=1 selects the explicit self-dual FK record. -/
scoped instance selfDualWeightCoe : Coe (Set.Ici (1 : ℝ)) Parameters :=
  ⟨criticalParameters⟩

def rectangleBottomSide (a : LatticeVertex) (w h : ℕ) : Finset LatticeVertex :=
  (latticeRectangle a w h).filter (fun v => v.2 = a.2)

/-- Closed top side, with both corners included. -/
def rectangleTopSide (a : LatticeVertex) (w h : ℕ) : Finset LatticeVertex :=
  (latticeRectangle a w h).filter (fun v => v.2 = a.2 + (h : ℤ))

def rectangleVertexEmbedding {a b : LatticeVertex} {w h w' h' : ℕ}
    (hrect : latticeRectangle a w h ⊆ latticeRectangle b w' h') :
    RectangleVertex a w h ↪ RectangleVertex b w' h' where
  toFun v := ⟨v.val, hrect v.property⟩
  inj' := by
    intro u v huv
    apply Subtype.ext
    exact congrArg (fun z : RectangleVertex b w' h' => z.val) huv

lemma rectangleGraph_map_rectangleVertexEmbedding {a b : LatticeVertex} {w h w' h' : ℕ}
    (hrect : latticeRectangle a w h ⊆ latticeRectangle b w' h') :
    (rectangleGraph a w h).map (rectangleVertexEmbedding hrect) ≤ rectangleGraph b w' h' := by
  intro x y hxy
  rw [SimpleGraph.map_adj] at hxy
  rcases hxy with ⟨u, v, huv, rfl, rfl⟩
  exact (rectangleGraph_adj_iff b w' h' _ _).2
    ((rectangleGraph_adj_iff a w h _ _).1 huv)

/-- The induced edge embedding retains the same unordered edge of the square lattice. -/
noncomputable def rectangleEdgeEmbedding {a b : LatticeVertex} {w h w' h' : ℕ}
    (hrect : latticeRectangle a w h ⊆ latticeRectangle b w' h') :
    (rectangleGraph a w h).edgeSet ↪ (rectangleGraph b w' h').edgeSet :=
  PD.FK.embeddedEdgeEmbedding (rectangleGraph a w h) (rectangleGraph b w' h')
    (rectangleVertexEmbedding hrect) (rectangleGraph_map_rectangleVertexEmbedding hrect)

lemma rectangleEdgeEmbedding_original {a b : LatticeVertex} {w h w' h' : ℕ}
    (hrect : latticeRectangle a w h ⊆ latticeRectangle b w' h')
    (e : (rectangleGraph a w h).edgeSet) :
    Sym2.map (fun v : RectangleVertex b w' h' => v.val)
        (rectangleEdgeEmbedding hrect e).val =
      Sym2.map (fun v : RectangleVertex a w h => v.val) e.val := by
  change Sym2.map (fun v : RectangleVertex b w' h' => v.val)
      (PD.FK.embeddedEdgeEmbedding (rectangleGraph a w h) (rectangleGraph b w' h')
        (rectangleVertexEmbedding hrect) (rectangleGraph_map_rectangleVertexEmbedding hrect) e).val = _
  rw [PD.FK.embeddedEdgeEmbedding_coe]
  change Sym2.map (fun v : RectangleVertex b w' h' => v.val)
      (Sym2.map (rectangleVertexEmbedding hrect) e.val) = _
  rw [Sym2.map_map]
  congr 1

variable (a : LatticeVertex) (w h : ℕ)
def rectangleVerticalCrossingEvent : Set (Configuration (rectangleGraph a w h)) :=
  {A | ∃ u v : RectangleVertex a w h,
    u.val ∈ rectangleBottomSide a w h ∧ v.val ∈ rectangleTopSide a w h ∧
      ActualConnected (rectangleGraph a w h) A u v}

attribute [local instance] configurationMeasurableSpace

theorem subgraphConfigurationEmbedding_restriction_subset {V : Type*}
    {G H : SimpleGraph V} (hGH : G ≤ H) (A : Configuration H) :
    subgraphConfigurationEmbedding hGH (subgraphConfigurationRestriction hGH A) ⊆ A := by
  intro e he
  obtain ⟨b, hb, rfl⟩ := Finset.mem_map.mp he
  exact (mem_subgraphConfigurationRestriction hGH A b).mp hb

variable {V W : Type*} [Finite V] [Finite W]
  (G : SimpleGraph V) (H : SimpleGraph W) (f : V ↪ W) (hGH : G.map f ≤ H)
theorem law_embeddedConfigurationRestriction_eq_of_frozen_partition
    (q : Parameters) (ξ : BoundaryCondition W) (η : BoundaryCondition V)
    (hη : ∀ K : RemovedConfiguration H (subgraphRemovedEdges (G.map f) H),
      (isolatedExtensionPullbackBoundary f
        (frozenBoundary ξ K.val)).partition = η.partition) :
    (law H q ξ).map (embeddedConfigurationRestriction G H f hGH) = law G q η := by
  rw [law_embeddedConfigurationRestriction_eq_bind_frozenMarginal]
  calc
    _ = (frozenMarginalLaw q ξ (subgraphRemovedEdges (G.map f) H)).bind
        (fun _ => law G q η) := by
          congr 1
          funext K
          exact law_eq_of_boundary_partition_eq q _ _ (hη K)
    _ = law G q η := PMF.bind_const _ _

end
end PottsContinuity.PlanarMixed.Square
