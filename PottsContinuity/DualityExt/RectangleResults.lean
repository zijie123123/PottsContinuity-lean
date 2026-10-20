module

public import PottsContinuity.PD.Duality.CrossingDuality
public import PottsContinuity.PD.Duality.FiniteDuality
public import PottsContinuity.PD.Duality.WholePlaneDualGraph
public import Mathlib.Tactic
public import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Source-facing finite planar duality interfaces

The finite graph interface below records an arbitrary finite square-lattice
subgraph by its vertices and normalized bonds. The rectangle results expose the
already proved PD crossing and FK-law identities in the form used in this
development.
-/

@[expose] public section

namespace PottsContinuity.DualityExt

open PottsContinuity.PD.Duality
open PottsContinuity.PD.FK
open PottsContinuity.PD.FK.Medial

/-- A finite square-lattice subgraph, with each unoriented unit edge represented
by its unique normalized bond. -/
structure FiniteLatticeSubgraph where
  vertexSet : Finset LatticeVertex
  edgeSet : Finset LatticeBond
  source_mem : ∀ e ∈ edgeSet, e.source ∈ vertexSet
  target_mem : ∀ e ∈ edgeSet, e.target ∈ vertexSet

/-- The bijection between a primal bond and the dual bond crossing it. -/
def primalDualBondEquiv : LatticeBond ≃ LatticeBond where
  toFun := dualBondOfPrimal
  invFun := primalBondOfDual
  left_inv := primalBondOfDual_dualBondOfPrimal
  right_inv := dualBondOfPrimal_primalBondOfDual

@[simp] theorem primalDualBondEquiv_apply (e : LatticeBond) :
    primalDualBondEquiv e = dualBondOfPrimal e := rfl

@[simp] theorem primalDualBondEquiv_symm_apply (e : LatticeBond) :
    primalDualBondEquiv.symm e = primalBondOfDual e := rfl

/-- The edge carrier of the dual graph, with each edge indexed by the unique
primal bond that it crosses. -/
def dualEdgeSet (G : FiniteLatticeSubgraph) : Finset LatticeBond :=
  G.edgeSet.map primalDualBondEquiv.toEmbedding

/-- The vertices of the dual graph are exactly the endpoints of its dual edges;
isolated vertices of the primal graph do not create dual vertices. -/
def dualVertexSet (G : FiniteLatticeSubgraph) : Finset LatticeVertex :=
  (dualEdgeSet G).image LatticeBond.source ∪
    (dualEdgeSet G).image LatticeBond.target

/-- The finite dual graph `G*`, represented by its actual dual bonds and their
endpoints. -/
def dualGraph (G : FiniteLatticeSubgraph) : FiniteLatticeSubgraph where
  vertexSet := dualVertexSet G
  edgeSet := dualEdgeSet G
  source_mem := by
    intro e he
    exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨e, he, rfl⟩)
  target_mem := by
    intro e he
    exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨e, he, rfl⟩)

@[simp] theorem dualGraph_edgeSet (G : FiniteLatticeSubgraph) :
    (dualGraph G).edgeSet = dualEdgeSet G := rfl

@[simp] theorem dualGraph_vertexSet (G : FiniteLatticeSubgraph) :
    (dualGraph G).vertexSet = dualVertexSet G := rfl

/-- The induced equivalence between primal and dual edge carriers. -/
def dualEdgeEquiv (G : FiniteLatticeSubgraph) :
    {e : LatticeBond // e ∈ G.edgeSet} ≃
      {d : LatticeBond // d ∈ dualEdgeSet G} where
  toFun e := ⟨primalDualBondEquiv e.1,
    Finset.mem_map.mpr ⟨e.1, e.2, rfl⟩⟩
  invFun d := ⟨primalDualBondEquiv.symm d.1, by
    rcases Finset.mem_map.mp d.2 with ⟨e, he, h⟩
    have hinv : primalDualBondEquiv.symm d.1 = e := by
      rw [← h]
      exact primalDualBondEquiv.symm_apply_apply e
    exact hinv ▸ he⟩
  left_inv e := by
    apply Subtype.ext
    exact primalDualBondEquiv.symm_apply_apply e.1
  right_inv d := by
    apply Subtype.ext
    exact primalDualBondEquiv.apply_symm_apply d.1

/-- A configuration on the dual graph is the complementary state on each
crossing primal bond. -/
def dualConfiguration (G : FiniteLatticeSubgraph)
    (ω : {e : LatticeBond // e ∈ G.edgeSet} → Bool) :
    (dualGraph G).edgeSet → Bool :=
  fun d => Bool.not (ω ((dualEdgeEquiv G).symm d))

/-- The complementary edge-state assignment is a bijection between finite
primal and dual configurations on every finite square-lattice subgraph. -/
noncomputable def dualConfigurationEquiv (G : FiniteLatticeSubgraph) :
    ({e : LatticeBond // e ∈ G.edgeSet} → Bool) ≃
      ({d : LatticeBond // d ∈ dualEdgeSet G} → Bool) where
  toFun ω d := Bool.not (ω ((dualEdgeEquiv G).symm d))
  invFun η e := Bool.not (η (dualEdgeEquiv G e))
  left_inv ω := by
    funext e
    simp
  right_inv η := by
    funext d
    simp

@[simp] theorem dualConfigurationEquiv_apply (G : FiniteLatticeSubgraph)
    (ω : {e : LatticeBond // e ∈ G.edgeSet} → Bool)
    (d : {d : LatticeBond // d ∈ dualEdgeSet G}) :
    dualConfigurationEquiv G ω d = dualConfiguration G ω d := rfl

@[simp] theorem dualConfigurationEquiv_apply_primalEdge (G : FiniteLatticeSubgraph)
    (ω : {e : LatticeBond // e ∈ G.edgeSet} → Bool)
    (e : {e : LatticeBond // e ∈ G.edgeSet}) :
    dualConfigurationEquiv G ω (dualEdgeEquiv G e) = Bool.not (ω e) := by
  simp [dualConfigurationEquiv]

@[simp] theorem dualConfiguration_edgeState (G : FiniteLatticeSubgraph)
    (ω : {e : LatticeBond // e ∈ G.edgeSet} → Bool)
    (e : {e : LatticeBond // e ∈ G.edgeSet}) :
    dualConfiguration G ω (dualEdgeEquiv G e) = Bool.not (ω e) := by
  simp [dualConfiguration]

/-- The free finite-volume rectangle law maps to the wired dual law at the
complementary parameter. -/
theorem rectangle_freeLaw_map_dual_wired
    (θ : Parameters) (a : LatticeVertex) (w h : ℕ) :
    (law (rectangleGraph a w h) θ (BoundaryCondition.free ∅)).map
        (rectanglePrimalDualConfigurationEquiv a w h) =
      law (rectangleDualGraph a w h) (dualParameters θ)
        (rectangleDualBoundaryCondition a w h) :=
  rectangleFKLaw_map_primalDualConfigurationEquiv θ a w h

end PottsContinuity.DualityExt
