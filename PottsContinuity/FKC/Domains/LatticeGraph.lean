-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `Domains/LatticeGraph.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.LatticeEmbedding
public import Mathlib.Analysis.Convex.Segment

/-!
# The lattice graph of a plane domain, including its boundary

The model on page 4 uses every mesh vertex in the closure of the domain and
every nearest-neighbor edge whose entire closed segment lies in that closure.
This is not in general just the induced graph on the interior vertices.
Finiteness is proved from boundedness, not supplied as an extra assumption.
Jordan/polygon and marked approximation data are constructed separately.
-/

@[expose] public section

namespace PottsContinuity.FKC

noncomputable section

/-- All lattice vertices in the domain closure, including boundary vertices. -/
abbrev DomainVertex (δ : PositiveMesh) (D : Set ℂ) :=
  {v : LatticeVertex // latticeEmbed δ v ∈ closure D}

/-- The faithful Euclidean placement of each domain-graph vertex. -/
def domainVertexEmbed (δ : PositiveMesh) (D : Set ℂ) : DomainVertex δ D → ℂ :=
  fun v => latticeEmbed δ v.val

/-- A bounded domain has a finite graph vertex carrier, including its full boundary. -/
theorem domainVertex_finite (δ : PositiveMesh) {D : Set ℂ}
    (hD : Bornology.IsBounded D) : Finite (DomainVertex δ D) :=
  (finite_preimage_latticeEmbed_of_isBounded δ hD.closure).to_subtype

/-- The source graph: an edge is kept only when its entire closed segment lies
in the domain closure. No convexity or polygon approximation is assumed here. -/
def domainLatticeGraph (δ : PositiveMesh) (D : Set ℂ) :
    SimpleGraph (DomainVertex δ D) where
  Adj u v := squareLattice.Adj u.val v.val ∧
    segment ℝ (domainVertexEmbed δ D u) (domainVertexEmbed δ D v) ⊆ closure D
  symm := ⟨by
    intro u v h
    refine ⟨h.1.symm, ?_⟩
    rw [segment_symm]
    exact h.2⟩
  loopless := ⟨by
    intro v h
    exact h.1.ne rfl⟩

theorem domainLatticeGraph_adj_iff (δ : PositiveMesh) (D : Set ℂ)
    (u v : DomainVertex δ D) :
    (domainLatticeGraph δ D).Adj u v ↔ squareLattice.Adj u.val v.val ∧
      segment ℝ (domainVertexEmbed δ D u) (domainVertexEmbed δ D v) ⊆ closure D := Iff.rfl

/-- Boundary vertices are retained as ordinary original graph vertices. -/
def domainBoundaryVertices (δ : PositiveMesh) (D : Set ℂ) : Set (DomainVertex δ D) :=
  {v | domainVertexEmbed δ D v ∈ frontier D}

end

end PottsContinuity.FKC
