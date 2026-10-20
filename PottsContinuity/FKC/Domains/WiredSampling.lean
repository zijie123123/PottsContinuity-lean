-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `Domains/WiredSampling.lean`, with
-- module and namespace relocated (wrappers of the SLE development replaced by `PottsContinuity.FKC.SLEWrap`)
-- and declarations not used here removed.
module

public import PottsContinuity.FKC.Domains.BoundaryWiring
public import PottsContinuity.FKC.FiniteFK.Marginal

/-!
# Sampling after removing the actual edges of a wired boundary arc

An edge is removed exactly when its entire embedded closed segment lies in the
specified geometric forward arc. Merely having both endpoints wired does not
qualify an edge for removal. The remaining configurations retain the original
graph and every original vertex; only these geometric boundary edges cease to
be sampled. Their subsequent forced opening gives the same drawing-configuration
law as sampling all original edges and then forcing them open.

The cyclic order is the supplied polygon order. No geometric counterclockwise
claim is made here. For the paper's Dobrushin convention, the eventual wired arc
is the complement of the free arc: start at `a + k`, with length `m + 3 - k`.
These sampling identities do not construct a medial strand or a scaling limit.
-/

@[expose] public section

namespace PottsContinuity.FKC.LatticePolygon

noncomputable section

open Set OAI.SLEExactGauge FiniteFK

variable {m : ℕ} (P : LatticePolygon m)

local instance samplingVertexFinite (δ : PositiveMesh) :
    Finite (DomainVertex δ (P.domain δ)) := P.finite_domainVertex δ

local instance samplingEdgeFintype (δ : PositiveMesh) :
    Fintype (domainLatticeGraph δ (P.domain δ)).edgeSet := Fintype.ofFinite _

local instance samplingEdgeDecidableEq (δ : PositiveMesh) :
    DecidableEq (domainLatticeGraph δ (P.domain δ)).edgeSet := Classical.decEq _

/-- The original graph edges whose entire closed geometric segments lie in the
specified forward boundary arc. The endpoint presentation is existential only
to express the geometric predicate on unordered edges. -/
def forwardArcRemovedEdges (δ : PositiveMesh) (a : ZMod (m + 3)) (k : ℕ) :
    Configuration (domainLatticeGraph δ (P.domain δ)) := by
  classical
  exact Finset.univ.filter fun e =>
    ∃ u v : DomainVertex δ (P.domain δ), e.val = s(u, v) ∧
      complexPlaneCoordinates ''
        segment ℝ (domainVertexEmbed δ (P.domain δ) u) (domainVertexEmbed δ (P.domain δ) v) ⊆
          (P.toPrePolygon δ).arc a k

/-- The removal rule is exactly geometric segment containment, independent of
the order chosen for an original edge's endpoints. In particular interior
chords with merely wired endpoints are not removed by this rule. -/
theorem mem_forwardArcRemovedEdges_iff (δ : PositiveMesh) (a : ZMod (m + 3)) (k : ℕ)
    (u v : DomainVertex δ (P.domain δ)) (huv : (domainLatticeGraph δ (P.domain δ)).Adj u v) :
    (⟨s(u, v), (domainLatticeGraph δ (P.domain δ)).mem_edgeSet.mpr huv⟩ :
      (domainLatticeGraph δ (P.domain δ)).edgeSet) ∈ P.forwardArcRemovedEdges δ a k ↔
      complexPlaneCoordinates ''
        segment ℝ (domainVertexEmbed δ (P.domain δ) u) (domainVertexEmbed δ (P.domain δ) v) ⊆
          (P.toPrePolygon δ).arc a k := by
  classical
  simp only [forwardArcRemovedEdges, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨x, y, he, hsegment⟩
    rcases Sym2.eq_iff.mp he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hsegment
    · simpa only [segment_symm] using hsegment
  · intro h
    exact ⟨u, v, rfl, h⟩

/-- The geometric removal rule really removes only edges with boundary-related
endpoints, discharging the premise of the finite FK marginal theorems. -/
theorem forwardArcRemovedEdges_related (δ : PositiveMesh) (a : ZMod (m + 3)) (k : ℕ)
    (u v : DomainVertex δ (P.domain δ)) (huv : (domainLatticeGraph δ (P.domain δ)).Adj u v)
    (hmem : (⟨s(u, v), (domainLatticeGraph δ (P.domain δ)).mem_edgeSet.mpr huv⟩ :
      (domainLatticeGraph δ (P.domain δ)).edgeSet) ∈ P.forwardArcRemovedEdges δ a k) :
    (P.forwardArcBoundary δ a k).partition.r u v :=
  P.forwardArcBoundary_related_of_segment_subset δ a k
    ((P.mem_forwardArcRemovedEdges_iff δ a k u v huv).mp hmem)

/-- Configurations with only the geometric forward-arc edges removed from sampling.
They use exactly the original vertex carrier, including all isolated vertices. -/
abbrev ForwardArcRemainingConfiguration (δ : PositiveMesh) (a : ZMod (m + 3)) (k : ℕ) :=
  RemainingConfiguration (domainLatticeGraph δ (P.domain δ)) (P.forwardArcRemovedEdges δ a k)

/-- The actual joint FK law of all remaining original edges. -/
def forwardArcRemainingLaw (δ : PositiveMesh) (q : ClusterWeight)
    (a : ZMod (m + 3)) (k : ℕ) : PMF (P.ForwardArcRemainingConfiguration δ a k) :=
  remainingLaw (domainLatticeGraph δ (P.domain δ)) q (P.forwardArcBoundary δ a k)
    (P.forwardArcRemovedEdges δ a k)

end

end PottsContinuity.FKC.LatticePolygon
