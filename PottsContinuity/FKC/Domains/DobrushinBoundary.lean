-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `Domains/DobrushinBoundary.lean`, with
-- module and namespace relocated (wrappers of the SLE development replaced by `PottsContinuity.FKC.SLEWrap`)
-- and declarations not used here removed.
module

public import PottsContinuity.FKC.Domains.MarkedHalfArcs
public import PottsContinuity.FKC.Domains.MarkedPolygonOrientation
public import PottsContinuity.FKC.Domains.WiredSampling

/-!
# Dobrushin wiring from any admissible marked boundary parametrization

The free arc is the actual first-to-second CCW half of the boundary path; the
wired arc is its second-to-first half. Vertices and removed edges are selected
geometrically on the full original closure graph. No polygon orientation or
particular admissible parametrization is assumed or selected in these definitions.
-/

@[expose] public section

namespace PottsContinuity.FKC.MarkedLatticeBoundary

noncomputable section

open Set OAI.SLEExactGauge FiniteFK

/-- Every original vertex in the closure of the actual polygonal domain. -/
abbrev Vertex (B : MarkedLatticeBoundary) :=
  DomainVertex B.mesh (B.polygon.domain B.mesh)

/-- The full original nearest-neighbor graph, including isolated vertices. -/
abbrev graph (B : MarkedLatticeBoundary) : SimpleGraph B.Vertex :=
  domainLatticeGraph B.mesh (B.polygon.domain B.mesh)

/-- The genuine counterclockwise boundary half from the first mark to the second. -/
def freeArc (B : MarkedLatticeBoundary) : Set ℂ := B.boundary.lowerHalf

/-- The genuine counterclockwise boundary half from the second mark back to the first. -/
def wiredArc (B : MarkedLatticeBoundary) : Set ℂ := B.boundary.upperHalf

/-- The arbitrary input parametrization has the polygon's two geometric arcs,
with their order selected by its actual positive winding orientation. -/
theorem half_arcs_eq_cyclic_or_reverse (B : MarkedLatticeBoundary) :
    (complexPlaneCoordinates '' B.freeArc =
        (B.polygon.toPrePolygon B.mesh).arc B.first (B.second - B.first).val ∧
      complexPlaneCoordinates '' B.wiredArc =
        (B.polygon.toPrePolygon B.mesh).arc B.second
          (B.size + 3 - (B.second - B.first).val)) ∨
    (complexPlaneCoordinates '' B.freeArc =
        (B.polygon.toPrePolygon B.mesh).arc B.second
          (B.size + 3 - (B.second - B.first).val) ∧
      complexPlaneCoordinates '' B.wiredArc =
        (B.polygon.toPrePolygon B.mesh).arc B.first (B.second - B.first).val) := by
  obtain ⟨β, hβ⟩ := B.polygon.exists_markedBoundaryParametrization_arc_pair
    B.mesh B.first B.second B.marks_ne
  have hl := B.boundary.lowerHalf_eq β
  have hu := B.boundary.upperHalf_eq β
  unfold freeArc wiredArc
  rw [hl, hu]
  exact hβ

/-- The wired set is a proper geometric forward arc of the supplied cyclic
polygon. If that cyclic order is reversed, the displayed set-level arc runs
from the first index to the second; the actual wired path still runs from the
second mark at time one-half to the first at time one. -/
theorem exists_wired_forwardArc (B : MarkedLatticeBoundary) :
    ∃ (i : ZMod (B.size + 3)) (k : ℕ), 1 ≤ k ∧ k ≤ B.size + 2 ∧
      ((i = B.second ∧ i + k = B.first) ∨ (i = B.first ∧ i + k = B.second)) ∧
      complexPlaneCoordinates '' B.wiredArc = (B.polygon.toPrePolygon B.mesh).arc i k := by
  obtain ⟨hk1, hk2, hadd⟩ :=
    LatticePolygon.markedArcLength_bounds B.first B.second B.marks_ne
  have hcomp1 : 1 ≤ B.size + 3 - (B.second - B.first).val := by omega
  have hcomp2 : B.size + 3 - (B.second - B.first).val ≤ B.size + 2 := by omega
  have hsum : ((B.second - B.first).val : ZMod (B.size + 3)) +
      ((B.size + 3 - (B.second - B.first).val : ℕ) : ZMod (B.size + 3)) = 0 := by
    rw [← Nat.cast_add, show (B.second - B.first).val +
      (B.size + 3 - (B.second - B.first).val) = B.size + 3 by omega]
    exact ZMod.natCast_self _
  have hfinish : B.second + ((B.size + 3 - (B.second - B.first).val : ℕ) :
      ZMod (B.size + 3)) = B.first := by
    nth_rw 1 [← hadd]
    rw [add_assoc, hsum, add_zero]
  rcases B.half_arcs_eq_cyclic_or_reverse with h | h
  · exact ⟨B.second, _, hcomp1, hcomp2, Or.inl ⟨rfl, hfinish⟩, h.2⟩
  · exact ⟨B.first, _, hk1, hk2, Or.inr ⟨rfl, hadd⟩, h.2⟩

theorem freeArc_union_wiredArc (B : MarkedLatticeBoundary) :
    B.freeArc ∪ B.wiredArc = frontier (B.polygon.domain B.mesh) :=
  B.boundary.lowerHalf_union_upperHalf

theorem freeArc_inter_wiredArc (B : MarkedLatticeBoundary) :
    B.freeArc ∩ B.wiredArc =
      {latticeEmbed B.mesh (B.polygon.vertex B.first),
       latticeEmbed B.mesh (B.polygon.vertex B.second)} :=
  B.boundary.lowerHalf_inter_upperHalf

/-- Wire exactly those original vertices lying on the actual closed wired half. -/
def wiredVertices (B : MarkedLatticeBoundary) : Set B.Vertex :=
  {v | domainVertexEmbed B.mesh (B.polygon.domain B.mesh) v ∈ B.wiredArc}

/-- Every wired vertex lies on the original geometric boundary. -/
theorem wiredVertices_subset_boundary (B : MarkedLatticeBoundary) :
    B.wiredVertices ⊆ domainBoundaryVertices B.mesh (B.polygon.domain B.mesh) := by
  intro v hv
  change domainVertexEmbed B.mesh (B.polygon.domain B.mesh) v ∈ frontier _
  rw [← B.freeArc_union_wiredArc]
  exact Or.inr hv

/-- Identify the wired vertices and leave every other original vertex singleton. -/
def boundaryCondition (B : MarkedLatticeBoundary) : BoundaryCondition B.Vertex :=
  BoundaryCondition.wired B.wiredVertices

theorem boundaryCondition_rel (B : MarkedLatticeBoundary) (u v : B.Vertex) :
    B.boundaryCondition.partition.r u v ↔
      u = v ∨ u ∈ B.wiredVertices ∧ v ∈ B.wiredVertices := Iff.rfl

/-- Any proved cyclic presentation of the same wired set yields the existing
forward-arc vertex set, without selecting a presentation in the definition. -/
theorem wiredVertices_eq_forwardArc (B : MarkedLatticeBoundary)
    (i : ZMod (B.size + 3)) (k : ℕ)
    (harc : complexPlaneCoordinates '' B.wiredArc = (B.polygon.toPrePolygon B.mesh).arc i k) :
    B.wiredVertices = B.polygon.forwardArcVertices B.mesh i k := by
  ext v
  change domainVertexEmbed B.mesh (B.polygon.domain B.mesh) v ∈ B.wiredArc ↔
    complexPlaneCoordinates (domainVertexEmbed B.mesh (B.polygon.domain B.mesh) v) ∈
      (B.polygon.toPrePolygon B.mesh).arc i k
  rw [← harc]
  exact complexPlaneCoordinates.injective.mem_set_image.symm

theorem boundaryCondition_eq_forwardArc (B : MarkedLatticeBoundary)
    (i : ZMod (B.size + 3)) (k : ℕ)
    (harc : complexPlaneCoordinates '' B.wiredArc = (B.polygon.toPrePolygon B.mesh).arc i k) :
    B.boundaryCondition = B.polygon.forwardArcBoundary B.mesh i k := by
  unfold boundaryCondition LatticePolygon.forwardArcBoundary
  rw [B.wiredVertices_eq_forwardArc i k harc]

local instance vertexFinite (B : MarkedLatticeBoundary) : Finite B.Vertex :=
  B.polygon.finite_domainVertex B.mesh

local instance edgeFintype (B : MarkedLatticeBoundary) : Fintype B.graph.edgeSet :=
  Fintype.ofFinite _

local instance edgeDecidableEq (B : MarkedLatticeBoundary) : DecidableEq B.graph.edgeSet :=
  Classical.decEq _

/-- Remove exactly the original edges whose entire closed segment lies on the
wired half, not merely those whose two endpoints are wired. -/
def removedEdges (B : MarkedLatticeBoundary) : Configuration B.graph := by
  classical
  exact Finset.univ.filter fun e => ∃ u v : B.Vertex, e.val = s(u, v) ∧
    segment ℝ (domainVertexEmbed B.mesh (B.polygon.domain B.mesh) u)
      (domainVertexEmbed B.mesh (B.polygon.domain B.mesh) v) ⊆ B.wiredArc

theorem mem_removedEdges_iff (B : MarkedLatticeBoundary) (u v : B.Vertex)
    (huv : B.graph.Adj u v) :
    (⟨s(u, v), B.graph.mem_edgeSet.mpr huv⟩ : B.graph.edgeSet) ∈ B.removedEdges ↔
      segment ℝ (domainVertexEmbed B.mesh (B.polygon.domain B.mesh) u)
        (domainVertexEmbed B.mesh (B.polygon.domain B.mesh) v) ⊆ B.wiredArc := by
  classical
  simp only [removedEdges, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨x, y, he, hsegment⟩
    rcases Sym2.eq_iff.mp he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hsegment
    · simpa only [segment_symm] using hsegment
  · intro h
    exact ⟨u, v, rfl, h⟩

/-- The actual geometric rule discharges the prewired-endpoint condition. -/
theorem removedEdges_related (B : MarkedLatticeBoundary) (u v : B.Vertex)
    (huv : B.graph.Adj u v)
    (he : (⟨s(u, v), B.graph.mem_edgeSet.mpr huv⟩ : B.graph.edgeSet) ∈ B.removedEdges) :
    B.boundaryCondition.partition.r u v := by
  have hs := (B.mem_removedEdges_iff u v huv).mp he
  exact Or.inr ⟨hs (left_mem_segment ℝ _ _), hs (right_mem_segment ℝ _ _)⟩

theorem removedEdges_eq_forwardArc (B : MarkedLatticeBoundary)
    (i : ZMod (B.size + 3)) (k : ℕ)
    (harc : complexPlaneCoordinates '' B.wiredArc = (B.polygon.toPrePolygon B.mesh).arc i k) :
    B.removedEdges = B.polygon.forwardArcRemovedEdges B.mesh i k := by
  classical
  ext e
  obtain ⟨⟨u, v⟩, he⟩ := Sym2.mk_surjective e.val
  have he0 : s(u, v) = e.val := he
  have huv : B.graph.Adj u v := B.graph.mem_edgeSet.mp (by rw [he0]; exact e.property)
  have he' : e = ⟨s(u, v), B.graph.mem_edgeSet.mpr huv⟩ := Subtype.ext he.symm
  subst e
  rw [B.mem_removedEdges_iff u v huv,
    B.polygon.mem_forwardArcRemovedEdges_iff B.mesh i k u v huv, ← harc]
  constructor
  · exact image_mono
  · intro h x hx
    exact complexPlaneCoordinates.injective.mem_set_image.mp (h (mem_image_of_mem _ hx))

/-- Both marked vertices belong to the closed wired half. -/
theorem marked_vertices_mem_wired (B : MarkedLatticeBoundary) :
    B.polygon.boundaryVertex B.mesh B.first ∈ B.wiredVertices ∧
      B.polygon.boundaryVertex B.mesh B.second ∈ B.wiredVertices := by
  constructor
  · refine ⟨1, by norm_num, ?_⟩
    exact B.boundary.path.extend_one
  · refine ⟨1 / 2, by norm_num, ?_⟩
    change B.boundary.path.extend (1 / 2) = latticeEmbed B.mesh (B.polygon.vertex B.second)
    simpa only [← midpointUnitInterval_coe, Path.extend_extends',
      LatticePolygon.markedDomain_b] using B.boundary.midpoint_eq

/-- The exact full-edge critical FK law with the actual Dobrushin wired half. -/
def fullLaw (B : MarkedLatticeBoundary) (q : ClusterWeight) : PMF (Configuration B.graph) :=
  FiniteFK.law B.graph q B.boundaryCondition

/-- Configurations on the remaining original edges; the original vertices are
unchanged, including all isolated vertices. -/
abbrev RemainingConfiguration (B : MarkedLatticeBoundary) :=
  FiniteFK.RemainingConfiguration B.graph B.removedEdges

/-- The full joint law of the original edges that are actually sampled. -/
def remainingLaw (B : MarkedLatticeBoundary) (q : ClusterWeight) :
    PMF B.RemainingConfiguration :=
  FiniteFK.remainingLaw B.graph q B.boundaryCondition B.removedEdges

theorem fullLaw_eq_forwardArc (B : MarkedLatticeBoundary) (q : ClusterWeight)
    (i : ZMod (B.size + 3)) (k : ℕ)
    (harc : complexPlaneCoordinates '' B.wiredArc = (B.polygon.toPrePolygon B.mesh).arc i k) :
    B.fullLaw q = B.polygon.forwardArcLaw B.mesh q i k := by
  unfold fullLaw LatticePolygon.forwardArcLaw
  rw [B.boundaryCondition_eq_forwardArc i k harc]

/-- The same actual remaining configuration has the same probability in the
existing forward-arc model; only the proof of its disjointness is transported. -/
theorem remainingLaw_apply_eq_forwardArc (B : MarkedLatticeBoundary) (q : ClusterWeight)
    (i : ZMod (B.size + 3)) (k : ℕ)
    (harc : complexPlaneCoordinates '' B.wiredArc = (B.polygon.toPrePolygon B.mesh).arc i k)
    (A : B.RemainingConfiguration) :
    B.remainingLaw q A = B.polygon.forwardArcRemainingLaw B.mesh q i k
      ⟨A.val, by rw [← B.removedEdges_eq_forwardArc i k harc]; exact A.property⟩ := by
  unfold remainingLaw LatticePolygon.forwardArcRemainingLaw
  simp only [FiniteFK.remainingLaw_formula,
    B.boundaryCondition_eq_forwardArc i k harc, B.removedEdges_eq_forwardArc i k harc]

/-- The finite FK law on the sampled-edge carrier, with the original wired
component count on all vertices. -/
theorem remainingLaw_formula (B : MarkedLatticeBoundary) (q : ClusterWeight)
    (A : B.RemainingConfiguration) :
    B.remainingLaw q A = ENNReal.ofReal
      (edgeParameter q ^ A.val.card *
        (1 - edgeParameter q) ^
          (Nat.card B.graph.edgeSet - B.removedEdges.card - A.val.card) *
        q.val ^ componentCount B.graph B.boundaryCondition A.val /
        remainingPartitionFunction B.graph q B.boundaryCondition B.removedEdges) :=
  FiniteFK.remainingLaw_formula _ _ _ _ _

/-- Summing the removed boundary-edge states leaves exactly the reduced
partition function, with no additional geometric or probability premise. -/
theorem partitionFunction_eq_remaining (B : MarkedLatticeBoundary) (q : ClusterWeight) :
    partitionFunction B.graph q B.boundaryCondition =
      remainingPartitionFunction B.graph q B.boundaryCondition B.removedEdges :=
  FiniteFK.partitionFunction_eq_remaining _ _ _ _ B.removedEdges_related

/-- The original sample splits into the complete remaining FK law and the
independent Bernoulli law on all removed geometric boundary edges. -/
theorem fullLaw_map_split (B : MarkedLatticeBoundary) (q : ClusterWeight) :
    (B.fullLaw q).map (configurationSplitEquiv B.graph B.removedEdges) =
      FiniteProbability.productPMF (B.remainingLaw q)
        (removedLaw B.graph q B.removedEdges) :=
  FiniteFK.law_map_split _ _ _ _ B.removedEdges_related

/-- Forgetting the geometric wired edges yields exactly the entire remaining
edge law, rather than only its individual edge marginals. -/
theorem fullLaw_map_remove (B : MarkedLatticeBoundary) (q : ClusterWeight) :
    (B.fullLaw q).map (fun C => (configurationSplitEquiv B.graph B.removedEdges C).1) =
      B.remainingLaw q :=
  FiniteFK.law_map_remove _ _ _ _ B.removedEdges_related

/-- For drawing, declaring every removed wired edge open has precisely the
same configuration law under full sampling and the prescribed reduced sampling.
No medial strand is defined or assumed by this identity. -/
theorem fullLaw_map_force_open (B : MarkedLatticeBoundary) (q : ClusterWeight) :
    (B.fullLaw q).map (fun C => C ∪ B.removedEdges) =
      (B.remainingLaw q).map (fun A => A.val ∪ B.removedEdges) :=
  FiniteFK.law_map_union_removed _ _ _ _ B.removedEdges_related

/-- A proved proper cyclic presentation simultaneously identifies the boundary
partition and every removed edge. It is a consequence for every arbitrary
admissible input boundary, not extra data carried by that boundary. -/
theorem exists_forwardArc_model (B : MarkedLatticeBoundary) :
    ∃ (i : ZMod (B.size + 3)) (k : ℕ), 1 ≤ k ∧ k ≤ B.size + 2 ∧
      ((i = B.second ∧ i + k = B.first) ∨ (i = B.first ∧ i + k = B.second)) ∧
      B.wiredVertices = B.polygon.forwardArcVertices B.mesh i k ∧
      B.boundaryCondition = B.polygon.forwardArcBoundary B.mesh i k ∧
      B.removedEdges = B.polygon.forwardArcRemovedEdges B.mesh i k ∧
      ∀ q : ClusterWeight, B.fullLaw q = B.polygon.forwardArcLaw B.mesh q i k := by
  obtain ⟨i, k, hk1, hk2, hends, harc⟩ := B.exists_wired_forwardArc
  exact ⟨i, k, hk1, hk2, hends, B.wiredVertices_eq_forwardArc i k harc,
    B.boundaryCondition_eq_forwardArc i k harc, B.removedEdges_eq_forwardArc i k harc,
    fun q => B.fullLaw_eq_forwardArc q i k harc⟩

end
end PottsContinuity.FKC.MarkedLatticeBoundary
