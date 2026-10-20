-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/RectangleBottomWiredDuality.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.RectangleDualBottomCollar
public import PottsContinuity.FKC.FiniteFK.RectangleFKDuality
public import PottsContinuity.FKC.FiniteFK.PMFConditioningEquiv
public import PottsContinuity.FKC.FiniteFK.ConditionalEmbeddedLaw

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK
open PottsContinuity.FKC PottsContinuity.FKC.Medial

noncomputable section

local instance rectangleBottomWiredPrimalOuterEdgeDecidableEq (n : ℕ) :
    DecidableEq (rectangleBottomCollarOuterGraph n).edgeSet := Classical.decEq _
local instance rectangleBottomWiredDualOuterEdgeDecidableEq (n : ℕ) :
    DecidableEq (rectangleDualBottomCollarOuterGraph n).edgeSet := Classical.decEq _
local instance rectangleBottomWiredPrimalInnerEdgeDecidableEq (n : ℕ) :
    DecidableEq (rectangleBottomCollarInnerGraph n).edgeSet := Classical.decEq _
local instance rectangleBottomWiredDualInnerEdgeDecidableEq (n : ℕ) :
    DecidableEq (rectangleDualBottomCollarInnerGraph n).edgeSet := Classical.decEq _


def rectangleOuterConfigurationCarrier (n : ℕ)
    (A : Configuration (rectangleBottomCollarOuterGraph n)) :
    Finset (rectanglePrimalEdgeCarrier (-(n:ℤ),-1) (2*n) (n+1)) := by
  change Finset (rectangleBottomCollarOuterGraph n).edgeSet
  exact A

def rectangleInnerConfigurationCarrier (n : ℕ)
    (A : Configuration (rectangleBottomCollarInnerGraph n)) :
    Finset (rectanglePrimalEdgeCarrier (-(n:ℤ),0) (2*n) n) := by
  change Finset (rectangleBottomCollarInnerGraph n).edgeSet
  exact A

private theorem rectanglePrimalDualConfiguration_eq_carrier (a : LatticeVertex)
    (w h : ℕ) (A : Configuration (rectangleGraph a w h)) :
    rectanglePrimalDualConfigurationEquiv a w h A =
      rectangleDualConfiguration a w h A := by
  rw [rectanglePrimalDualConfigurationEquiv_apply]
  rfl


private theorem rectangleBottomWiredDuality_primalDual_restriction_square (n : ℕ)
    (A : Configuration (rectangleBottomCollarOuterGraph n)) :
    embeddedConfigurationRestriction (rectangleDualBottomCollarInnerGraph n)
      (rectangleDualBottomCollarOuterGraph n)
      (rectangleDualBottomCollarVertexEmbedding n)
      (by
        rw [← rectangleDualBottomCollar_remainingGraph_eq_map_inner]
        exact edgeRestriction_le _ _)
      (rectanglePrimalDualConfigurationEquiv (-(n:ℤ),-1) (2*n) (n+1) A) =
    rectanglePrimalDualConfigurationEquiv (-(n:ℤ),0) (2*n) n
      (embeddedConfigurationRestriction (rectangleBottomCollarInnerGraph n)
        (rectangleBottomCollarOuterGraph n)
        (rectangleBottomCollarEmbedding n)
        (rectangleBottomCollar_primalMap_le n) A) := by
  classical
  ext d
  rw [rectanglePrimalDualConfiguration_eq_carrier,
      rectanglePrimalDualConfiguration_eq_carrier]
  have hdualEdge (d : (rectangleDualBottomCollarInnerGraph n).edgeSet) :
      rectangleDualGraphEdgeEquiv (-(n:ℤ),-1) (2*n) (n+1)
          (rectangleDualBottomCollarDualEdgeEmbedding n
            ((rectangleDualGraphEdgeEquiv (-(n:ℤ),0) (2*n) n).symm d)) =
        embeddedEdgeEmbedding (rectangleDualBottomCollarInnerGraph n)
          (rectangleDualBottomCollarOuterGraph n)
          (rectangleDualBottomCollarVertexEmbedding n)
          (by
            calc
              (rectangleDualBottomCollarInnerGraph n).map
                  (rectangleDualBottomCollarVertexEmbedding n) =
                  rectangleDualBottomCollarRemainingGraph n :=
                (rectangleDualBottomCollar_remainingGraph_eq_map_inner n).symm
              _ ≤ rectangleDualBottomCollarOuterGraph n := by
                change edgeRestriction _ _ ≤ _
                exact edgeRestriction_le _ _)
          d := by
      apply Subtype.ext
      change rectangleDualCarrierPair _ _ _ _ = _
      rw [rectangleDualBottomCollarDualEdgeEmbedding_pair, embeddedEdgeEmbedding_coe]
      have hpair : rectangleDualCarrierPair (-(n:ℤ),0) (2*n) n
          ((rectangleDualGraphEdgeEquiv (-(n:ℤ),0) (2*n) n).symm d) = d.val := by
        exact congrArg Subtype.val (Equiv.apply_symm_apply
          (rectangleDualGraphEdgeEquiv (-(n:ℤ),0) (2*n) n) d)
      rw [hpair]
      rfl
  have hprimalEdge (e : (rectangleBottomCollarInnerGraph n).edgeSet) :
      rectangleDualBottomCollarPrimalEdgeEmbedding n e =
        embeddedEdgeEmbedding (rectangleBottomCollarInnerGraph n)
          (rectangleBottomCollarOuterGraph n) (rectangleBottomCollarEmbedding n)
          (rectangleBottomCollar_primalMap_le n) e := by
    apply Subtype.ext
    rfl
  rw [mem_embeddedConfigurationRestriction]
  rw [← hdualEdge d]
  rw [mem_rectangleDualConfiguration (-(n:ℤ),-1) (2*n) (n+1) A
    (rectangleDualBottomCollarDualEdgeEmbedding n
      ((rectangleDualGraphEdgeEquiv (-(n:ℤ),0) (2*n) n).symm d))]
  have hrhs : d ∈ rectangleDualConfiguration (-(n:ℤ),0) (2*n) n
      (embeddedConfigurationRestriction (rectangleBottomCollarInnerGraph n)
        (rectangleBottomCollarOuterGraph n) (rectangleBottomCollarEmbedding n)
        (rectangleBottomCollar_primalMap_le n) A) ↔
      ((rectangleDualGraphEdgeEquiv (-(n:ℤ),0) (2*n) n).symm d).primalEdge ∉
        rectangleInnerConfigurationCarrier n
          (embeddedConfigurationRestriction (rectangleBottomCollarInnerGraph n)
            (rectangleBottomCollarOuterGraph n) (rectangleBottomCollarEmbedding n)
            (rectangleBottomCollar_primalMap_le n) A) := by
    rw [← Equiv.apply_symm_apply
      (rectangleDualGraphEdgeEquiv (-(n:ℤ),0) (2*n) n) d]
    simpa only [Equiv.symm_apply_apply, rectangleInnerConfigurationCarrier, Function.id_def] using
      (mem_rectangleDualConfiguration (-(n:ℤ),0) (2*n) n
        (rectangleInnerConfigurationCarrier n
          (embeddedConfigurationRestriction (rectangleBottomCollarInnerGraph n)
            (rectangleBottomCollarOuterGraph n) (rectangleBottomCollarEmbedding n)
            (rectangleBottomCollar_primalMap_le n) A))
        ((rectangleDualGraphEdgeEquiv (-(n:ℤ),0) (2*n) n).symm d))
  rw [hrhs]
  simp only [rectangleDualBottomCollarDualEdgeEmbedding_primalEdge]
  rw [hprimalEdge ((rectangleDualGraphEdgeEquiv (-(n:ℤ),0) (2*n) n).symm d).primalEdge]
  change ((embeddedEdgeEmbedding (rectangleBottomCollarInnerGraph n)
      (rectangleBottomCollarOuterGraph n) (rectangleBottomCollarEmbedding n)
      (rectangleBottomCollar_primalMap_le n)
      ((rectangleDualGraphEdgeEquiv (-(n:ℤ),0) (2*n) n).symm d).primalEdge ∉ A) ↔
    ((rectangleDualGraphEdgeEquiv (-(n:ℤ),0) (2*n) n).symm d).primalEdge ∉
      embeddedConfigurationRestriction (rectangleBottomCollarInnerGraph n)
        (rectangleBottomCollarOuterGraph n) (rectangleBottomCollarEmbedding n)
        (rectangleBottomCollar_primalMap_le n) A)
  exact (not_congr (mem_embeddedConfigurationRestriction
    (rectangleBottomCollarInnerGraph n) (rectangleBottomCollarOuterGraph n)
    (rectangleBottomCollarEmbedding n) (rectangleBottomCollar_primalMap_le n) A
    ((rectangleDualGraphEdgeEquiv (-(n:ℤ),0) (2*n) n).symm d).primalEdge)).symm




private theorem rectangleBottomWiredDuality_edgeRestriction_injective {V : Type*}
    (G : SimpleGraph V) (R S : Configuration G)
    (h : edgeRestriction G R = edgeRestriction G S) : R = S := by
  classical
  apply Finset.ext
  intro e
  have hset : G.edgeSet \ openEdges G R = G.edgeSet \ openEdges G S := by
    have he := congrArg SimpleGraph.edgeSet h
    simpa only [edgeRestriction_edgeSet] using he
  have hopen : e.val ∈ openEdges G R ↔ e.val ∈ openEdges G S := by
    constructor
    · intro he
      by_contra hnot
      have hmem : e.val ∈ G.edgeSet \ openEdges G R := by
        simpa only [hset] using (show e.val ∈ G.edgeSet \ openEdges G S from
          ⟨e.property, hnot⟩)
      exact hmem.2 he
    · intro he
      by_contra hnot
      have hmem : e.val ∈ G.edgeSet \ openEdges G S := by
        simpa only [← hset] using (show e.val ∈ G.edgeSet \ openEdges G R from
          ⟨e.property, hnot⟩)
      exact hmem.2 he
  rw [← coe_mem_openEdges_iff G R e, ← coe_mem_openEdges_iff G S e]
  exact hopen

private theorem rectangleDualBottomCollar_removed_eq_subgraphRemoved (n : ℕ) :
    rectangleDualBottomCollarRemovedDualEdges n =
      subgraphRemovedEdges
        ((rectangleDualBottomCollarInnerGraph n).map
          (rectangleDualBottomCollarVertexEmbedding n))
        (rectangleDualBottomCollarOuterGraph n) := by
  have hmaple : (rectangleDualBottomCollarInnerGraph n).map
      (rectangleDualBottomCollarVertexEmbedding n) ≤
        rectangleDualBottomCollarOuterGraph n := by
    rw [← rectangleDualBottomCollar_remainingGraph_eq_map_inner n]
    simpa only [rectangleDualBottomCollarRemainingGraph] using
      (edgeRestriction_le (rectangleDualBottomCollarOuterGraph n)
        (rectangleDualBottomCollarRemovedDualEdges n))
  apply rectangleBottomWiredDuality_edgeRestriction_injective
  calc
    edgeRestriction (rectangleDualBottomCollarOuterGraph n)
        (rectangleDualBottomCollarRemovedDualEdges n) =
        rectangleDualBottomCollarRemainingGraph n := rfl
    _ = (rectangleDualBottomCollarInnerGraph n).map
        (rectangleDualBottomCollarVertexEmbedding n) :=
      rectangleDualBottomCollar_remainingGraph_eq_map_inner n
    _ = edgeRestriction (rectangleDualBottomCollarOuterGraph n)
        (subgraphRemovedEdges
          ((rectangleDualBottomCollarInnerGraph n).map
            (rectangleDualBottomCollarVertexEmbedding n))
          (rectangleDualBottomCollarOuterGraph n)) := by
      symm
      exact edgeRestriction_subgraphRemovedEdges hmaple

def rectangleDualBottomCollarClosedState (n : ℕ) :
    RemovedConfiguration (rectangleDualBottomCollarOuterGraph n)
      (rectangleDualBottomCollarRemovedDualEdges n) :=
  ⟨∅, Finset.empty_subset _⟩

theorem rectangleBottomWiredDuality_collar_event (n : ℕ)
    (A : Configuration (rectangleBottomCollarOuterGraph n)) :
    A ∈ frozenStateEvent (rectangleBottomCollarRemoved n)
        (rectangleBottomCollarState n) ↔
      rectanglePrimalDualConfigurationEquiv (-(n:ℤ),-1) (2*n) (n+1) A ∈
        frozenStateEvent (rectangleDualBottomCollarRemovedDualEdges n)
          (rectangleDualBottomCollarClosedState n) := by
  classical
  simp only [frozenStateEvent, rectangleBottomCollarState,
    rectangleDualBottomCollarClosedState, Set.mem_ofPred_eq]
  rw [rectanglePrimalDualConfiguration_eq_carrier]
  change A ∩ rectangleBottomCollarRemoved n = rectangleBottomCollarRemoved n ↔
    rectangleDualConfiguration (-(n:ℤ),-1) (2*n) (n+1)
        (rectangleOuterConfigurationCarrier n A) ∩
      rectangleDualBottomCollarRemovedDualEdges n = ∅
  constructor
  · intro hA
    apply Finset.ext
    intro g
    simp only [Finset.mem_inter, Finset.notMem_empty]
    constructor
    · rintro ⟨hgB, hgD⟩
      let e := (rectangleDualGraphEdgeEquiv (-(n:ℤ),-1) (2*n) (n+1)).symm g
      have hgEq : rectangleDualGraphEdgeEquiv (-(n:ℤ),-1) (2*n) (n+1) e = g :=
        Equiv.apply_symm_apply _ _
      have hremoved : rectangleDualBottomCollarPrimalEdgeAsGraphEdge n e.primalEdge ∈
          rectangleBottomCollarRemoved n := by
        apply (rectangleDualBottomCollar_removedDual_mem_iff n e).mp
        rw [hgEq]
        exact hgD
      have hA' : rectangleDualBottomCollarPrimalEdgeAsGraphEdge n e.primalEdge ∈ A := by
        have hsub : rectangleBottomCollarRemoved n ⊆ A := by
          intro x hx
          have hx' : x ∈ A ∩ rectangleBottomCollarRemoved n := by rw [hA]; exact hx
          exact (Finset.mem_inter.mp hx').1
        exact hsub hremoved
      have hB' : rectangleDualGraphEdgeEquiv (-(n:ℤ),-1) (2*n) (n+1) e ∈
          rectangleDualConfiguration (-(n:ℤ),-1) (2*n) (n+1)
            (rectangleOuterConfigurationCarrier n A) := by
        rw [hgEq]
        exact hgB
      have hclosed := (mem_rectangleDualConfiguration _ _ _ _ e).mp hB'
      have hA'' : e.primalEdge ∈ rectangleOuterConfigurationCarrier n A := by
        change e.primalEdge ∈ A
        change e.primalEdge ∈ A at hA'
        exact hA'
      exact hclosed hA''
    · intro hfalse
      exact False.elim hfalse
  · intro hD
    have hA : rectangleBottomCollarRemoved n ⊆ A := by
      intro x hx
      by_contra hnot
      let ep : rectanglePrimalEdgeCarrier (-(n:ℤ),-1) (2*n) (n+1) := x
      let d := rectanglePrimalDualEdgeEquiv (-(n:ℤ),-1) (2*n) (n+1) ep
      have hdualR : rectangleDualGraphEdgeEquiv (-(n:ℤ),-1) (2*n) (n+1) d ∈
          rectangleDualBottomCollarRemovedDualEdges n := by
        apply (rectangleDualBottomCollar_removedDual_mem_iff n d).mpr
        change rectangleDualBottomCollarPrimalEdgeAsGraphEdge n ep ∈
          rectangleBottomCollarRemoved n
        simpa [rectangleDualBottomCollarPrimalEdgeAsGraphEdge, ep, d] using hx
      have hdualOpen : rectangleDualGraphEdgeEquiv (-(n:ℤ),-1) (2*n) (n+1) d ∈
          rectangleDualConfiguration (-(n:ℤ),-1) (2*n) (n+1)
            (rectangleOuterConfigurationCarrier n A) := by
        apply (mem_rectangleDualConfiguration _ _ _ _ d).mpr
        change ep ∉ A
        exact hnot
      have hpair : rectangleDualGraphEdgeEquiv (-(n:ℤ),-1) (2*n) (n+1) d ∈
          rectangleDualConfiguration (-(n:ℤ),-1) (2*n) (n+1)
            (rectangleOuterConfigurationCarrier n A) ∩
          rectangleDualBottomCollarRemovedDualEdges n :=
        Finset.mem_inter.mpr ⟨hdualOpen, hdualR⟩
      rw [hD] at hpair
      exact Finset.notMem_empty _ hpair
    apply Finset.ext
    intro x
    simp only [Finset.mem_inter]
    constructor
    · rintro ⟨_,hx⟩
      exact hx
    · intro hx
      exact ⟨hA hx, hx⟩



private theorem rectangleBottomWiredDuality_dualConditional_map (n : ℕ)
    (q : ClusterWeight) :
    (((law (rectangleDualBottomCollarOuterGraph n) q
        (rectangleDualBoundaryCondition (-(n:ℤ),-1) (2*n) (n+1))).filter
      (frozenStateEvent
        (subgraphRemovedEdges
          ((rectangleDualBottomCollarInnerGraph n).map
            (rectangleDualBottomCollarVertexEmbedding n))
          (rectangleDualBottomCollarOuterGraph n))
        (⟨∅, Finset.empty_subset _⟩ : RemovedConfiguration
          (rectangleDualBottomCollarOuterGraph n)
          (subgraphRemovedEdges
            ((rectangleDualBottomCollarInnerGraph n).map
              (rectangleDualBottomCollarVertexEmbedding n))
            (rectangleDualBottomCollarOuterGraph n))))
      (frozenStateEvent_support q
        (rectangleDualBoundaryCondition (-(n:ℤ),-1) (2*n) (n+1))
        (subgraphRemovedEdges
          ((rectangleDualBottomCollarInnerGraph n).map
            (rectangleDualBottomCollarVertexEmbedding n))
          (rectangleDualBottomCollarOuterGraph n))
        ⟨∅, Finset.empty_subset _⟩)).map
      (embeddedConfigurationRestriction (rectangleDualBottomCollarInnerGraph n)
        (rectangleDualBottomCollarOuterGraph n)
        (rectangleDualBottomCollarVertexEmbedding n)
        (by
          rw [← rectangleDualBottomCollar_remainingGraph_eq_map_inner n]
          change edgeRestriction _ _ ≤ _
          exact edgeRestriction_le _ _))) =
      law (rectangleDualBottomCollarInnerGraph n) q
        (BoundaryCondition.wired (rectangleDualBottomCollarInnerThreeSides n)) := by
  let G := rectangleDualBottomCollarInnerGraph n
  let H := rectangleDualBottomCollarOuterGraph n
  let f := rectangleDualBottomCollarVertexEmbedding n
  let R : Configuration H := subgraphRemovedEdges (G.map f) H
  let K : RemovedConfiguration H R := ⟨∅, Finset.empty_subset _⟩
  let ξ := rectangleDualBoundaryCondition (-(n:ℤ),-1) (2*n) (n+1)
  have hmap : G.map f ≤ H := by
    rw [← rectangleDualBottomCollar_remainingGraph_eq_map_inner n]
    change edgeRestriction H (rectangleDualBottomCollarRemovedDualEdges n) ≤ H
    exact edgeRestriction_le H _
  have hcond := law_filter_frozen_map_embeddedRestriction G H f hmap q ξ K
  have hpartition :
      (isolatedExtensionPullbackBoundary f (frozenBoundary ξ K.val)).partition =
        (BoundaryCondition.wired
          (rectangleDualBottomCollarInnerThreeSides n)).partition := by
    apply Setoid.ext
    intro u v
    change (Setoid.comap f (componentSetoid H ξ K.val)).r u v ↔ _
    change (Setoid.comap f (componentSetoid H ξ ∅)).r u v ↔ _
    rw [Setoid.comap_rel, componentSetoid_empty]
    change ξ.partition.r (f u) (f v) ↔ _
    exact rectangleDualBottomCollar_outerBoundaryCondition_pullback n u v
  rw [law_eq_of_boundary_partition_eq q _ _ hpartition] at hcond
  simpa [R, K] using hcond

/-- The bottom-wired primal FK law is exactly dual to the law wired only on
three sides of the expanded inner dual rectangle. -/
theorem rectangleBottomWiredDuality_law_map (n : ℕ) (q : ClusterWeight) :
    (law (rectangleBottomCollarInnerGraph n) q
      (BoundaryCondition.wired (rectangleBottomCollarBottom n))).map
        (rectanglePrimalDualConfigurationEquiv (-(n:ℤ),0) (2*n) n) =
      law (rectangleDualBottomCollarInnerGraph n) q
        (BoundaryCondition.wired (rectangleDualBottomCollarInnerThreeSides n)) := by
  classical
  let Pout := rectangleBottomCollarOuterGraph n
  let Pin := rectangleBottomCollarInnerGraph n
  let Dout := rectangleDualBottomCollarOuterGraph n
  let Din := rectangleDualBottomCollarInnerGraph n
  let ep := rectangleBottomCollarEmbedding n
  let ed := rectangleDualBottomCollarVertexEmbedding n
  let eout := rectanglePrimalDualConfigurationEquiv (-(n:ℤ),-1) (2*n) (n+1)
  let ein := rectanglePrimalDualConfigurationEquiv (-(n:ℤ),0) (2*n) n
  let erp := embeddedConfigurationRestriction Pin Pout ep
    (rectangleBottomCollar_primalMap_le n)
  let erd := embeddedConfigurationRestriction Din Dout ed
    (by rw [← rectangleDualBottomCollar_remainingGraph_eq_map_inner n]; exact edgeRestriction_le _ _)
  let Rp := rectangleBottomCollarRemoved n
  let Kp := rectangleBottomCollarState n
  let Rd := rectangleDualBottomCollarRemovedDualEdges n
  let Kd := rectangleDualBottomCollarClosedState n
  let ξp := BoundaryCondition.free (∅ : Set (rectangleBottomCollarOuterVertex n))
  let ξd := rectangleDualBoundaryCondition (-(n:ℤ),-1) (2*n) (n+1)
  let outerPrimalLaw := law Pout q ξp
  have hdual := rectangleFKLaw_map_primalDualConfigurationEquiv q
    (-(n:ℤ),-1) (2*n) (n+1)
  have himage : eout '' frozenStateEvent Rp Kp = frozenStateEvent Rd Kd := by
    apply Set.ext
    intro B
    constructor
    · rintro ⟨A,hA,rfl⟩
      exact (rectangleBottomWiredDuality_collar_event n A).mp hA
    · intro hB
      refine ⟨eout.symm B, ?_, eout.apply_symm_apply B⟩
      exact (rectangleBottomWiredDuality_collar_event n (eout.symm B)).mpr
        (by simpa [eout, Rd, Kd] using hB)
  have hfiltered :
      (outerPrimalLaw.filter (frozenStateEvent Rp Kp)
        (frozenStateEvent_support q ξp Rp Kp)).map eout =
      (law Dout q ξd).filter (frozenStateEvent Rd Kd)
        (frozenStateEvent_support q ξd Rd Kd) := by
    have hfm := pmf_filter_map_equiv outerPrimalLaw eout
      (frozenStateEvent Rp Kp) (frozenStateEvent_support q ξp Rp Kp)
    have hsupportImage := pmf_map_equiv_filter_witness outerPrimalLaw eout
      (frozenStateEvent Rp Kp) (frozenStateEvent_support q ξp Rp Kp)
    have hsupportDual : ∃ B ∈ frozenStateEvent Rd Kd,
        B ∈ (outerPrimalLaw.map eout).support := by
      simpa [himage] using hsupportImage
    have himageFilter :
        (outerPrimalLaw.map eout).filter (eout '' frozenStateEvent Rp Kp)
            hsupportImage =
          (outerPrimalLaw.map eout).filter (frozenStateEvent Rd Kd)
            hsupportDual := by
      ext B
      rw [PMF.filter_apply, PMF.filter_apply]
      have hnum : (eout '' frozenStateEvent Rp Kp).indicator
          (outerPrimalLaw.map eout) B =
          (frozenStateEvent Rd Kd).indicator (outerPrimalLaw.map eout) B := by
        rw [himage]
      rw [hnum]
      have hnumAll (B : Configuration Dout) :
          (eout '' frozenStateEvent Rp Kp).indicator (outerPrimalLaw.map eout) B =
            (frozenStateEvent Rd Kd).indicator (outerPrimalLaw.map eout) B := by
        rw [himage]
      have hden : (∑' B : Configuration Dout,
          (eout '' frozenStateEvent Rp Kp).indicator (outerPrimalLaw.map eout) B) =
          ∑' B : Configuration Dout,
            (frozenStateEvent Rd Kd).indicator (outerPrimalLaw.map eout) B :=
        tsum_congr hnumAll
      rw [hden]
    have hdualFilter :
        (outerPrimalLaw.map eout).filter (frozenStateEvent Rd Kd)
            hsupportDual =
          (law Dout q ξd).filter (frozenStateEvent Rd Kd)
            (frozenStateEvent_support q ξd Rd Kd) := by
      have hdual' : outerPrimalLaw.map eout = law Dout q ξd := by
        simpa [outerPrimalLaw, ξp, ξd, Pout, Dout, eout] using hdual
      ext B
      rw [PMF.filter_apply, PMF.filter_apply]
      have hv (B : Configuration Dout) : (outerPrimalLaw.map eout) B =
          (law Dout q ξd) B := congrArg (fun μ : PMF (Configuration Dout) => μ B) hdual'
      have hnum (B : Configuration Dout) :
          (frozenStateEvent Rd Kd).indicator (outerPrimalLaw.map eout) B =
          (frozenStateEvent Rd Kd).indicator (law Dout q ξd) B := by
        rw [Set.indicator_apply, Set.indicator_apply, hv B]
      rw [hnum B]
      have hden : (∑' B : Configuration Dout,
          (frozenStateEvent Rd Kd).indicator (outerPrimalLaw.map eout) B) =
          ∑' B : Configuration Dout,
            (frozenStateEvent Rd Kd).indicator (law Dout q ξd) B :=
        tsum_congr hnum
      rw [hden]
    exact hfm.trans (himageFilter.trans hdualFilter)
  have hprimalConditional := rectangleBottomCollar_conditional_law_map n q
  have hdualConditional := rectangleBottomWiredDuality_dualConditional_map n q
  have hfun : erd ∘ eout = ein ∘ erp := by
    funext A
    exact rectangleBottomWiredDuality_primalDual_restriction_square n A
  calc
    (law Pin q (BoundaryCondition.wired (rectangleBottomCollarBottom n))).map ein
        = ((outerPrimalLaw.filter (frozenStateEvent Rp Kp)
            (frozenStateEvent_support q ξp Rp Kp)).map erp).map ein := by
          rw [hprimalConditional]
    _ = ((outerPrimalLaw.filter (frozenStateEvent Rp Kp)
            (frozenStateEvent_support q ξp Rp Kp)).map eout).map erd := by
          rw [PMF.map_comp, PMF.map_comp, ← hfun]
    _ = ((law Dout q ξd).filter (frozenStateEvent Rd Kd)
            (frozenStateEvent_support q ξd Rd Kd)).map erd := by
          rw [hfiltered]
    _ = law Din q (BoundaryCondition.wired (rectangleDualBottomCollarInnerThreeSides n)) := by
          have hremoved := rectangleDualBottomCollar_removed_eq_subgraphRemoved n
          let Rstd := subgraphRemovedEdges
            ((rectangleDualBottomCollarInnerGraph n).map
              (rectangleDualBottomCollarVertexEmbedding n))
            (rectangleDualBottomCollarOuterGraph n)
          let Kstd : RemovedConfiguration (rectangleDualBottomCollarOuterGraph n) Rstd :=
            ⟨∅, Finset.empty_subset _⟩
          have hevent : frozenStateEvent Rd Kd = frozenStateEvent Rstd Kstd := by
            ext C
            simp [frozenStateEvent, Rd, Kd, Kstd, Rstd,
              rectangleDualBottomCollarClosedState, rectangleDualBottomCollarRemovedDualEdges,
              hremoved]
          have hfilter :
              (law Dout q ξd).filter (frozenStateEvent Rd Kd)
                  (frozenStateEvent_support q ξd Rd Kd) =
                (law Dout q ξd).filter (frozenStateEvent Rstd Kstd)
                  (frozenStateEvent_support q ξd Rstd Kstd) := by
            ext C
            rw [PMF.filter_apply, PMF.filter_apply, hevent]
          have hmapfilter := congrArg (PMF.map erd) hfilter
          rw [hmapfilter]
          simpa [erd, Din, Dout, Rstd, Kstd] using hdualConditional

end
end PottsContinuity.FKC.FiniteFK
