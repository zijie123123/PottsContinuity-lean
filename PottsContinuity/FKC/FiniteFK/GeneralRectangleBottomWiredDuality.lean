-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/GeneralRectangleBottomWiredDuality.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.GeneralRectangleDualBottomCollarBoundary
public import PottsContinuity.FKC.FiniteFK.GeneralRectangleBottomCollarLaw

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK
open PottsContinuity.FKC PottsContinuity.FKC.Medial
noncomputable section

local instance grbw_pout (a : LatticeVertex) (w h : ℕ) :
    DecidableEq (rectangleArbitraryBottomCollarOuterGraph a w h).edgeSet := Classical.decEq _
local instance grbw_dout (a : LatticeVertex) (w h : ℕ) :
    DecidableEq (generalRectangleDualBottomCollarOuterGraph a w h).edgeSet := Classical.decEq _
local instance grbw_pin (a : LatticeVertex) (w h : ℕ) :
    DecidableEq (rectangleArbitraryBottomCollarInnerGraph a w h).edgeSet := Classical.decEq _
local instance grbw_din (a : LatticeVertex) (w h : ℕ) :
    DecidableEq (generalRectangleDualBottomCollarInnerGraph a w h).edgeSet := Classical.decEq _

private theorem grbw_edgeRestriction_injective {V : Type*} (G : SimpleGraph V)
    (R S : Configuration G) (h : edgeRestriction G R = edgeRestriction G S) : R = S := by
  classical
  apply Finset.ext
  intro e
  have hs : G.edgeSet \ openEdges G R = G.edgeSet \ openEdges G S := by
    have hh := congrArg SimpleGraph.edgeSet h
    simpa only [edgeRestriction_edgeSet] using hh
  have ho : e.val ∈ openEdges G R ↔ e.val ∈ openEdges G S := by
    constructor
    · intro he
      by_contra hn
      have hm : e.val ∈ G.edgeSet \ openEdges G R := by
        simpa only [hs] using (show e.val ∈ G.edgeSet \ openEdges G S from ⟨e.property, hn⟩)
      exact hm.2 he
    · intro he
      by_contra hn
      have hm : e.val ∈ G.edgeSet \ openEdges G S := by
        simpa only [← hs] using (show e.val ∈ G.edgeSet \ openEdges G R from ⟨e.property, hn⟩)
      exact hm.2 he
  rw [← coe_mem_openEdges_iff G R e, ← coe_mem_openEdges_iff G S e]
  exact ho

private theorem grbw_removed_eq_subgraphRemoved (a : LatticeVertex) (w h : ℕ) :
    generalRectangleDualBottomCollarRemovedDualEdges a w h =
      subgraphRemovedEdges
        ((generalRectangleDualBottomCollarInnerGraph a w h).map
          (generalRectangleDualBottomCollar_vertexEmbedding a w h))
        (generalRectangleDualBottomCollarOuterGraph a w h) := by
  have hle := generalRectangleDualBottomCollar_dualMap_le a w h
  apply grbw_edgeRestriction_injective _ _ _
  calc
    edgeRestriction _ (generalRectangleDualBottomCollarRemovedDualEdges a w h) =
        generalRectangleDualBottomCollarRemainingGraph a w h := rfl
    _ = _ := generalRectangleDualBottomCollar_remainingGraph_eq_map_inner a w h
    _ = edgeRestriction _ (subgraphRemovedEdges
        ((generalRectangleDualBottomCollarInnerGraph a w h).map
          (generalRectangleDualBottomCollar_vertexEmbedding a w h))
        (generalRectangleDualBottomCollarOuterGraph a w h)) := by
      symm
      exact edgeRestriction_subgraphRemovedEdges hle

private theorem grbw_dualConditional_map (a : LatticeVertex) (w h : ℕ)
    (q : ClusterWeight) :
    ((law (generalRectangleDualBottomCollarOuterGraph a w h) q
        (rectangleDualBoundaryCondition (a.1, a.2 - 1) w (h + 1))).filter
      (frozenStateEvent
        (subgraphRemovedEdges
          ((generalRectangleDualBottomCollarInnerGraph a w h).map
            (generalRectangleDualBottomCollar_vertexEmbedding a w h))
          (generalRectangleDualBottomCollarOuterGraph a w h))
        (⟨∅, Finset.empty_subset _⟩ : RemovedConfiguration
          (generalRectangleDualBottomCollarOuterGraph a w h)
          (subgraphRemovedEdges
            ((generalRectangleDualBottomCollarInnerGraph a w h).map
              (generalRectangleDualBottomCollar_vertexEmbedding a w h))
            (generalRectangleDualBottomCollarOuterGraph a w h))))
      (frozenStateEvent_support q
        (rectangleDualBoundaryCondition (a.1, a.2 - 1) w (h + 1))
        (subgraphRemovedEdges
          ((generalRectangleDualBottomCollarInnerGraph a w h).map
            (generalRectangleDualBottomCollar_vertexEmbedding a w h))
          (generalRectangleDualBottomCollarOuterGraph a w h))
        ⟨∅, Finset.empty_subset _⟩)).map
      (embeddedConfigurationRestriction
        (generalRectangleDualBottomCollarInnerGraph a w h)
        (generalRectangleDualBottomCollarOuterGraph a w h)
        (generalRectangleDualBottomCollar_vertexEmbedding a w h)
        (generalRectangleDualBottomCollar_dualMap_le a w h)) =
      law (generalRectangleDualBottomCollarInnerGraph a w h) q
        (BoundaryCondition.wired
          (generalRectangleDualBottomCollarInnerThreeSides a w h)) := by
  let G := generalRectangleDualBottomCollarInnerGraph a w h
  let H := generalRectangleDualBottomCollarOuterGraph a w h
  let f := generalRectangleDualBottomCollar_vertexEmbedding a w h
  let R : Configuration H := subgraphRemovedEdges (G.map f) H
  let K : RemovedConfiguration H R := ⟨∅, Finset.empty_subset _⟩
  let ξ := rectangleDualBoundaryCondition (a.1, a.2 - 1) w (h + 1)
  have hcond := law_filter_frozen_map_embeddedRestriction G H f
    (generalRectangleDualBottomCollar_dualMap_le a w h) q ξ K
  have hpart : (isolatedExtensionPullbackBoundary f (frozenBoundary ξ K.val)).partition =
      (BoundaryCondition.wired (generalRectangleDualBottomCollarInnerThreeSides a w h)).partition := by
    apply Setoid.ext
    intro u v
    change (Setoid.comap f (componentSetoid H ξ K.val)).r u v ↔ _
    change (Setoid.comap f (componentSetoid H ξ ∅)).r u v ↔ _
    rw [Setoid.comap_rel, componentSetoid_empty]
    change ξ.partition.r (f u) (f v) ↔ _
    exact generalRectangleDualBottomCollar_outerBoundaryCondition_pullback a w h u v
  rw [law_eq_of_boundary_partition_eq q _ _ hpart] at hcond
  simpa [R, K] using hcond

/-- The actual finite FK law with the bottom wired is transported by the
complementary-edge duality to the actual dual law wired on its three exposed
sides. -/
theorem generalRectangleBottomWiredDuality_law_map
    (a : LatticeVertex) (w h : ℕ) (q : ClusterWeight) :
    (law (rectangleArbitraryBottomCollarInnerGraph a w h) q
      (BoundaryCondition.wired (rectangleArbitraryBottomCollarBottom a w h))).map
        (rectanglePrimalDualConfigurationEquiv a w h) =
      law (generalRectangleDualBottomCollarInnerGraph a w h) q
        (BoundaryCondition.wired (generalRectangleDualBottomCollarInnerThreeSides a w h)) := by
  classical
  let Pout := rectangleArbitraryBottomCollarOuterGraph a w h
  let Pin := rectangleArbitraryBottomCollarInnerGraph a w h
  let Dout := generalRectangleDualBottomCollarOuterGraph a w h
  let Din := generalRectangleDualBottomCollarInnerGraph a w h
  let ep := rectangleArbitraryBottomCollarEmbedding a w h
  let ed := generalRectangleDualBottomCollar_vertexEmbedding a w h
  let eout := rectanglePrimalDualConfigurationEquiv (a.1, a.2 - 1) w (h + 1)
  let ein := rectanglePrimalDualConfigurationEquiv a w h
  let erp := embeddedConfigurationRestriction Pin Pout ep
    (generalRectangleDualBottomCollar_primalMap_le a w h)
  let erd := embeddedConfigurationRestriction Din Dout ed
    (generalRectangleDualBottomCollar_dualMap_le a w h)
  let Rp := rectangleArbitraryBottomCollarRemoved a w h
  let Kp := rectangleArbitraryBottomCollarState a w h
  let Rd := generalRectangleDualBottomCollarRemovedDualEdges a w h
  let Kd := generalRectangleDualBottomCollarClosedState a w h
  let ξp := BoundaryCondition.free (∅ : Set (rectangleArbitraryBottomCollarOuterVertex a w h))
  let ξd := rectangleDualBoundaryCondition (a.1, a.2 - 1) w (h + 1)
  let outerPrimalLaw := law Pout q ξp
  have hdual := rectangleFKLaw_map_primalDualConfigurationEquiv q
    (a.1, a.2 - 1) w (h + 1)
  have himage : eout '' frozenStateEvent Rp Kp = frozenStateEvent Rd Kd := by
    apply Set.ext
    intro B
    constructor
    · rintro ⟨A, hA, rfl⟩
      exact (generalRectangleDualBottomCollar_collar_event a w h A).mp hA
    · intro hB
      refine ⟨eout.symm B, ?_, eout.apply_symm_apply B⟩
      exact (generalRectangleDualBottomCollar_collar_event a w h (eout.symm B)).mpr
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
        (outerPrimalLaw.map eout).filter (eout '' frozenStateEvent Rp Kp) hsupportImage =
        (outerPrimalLaw.map eout).filter (frozenStateEvent Rd Kd) hsupportDual := by
      ext B
      rw [PMF.filter_apply, PMF.filter_apply]
      have hnum : (eout '' frozenStateEvent Rp Kp).indicator
          (outerPrimalLaw.map eout) B =
          (frozenStateEvent Rd Kd).indicator (outerPrimalLaw.map eout) B := by rw [himage]
      rw [hnum]
      have hnumAll (B : Configuration Dout) :
          (eout '' frozenStateEvent Rp Kp).indicator (outerPrimalLaw.map eout) B =
            (frozenStateEvent Rd Kd).indicator (outerPrimalLaw.map eout) B := by rw [himage]
      rw [show (∑' B : Configuration Dout,
          (eout '' frozenStateEvent Rp Kp).indicator (outerPrimalLaw.map eout) B) =
          ∑' B : Configuration Dout,
            (frozenStateEvent Rd Kd).indicator (outerPrimalLaw.map eout) B from tsum_congr hnumAll]
    have hdual' : outerPrimalLaw.map eout = law Dout q ξd := by
      simpa [outerPrimalLaw, ξp, ξd, Pout, Dout, eout] using hdual
    have hdualFilter :
        (outerPrimalLaw.map eout).filter (frozenStateEvent Rd Kd) hsupportDual =
        (law Dout q ξd).filter (frozenStateEvent Rd Kd)
          (frozenStateEvent_support q ξd Rd Kd) := by
      ext B
      rw [PMF.filter_apply, PMF.filter_apply]
      have hv (B : Configuration Dout) := congrArg (fun μ : PMF (Configuration Dout) => μ B) hdual'
      have hnum (B : Configuration Dout) :
          (frozenStateEvent Rd Kd).indicator (outerPrimalLaw.map eout) B =
          (frozenStateEvent Rd Kd).indicator (law Dout q ξd) B := by
        rw [Set.indicator_apply, Set.indicator_apply, hv B]
      rw [hnum B]
      rw [show (∑' B : Configuration Dout,
          (frozenStateEvent Rd Kd).indicator (outerPrimalLaw.map eout) B) =
          ∑' B : Configuration Dout,
            (frozenStateEvent Rd Kd).indicator (law Dout q ξd) B from tsum_congr hnum]
    exact hfm.trans (himageFilter.trans hdualFilter)
  have hprimalConditional := rectangleArbitraryBottomCollar_conditional_law_map a w h q
  have hdualConditional := grbw_dualConditional_map a w h q
  have hfun : erd ∘ eout = ein ∘ erp := by
    funext A
    exact generalRectangleDualBottomCollar_primalDual_restriction_square a w h A
  calc
    (law Pin q (BoundaryCondition.wired (rectangleArbitraryBottomCollarBottom a w h))).map ein
        = ((outerPrimalLaw.filter (frozenStateEvent Rp Kp)
            (frozenStateEvent_support q ξp Rp Kp)).map erp).map ein := by rw [hprimalConditional]
    _ = ((outerPrimalLaw.filter (frozenStateEvent Rp Kp)
            (frozenStateEvent_support q ξp Rp Kp)).map eout).map erd := by
          rw [PMF.map_comp, PMF.map_comp, ← hfun]
    _ = ((law Dout q ξd).filter (frozenStateEvent Rd Kd)
            (frozenStateEvent_support q ξd Rd Kd)).map erd := by rw [hfiltered]
    _ = law Din q (BoundaryCondition.wired
          (generalRectangleDualBottomCollarInnerThreeSides a w h)) := by
          have hremoved := grbw_removed_eq_subgraphRemoved a w h
          let Rstd := subgraphRemovedEdges (Din.map ed) Dout
          let Kstd : RemovedConfiguration Dout Rstd := ⟨∅, Finset.empty_subset _⟩
          have hevent : frozenStateEvent Rd Kd = frozenStateEvent Rstd Kstd := by
            ext C
            change (C ∩ generalRectangleDualBottomCollarRemovedDualEdges a w h = ∅) ↔
              C ∩ subgraphRemovedEdges (Din.map ed) Dout = ∅
            rw [hremoved]
          have hfilter : (law Dout q ξd).filter (frozenStateEvent Rd Kd)
              (frozenStateEvent_support q ξd Rd Kd) =
            (law Dout q ξd).filter (frozenStateEvent Rstd Kstd)
              (frozenStateEvent_support q ξd Rstd Kstd) := by
            ext C
            rw [PMF.filter_apply, PMF.filter_apply, hevent]
          rw [congrArg (PMF.map erd) hfilter]
          simpa [erd, Din, Dout, Rstd, Kstd] using hdualConditional

end
end PottsContinuity.FKC.FiniteFK
