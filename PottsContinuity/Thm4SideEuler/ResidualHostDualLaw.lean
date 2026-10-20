module

public import PottsContinuity.Thm4Side.SideExactLawSpecialization
public import PottsContinuity.FKC.FiniteFK.SlitBoxDomain

@[expose] public section

namespace PottsContinuity.Thm4SideEuler

open PottsContinuity.DualityExt
open PottsContinuity.Exploration
open PottsContinuity.PD.FK
open PottsContinuity.RSW
open PottsContinuity.Thm4
open PottsContinuity.Thm4Plane
open PottsContinuity.Thm4Side

noncomputable section

local instance sideResidualHostDualEdgeFintype {V : Type*} [Finite V]
    {G : SimpleGraph V} : Fintype G.edgeSet := Fintype.ofFinite _

local instance sideResidualHostDualConfigFintype {V : Type*} [Finite V]
    {G : SimpleGraph V} : Fintype (PD.FK.Configuration G) := Fintype.ofFinite _

local instance sideResidualHostDualRestrictedConfigFintype {V : Type*} [Finite V]
    {G : SimpleGraph V} (R : PD.FK.Configuration G) :
    Fintype (PD.FK.Configuration (edgeRestriction G R)) := Fintype.ofFinite _

local instance sideResidualHostDualRemainingFintype {V : Type*} [Finite V]
    {G : SimpleGraph V} (R : PD.FK.Configuration G) :
    Fintype (PD.FK.RemainingConfiguration G R) := Fintype.ofFinite _

private theorem remainingLaw_map_conditioned_subgraphDual_of_partition_eq
    {a : LatticeVertex} {w h : ℕ}
    {V : Type*} [Finite V] {G : SimpleGraph V}
    (R O : PD.FK.Configuration G)
    (f : positiveActiveVertexSet (edgeRestriction G R) ↪
      RectangleVertex a w h)
    (q : Set.Ici (1 : ℝ)) (ξ : PD.FK.BoundaryCondition V)
    (hJR : (positiveActiveGraph (edgeRestriction G R)).map f ≤
      rectangleGraph a w h)
    (H : RemovedConfiguration (rectangleGraph a w h)
      (subgraphRemovedEdges
        ((positiveActiveGraph (edgeRestriction G R)).map f)
        (rectangleGraph a w h)))
    (hξ : (isolatedExtensionPullbackBoundary
        (positiveActiveInclusion (edgeRestriction G R))
        (frozenBoundary ξ O)).partition =
      (isolatedExtensionPullbackBoundary f
        (frozenBoundary (BoundaryCondition.free ∅) H.val)).partition) :
    (remainingLaw G (criticalParameters q) (frozenBoundary ξ O) R).map
        ((edgeRestrictionConfigurationEquiv G R).symm.trans
          ((positiveActiveConfigurationEquiv (edgeRestriction G R)).symm.trans
            ((isolatedExtensionConfigurationEquiv
                (positiveActiveGraph (edgeRestriction G R)) f).trans
              (rectangleSubgraphDualConfigurationEquiv hJR)))) =
      law (rectangleSubgraphDualGraph hJR) (criticalParameters q)
        (frozenBoundary (rectangleDualBoundaryCondition a w h)
          (rectangleSubgraphDualOpenRemovedState hJR H).val) := by
  let J := edgeRestriction G R
  let A := positiveActiveGraph J
  let θ := criticalParameters q
  let ξ₀ := frozenBoundary ξ O
  let ξA := isolatedExtensionPullbackBoundary (positiveActiveInclusion J) ξ₀
  let aeq := positiveActiveConfigurationEquiv J
  let δ := (isolatedExtensionConfigurationEquiv A f).trans
    (rectangleSubgraphDualConfigurationEquiv hJR)
  let ξD := frozenBoundary (rectangleDualBoundaryCondition a w h)
    (rectangleSubgraphDualOpenRemovedState hJR H).val
  have hrem : (remainingLaw G θ ξ₀ R).map
      (edgeRestrictionConfigurationEquiv G R).symm = law J θ ξ₀ := by
    ext B
    rw [FiniteProbability.map_equiv_apply]
    simpa only [Equiv.symm_symm] using
      (remainingLaw_apply_edgeRestriction (G := G) θ ξ₀ R B)
  have hactivePos := positiveFKLaw_activeGraph_map_boundary_pullback J
    (clusterWeight_pos θ) (edgeParameter_pos θ) (edgeParameter_lt_one θ) ξ₀
  have hactivePos' :
      (positiveFKLaw A θ.val (edgeParameter θ) (clusterWeight_pos θ)
        (edgeParameter_pos θ) (edgeParameter_lt_one θ) ξA).map aeq =
      positiveFKLaw J θ.val (edgeParameter θ) (clusterWeight_pos θ)
        (edgeParameter_pos θ) (edgeParameter_lt_one θ) ξ₀ := by
    simpa [A, ξA, aeq, positiveActiveConfigurationEquiv] using hactivePos
  have hactivePosBack :
      (positiveFKLaw J θ.val (edgeParameter θ) (clusterWeight_pos θ)
        (edgeParameter_pos θ) (edgeParameter_lt_one θ) ξ₀).map aeq.symm =
      positiveFKLaw A θ.val (edgeParameter θ) (clusterWeight_pos θ)
        (edgeParameter_pos θ) (edgeParameter_lt_one θ) ξA := by
    calc
      _ = ((positiveFKLaw A θ.val (edgeParameter θ) (clusterWeight_pos θ)
          (edgeParameter_pos θ) (edgeParameter_lt_one θ) ξA).map aeq).map
            aeq.symm := by rw [hactivePos']
      _ = _ := by
        rw [PMF.map_comp]
        have hcomp : aeq.symm ∘ aeq = id := by
          funext C
          exact Equiv.symm_apply_apply aeq C
        rw [hcomp, PMF.map_id]
  have hactive : (law J θ ξ₀).map aeq.symm = law A θ ξA := by
    rw [← positiveFKLaw_eq_PD_law (G := J) (θ := θ) (ξ := ξ₀)]
    rw [← positiveFKLaw_eq_PD_law (G := A) (θ := θ) (ξ := ξA)]
    exact hactivePosBack
  have hdual :=
    embedded_subgraph_conditioned_duality_law_PD_at_selfDualParameter_of_partition_eq
      (J := A) f hJR q ξA H hξ ξD rfl
  calc
    _ = (((remainingLaw G θ ξ₀ R).map
          (edgeRestrictionConfigurationEquiv G R).symm).map aeq.symm).map δ := by
          rw [PMF.map_comp, PMF.map_comp]
          rfl
    _ = ((law J θ ξ₀).map aeq.symm).map δ := by rw [hrem]
    _ = (law A θ ξA).map δ := by rw [hactive]
    _ = law (rectangleSubgraphDualGraph hJR) θ ξD := hdual

/-- The right fixed-reveal residual law on the retained host-dual graph.
The boundary records the host exterior wiring and the dual image of the
auxiliary open ring together with the revealed source state. -/
theorem slitRight_residual_hostDual_law (m : ℕ)
    (q : Set.Ici (1 : ℝ))
    (X : PD.FK.Configuration
      (PottsContinuity.FKC.FiniteFK.slitBoxGraph (16 * m))) :
    (remainingLaw (PottsContinuity.FKC.FiniteFK.slitBoxGraph (16 * m)) (criticalParameters q)
      (frozenBoundary (fkcBoundaryToPD
        (PottsContinuity.FKC.FiniteFK.slitBoxBoundary (16 * m)))
        (revealRecordConfiguration (slitRightDualRectangleReveal m) X).val)
      (slitRightDualRectangleReveal m X)).map
        ((edgeRestrictionConfigurationEquiv
            (PottsContinuity.FKC.FiniteFK.slitBoxGraph (16 * m))
            (slitRightDualRectangleReveal m X)).symm.trans
          ((positiveActiveConfigurationEquiv
              (edgeRestriction (PottsContinuity.FKC.FiniteFK.slitBoxGraph (16 * m))
                (slitRightDualRectangleReveal m X))).symm.trans
            ((isolatedExtensionConfigurationEquiv
                (positiveActiveGraph (edgeRestriction
                  (PottsContinuity.FKC.FiniteFK.slitBoxGraph (16 * m))
                  (slitRightDualRectangleReveal m X)))
                (sideExactLawHostEmbedding m
                  (slitRightDualRectangleReveal m X))).trans
              (rectangleSubgraphDualConfigurationEquiv
                (sideExactLawHostSubgraph_le m
                  (slitRightDualRectangleReveal m X)))))) =
      law
        (rectangleSubgraphDualGraph
          (sideExactLawHostSubgraph_le m
            (slitRightDualRectangleReveal m X)))
        (criticalParameters q)
        (frozenBoundary
          (rectangleDualBoundaryCondition
            (-((16 * m + 1 : ℕ) : ℤ), -((16 * m + 1 : ℕ) : ℤ))
            (2 * (16 * m + 1)) (2 * (16 * m + 1)))
          (rectangleSubgraphDualOpenRemovedState
            (sideExactLawHostSubgraph_le m
              (slitRightDualRectangleReveal m X))
            (slitRightDualRectangleHostRemovedState m X)).val) := by
  let R := slitRightDualRectangleReveal m X
  let O := (revealRecordConfiguration (slitRightDualRectangleReveal m) X).val
  let f := sideExactLawHostEmbedding m R
  let hJR := sideExactLawHostSubgraph_le m R
  let H := slitRightDualRectangleHostRemovedState m X
  have hmain := remainingLaw_map_conditioned_subgraphDual_of_partition_eq
    (a := (-((16 * m + 1 : ℕ) : ℤ), -((16 * m + 1 : ℕ) : ℤ)))
    (w := 2 * (16 * m + 1)) (h := 2 * (16 * m + 1))
    R O f q (fkcBoundaryToPD
      (PottsContinuity.FKC.FiniteFK.slitBoxBoundary (16 * m)))
    hJR H (slitRightDualRectangle_sourcePartition m X)
  convert hmain using 1

end
end PottsContinuity.Thm4SideEuler
