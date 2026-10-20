module

public import PottsContinuity.DualityExt.PositiveAnnulusPrimalDMP
public import PottsContinuity.DualityExt.PositiveBoundaryMergePDTransfer
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Probability.ProbabilityMassFunction.Constructions

@[expose] public section

namespace PottsContinuity.DualityExt

open PottsContinuity.PD.FK

noncomputable section

/-- The event-level annulus transfer retains a specified dual subevent. If
that event is contained in the exact dual image of primal disconnection, its
probability transfers to the same pullback under joint wiring. -/
theorem annulus_jointWired_dualSubevent_measure_ge_div_of_doubleDualGeometry
    (N : ℕ) (hN : 1 ≤ N)
    {a : LatticeVertex} {w h : ℕ}
    {K : SimpleGraph (RectangleVertex a w h)}
    (hK : K ≤ rectangleGraph a w h)
    (e : positiveActiveVertexSet (rectangleSubgraphDualGraph hK) ≃
      {v : LatticeVertex // v ∈ annulusVertexSet N})
    (hgraph : (positiveActiveGraph (rectangleSubgraphDualGraph hK)).map
        e.toEmbedding = annulusSourceGraph N)
    (hpartition : (positiveWiredSubgraphDualBoundary hK e).partition =
        (annulusPrimalSeparatedBoundary N hN).partition)
    (q : Set.Ici (1 : ℝ)) (c : ℝ)
    (u v : {x : LatticeVertex // x ∈ annulusVertexSet N})
    (hu : u ∈ annulusPrimalInnerBoundaryClass N hN)
    (hv : v ∈ annulusPrimalOuterBoundaryClass N hN)
    (S T : Set (Configuration K))
    (hevent : positiveBoundaryDisconnectedEvent (G := annulusSourceGraph N)
        (positiveTwoBlockBoundary
          (annulusPrimalInnerBoundaryClass N hN)
          (annulusPrimalOuterBoundaryClass N hN)
          (annulusPrimalInnerOuter_disjoint N hN)) u v =
        (annulusPrimalToEmbeddedDualConfigurationEquiv N hK e hgraph) ⁻¹' S)
    (hTsubset : T ⊆ S)
    (hdual : c ≤ (PottsContinuity.PD.FK.measure K
        (PottsContinuity.PD.FK.criticalParameters q)
        (BoundaryCondition.free ∅) T).toReal) :
    c / (q : ℝ) ≤
      (PottsContinuity.PD.FK.measure (annulusSourceGraph N)
        (PottsContinuity.PD.FK.criticalParameters q)
        (BoundaryCondition.wired
          (annulusPrimalInnerBoundaryClass N hN ∪
            annulusPrimalOuterBoundaryClass N hN))
        ((annulusPrimalToEmbeddedDualConfigurationEquiv N hK e hgraph) ⁻¹' T)).toReal := by
  let I := annulusPrimalInnerBoundaryClass N hN
  let O := annulusPrimalOuterBoundaryClass N hN
  let ξ := positiveTwoBlockBoundary I O (annulusPrimalInnerOuter_disjoint N hN)
  let d := annulusPrimalToEmbeddedDualConfigurationEquiv N hK e hgraph
  have hsep : (annulusPrimalSeparatedBoundary N hN).partition = ξ.partition := by
    simpa only [I, O, ξ] using annulusPrimalSeparatedBoundary_partition_eq_twoBlock N hN
  have hrename := PottsContinuity.PD.FK.law_eq_of_boundary_partition_eq
    (G := annulusSourceGraph N)
    (PottsContinuity.PD.FK.criticalParameters q) ξ
    (annulusPrimalSeparatedBoundary N hN) hsep.symm
  have hseparateLaw := annulus_separatelyWired_law_eq_embeddedDual_free_at_selfDualParameter_of_doubleDualGeometry
    N hN hK e hgraph hpartition q
  have hlaw :
      (PottsContinuity.PD.FK.law (annulusSourceGraph N)
        (PottsContinuity.PD.FK.criticalParameters q) ξ).map d =
      PottsContinuity.PD.FK.law K
        (PottsContinuity.PD.FK.criticalParameters q)
        (BoundaryCondition.free ∅) := by
    calc
      _ = (PottsContinuity.PD.FK.law (annulusSourceGraph N)
          (PottsContinuity.PD.FK.criticalParameters q)
          (annulusPrimalSeparatedBoundary N hN)).map d :=
            congrArg (fun μ => μ.map d) hrename
      _ = _ := hseparateLaw
  exact positive_twoBlock_dual_transfer_measure_ge_div_at_selfDualParameter_of_law_and_subEvent
    q c I O (annulusPrimalInnerOuter_disjoint N hN) (u := u) (v := v) hu hv
    (BoundaryCondition.free ∅) d S T hlaw
    (by simpa only [I, O, d] using hevent) hTsubset hdual

end

end PottsContinuity.DualityExt
