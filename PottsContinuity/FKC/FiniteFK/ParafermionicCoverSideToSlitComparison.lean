-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/ParafermionicCoverSideToSlitComparison.lean`, with
-- module and namespace relocated (wrappers of the SLE development replaced by `PottsContinuity.FKC.SLEWrap`)
-- and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.ParafermionicCoverRotatedSideEndpoint
public import PottsContinuity.FKC.FiniteFK.ParafermionicCoverRotatedOriginArc
public import PottsContinuity.FKC.FiniteFK.ParafermionicCoverRotatedEnlargementComparison
public import PottsContinuity.FKC.FiniteFK.SlitBoxShiftedProbabilityComparison
public import PottsContinuity.FKC.FiniteFK.ConnectionPathFiniteEnergy
public import PottsContinuity.FKC.FiniteFK.ParafermionicCoverBoundarySums
public import Mathlib.Tactic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.CategoryTheory.Countable
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Data.Int.Star
public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import Mathlib.Probability.ProbabilityMassFunction.Basic

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

open PottsContinuity.FKC PottsContinuity.FKC.Medial MeasureTheory
noncomputable section


private theorem coverBoxOrigin_mem (n : ℕ) :
    ((0, 0), 0) ∈ parafermionicCoverBoxVertices n := by
  rw [parafermionicCoverBoxVertices_mem]
  simp only
  have hn : 0 ≤ (n : ℤ) := Int.natCast_nonneg n
  have hpow : 0 ≤ ((n ^ 5 : ℕ) : ℤ) := by positivity
  omega

private theorem coverBoxWalk_of_side_extension
    (m : ℕ) {z w : ParafermionicCoverVertex}
    (hz : z ∈ parafermionicCoverBoxVertices m)
    (hw : w ∈ parafermionicCoverBoxVertices m)
    (hrel : z = w ∨ parafermionicCoverGraph.Adj z w) :
    ∃ r : (parafermionicCoverBoxGraph m).Walk ⟨z, hz⟩ ⟨w, hw⟩,
      r.length ≤ 1 := by
  rcases hrel with heq | hadj
  · have heq' : (⟨z, hz⟩ : ParafermionicCoverBoxVertex m) = ⟨w, hw⟩ :=
      Subtype.ext heq
    subst w
    exact ⟨SimpleGraph.Walk.nil, by simp⟩
  · have hadj' : (parafermionicCoverBoxGraph m).Adj ⟨z, hz⟩ ⟨w, hw⟩ := by
      change parafermionicCoverGraph.Adj z w
      exact hadj
    exact ⟨SimpleGraph.Walk.cons hadj' SimpleGraph.Walk.nil, by simp⟩

/-- Each actual cover exterior-neighbor vertex has a rotated bottom-side
representative that yields an actual slit-arc hit in the original FK law,
with only three finite-energy edge costs. The three costs are the two-edge
rotated-origin route and the at-most-one-edge bottom extension. -/
theorem parafermionicCoverBoxOriginConnectionWeight_le_slitBoxArcHit_of_side
    (n : ℕ) (hn : 1 ≤ n) (q : ClusterWeight)
    {v : ParafermionicCoverVertex}
    (hv : v ∈ parafermionicCoverExteriorNeighborBoundary n) :
    ∃ u : SlitBoxVertex (n + 1),
      u.val.2 = -((n + 1 : ℕ) : ℤ) ∧
      (1 / (1 + loopWeight q) : ℝ) ^ 3 *
          parafermionicCoverBoxOriginConnectionWeight n q v ≤
        (measure (slitBoxGraph (n + 1)) q (slitBoxBoundary (n + 1))
          (slitBoxWiredArcConnectionEvent (n + 1) u)).toReal := by
  classical
  have hv' := hv
  unfold parafermionicCoverExteriorNeighborBoundary at hv'
  have hvbox : v ∈ parafermionicCoverBoxVertices n := (Finset.mem_filter.mp hv').1
  obtain ⟨j, z, w, u, k, hklo, hkhi, hz, hside, hw, hwbox, hzrel, hEmbed⟩ :=
    parafermionicCoverRotatedSideEndpoint_shiftedInterior n hn hv
  obtain ⟨t, htbase, htsheet, p, hpLen⟩ :=
    parafermionicCoverQuarterTurn_origin_reaches_slitArcBase (n + 1) (by omega) j
  have hOmem : ((0, 0), 0) ∈ parafermionicCoverBoxVertices n := coverBoxOrigin_mem n
  have hImageMem : parafermionicCoverQuarterTurnOriginImage j ∈
      parafermionicCoverBoxVertices (n + 1) := by
    have h := parafermionicCoverQuarterTurn_iterates_mem_box_succ n ((0, 0), 0) hOmem j
    rw [← parafermionicCoverQuarterTurnIsoIterate_apply,
      parafermionicCoverQuarterTurn_iterate_origin_eq_routePoint] at h
    exact h
  have hzbox : z ∈ parafermionicCoverBoxVertices (n + 1) := by
    rw [hz]
    simpa only [parafermionicCoverQuarterTurnIsoIterate_apply] using
      (parafermionicCoverQuarterTurn_iterates_mem_box_succ n v
        hvbox j)
  let originImage : ParafermionicCoverBoxVertex (n + 1) :=
    ⟨parafermionicCoverQuarterTurnOriginImage j, hImageMem⟩
  let zImage : ParafermionicCoverBoxVertex (n + 1) := ⟨z, hzbox⟩
  let wImage : ParafermionicCoverBoxVertex (n + 1) := ⟨w, hwbox⟩
  have hOembed : parafermionicCoverQuarterTurnEnlargementEmbedding n j
      (parafermionicCoverBoxOrigin n) = originImage := by
    apply Subtype.ext
    rw [parafermionicCoverQuarterTurnEnlargementEmbedding_val,
      parafermionicCoverBoxOrigin_val, ← parafermionicCoverQuarterTurnIsoIterate_apply]
    exact parafermionicCoverQuarterTurn_iterate_origin_eq_routePoint j
  have hVembed : parafermionicCoverQuarterTurnEnlargementEmbedding n j
      ⟨v, hvbox⟩ = zImage := by
    apply Subtype.ext
    rw [parafermionicCoverQuarterTurnEnlargementEmbedding_val]
    change parafermionicCoverQuarterTurn^[j.val] v = z
    rw [← parafermionicCoverQuarterTurnIsoIterate_apply]
    exact hz.symm
  have hsource : parafermionicCoverBoxOriginConnectionWeight n q v =
      (measure (parafermionicCoverBoxGraph n) q
        (BoundaryCondition.free (∅ : Set (ParafermionicCoverBoxVertex n)))
        (connectivityEvent (parafermionicCoverBoxGraph n)
          (parafermionicCoverBoxOrigin n) ⟨v, hvbox⟩)).toReal := by
    simpa [ParafermionicAmbientGraph, ParafermionicAmbientVertex, connectivityEvent,
      measure] using
      (parafermionicCoverBoxOriginConnectionWeight_subtype n q
        (⟨v, hvbox⟩ : ParafermionicAmbientVertex n))
  have hrotate := parafermionicCoverQuarterTurn_enlargement_connection_probability_le
    n j q (parafermionicCoverBoxOrigin n) ⟨v, hvbox⟩
  have hrot :
      (measure (parafermionicCoverBoxGraph n) q
        (BoundaryCondition.free (∅ : Set (ParafermionicCoverBoxVertex n)))
        (connectivityEvent (parafermionicCoverBoxGraph n)
          (parafermionicCoverBoxOrigin n) ⟨v, hvbox⟩)).toReal ≤
      (measure (parafermionicCoverBoxGraph (n + 1)) q
        (BoundaryCondition.free (∅ : Set (ParafermionicCoverBoxVertex (n + 1))))
        {A | ActualConnected (parafermionicCoverBoxGraph (n + 1)) A
          originImage zImage}).toReal := by
    simpa [connectivityEvent, hOembed, hVembed] using hrotate
  obtain ⟨r, hrLen⟩ := coverBoxWalk_of_side_extension (n + 1) hzbox hwbox hzrel
  have hfinite := actualConnection_probability_two_walks_length_le
    (G := parafermionicCoverBoxGraph (n + 1)) q
    (BoundaryCondition.free (∅ : Set (ParafermionicCoverBoxVertex (n + 1))))
    p r 2 1 hpLen hrLen
  have hboxTargetCoords : t.val.1.1 = 0 ∧ 0 ≤ t.val.1.2 ∧
      t.val.1.2 ≤ (n + 1 : ℕ) := by
    rw [htbase]
    norm_num
    omega
  have htOutside := slitBoxSplitShiftedCover_arc_base_not_interior_image
    (n + 1) (by omega) k hklo hkhi t hboxTargetCoords
  have hshift := slitBoxShiftedCover_connection_probability_le_slit_wired_arc_hit
    (n + 1) (by omega) q k hklo hkhi u t htOutside
  have hEmbedSubtype : slitBoxSplitShiftedEmbedding (n + 1) (by omega) k
      hklo hkhi (Sum.inl u) = ⟨w, hwbox⟩ := by
    apply Subtype.ext
    exact hEmbed
  have hsetsym : {A : Configuration (parafermionicCoverBoxGraph (n + 1)) |
      ActualConnected (parafermionicCoverBoxGraph (n + 1)) A t wImage} =
      {A | ActualConnected (parafermionicCoverBoxGraph (n + 1)) A
        (slitBoxSplitShiftedEmbedding (n + 1) (by omega) k hklo hkhi (Sum.inl u)) t} := by
    ext A
    rw [hEmbedSubtype]
    exact ⟨fun h => h.symm, fun h => h.symm⟩
  have hshift' :
      (measure (parafermionicCoverBoxGraph (n + 1)) q
        (BoundaryCondition.free (∅ : Set (ParafermionicCoverBoxVertex (n + 1))))
        {A | ActualConnected (parafermionicCoverBoxGraph (n + 1)) A t wImage}).toReal ≤
      (measure (slitBoxGraph (n + 1)) q (slitBoxBoundary (n + 1))
        (slitBoxWiredArcConnectionEvent (n + 1) u.1)).toReal := by
    simpa only [← hsetsym] using hshift
  have hrotFinite :
      (1 / (1 + loopWeight q) : ℝ) ^ 3 *
        parafermionicCoverBoxOriginConnectionWeight n q v ≤
      (measure (parafermionicCoverBoxGraph (n + 1)) q
        (BoundaryCondition.free (∅ : Set (ParafermionicCoverBoxVertex (n + 1))))
        {A | ActualConnected (parafermionicCoverBoxGraph (n + 1)) A t wImage}).toReal := by
    have hε : 0 ≤ (1 / (1 + loopWeight q) : ℝ) := by
      exact div_nonneg (by norm_num)
        (le_of_lt (PottsContinuity.FKC.one_add_loopWeight_pos q))
    calc
      (1 / (1 + loopWeight q) : ℝ) ^ 3 *
          parafermionicCoverBoxOriginConnectionWeight n q v ≤
        (1 / (1 + loopWeight q) : ℝ) ^ 3 *
          (measure (parafermionicCoverBoxGraph n) q
            (BoundaryCondition.free (∅ : Set (ParafermionicCoverBoxVertex n)))
            (connectivityEvent (parafermionicCoverBoxGraph n)
              (parafermionicCoverBoxOrigin n) ⟨v, (Finset.mem_filter.mp hv).1⟩)).toReal :=
            mul_le_mul_of_nonneg_left hsource.le (pow_nonneg hε 3)
      _ ≤ (measure (parafermionicCoverBoxGraph (n + 1)) q
            (BoundaryCondition.free (∅ : Set (ParafermionicCoverBoxVertex (n + 1))))
            {A | ActualConnected (parafermionicCoverBoxGraph (n + 1)) A t wImage}).toReal := by
              have hrotScaled := mul_le_mul_of_nonneg_left hrot
                (pow_nonneg hε 3)
              calc
                _ ≤ (1 / (1 + loopWeight q) : ℝ) ^ 3 *
                    (measure (parafermionicCoverBoxGraph (n + 1)) q
                      (BoundaryCondition.free (∅ : Set
                        (ParafermionicCoverBoxVertex (n + 1))))
                      {A | ActualConnected (parafermionicCoverBoxGraph (n + 1)) A
                        originImage zImage}).toReal := hrotScaled
                _ ≤ (measure (parafermionicCoverBoxGraph (n + 1)) q
                      (BoundaryCondition.free (∅ : Set
                        (ParafermionicCoverBoxVertex (n + 1))))
                      {A | ActualConnected (parafermionicCoverBoxGraph (n + 1)) A t wImage}).toReal := by
                    simpa [originImage, zImage, wImage] using hfinite
  refine ⟨u.1, ?_, ?_⟩
  · have hbottom := congrArg (fun a : ParafermionicCoverVertex => a.1.2) hEmbed
    rw [hw] at hbottom
    simpa [slitBoxSplitShiftedEmbedding_val, slitBoxSplitCoverMap,
      slitBoxInteriorCoverLift, parafermionicCoverSheetTranslate] using hbottom
  · exact hrotFinite.trans hshift'

end
end PottsContinuity.FKC.FiniteFK
