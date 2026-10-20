-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `Curves/DualWalkAvoidance.lean`, with
-- module and namespace relocated (wrappers of the SLE development replaced by `PottsContinuity.FKC.SLEWrap`)
-- and declarations not used here removed.
module

public import PottsContinuity.FKC.Curves.ClosedDualWalk
public import PottsContinuity.FKC.Curves.LatticeWalkInterpolation

@[expose] public section

namespace PottsContinuity.FKC.Medial

open PottsContinuity.FKC.Curves Set

noncomputable section

private theorem dualAvoidEdge_subset (δ : PositiveMesh) (ω : LatticeConfiguration)
    {u v : LatticeVertex} (h : (wholePlaneClosedDualGraph ω).Adj u v) :
    ∃ d : LatticeBond,
      latticeConfigurationBondState ω (primalBondOfDual d) = false ∧
      Set.range (Path.segment (dualFaceCenter δ u) (dualFaceCenter δ v)) ⊆
        dualBondSegment δ d := by
  rcases (wholePlaneClosedDualGraph_adj_iff_dualBond ω u v).mp h with ⟨d, hc, hd | hd⟩
  · refine ⟨d, hc, ?_⟩
    rw [Path.range_segment, hd.1, hd.2]
    rfl
  · refine ⟨d, hc, ?_⟩
    rw [Path.range_segment, hd.1, hd.2]
    exact (segment_symm ℝ _ _).subset

private theorem dualSegment_avoids_primalVertex (δ : PositiveMesh)
    (u x : LatticeVertex) : dualFaceCenter δ u ≠ latticeEmbed δ x := by
  let b : LatticeBond := ⟨x, .horizontal⟩
  have hx : latticeEmbed δ x ∈ primalBondSegment δ b := by
    change latticeEmbed δ x ∈ segment ℝ (latticeEmbed δ b.source) (latticeEmbed δ b.target)
    simp [b, LatticeBond.source, LatticeBond.target, left_mem_segment]
  intro heq
  exact (dualFaceCenter_not_mem_primalBondSegment δ u b) (by simpa [heq] using hx)

private theorem dualSegment_range_avoids_vertex (δ : PositiveMesh) (ω : LatticeConfiguration)
    {u v : LatticeVertex} (h : (wholePlaneClosedDualGraph ω).Adj u v) (x : LatticeVertex)
    {z : ℂ} (hz : z ∈ Set.range (Path.segment (dualFaceCenter δ u) (dualFaceCenter δ v))) :
    z ≠ latticeEmbed δ x := by
  obtain ⟨d, _, hsub⟩ := dualAvoidEdge_subset δ ω h
  intro heq
  apply latticeVertex_not_mem_dualBondSegment δ x d
  simpa [heq] using hsub hz

private theorem dualSegment_range_avoids_openBond (δ : PositiveMesh) (ω : LatticeConfiguration)
    {u v : LatticeVertex} (h : (wholePlaneClosedDualGraph ω).Adj u v) (b : LatticeBond)
    (hb : latticeConfigurationBondState ω b = true)
    {z : ℂ} (hz : z ∈ Set.range (Path.segment (dualFaceCenter δ u) (dualFaceCenter δ v))) :
    z ∉ primalBondSegment δ b := by
  obtain ⟨d, hclosed, hsub⟩ := dualAvoidEdge_subset δ ω h
  have hdis := openPrimal_disjoint_closedDual_segments δ ω b d hb hclosed
  rw [Set.disjoint_left] at hdis
  intro hzP
  exact hdis hzP (hsub hz)

theorem closedDualWalkPath_avoids_vertex_of_any_endpoints (δ : PositiveMesh)
    (ω : LatticeConfiguration) {u v : LatticeVertex}
    (p : (wholePlaneClosedDualGraph ω).Walk u v) (x : LatticeVertex)
    {z : ℂ} (hz : z ∈ Set.range (closedDualWalkPath δ ω p)) :
    z ≠ latticeEmbed δ x := by
  induction p generalizing z with
  | nil =>
      rcases hz with ⟨t, ht, rfl⟩
      exact dualSegment_avoids_primalVertex δ _ x
  | @cons a b c h p ih =>
      change z ∈ Set.range ((Path.segment (dualFaceCenter δ a) (dualFaceCenter δ b)).trans
        (closedDualWalkPath δ ω p)) at hz
      rw [Path.trans_range] at hz
      rcases hz with hz | hz
      · exact dualSegment_range_avoids_vertex δ ω h x hz
      · exact ih hz

theorem closedDualWalkPath_avoids_openPrimal_of_any_endpoints (δ : PositiveMesh)
    (ω : LatticeConfiguration) {u v : LatticeVertex}
    (p : (wholePlaneClosedDualGraph ω).Walk u v) (b : LatticeBond)
    (hb : latticeConfigurationBondState ω b = true)
    {z : ℂ} (hz : z ∈ Set.range (closedDualWalkPath δ ω p)) :
    z ∉ primalBondSegment δ b := by
  induction p generalizing z with
  | nil =>
      rcases hz with ⟨t, ht, rfl⟩
      exact dualFaceCenter_not_mem_primalBondSegment δ _ b
  | @cons a c d h p ih =>
      change z ∈ Set.range ((Path.segment (dualFaceCenter δ a) (dualFaceCenter δ c)).trans
        (closedDualWalkPath δ ω p)) at hz
      rw [Path.trans_range] at hz
      rcases hz with hz | hz
      · exact dualSegment_range_avoids_openBond δ ω h b hb hz
      · exact ih hz

theorem closedDualWalkPath_range_disjoint_openPrimal_any (δ : PositiveMesh)
    (ω : LatticeConfiguration) {u v : LatticeVertex}
    (p : (wholePlaneClosedDualGraph ω).Walk u v) (b : LatticeBond)
    (hb : latticeConfigurationBondState ω b = true) :
    Disjoint (Set.range (closedDualWalkPath δ ω p)) (primalBondSegment δ b) := by
  rw [Set.disjoint_left]
  intro z hzPath hzBond
  exact (closedDualWalkPath_avoids_openPrimal_of_any_endpoints δ ω p b hb hzPath) hzBond

def openPrimalWalkToLatticeWalk {ω : LatticeConfiguration} : {u v : LatticeVertex} →
    (wholePlaneOpenPrimalGraph ω).Walk u v → squareLattice.Walk u v
  | _, _, .nil => .nil
  | _, _, .cons h p => .cons h.1 (openPrimalWalkToLatticeWalk p)

private theorem openAdj_exists_bond (ω : LatticeConfiguration) {u v : LatticeVertex}
    (h : (wholePlaneOpenPrimalGraph ω).Adj u v) :
    ∃ b : LatticeBond, b.toSym2 = s(u,v) ∧
      latticeConfigurationBondState ω b = true := by
  rcases h with ⟨hadj, hstate⟩
  obtain ⟨b, hb⟩ := LatticeBond.exists_of_adj hadj
  refine ⟨b, hb, ?_⟩
  have hedge : (latticeBondEdge b : squareLattice.edgeSet) =
      ⟨s(u,v), squareLattice.mem_edgeSet.mpr hadj⟩ := by
    apply Subtype.ext
    change b.toSym2 = s(u,v)
    exact hb
  change ω (latticeBondEdge b) = true
  rw [hedge]
  exact hstate

private theorem latticeSegment_eq_primalBondSegment (δ : PositiveMesh)
    {u v : LatticeVertex} {b : LatticeBond} (hb : b.toSym2 = s(u,v)) :
    Set.range (Path.segment (latticeEmbed δ u) (latticeEmbed δ v)) =
      primalBondSegment δ b := by
  rw [Path.range_segment]
  change segment ℝ (latticeEmbed δ u) (latticeEmbed δ v) =
    segment ℝ (latticeEmbed δ b.source) (latticeEmbed δ b.target)
  have hs : s(b.source,b.target) = s(u,v) := by
    simpa [LatticeBond.toSym2] using hb
  rcases Sym2.eq_iff.mp hs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rfl
  · exact segment_symm ℝ _ _

/-- The straight interpolation of an actual open-primal graph walk is disjoint
from the actual closed-dual interpolation in the same configuration. The
primal path uses the existing `latticeWalkPath` after forgetting only the
open-state witness on each original edge. -/
theorem closedDualWalkPath_range_disjoint_openPrimalWalk
    (δ : PositiveMesh) (ω : LatticeConfiguration) {u v x y : LatticeVertex}
    (p : (wholePlaneClosedDualGraph ω).Walk u v)
    (q : (wholePlaneOpenPrimalGraph ω).Walk x y) :
    Disjoint (Set.range (closedDualWalkPath δ ω p))
      (Set.range (latticeWalkPath δ (openPrimalWalkToLatticeWalk (ω := ω) q))) := by
  rw [Set.disjoint_left]
  intro z hzDual hzPrimal
  induction q generalizing z with
  | @nil a =>
      rcases hzPrimal with ⟨t, ht, rfl⟩
      exact (closedDualWalkPath_avoids_vertex_of_any_endpoints δ ω p a hzDual)
        (by simp [latticeWalkPath, openPrimalWalkToLatticeWalk])
  | @cons a b c h q ih =>
      change z ∈ Set.range ((Path.segment (latticeEmbed δ a) (latticeEmbed δ b)).trans
        (latticeWalkPath δ (openPrimalWalkToLatticeWalk (ω := ω) q))) at hzPrimal
      rw [Path.trans_range] at hzPrimal
      rcases hzPrimal with hzHead | hzTail
      · obtain ⟨e, he, hopen⟩ := openAdj_exists_bond ω h
        have heq := latticeSegment_eq_primalBondSegment δ he
        rw [heq] at hzHead
        exact (closedDualWalkPath_avoids_openPrimal_of_any_endpoints
          δ ω p e hopen hzDual) hzHead
      · exact ih hzDual hzTail

end
end PottsContinuity.FKC.Medial
