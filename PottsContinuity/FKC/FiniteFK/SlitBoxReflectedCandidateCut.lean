-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/SlitBoxReflectedCandidateCut.lean`, with
-- module and namespace relocated (wrappers of the SLE development replaced by `PottsContinuity.FKC.SLEWrap`)
-- and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.SlitBoxCandidateOuterStarRevealed
public import PottsContinuity.FKC.FiniteFK.SlitBoxBottomCenterUnrevealed
public import PottsContinuity.FKC.FiniteFK.SlitBoxHorizontalReflection
public import PottsContinuity.FKC.FiniteFK.Isomorphism
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

open PottsContinuity.FKC

/-- The reflected reveal cut is the literal image of the actual candidate
filling's incident-edge configuration under the graph-isomorphism edge map. -/
noncomputable def slitBoxReflectedCandidateCellIncidentCut
    (n : ℕ) (hn : 1 ≤ n) (u : SlitBoxVertex n)
    (huY : u.val.2 = -(n : ℤ)) (huX : 0 ≤ u.val.1)
    (δ : PositiveMesh) (p : SlitBoxFirstHitBaseCandidates n u) :
    Configuration (slitBoxGraph n) :=
  configurationIso (slitBoxGraphHorizontalReflectionIso n)
    (slitBoxCellIncidentEdges n
      ((slitBoxFirstHitCandidatePolygon n hn u huY huX p).interiorCellBases δ))

/-- Membership in the reflected cut pulls back by the inverse edge-set
equivalence, preserving the actual edge subtype. -/
theorem mem_slitBoxReflectedCandidateCellIncidentCut_iff
    (n : ℕ) (hn : 1 ≤ n) (u : SlitBoxVertex n)
    (huY : u.val.2 = -(n : ℤ)) (huX : 0 ≤ u.val.1)
    (δ : PositiveMesh) (p : SlitBoxFirstHitBaseCandidates n u)
    (e : (slitBoxGraph n).edgeSet) :
    e ∈ slitBoxReflectedCandidateCellIncidentCut n hn u huY huX δ p ↔
      (configurationIsoEdgeEquiv (slitBoxGraphHorizontalReflectionIso n)).symm e ∈
        slitBoxCellIncidentEdges n
          ((slitBoxFirstHitCandidatePolygon n hn u huY huX p).interiorCellBases δ) := by
  classical
  let σ := slitBoxGraphHorizontalReflectionIso n
  let C := slitBoxCellIncidentEdges n
    ((slitBoxFirstHitCandidatePolygon n hn u huY huX p).interiorCellBases δ)
  change e ∈ C.map (configurationIsoEdgeEquiv σ).toEmbedding ↔
    (configurationIsoEdgeEquiv σ).symm e ∈ C
  exact Finset.mem_map_equiv

private theorem slitBoxReflection_involutive
    (n : ℕ) (v : SlitBoxVertex n) :
    slitBoxGraphHorizontalReflectionIso n
        (slitBoxGraphHorizontalReflectionIso n v) = v := by
  apply Subtype.ext
  have hval (x : SlitBoxVertex n) :
      (slitBoxGraphHorizontalReflectionIso n x).val = (-x.val.1, x.val.2) := rfl
  rw [hval, hval]
  ext <;> simp

private theorem slitBoxReflectedEdge_incident_iff
    (n : ℕ) (v : SlitBoxVertex n) (e : (slitBoxGraph n).edgeSet) :
    v ∈ e.val ↔
      (slitBoxGraphHorizontalReflectionIso n v) ∈
        ((configurationIsoEdgeEquiv (slitBoxGraphHorizontalReflectionIso n)).symm e).val := by
  let σ := slitBoxGraphHorizontalReflectionIso n
  let f := (configurationIsoEdgeEquiv σ).symm e
  have hmap : configurationIsoEdgeEquiv σ f = e := Equiv.apply_symm_apply _ _
  have hval : Sym2.map σ f.val = e.val := by
    simpa [f, configurationIsoEdgeEquiv, σ] using congrArg Subtype.val hmap
  constructor
  · intro hv
    have hv' : v ∈ Sym2.map σ f.val := by simpa [hval] using hv
    obtain ⟨w, hw, hwi⟩ := Sym2.mem_map.mp hv'
    have hweq : σ w = v := hwi
    have : σ v = w := by
      calc
        σ v = σ (σ w) := by rw [hweq]
        _ = w := slitBoxReflection_involutive n w
    exact this.symm ▸ hw
  · intro hv
    have hv' : v ∈ Sym2.map σ f.val := by
      exact Sym2.mem_map.mpr ⟨σ v, hv, slitBoxReflection_involutive n v⟩
    change v ∈ e.val
    rw [← hval]
    exact hv'

/-- At a vertex whose reflected image is off the candidate path and wired arc,
every incident edge has the same reveal status in the reflected cut as the
actual right-candidate cell-incidence status at the reflected vertex. -/
theorem slitBoxReflectedCandidateCellIncidentCut_incident_edge_mem_iff
    (n : ℕ) (hn : 1 ≤ n) (u : SlitBoxVertex n)
    (huY : u.val.2 = -(n : ℤ)) (huX : 0 ≤ u.val.1)
    (δ : PositiveMesh) (p : SlitBoxFirstHitBaseCandidates n u)
    (v : SlitBoxVertex n)
    (hvPath : (slitBoxGraphHorizontalReflectionIso n v) ∉
      (p.val.2 : (slitBoxGraph n).Walk u p.val.1).support)
    (hvArc : slitBoxGraphHorizontalReflectionIso n v ∉ slitBoxWiredArc n)
    (e : (slitBoxGraph n).edgeSet) (hincident : v ∈ e.val) :
    e ∈ slitBoxReflectedCandidateCellIncidentCut n hn u huY huX δ p ↔
      (slitBoxGraphHorizontalReflectionIso n v).val ∈
        (slitBoxFirstHitCandidatePolygon n hn u huY huX p).interiorCellBases δ := by
  rw [mem_slitBoxReflectedCandidateCellIncidentCut_iff]
  have hincident' := (slitBoxReflectedEdge_incident_iff n v e).mp hincident
  have hstar := slitBoxCandidate_off_path_arc_incident_edge_mem_iff_cell_mem
    n hn u huY huX δ p (slitBoxGraphHorizontalReflectionIso n v) hvPath hvArc
    ((configurationIsoEdgeEquiv (slitBoxGraphHorizontalReflectionIso n)).symm e)
    hincident'
  exact hstar

/-- The reflected image of the literal bottom-center vertex is itself. -/
theorem slitBoxGraphHorizontalReflection_fixes_bottomCenter (n : ℕ) :
    slitBoxGraphHorizontalReflectionIso n (slitBoxBottomCenterVertex n) =
      slitBoxBottomCenterVertex n := by
  apply Subtype.ext
  have hval (v : SlitBoxVertex n) :
      (slitBoxGraphHorizontalReflectionIso n v).val = (-v.val.1, v.val.2) := rfl
  rw [hval, slitBoxBottomCenterVertex_val]
  simp

/-- If the bottom center is off the retained candidate path, all its actual
incident slit edges lie outside the reflected reveal cut. -/
theorem slitBoxBottomCenter_all_incident_edges_outside_reflectedCut
    (n : ℕ) (hn : 1 ≤ n) (u : SlitBoxVertex n)
    (huY : u.val.2 = -(n : ℤ)) (huX : 0 < u.val.1)
    (δ : PositiveMesh) (p : SlitBoxFirstHitBaseCandidates n u)
    (hcenterPath : slitBoxBottomCenterVertex n ∉
      (p.val.2 : (slitBoxGraph n).Walk u p.val.1).support)
    (e : (slitBoxGraph n).edgeSet)
    (hincident : slitBoxBottomCenterVertex n ∈ e.val) :
    e ∉ slitBoxReflectedCandidateCellIncidentCut n hn u huY (le_of_lt huX) δ p := by
  intro he
  have he' := (mem_slitBoxReflectedCandidateCellIncidentCut_iff
    n hn u huY (le_of_lt huX) δ p e).mp he
  have hincident' : slitBoxBottomCenterVertex n ∈
      ((configurationIsoEdgeEquiv (slitBoxGraphHorizontalReflectionIso n)).symm e).val := by
    have h := (slitBoxReflectedEdge_incident_iff n
      (slitBoxBottomCenterVertex n) e).mp hincident
    simpa [slitBoxGraphHorizontalReflection_fixes_bottomCenter] using h
  exact (slitBoxBottomCenter_all_incident_edges_unrevealed
    n hn u huY huX δ p hcenterPath
    ((configurationIsoEdgeEquiv (slitBoxGraphHorizontalReflectionIso n)).symm e)
    hincident') he'

/-- Transport of the actual right/top exterior reveal to the left side using
the same candidate's literal reflected incident-edge configuration. -/
theorem slitBoxFirstHitCandidate_reflected_left_star_incident_edges_revealed
    (n : ℕ) (hn : 1 ≤ n) (u : SlitBoxVertex n)
    (huY : u.val.2 = -(n : ℤ)) (huX : 0 ≤ u.val.1)
    (δ : PositiveMesh) (p : SlitBoxFirstHitBaseCandidates n u)
    (v : SlitBoxVertex n)
    (hvPath : (slitBoxGraphHorizontalReflectionIso n v) ∉
      (p.val.2 : (slitBoxGraph n).Walk u p.val.1).support)
    (hvArc : slitBoxGraphHorizontalReflectionIso n v ∉ slitBoxWiredArc n)
    (hside : v.val.1 = -(n : ℤ) ∨
      (v.val.2 = n ∧ v.val.1 ≤ 0))
    (e : (slitBoxGraph n).edgeSet) (hincident : v ∈ e.val) :
    e ∈ slitBoxReflectedCandidateCellIncidentCut n hn u huY huX δ p := by
  apply (slitBoxReflectedCandidateCellIncidentCut_incident_edge_mem_iff
    n hn u huY huX δ p v hvPath hvArc e hincident).2
  have hside' :
      (slitBoxGraphHorizontalReflectionIso n v).val.1 = n ∨
        ((slitBoxGraphHorizontalReflectionIso n v).val.2 = n ∧
          0 ≤ (slitBoxGraphHorizontalReflectionIso n v).val.1) := by
    rcases hside with hleft | ⟨htop, hneg⟩
    · left
      change -v.val.1 = n
      omega
    · right
      change v.val.2 = n ∧ 0 ≤ -v.val.1
      exact ⟨htop, by omega⟩
  have hrevealed := slitBoxFirstHitCandidate_outer_star_incident_edges_revealed
    n hn u huY huX δ p (slitBoxGraphHorizontalReflectionIso n v)
    hvPath hvArc hside'
    ((configurationIsoEdgeEquiv (slitBoxGraphHorizontalReflectionIso n)).symm e)
    ((slitBoxReflectedEdge_incident_iff n v e).mp hincident)
  have hcell := (slitBoxCandidate_off_path_arc_incident_edge_mem_iff_cell_mem
    n hn u huY huX δ p (slitBoxGraphHorizontalReflectionIso n v) hvPath hvArc
    ((configurationIsoEdgeEquiv (slitBoxGraphHorizontalReflectionIso n)).symm e)
    ((slitBoxReflectedEdge_incident_iff n v e).mp hincident)).mp hrevealed
  exact hcell

end PottsContinuity.FKC.FiniteFK
