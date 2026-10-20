-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/SlitBoxPairedCandidateRestoration.lean`, with
-- module and namespace relocated (wrappers of the SLE development replaced by `PottsContinuity.FKC.SLEWrap`)
-- and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.SlitBoxPairedCandidateComponent
public import PottsContinuity.FKC.FiniteFK.SlitBoxCandidateReflection
public import PottsContinuity.FKC.FiniteFK.SlitBoxOpenCandidateVertexConnection
public import PottsContinuity.FKC.FiniteFK.RemainingConnectionRestoration
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Paths

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

noncomputable section

private theorem slitBox_actualConnected_refl
    (n : ℕ) (A : Configuration (slitBoxGraph n)) (v : SlitBoxVertex n) :
    ActualConnected (slitBoxGraph n) A v v := by
  apply (actualConnected_iff_walk (slitBoxGraph n) A v v).2
  exact ⟨SimpleGraph.Walk.nil⟩

/-- Every vertex of the paired exception has an actual connection through the
frozen candidate paths to the wired arc. -/
theorem slitBoxPairedCandidateException_bridges_to_arc
    (n : ℕ) (_hn : 1 ≤ n) (u : SlitBoxVertex n)
    (_huY : u.val.2 = -(n : ℤ)) (_huX : 0 < u.val.1)
    (_δ : PositiveMesh) (p q : SlitBoxFirstHitBaseCandidates n u)
    (K : Configuration (slitBoxGraph n))
    (hpK : slitBoxCandidateOriginalPathEdgeSupport n u p ⊆ K)
    (hqK : slitBoxCandidateOriginalPathEdgeSupport n
        (slitBoxReflectVertex n u) (slitBoxReflectCandidate n u q) ⊆ K) :
    ∀ v ∈ slitBoxPairedCandidateException n u p q,
      ∃ z ∈ slitBoxWiredArc n, ActualConnected (slitBoxGraph n) K v z := by
  intro v hv
  simp only [slitBoxPairedCandidateException, Set.mem_ofPred_eq] at hv
  rcases hv with hp | hq | harc
  · have hconn := slitBoxCandidate_vertex_actualConnected_to_endpoint_of_open
      n u p K hpK v hp
    exact ⟨p.val.1, p.property.1, hconn⟩
  · let σ := slitBoxGraphHorizontalReflectionIso n
    let rp := slitBoxReflectCandidate n u q
    have hmem : v ∈ (rp.val.2 : (slitBoxGraph n).Walk
        (slitBoxReflectVertex n u) rp.val.1).support := by
      change v ∈ finiteSimplePathSupport rp.val
      rw [slitBoxReflectCandidate_orderedSupport]
      apply List.mem_map.mpr
      refine ⟨σ v, ?_, ?_⟩
      · exact hq
      · exact slitBoxReflectVertex_involutive n v
    have hconn := slitBoxCandidate_vertex_actualConnected_to_endpoint_of_open
      n (slitBoxReflectVertex n u) rp K hqK v hmem
    exact ⟨rp.val.1, rp.property.1, hconn⟩
  · exact ⟨v, harc, slitBox_actualConnected_refl n K v⟩

/-- A remaining-graph connection from the bottom center to the paired
exception becomes an actual connection to the wired arc after restoring the
frozen paired candidate reveal. -/
theorem slitBoxPairedCandidate_remaining_hit_restores_arc
    (n : ℕ) (hn : 1 ≤ n) (u : SlitBoxVertex n)
    (huY : u.val.2 = -(n : ℤ)) (huX : 0 < u.val.1)
    (δ : PositiveMesh) (p q : SlitBoxFirstHitBaseCandidates n u)
    (K : Configuration (slitBoxGraph n))
    (hpK : slitBoxCandidateOriginalPathEdgeSupport n u p ⊆ K)
    (hqK : slitBoxCandidateOriginalPathEdgeSupport n
        (slitBoxReflectVertex n u) (slitBoxReflectCandidate n u q) ⊆ K)
    (A : Configuration (edgeRestriction (slitBoxGraph n)
      (slitBoxPairedCandidateReveal n hn u huY huX δ p q)))
    (hremaining : ∃ v ∈ slitBoxPairedCandidateException n u p q,
      ActualConnected (edgeRestriction (slitBoxGraph n)
        (slitBoxPairedCandidateReveal n hn u huY huX δ p q)) A
        (slitBoxBottomCenterVertex n) v) :
    ((edgeRestrictionConfigurationEquiv (slitBoxGraph n)
      (slitBoxPairedCandidateReveal n hn u huY huX δ p q) A).val ∪ K) ∈
      slitBoxWiredArcConnectionEvent n (slitBoxBottomCenterVertex n) := by
  have hbridge := slitBoxPairedCandidateException_bridges_to_arc
    n hn u huY huX δ p q K hpK hqK
  have hhit := actualConnected_remaining_restoration_hits_target
    (slitBoxPairedCandidateReveal n hn u huY huX δ p q) K A
    (slitBoxBottomCenterVertex n) (slitBoxPairedCandidateException n u p q)
    (slitBoxWiredArc n) hbridge hremaining
  exact hhit

/-- If the center is already on either frozen candidate path, the restored
configuration has a wired-arc connection directly through that path. -/
theorem slitBoxPairedCandidate_center_path_restores_arc
    (n : ℕ) (u : SlitBoxVertex n)
    (p q : SlitBoxFirstHitBaseCandidates n u)
    (K : Configuration (slitBoxGraph n))
    (R : Configuration (slitBoxGraph n))
    (A : Configuration (edgeRestriction (slitBoxGraph n) R))
    (hpK : slitBoxCandidateOriginalPathEdgeSupport n u p ⊆ K)
    (hqK : slitBoxCandidateOriginalPathEdgeSupport n
        (slitBoxReflectVertex n u) (slitBoxReflectCandidate n u q) ⊆ K)
    (hcenterP : slitBoxBottomCenterVertex n ∈
      (p.val.2 : (slitBoxGraph n).Walk u p.val.1).support ∨
      slitBoxGraphHorizontalReflectionIso n (slitBoxBottomCenterVertex n) ∈
        (q.val.2 : (slitBoxGraph n).Walk u q.val.1).support) :
    ((edgeRestrictionConfigurationEquiv (slitBoxGraph n) R A).val ∪ K) ∈
      slitBoxWiredArcConnectionEvent n (slitBoxBottomCenterVertex n) := by
  have hK : K ∈ slitBoxWiredArcConnectionEvent n
      (slitBoxBottomCenterVertex n) := by
    rcases hcenterP with hp | hq
    · exact slitBoxBottomCenter_actual_arc_hit_of_candidate_path_open n u p K hpK hp
    · have hfix : slitBoxGraphHorizontalReflectionIso n
        (slitBoxBottomCenterVertex n) = slitBoxBottomCenterVertex n := by
        apply Subtype.ext
        change (-((slitBoxBottomCenterVertex n).val.1),
          (slitBoxBottomCenterVertex n).val.2) =
            (slitBoxBottomCenterVertex n).val
        simp [slitBoxBottomCenterVertex_val]
      have hq' := hq
      rw [hfix] at hq'
      change slitBoxBottomCenterVertex n ∈ finiteSimplePathSupport q.val at hq'
      have hmem : slitBoxBottomCenterVertex n ∈
        ((slitBoxReflectCandidate n u q).val.2 :
          (slitBoxGraph n).Walk (slitBoxReflectVertex n u)
            (slitBoxReflectCandidate n u q).val.1).support := by
        change slitBoxBottomCenterVertex n ∈
          finiteSimplePathSupport (slitBoxReflectCandidate n u q).val
        rw [slitBoxReflectCandidate_orderedSupport]
        apply List.mem_map.mpr
        exact ⟨slitBoxBottomCenterVertex n, hq', hfix⟩
      exact slitBoxBottomCenter_actual_arc_hit_of_candidate_path_open
        n (slitBoxReflectVertex n u) (slitBoxReflectCandidate n u q) K hqK hmem
  rcases hK with ⟨z, hz, hconn⟩
  exact ⟨z, hz, actualConnected_mono Finset.subset_union_right hconn⟩

end

end PottsContinuity.FKC.FiniteFK

