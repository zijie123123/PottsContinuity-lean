-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/SlitBoxPairedCandidateComponent.lean`, with
-- module and namespace relocated (wrappers of the SLE development replaced by `PottsContinuity.FKC.SLEWrap`)
-- and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.SlitBoxReflectedCandidateCut
public import PottsContinuity.FKC.FiniteFK.SlitBoxCandidateRemainingComponent
public import PottsContinuity.FKC.FiniteFK.EdgeRestrictionReachableSeed
public import PottsContinuity.FKC.FiniteFK.EdgeRestrictionReachableComponent
public import PottsContinuity.FKC.FiniteFK.SlitBoxReferenceRectangle
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Paths

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

open PottsContinuity.FKC
open PottsContinuity.FKC.Medial

/-- Vertices where one of the candidate paths or the wired arc can interrupt
the all-or-none incident reveal argument. -/
def slitBoxPairedCandidateException
    (n : ℕ) (u : SlitBoxVertex n)
    (p q : SlitBoxFirstHitBaseCandidates n u) : Set (SlitBoxVertex n) :=
  {v | v ∈ (p.val.2 : (slitBoxGraph n).Walk u p.val.1).support ∨
    (slitBoxGraphHorizontalReflectionIso n v) ∈
      (q.val.2 : (slitBoxGraph n).Walk u q.val.1).support ∨
    v ∈ slitBoxWiredArc n}

/-- Union of the two actual candidate-filling incident-edge reveals. -/
noncomputable def slitBoxPairedCandidateReveal
    (n : ℕ) (hn : 1 ≤ n) (u : SlitBoxVertex n)
    (huY : u.val.2 = -(n : ℤ)) (huX : 0 < u.val.1)
    (δ : PositiveMesh) (p q : SlitBoxFirstHitBaseCandidates n u) :
    Configuration (slitBoxGraph n) :=
  slitBoxCandidateRemainingReveal n hn u huY (le_of_lt huX) δ p ∪
    slitBoxReflectedCandidateCellIncidentCut n hn u huY (le_of_lt huX) δ q

private theorem slitBoxPairedException_parts
    (n : ℕ) (u : SlitBoxVertex n)
    (p q : SlitBoxFirstHitBaseCandidates n u)
    {v : SlitBoxVertex n} (hv : v ∉ slitBoxPairedCandidateException n u p q) :
    v ∉ (p.val.2 : (slitBoxGraph n).Walk u p.val.1).support ∧
    (slitBoxGraphHorizontalReflectionIso n v) ∉
      (q.val.2 : (slitBoxGraph n).Walk u q.val.1).support ∧
    v ∉ slitBoxWiredArc n := by
  simpa [slitBoxPairedCandidateException] using hv

private theorem slitBoxReflection_off_arc_iff
    (n : ℕ) (v : SlitBoxVertex n) :
    (slitBoxGraphHorizontalReflectionIso n v) ∉ slitBoxWiredArc n ↔
      v ∉ slitBoxWiredArc n := by
  constructor
  · intro h hv
    have hc := (mem_slitBoxWiredArc_iff n v).mp hv
    apply h
    apply (mem_slitBoxWiredArc_iff n _).2
    change -v.val.1 = 0 ∧ 0 ≤ v.val.2 ∧ v.val.2 ≤ n
    exact ⟨by omega, hc.2.1, hc.2.2⟩
  · intro h hv
    apply h
    have hc := (mem_slitBoxWiredArc_iff n
      (slitBoxGraphHorizontalReflectionIso n v)).mp hv
    apply (mem_slitBoxWiredArc_iff n v).2
    change -v.val.1 = 0 ∧ 0 ≤ v.val.2 ∧ v.val.2 ≤ n at hc
    exact ⟨by omega, hc.2.1, hc.2.2⟩

/-- Away from both actual paths and the wired arc, reveal status is uniform on
the full actual slit-graph incident star. -/
theorem slitBoxPairedCandidateReveal_incident_status_uniform
    (n : ℕ) (hn : 1 ≤ n) (u : SlitBoxVertex n)
    (huY : u.val.2 = -(n : ℤ)) (huX : 0 < u.val.1)
    (δ : PositiveMesh) (p q : SlitBoxFirstHitBaseCandidates n u)
    {v : SlitBoxVertex n} (hv : v ∉ slitBoxPairedCandidateException n u p q)
    (e f : (slitBoxGraph n).edgeSet) (he : v ∈ e.val) (hf : v ∈ f.val) :
    (e ∈ slitBoxPairedCandidateReveal n hn u huY huX δ p q) ↔
      (f ∈ slitBoxPairedCandidateReveal n hn u huY huX δ p q) := by
  classical
  rcases slitBoxPairedException_parts n u p q hv with ⟨hvP, hvQ, hvArc⟩
  have hvQArc := (slitBoxReflection_off_arc_iff n v).2 hvArc
  have hp := slitBoxCandidateRemainingReveal_incident_status_uniform
    n hn u huY (le_of_lt huX) δ p (by
      simpa [slitBoxCandidatePathArcException] using And.intro hvP hvArc) e f he hf
  have hqE := slitBoxReflectedCandidateCellIncidentCut_incident_edge_mem_iff
    n hn u huY (le_of_lt huX) δ q v hvQ hvQArc e he
  have hqF := slitBoxReflectedCandidateCellIncidentCut_incident_edge_mem_iff
    n hn u huY (le_of_lt huX) δ q v hvQ hvQArc f hf
  change (e ∈ slitBoxCandidateRemainingReveal n hn u huY (le_of_lt huX) δ p ∪
      slitBoxReflectedCandidateCellIncidentCut n hn u huY (le_of_lt huX) δ q) ↔
    (f ∈ slitBoxCandidateRemainingReveal n hn u huY (le_of_lt huX) δ p ∪
      slitBoxReflectedCandidateCellIncidentCut n hn u huY (le_of_lt huX) δ q)
  simp only [Finset.mem_union]
  constructor
  · rintro (heP | heQ)
    · exact Or.inl (hp.1 heP)
    · exact Or.inr (hqF.mpr (hqE.mp heQ))
  · rintro (hfP | hfQ)
    · exact Or.inl (hp.2 hfP)
    · exact Or.inr (hqE.mpr (hqF.mp hfQ))

/-- A genuine origin seed survives the union reveal if both actual paths
avoid the bottom center. -/
theorem slitBoxPairedCandidateReveal_origin_seed
    (n : ℕ) (hn : 1 ≤ n) (u : SlitBoxVertex n)
    (huY : u.val.2 = -(n : ℤ)) (huX : 0 < u.val.1)
    (δ : PositiveMesh) (p q : SlitBoxFirstHitBaseCandidates n u)
    (hcenterP : slitBoxBottomCenterVertex n ∉
      (p.val.2 : (slitBoxGraph n).Walk u p.val.1).support)
    (hcenterQ : slitBoxBottomCenterVertex n ∉
      (q.val.2 : (slitBoxGraph n).Walk u q.val.1).support) :
    ∃ e : (slitBoxGraph n).edgeSet,
      slitBoxBottomCenterVertex n ∈ e.val ∧
      e ∉ slitBoxPairedCandidateReveal n hn u huY huX δ p q := by
  obtain ⟨e, he, hnotP⟩ := slitBoxCandidateRemainingReveal_origin_seed
    n hn u huY huX δ p hcenterP
  have hnotQ := slitBoxBottomCenter_all_incident_edges_outside_reflectedCut
    n hn u huY huX δ q hcenterQ e he
  refine ⟨e, he, ?_⟩
  simp only [slitBoxPairedCandidateReveal, Finset.mem_union]
  exact fun h => h.elim hnotP hnotQ

private theorem slitBoxReferenceOuterWiredSet_sides
    (n : ℕ) (v : SlitBoxVertex n)
    (hv : v ∈ slitBoxReferenceOuterWiredSet n) :
    v.val.1 = -(n : ℤ) ∨ v.val.1 = n ∨ v.val.2 = n := by
  change v.val ∈ (rectangleLeftSide (-(n : ℤ), -(n : ℤ)) (2*n) (2*n) ∪
      rectangleRightSide (-(n : ℤ), -(n : ℤ)) (2*n) (2*n)) ∪
      rectangleTopSide (-(n : ℤ), -(n : ℤ)) (2*n) (2*n) at hv
  simp only [Finset.mem_union] at hv
  rcases hv with hleft | htop
  · rcases hleft with hleft | hright
    · left
      have hx := (Finset.mem_filter.mp hleft).2
      exact hx
    · right; left
      have hx := (Finset.mem_filter.mp hright).2
      have hright' : v.val.1 = -(n : ℤ) + (2*n : ℕ) := by
        simpa [rectangleRightSide] using hx
      push_cast at hright'
      omega
  · right; right
    have hy := (Finset.mem_filter.mp htop).2
    have htop' : v.val.2 = -(n : ℤ) + (2*n : ℕ) := by
      simpa [rectangleTopSide] using hy
    push_cast at htop'
    have hvbox := (mem_latticeRectangle _ v.val (2*n) (2*n)).mp v.property
    omega

/-- Outside the actual path-and-arc exception set, the actual union-reveal
component avoids the reference wired boundary. -/
theorem slitBoxPairedCandidateComponent_avoids_reference_outer_wired_set
    (n : ℕ) (hn : 1 ≤ n) (u : SlitBoxVertex n)
    (huY : u.val.2 = -(n : ℤ)) (huX : 0 < u.val.1)
    (δ : PositiveMesh) (p q : SlitBoxFirstHitBaseCandidates n u)
    (hcenterP : slitBoxBottomCenterVertex n ∉
      (p.val.2 : (slitBoxGraph n).Walk u p.val.1).support)
    (hcenterQ : slitBoxBottomCenterVertex n ∉
      (q.val.2 : (slitBoxGraph n).Walk u q.val.1).support) :
    let R := slitBoxPairedCandidateReveal n hn u huY huX δ p q
    let B := slitBoxPairedCandidateException n u p q
    ∀ x : edgeRestrictionReachableComponentCarrier (slitBoxGraph n) R
        (slitBoxBottomCenterVertex n),
      x.val ∉ B → x.val ∉ slitBoxReferenceOuterWiredSet n := by
  classical
  dsimp
  let R := slitBoxPairedCandidateReveal n hn u huY huX δ p q
  let B := slitBoxPairedCandidateException n u p q
  let o := slitBoxBottomCenterVertex n
  have horigin : ∃ e : (slitBoxGraph n).edgeSet, o ∈ e.val ∧ e ∉ R := by
    simpa [o, R] using slitBoxPairedCandidateReveal_origin_seed
      n hn u huY huX δ p q hcenterP hcenterQ
  intro x hxB hxOuter
  obtain ⟨e, he, hnotR⟩ := edgeRestriction_reachable_has_unrevealed_incident_edge
    (slitBoxGraph n) R o x.val x.property horigin
  have hside := slitBoxReferenceOuterWiredSet_sides n x.val hxOuter
  have hall : ∀ f : (slitBoxGraph n).edgeSet, x.val ∈ f.val → f ∈ R := by
    intro f hf
    rcases slitBoxPairedException_parts n u p q hxB with ⟨hxP, hxQ, hxArc⟩
    have hσArc := (slitBoxReflection_off_arc_iff n x.val).2 hxArc
    rcases hside with hleft | hright | htop
    · have hrevealed := slitBoxFirstHitCandidate_reflected_left_star_incident_edges_revealed
        n hn u huY (le_of_lt huX) δ q x.val hxQ hσArc (Or.inl hleft) f hf
      exact Finset.mem_union.mpr (Or.inr hrevealed)
    · have hrevealed := slitBoxFirstHitCandidate_outer_star_incident_edges_revealed
        n hn u huY (le_of_lt huX) δ p x.val hxP hxArc (Or.inl hright) f hf
      exact Finset.mem_union.mpr (Or.inl hrevealed)
    · have htop := htop
      by_cases hxNonneg' : (0 : ℤ) ≤ x.val.val.1
      · have hrevealed := slitBoxFirstHitCandidate_outer_star_incident_edges_revealed
          n hn u huY (le_of_lt huX) δ p x.val hxP hxArc
          (Or.inr ⟨htop, hxNonneg'⟩) f hf
        exact Finset.mem_union.mpr (Or.inl hrevealed)
      · have hrevealed := slitBoxFirstHitCandidate_reflected_left_star_incident_edges_revealed
          n hn u huY (le_of_lt huX) δ q x.val hxQ hσArc
          (Or.inr ⟨htop, by omega⟩) f hf
        exact Finset.mem_union.mpr (Or.inr hrevealed)
  exact hnotR (hall e he)

/-- The actual union-reveal component is closed under reference neighbors away
from both actual path supports and the wired arc. -/
theorem slitBoxPairedCandidateComponent_closed_under_reference_neighbors
    (n : ℕ) (hn : 1 ≤ n) (u : SlitBoxVertex n)
    (huY : u.val.2 = -(n : ℤ)) (huX : 0 < u.val.1)
    (δ : PositiveMesh) (p q : SlitBoxFirstHitBaseCandidates n u)
    (hcenterP : slitBoxBottomCenterVertex n ∉
      (p.val.2 : (slitBoxGraph n).Walk u p.val.1).support)
    (hcenterQ : slitBoxBottomCenterVertex n ∉
      (q.val.2 : (slitBoxGraph n).Walk u q.val.1).support) :
    let R := slitBoxPairedCandidateReveal n hn u huY huX δ p q
    let B := slitBoxPairedCandidateException n u p q
    ∀ ⦃x : edgeRestrictionReachableComponentCarrier (slitBoxGraph n) R
        (slitBoxBottomCenterVertex n)⦄,
      x.val ∉ B → ∀ ⦃y : SlitBoxVertex n⦄,
        (slitBoxReferenceGraph n).Adj x.val y →
        ∃ z : edgeRestrictionReachableComponentCarrier (slitBoxGraph n) R
            (slitBoxBottomCenterVertex n),
          z.val = y ∧
          (edgeRestrictionReachableComponentGraph (slitBoxGraph n) R
            (slitBoxBottomCenterVertex n)).Adj x z := by
  classical
  dsimp
  let R := slitBoxPairedCandidateReveal n hn u huY huX δ p q
  let B := slitBoxPairedCandidateException n u p q
  let o := slitBoxBottomCenterVertex n
  have huniform : ∀ v, v ∉ B → ∀ e f : (slitBoxGraph n).edgeSet,
      v ∈ e.val → v ∈ f.val → (e ∈ R ↔ f ∈ R) := by
    intro v hv e f he hf
    exact slitBoxPairedCandidateReveal_incident_status_uniform
      n hn u huY huX δ p q hv e f he hf
  have horigin : ∃ e : (slitBoxGraph n).edgeSet, o ∈ e.val ∧ e ∉ R := by
    simpa [o, R] using slitBoxPairedCandidateReveal_origin_seed
      n hn u huY huX δ p q hcenterP hcenterQ
  intro x hxB y hxy
  have hxArc := (slitBoxPairedException_parts n u p q hxB).2.2
  have hrect :
      (rectangleGraph (-(n : ℤ), -(n : ℤ)) (2*n) (2*n)).Adj x.val y := hxy
  have hslit : (slitBoxGraph n).Adj x.val y := by
    apply (slitBoxGraph_adj_iff n x.val y).2
    refine ⟨(rectangleGraph_adj_iff _ _ _ _ _).mp hrect, ?_⟩
    intro hboth
    exact hxArc ((mem_slitBoxWiredArc_iff n x.val).2 hboth.1)
  exact edgeRestrictionReachableComponent_closed_under_original_neighbors
    (slitBoxGraph n) R o B huniform horigin hxB hslit

/-- The paired component graph embeds into the full reference square graph by
the literal vertex inclusion. -/
theorem slitBoxPairedCandidateComponent_map_le_reference
    (n : ℕ) (hn : 1 ≤ n) (u : SlitBoxVertex n)
    (huY : u.val.2 = -(n : ℤ)) (huX : 0 < u.val.1)
    (δ : PositiveMesh) (p q : SlitBoxFirstHitBaseCandidates n u) :
    let R := slitBoxPairedCandidateReveal n hn u huY huX δ p q
    (edgeRestrictionReachableComponentGraph (slitBoxGraph n) R
      (slitBoxBottomCenterVertex n)).map
      (edgeRestrictionReachableComponentEmbedding (slitBoxGraph n) R
        (slitBoxBottomCenterVertex n)) ≤ slitBoxReferenceGraph n := by
  intro R a b hab
  obtain ⟨x, y, hxy, rfl, rfl⟩ :=
    (SimpleGraph.map_adj
      (edgeRestrictionReachableComponentEmbedding (slitBoxGraph n) R
        (slitBoxBottomCenterVertex n))
      (edgeRestrictionReachableComponentGraph (slitBoxGraph n) R
        (slitBoxBottomCenterVertex n)) a b).mp hab
  change (rectangleGraph (-(n : ℤ), -(n : ℤ)) (2*n) (2*n)).Adj x.val y.val
  exact (edgeRestriction_le (slitBoxGraph n) R
    (SimpleGraph.induce_adj.mp hxy)).1

end PottsContinuity.FKC.FiniteFK
