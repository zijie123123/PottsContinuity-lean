-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/SlitBoxPairedRecordCandidates.lean`, with
-- module and namespace relocated (wrappers of the SLE development replaced by `PottsContinuity.FKC.SLEWrap`)
-- and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.SlitBoxPairedCandidateComponent
public import PottsContinuity.FKC.FiniteFK.SlitBoxPairedReveal
public import PottsContinuity.FKC.FiniteFK.SlitBoxLeastCandidateReveal
public import PottsContinuity.FKC.FiniteFK.SlitBoxCandidateReflection
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Combinatorics.SimpleGraph.Walk.Basic

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

open PottsContinuity.FKC

noncomputable section

/-- The selected actual right path and the reflected selected path are
contained in the actual paired revealed state whenever both connection
events occur. This statement only needs the nonnegative half-box condition. -/
theorem slitBoxPairedReveal_selected_supports_on_good
    (n : ℕ) (hn : 1 ≤ n) (u : SlitBoxVertex n)
    (huY : u.val.2 = -(n : ℤ)) (huX : 0 ≤ u.val.1)
    (δ : PositiveMesh) (A : Configuration (slitBoxGraph n))
    (hA : A ∈ slitBoxWiredArcConnectionEvent n u)
    (hAReflect : configurationIso (slitBoxGraphHorizontalReflectionIso n) A ∈
      slitBoxWiredArcConnectionEvent n u) :
    let p := slitBoxLeastOpenCandidateOnEvent n hn u huY huX δ A hA
    let q := slitBoxLeastOpenCandidateOnEvent n hn u huY huX δ
      (configurationIso (slitBoxGraphHorizontalReflectionIso n) A) hAReflect
    slitBoxCandidateOriginalPathEdgeSupport n u p ⊆
        A ∩ slitBoxPairedReveal n hn u huY huX δ A ∧
      slitBoxCandidateOriginalPathEdgeSupport n (slitBoxReflectVertex n u)
          (slitBoxReflectCandidate n u q) ⊆
        A ∩ slitBoxPairedReveal n hn u huY huX δ A := by
  classical
  let σ := slitBoxGraphHorizontalReflectionIso n
  let e := configurationIso σ
  let p := slitBoxLeastOpenCandidateOnEvent n hn u huY huX δ A hA
  let q := slitBoxLeastOpenCandidateOnEvent n hn u huY huX δ (e A) hAReflect
  let pSupport := slitBoxCandidateOriginalPathEdgeSupport n u p
  let qSupport := slitBoxCandidateOriginalPathEdgeSupport n u q
  let R := slitBoxPairedReveal n hn u huY huX δ A
  have hpairedExpanded : R =
      slitBoxLeastCandidateReveal n hn u huY huX δ A ∪
        slitBoxLeftReveal n hn u huY huX δ A := by
    ext f
    simp only [R, slitBoxPairedReveal, Finset.mem_union]
    change (f ∈ slitBoxLeastCandidateReveal n hn u huY huX δ A ∨
      f ∈ slitBoxLeftReveal n hn u huY huX δ A) ↔ _
    rfl
  have hreflectInvolutive : ∀ B : Configuration (slitBoxGraph n), e (e B) = B := by
    intro B
    simp [e, σ]
  have hreflectSymm : e.symm = e := by
    apply Equiv.ext
    intro B
    apply e.injective
    calc
      e (e.symm B) = B := e.apply_symm_apply B
      _ = e (e B) := (hreflectInvolutive B).symm
  have hpReveal : pSupport ⊆ slitBoxLeastCandidateReveal n hn u huY huX δ A := by
    simpa [p, pSupport] using slitBoxLeastCandidateReveal_support_subset_of_hit
      n hn u huY huX δ A hA
  have hqReveal : qSupport ⊆ slitBoxLeastCandidateReveal n hn u huY huX δ (e A) := by
    simpa [q, qSupport, e] using slitBoxLeastCandidateReveal_support_subset_of_hit
      n hn u huY huX δ (e A) hAReflect
  have hpOpen : pSupport ⊆ A := by
    have hchar := slitBoxLeastOpenCandidateOnEvent_characterization
      n hn u huY huX δ A hA
    simpa [p, pSupport] using hchar.1
  have hqOpen : qSupport ⊆ e A := by
    have hchar := slitBoxLeastOpenCandidateOnEvent_characterization
      n hn u huY huX δ (e A) hAReflect
    simpa [q, qSupport, e] using hchar.1
  have hpPaired : pSupport ⊆ R := by
    rw [hpairedExpanded]
    exact Finset.Subset.trans hpReveal Finset.subset_union_left
  have hqReflectedInA :
      slitBoxCandidateOriginalPathEdgeSupport n (slitBoxReflectVertex n u)
          (slitBoxReflectCandidate n u q) ⊆ A := by
    rw [← slitBoxReflectCandidate_edgeSupport n u q]
    have hmapped : e qSupport ⊆ e (e A) := by
      change Finset.map (configurationIsoEdgeEquiv σ).toEmbedding qSupport ⊆
        Finset.map (configurationIsoEdgeEquiv σ).toEmbedding (e A)
      exact Finset.map_subset_map.mpr hqOpen
    rw [hreflectInvolutive A] at hmapped
    exact hmapped
  have hleftIdentity :
      e (slitBoxLeastCandidateReveal n hn u huY huX δ (e A)) =
        slitBoxLeftReveal n hn u huY huX δ A := by
    unfold slitBoxLeftReveal
    change e (slitBoxLeastCandidateReveal n hn u huY huX δ (e A)) =
      e.symm (slitBoxLeastCandidateReveal n hn u huY huX δ (e A))
    rw [hreflectSymm]
  have hqReflectedInLeft :
      slitBoxCandidateOriginalPathEdgeSupport n (slitBoxReflectVertex n u)
          (slitBoxReflectCandidate n u q) ⊆ slitBoxLeftReveal n hn u huY huX δ A := by
    rw [← slitBoxReflectCandidate_edgeSupport n u q]
    have hmapped : e qSupport ⊆ e (slitBoxLeastCandidateReveal n hn u huY huX δ (e A)) := by
      change Finset.map (configurationIsoEdgeEquiv σ).toEmbedding qSupport ⊆
        Finset.map (configurationIsoEdgeEquiv σ).toEmbedding
          (slitBoxLeastCandidateReveal n hn u huY huX δ (e A))
      exact Finset.map_subset_map.mpr hqReveal
    rw [hleftIdentity] at hmapped
    exact hmapped
  have hqReflectedPaired :
      slitBoxCandidateOriginalPathEdgeSupport n (slitBoxReflectVertex n u)
          (slitBoxReflectCandidate n u q) ⊆ R := by
    rw [hpairedExpanded]
    exact Finset.Subset.trans hqReflectedInLeft Finset.subset_union_right
  exact ⟨Finset.subset_inter hpOpen hpPaired,
    Finset.subset_inter hqReflectedInA hqReflectedPaired⟩

/-- On the genuine two-sided connection event, the total paired reveal is
the union of the actual filling cut of the selected right candidate and the
reflected filling cut of the selected candidate in the reflected state.
Both selected original paths remain inside the revealed state. -/
theorem slitBoxPairedReveal_eq_candidates_on_good
    (n : ℕ) (hn : 1 ≤ n) (u : SlitBoxVertex n)
    (huY : u.val.2 = -(n : ℤ)) (huX : 0 < u.val.1)
    (δ : PositiveMesh) (A : Configuration (slitBoxGraph n))
    (hA : A ∈ slitBoxWiredArcConnectionEvent n u)
    (hAReflect : configurationIso (slitBoxGraphHorizontalReflectionIso n) A ∈
      slitBoxWiredArcConnectionEvent n u) :
    let p := slitBoxLeastOpenCandidateOnEvent n hn u huY (le_of_lt huX) δ A hA
    let q := slitBoxLeastOpenCandidateOnEvent n hn u huY (le_of_lt huX) δ
      (configurationIso (slitBoxGraphHorizontalReflectionIso n) A) hAReflect
    slitBoxPairedReveal n hn u huY (le_of_lt huX) δ A =
        slitBoxPairedCandidateReveal n hn u huY huX δ p q ∧
      slitBoxCandidateOriginalPathEdgeSupport n u p ⊆
        A ∩ slitBoxPairedReveal n hn u huY (le_of_lt huX) δ A ∧
      slitBoxCandidateOriginalPathEdgeSupport n (slitBoxReflectVertex n u)
          (slitBoxReflectCandidate n u q) ⊆
        A ∩ slitBoxPairedReveal n hn u huY (le_of_lt huX) δ A := by
  classical
  let σ := slitBoxGraphHorizontalReflectionIso n
  let e := configurationIso σ
  let p := slitBoxLeastOpenCandidateOnEvent n hn u huY (le_of_lt huX) δ A hA
  let q := slitBoxLeastOpenCandidateOnEvent n hn u huY (le_of_lt huX) δ (e A) hAReflect
  let pSupport := slitBoxCandidateOriginalPathEdgeSupport n u p
  let qSupport := slitBoxCandidateOriginalPathEdgeSupport n u q
  let K := A ∩ slitBoxPairedReveal n hn u huY (le_of_lt huX) δ A
  have hsupp := slitBoxPairedReveal_selected_supports_on_good
    n hn u huY (le_of_lt huX) δ A hA hAReflect
  have hright : slitBoxLeastCandidateReveal n hn u huY (le_of_lt huX) δ A =
      slitBoxCandidateRemainingReveal n hn u huY (le_of_lt huX) δ p := by
    rw [slitBoxLeastCandidateReveal_eq_actual_cut_of_hit
      n hn u huY (le_of_lt huX) δ A hA]
    rfl
  have hreflectInvolutive : ∀ B : Configuration (slitBoxGraph n), e (e B) = B := by
    intro B
    simp [e, σ]
  have hreflectSymm : e.symm = e := by
    apply Equiv.ext
    intro B
    apply e.injective
    calc
      e (e.symm B) = B := e.apply_symm_apply B
      _ = e (e B) := (hreflectInvolutive B).symm
  have hleft : slitBoxLeftReveal n hn u huY (le_of_lt huX) δ A =
      slitBoxReflectedCandidateCellIncidentCut n hn u huY (le_of_lt huX) δ q := by
    change e.symm (slitBoxLeastCandidateReveal n hn u huY (le_of_lt huX) δ (e A)) = _
    rw [slitBoxLeastCandidateReveal_eq_actual_cut_of_hit
      n hn u huY (le_of_lt huX) δ (e A) hAReflect]
    rw [hreflectSymm]
    rfl
  have hpair : slitBoxPairedReveal n hn u huY (le_of_lt huX) δ A =
      slitBoxPairedCandidateReveal n hn u huY huX δ p q := by
    ext e
    simp only [slitBoxPairedReveal, slitBoxPairedCandidateReveal,
      Finset.mem_union]
    constructor
    · rintro (hR | hL)
      · left
        change e ∈ slitBoxLeastCandidateReveal n hn u huY (le_of_lt huX) δ A at hR
        rw [hright] at hR
        exact hR
      · right
        rw [hleft] at hL
        exact hL
    · rintro (hR | hL)
      · left
        change e ∈ slitBoxLeastCandidateReveal n hn u huY (le_of_lt huX) δ A
        rw [hright]
        exact hR
      · right
        rw [hleft]
        exact hL
  exact ⟨by simpa [p, q, K] using hpair,
    by simpa [pSupport, p, K] using hsupp.1,
    by simpa [q, K] using hsupp.2⟩

end
end PottsContinuity.FKC.FiniteFK
