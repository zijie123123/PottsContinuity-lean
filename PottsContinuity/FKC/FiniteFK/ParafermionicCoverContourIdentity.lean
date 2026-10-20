-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/ParafermionicCoverContourIdentity.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.Medial.ParafermionicCoverPathPhaseZeroTurn
public import PottsContinuity.FKC.Medial.ParafermionicCoverContourBoundary
public import PottsContinuity.FKC.Medial.ParafermionicCoverPortOrientation
public import PottsContinuity.FKC.FiniteFK.ParafermionicCoverPathObservable
public import PottsContinuity.FKC.FiniteFK.ParafermionicCoverPathObservableSum
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

open PottsContinuity.FKC PottsContinuity.FKC.Medial
open scoped BigOperators
noncomputable section

local instance contourIdentityPortFintype (n : ℕ) : Fintype (ParafermionicCoverFinitePort n) :=
  Fintype.ofFinite _

 def contourIdentityInternal (n : ℕ) (c : ParafermionicCoverFinitePort n) : Prop :=
  parafermionicCoverFinitePortOtherEndpointInBox n c

local instance contourIdentityInternalDecidable (n : ℕ) :
    DecidablePred (contourIdentityInternal n) := Classical.decPred _

 def contourIdentitySign (n : ℕ) (c : ParafermionicCoverFinitePort n) : ℂ :=
  if parafermionicCoverIncomingPrimalLeft c.1 then 1 else -1

 def contourIdentityValue (q : ClusterWeight) (n : ℕ) (hn : 1 ≤ n)
    (c : ParafermionicCoverFinitePort n) : ℂ :=
  parafermionicCoverPathPhaseExpectation q n hn (c, true)

private theorem contourIdentityValue_corner_eq (q : ClusterWeight) (n : ℕ)
    (hn : 1 ≤ n)
    (c : ParafermionicCoverFinitePort n)
    (hc : c ≠ parafermionicCoverFiniteOriginCornerPort n hn ∧
      c ≠ parafermionicCoverFiniteCornerPairPerm n
        (parafermionicCoverFiniteOriginCornerPort n hn)) :
    contourIdentityValue q n hn c =
      contourIdentityValue q n hn (parafermionicCoverFiniteCornerPairPerm n c) := by
  change parafermionicCoverPathPhaseExpectation q n hn (c, true) =
    parafermionicCoverPathPhaseExpectation q n hn
      (parafermionicCoverFiniteCornerPairPerm n c, true)
  rw [parafermionicCoverPathPhaseExpectation_eq_configuration_sum,
    parafermionicCoverPathPhaseExpectation_eq_configuration_sum]
  apply Finset.sum_congr rfl
  intro A hA
  rw [parafermionicCoverPathPhaseAtom_corner_eq_of_not_cut q n hn A c hc]

private theorem contourIdentitySign_corner (n : ℕ)
    (c : ParafermionicCoverFinitePort n) :
    contourIdentitySign n (parafermionicCoverFiniteCornerPairPerm n c) =
      -contourIdentitySign n c := by
  cases h : parafermionicCoverIncomingPrimalLeft c.1 <;>
    simp [contourIdentitySign, parafermionicCoverFiniteCornerPairPerm_val,
      parafermionicCoverIncomingPrimalLeft_cornerPair, h]

private theorem contourIdentity_origin_internal (n : ℕ) (hn : 1 ≤ n) :
    contourIdentityInternal n (parafermionicCoverFiniteOriginCornerPort n hn) := by
  apply (parafermionicCoverFinitePortEdgeEndpointsInBox_iff n _).1
  intro v hv
  exact parafermionicCoverOriginCornerPort_edge_endpoints_in_box n hn _ (Or.inl rfl) v hv

private theorem contourIdentity_originPartner_internal (n : ℕ) (hn : 1 ≤ n) :
    contourIdentityInternal n
      (parafermionicCoverFiniteCornerPairPerm n
        (parafermionicCoverFiniteOriginCornerPort n hn)) := by
  apply (parafermionicCoverFinitePortEdgeEndpointsInBox_iff n _).1
  intro v hv
  have hpair : (parafermionicCoverFiniteCornerPairPerm n
      (parafermionicCoverFiniteOriginCornerPort n hn)).1 =
        parafermionicCoverOriginCornerPortOther := by
    exact parafermionicCoverFiniteCornerPairPerm_origin n hn
  rw [hpair] at hv
  exact parafermionicCoverOriginCornerPort_edge_endpoints_in_box n hn _ (Or.inr rfl) v hv

private theorem contourIdentity_originSign (n : ℕ) (hn : 1 ≤ n) :
    contourIdentitySign n (parafermionicCoverFiniteOriginCornerPort n hn) = 1 := by
  simp [contourIdentitySign, parafermionicCoverFiniteOriginCornerPort_val,
    parafermionicCoverIncomingPrimalLeft_origin]

private theorem contourIdentity_originPartnerSign (n : ℕ) (hn : 1 ≤ n) :
    contourIdentitySign n
      (parafermionicCoverFiniteCornerPairPerm n
        (parafermionicCoverFiniteOriginCornerPort n hn)) = -1 := by
  rw [contourIdentitySign_corner, contourIdentity_originSign]

 def contourIdentityBulkTerm (q : ClusterWeight) (n : ℕ)
    (hn : 1 ≤ n) (c : ParafermionicCoverFinitePort n) : ℂ := by
  classical
  exact if contourIdentityInternal n c then
    contourIdentitySign n c * contourIdentityValue q n hn c else 0

 def contourIdentityExposedTerm (q : ClusterWeight) (n : ℕ)
    (hn : 1 ≤ n) (c : ParafermionicCoverFinitePort n) : ℂ := by
  classical
  exact if contourIdentityInternal n c ∧
      ¬ contourIdentityInternal n (parafermionicCoverFiniteCornerPairPerm n c) then
    contourIdentitySign n c * contourIdentityValue q n hn c else 0

 def contourIdentityDefectTerm (q : ClusterWeight) (n : ℕ)
    (hn : 1 ≤ n) (c : ParafermionicCoverFinitePort n) : ℂ := by
  classical
  let s := parafermionicCoverFiniteOriginCornerPort n hn
  let Bs := parafermionicCoverFiniteCornerPairPerm n s
  exact if c = s ∨ c = Bs then
    contourIdentityValue q n hn s - contourIdentityValue q n hn Bs else 0

private theorem contourIdentity_pair_balance (q : ClusterWeight) (n : ℕ)
    (hn : 1 ≤ n) (c : ParafermionicCoverFinitePort n) :
    contourIdentityBulkTerm q n hn c +
        contourIdentityBulkTerm q n hn (parafermionicCoverFiniteCornerPairPerm n c) =
      contourIdentityExposedTerm q n hn c +
        contourIdentityExposedTerm q n hn (parafermionicCoverFiniteCornerPairPerm n c) +
          contourIdentityDefectTerm q n hn c := by
  classical
  let s := parafermionicCoverFiniteOriginCornerPort n hn
  let Bs := parafermionicCoverFiniteCornerPairPerm n s
  let B := parafermionicCoverFiniteCornerPairPerm n
  have hBinv := parafermionicCoverFiniteCornerPairPerm_involutive n
  have hIs : contourIdentityInternal n s := contourIdentity_origin_internal n hn
  have hIBs : contourIdentityInternal n Bs := contourIdentity_originPartner_internal n hn
  change parafermionicCoverFinitePortOtherEndpointInBox n s at hIs
  change parafermionicCoverFinitePortOtherEndpointInBox n Bs at hIBs
  have hss : contourIdentitySign n s = 1 := contourIdentity_originSign n hn
  have hSBs : contourIdentitySign n Bs = -1 := contourIdentity_originPartnerSign n hn
  have hBss : B Bs = s := hBinv s
  have hB2 : ∀ x, B (B x) = x := hBinv
  by_cases hcCut : c = s ∨ c = Bs
  · rcases hcCut with rfl | hcCut
    · simp [contourIdentityBulkTerm, contourIdentityExposedTerm,
        contourIdentityDefectTerm, contourIdentityInternal, s, Bs, B,
        hIs, hIBs, hss, hSBs, hBss]
      ring
    · have hcs : c = Bs := hcCut
      subst c
      simp [contourIdentityBulkTerm, contourIdentityExposedTerm,
        contourIdentityDefectTerm, contourIdentityInternal, s, Bs, B,
        hIs, hIBs, hss, hSBs, hBss]
      ring
  · have hregular : c ≠ s ∧ c ≠ Bs := by
      constructor
      · intro h
        exact hcCut (Or.inl h)
      · intro h
        exact hcCut (Or.inr h)
    have hregularB : B c ≠ s ∧ B c ≠ Bs := by
      constructor
      · intro h
        apply hcCut
        right
        calc
          c = B (B c) := (hBinv c).symm
          _ = B s := congrArg B h
          _ = Bs := rfl
      · intro h
        apply hcCut
        left
        calc
          c = B (B c) := (hBinv c).symm
          _ = B Bs := congrArg B h
          _ = s := hBss
    have hval := contourIdentityValue_corner_eq q n hn c hregular
    have hsgn := contourIdentitySign_corner n c
    by_cases hi : contourIdentityInternal n c
    · change parafermionicCoverFinitePortOtherEndpointInBox n c at hi
      by_cases hj : contourIdentityInternal n (B c)
      · change parafermionicCoverFinitePortOtherEndpointInBox n (B c) at hj
        simp [contourIdentityBulkTerm, contourIdentityExposedTerm,
          contourIdentityDefectTerm, contourIdentityInternal, s, Bs, B,
          hregular, hi, hj, hval, hsgn, hB2]
      · change ¬ parafermionicCoverFinitePortOtherEndpointInBox n (B c) at hj
        simp [contourIdentityBulkTerm, contourIdentityExposedTerm,
          contourIdentityDefectTerm, contourIdentityInternal, s, Bs, B,
          hregular, hi, hj, hval, hB2]
    · change ¬ parafermionicCoverFinitePortOtherEndpointInBox n c at hi
      by_cases hj : contourIdentityInternal n (B c)
      · change parafermionicCoverFinitePortOtherEndpointInBox n (B c) at hj
        simp [contourIdentityBulkTerm, contourIdentityExposedTerm,
          contourIdentityDefectTerm, contourIdentityInternal, s, Bs, B,
          hregular, hi, hj, hsgn, hB2]
      · change ¬ parafermionicCoverFinitePortOtherEndpointInBox n (B c) at hj
        simp [contourIdentityBulkTerm, contourIdentityExposedTerm,
          contourIdentityDefectTerm, contourIdentityInternal, s, Bs, B,
          hregular, hi, hj, hB2]

private theorem contourIdentity_exposed_sum (q : ClusterWeight) (n : ℕ)
    (hn : 1 ≤ n) :
    (∑ c : ParafermionicCoverFinitePort n, contourIdentityExposedTerm q n hn c) =
      ∑ e ∈ parafermionicCoverExposedCorners n,
        contourIdentitySign n e.1 * contourIdentityValue q n hn e.1 := by
  classical
  let P : ParafermionicCoverFinitePort n → Prop := fun c =>
    contourIdentityInternal n c ∧
      ¬ contourIdentityInternal n (parafermionicCoverFiniteCornerPairPerm n c)
  let : Fintype {c : ParafermionicCoverFinitePort n // P c} := Fintype.ofFinite _
  have hsum : (∑ c : ParafermionicCoverFinitePort n,
      contourIdentityExposedTerm q n hn c) =
      ∑ c ∈ Finset.univ.filter P,
        contourIdentitySign n c * contourIdentityValue q n hn c := by
    simp [contourIdentityExposedTerm, P, Finset.sum_filter]
  rw [hsum]
  unfold parafermionicCoverExposedCorners parafermionicCoverExposedCornerOccurrence
  have hmem : ∀ c : ParafermionicCoverFinitePort n,
      c ∈ Finset.univ.filter P ↔ P c := by
    intro c
    simp [P]
  rw [Finset.sum_subtype (Finset.univ.filter P) hmem
    (fun c => contourIdentitySign n c * contourIdentityValue q n hn c)]
  rfl

local instance contourIdentityEndpointDecidable (n : ℕ) :
    DecidablePred (fun c : ParafermionicCoverFinitePort n =>
      parafermionicCoverFinitePortOtherEndpointInBox n c) := Classical.decPred _

theorem parafermionicCoverPathPhaseExpectation_contour_identity
    (q : ClusterWeight) (n : ℕ) (hn : 1 ≤ n) :
    (∑ c ∈ Finset.univ.filter
        (fun c : ParafermionicCoverFinitePort n =>
          parafermionicCoverFinitePortOtherEndpointInBox n c),
      (if parafermionicCoverIncomingPrimalLeft c.1 then (1 : ℂ) else -1) *
        parafermionicCoverPathPhaseExpectation q n hn (c, true)) =
      (∑ e ∈ parafermionicCoverExposedCorners n,
        (if parafermionicCoverIncomingPrimalLeft e.1.1 then (1 : ℂ) else -1) *
          parafermionicCoverPathPhaseExpectation q n hn (e.1, true)) +
        parafermionicCoverPathPhaseExpectation q n hn
          (parafermionicCoverFiniteOriginCornerPort n hn, true) -
        parafermionicCoverPathPhaseExpectation q n hn
          (parafermionicCoverFiniteCornerPairPerm n
            (parafermionicCoverFiniteOriginCornerPort n hn), true) := by
  classical
  change (∑ c ∈ Finset.univ.filter (contourIdentityInternal n),
      contourIdentitySign n c * contourIdentityValue q n hn c) =
    (∑ e ∈ parafermionicCoverExposedCorners n,
      contourIdentitySign n e.1 * contourIdentityValue q n hn e.1) +
      contourIdentityValue q n hn (parafermionicCoverFiniteOriginCornerPort n hn) -
      contourIdentityValue q n hn
        (parafermionicCoverFiniteCornerPairPerm n
          (parafermionicCoverFiniteOriginCornerPort n hn))
  let B := parafermionicCoverFiniteCornerPairPerm n
  let bulk := contourIdentityBulkTerm q n hn
  let exposed := contourIdentityExposedTerm q n hn
  let defect := contourIdentityDefectTerm q n hn
  let s := parafermionicCoverFiniteOriginCornerPort n hn
  let Bs := B s
  have hBinv := parafermionicCoverFiniteCornerPairPerm_involutive n
  have hpair : (∑ c : ParafermionicCoverFinitePort n, bulk c) +
      (∑ c : ParafermionicCoverFinitePort n, bulk (B c)) =
      (∑ c : ParafermionicCoverFinitePort n, exposed c) +
        (∑ c : ParafermionicCoverFinitePort n, exposed (B c)) +
          ∑ c : ParafermionicCoverFinitePort n, defect c := by
    calc
      _ = ∑ c : ParafermionicCoverFinitePort n, (bulk c + bulk (B c)) := by
        rw [Finset.sum_add_distrib, Equiv.sum_comp B]
      _ = ∑ c : ParafermionicCoverFinitePort n,
          (exposed c + exposed (B c) + defect c) := by
        apply Finset.sum_congr rfl
        intro c hc
        exact contourIdentity_pair_balance q n hn c
      _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
          Equiv.sum_comp B]
  have hbulk : (∑ c : ParafermionicCoverFinitePort n, bulk c) =
      ∑ c ∈ Finset.univ.filter (contourIdentityInternal n),
        contourIdentitySign n c * contourIdentityValue q n hn c := by
    simp [bulk, contourIdentityBulkTerm, Finset.sum_filter]
  have hexposed := contourIdentity_exposed_sum q n hn
  have hdefect : (∑ c : ParafermionicCoverFinitePort n, defect c) =
      2 * (contourIdentityValue q n hn s - contourIdentityValue q n hn Bs) := by
    let R := contourIdentityValue q n hn s - contourIdentityValue q n hn Bs
    have hBsne : s ≠ Bs := parafermionicCoverFiniteCornerPairPerm_origin_ne n hn
    have hfilter : Finset.univ.filter (fun c : ParafermionicCoverFinitePort n =>
        c = s ∨ c = Bs) = {s, Bs} := by
      ext c
      simp
    calc
      (∑ c : ParafermionicCoverFinitePort n, defect c) =
          ∑ c : ParafermionicCoverFinitePort n,
            if c = s ∨ c = Bs then R else 0 := by
        apply Finset.sum_congr rfl
        intro c hc
        simp [defect, contourIdentityDefectTerm, s, Bs, B, R]
      _ = ∑ c ∈ Finset.univ.filter
            (fun c : ParafermionicCoverFinitePort n => c = s ∨ c = Bs), R := by
        symm
        exact Finset.sum_filter _ _
      _ = R + R := by
        rw [hfilter]
        simp [hBsne]
        ring
      _ = 2 * (contourIdentityValue q n hn s -
          contourIdentityValue q n hn Bs) := by
        simpa [R] using
          (two_mul (contourIdentityValue q n hn s -
            contourIdentityValue q n hn Bs)).symm
  have hsumB : (∑ c : ParafermionicCoverFinitePort n, bulk (B c)) =
      ∑ c : ParafermionicCoverFinitePort n, bulk c := Equiv.sum_comp B _
  have hsumE : (∑ c : ParafermionicCoverFinitePort n, exposed (B c)) =
      ∑ c : ParafermionicCoverFinitePort n, exposed c := Equiv.sum_comp B _
  have hpair' : (2 : ℂ) *
      (∑ c : ParafermionicCoverFinitePort n, bulk c) =
      2 * (∑ c : ParafermionicCoverFinitePort n, exposed c) +
        2 * (contourIdentityValue q n hn s - contourIdentityValue q n hn Bs) := by
    have hpair0 := hpair
    rw [hsumB, hsumE, hdefect] at hpair0
    simpa [two_mul, add_assoc] using hpair0
  have htwo : (2 : ℂ) ≠ 0 := by norm_num
  apply (mul_left_cancel₀ htwo)
  calc
    (2 : ℂ) * (∑ c ∈ Finset.univ.filter (contourIdentityInternal n),
        contourIdentitySign n c * contourIdentityValue q n hn c) =
        (2 : ℂ) * (∑ c : ParafermionicCoverFinitePort n, bulk c) := by
      rw [hbulk]
    _ =
        2 * (∑ c : ParafermionicCoverFinitePort n, exposed c) +
          2 * (contourIdentityValue q n hn s - contourIdentityValue q n hn Bs) := hpair'
    _ = 2 * ((∑ e ∈ parafermionicCoverExposedCorners n,
          contourIdentitySign n e.1 * contourIdentityValue q n hn e.1) +
          contourIdentityValue q n hn s - contourIdentityValue q n hn Bs) := by
      rw [← hexposed]
      ring

end
end PottsContinuity.FKC.FiniteFK
