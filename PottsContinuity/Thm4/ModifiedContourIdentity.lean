/- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
accessible (see `related_formalizations` in formalization.yaml): file
`FiniteFK/ParafermionicCoverContourIdentity.lean`.
This module now contains only auxiliary private lemmas about corner terms of the
modified expectation on the closed range [1,4]; the main theorems do not use them. The
q = 4 contour statements used by the proof are `modifiedPathExpectation_four_bulk_zero`
(`Thm4/WindingBulk.lean`) and `exterior_signed_winding_mean` (`Thm4/WindingVisitMass.lean`).
-/
module

public import PottsContinuity.Thm4.ZeroTurn
public import PottsContinuity.Thm4.ContourBoundary
public import PottsContinuity.Thm4.PortOrientation
public import PottsContinuity.Thm4.PathObservable
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.Thm4

open PottsContinuity.PD.FK PottsContinuity.Thm4.Medial
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

 def contourIdentityValue (q : Set.Icc (1 : ℝ) 4) (n : ℕ) (hn : 1 ≤ n)
    (c : ParafermionicCoverFinitePort n) : ℂ :=
  parafermionicCoverModifiedPathExpectation q n hn (c, true)

private theorem contourIdentityValue_corner_eq (q : Set.Icc (1 : ℝ) 4) (n : ℕ)
    (hn : 1 ≤ n)
    (c : ParafermionicCoverFinitePort n)
    (hc : c ≠ parafermionicCoverFiniteOriginCornerPort n hn ∧
      c ≠ parafermionicCoverFiniteCornerPairPerm n
        (parafermionicCoverFiniteOriginCornerPort n hn)) :
    contourIdentityValue q n hn c =
      contourIdentityValue q n hn (parafermionicCoverFiniteCornerPairPerm n c) := by
  unfold contourIdentityValue parafermionicCoverModifiedPathExpectation
  apply MeasureTheory.integral_congr_ae
  exact Filter.Eventually.of_forall (fun A =>
    parafermionicCoverModifiedPathAtom_corner_eq_of_not_cut q n hn A c hc)

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

 def contourIdentityBulkTerm (q : Set.Icc (1 : ℝ) 4) (n : ℕ)
    (hn : 1 ≤ n) (c : ParafermionicCoverFinitePort n) : ℂ := by
  classical
  exact if contourIdentityInternal n c then
    contourIdentitySign n c * contourIdentityValue q n hn c else 0

 def contourIdentityExposedTerm (q : Set.Icc (1 : ℝ) 4) (n : ℕ)
    (hn : 1 ≤ n) (c : ParafermionicCoverFinitePort n) : ℂ := by
  classical
  exact if contourIdentityInternal n c ∧
      ¬ contourIdentityInternal n (parafermionicCoverFiniteCornerPairPerm n c) then
    contourIdentitySign n c * contourIdentityValue q n hn c else 0

 def contourIdentityDefectTerm (q : Set.Icc (1 : ℝ) 4) (n : ℕ)
    (hn : 1 ≤ n) (c : ParafermionicCoverFinitePort n) : ℂ := by
  classical
  let s := parafermionicCoverFiniteOriginCornerPort n hn
  let Bs := parafermionicCoverFiniteCornerPairPerm n s
  exact if c = s ∨ c = Bs then
    contourIdentityValue q n hn s - contourIdentityValue q n hn Bs else 0

private theorem contourIdentity_pair_balance (q : Set.Icc (1 : ℝ) 4) (n : ℕ)
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

private theorem contourIdentity_exposed_sum (q : Set.Icc (1 : ℝ) 4) (n : ℕ)
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

end
end PottsContinuity.Thm4
