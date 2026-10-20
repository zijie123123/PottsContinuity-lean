module

public import PottsContinuity.Thm4.LocalWinding
public import PottsContinuity.Thm4.ContourBoundary
public import PottsContinuity.Thm4.FinitePairSum

@[expose] public section

namespace PottsContinuity.Thm4
open PottsContinuity.PD.FK PottsContinuity.Thm4.Medial
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Exterior bonds are genuinely closed in the finite configuration extension. -/
theorem exteriorPort_state_false (n : ℕ)
    (A : Configuration (ParafermionicAmbientGraph n)) (c : ParafermionicCoverFinitePort n)
    (hc : ¬ parafermionicCoverFinitePortOtherEndpointInBox n c) :
    parafermionicCoverPortBondState (parafermionicCoverConfigurationExtensionState n A)
      c.1 = false := by
  apply Bool.eq_false_iff.mpr
  intro h
  apply hc
  have he := parafermionicCoverConfigurationExtensionState_true_endpoints_in_box n A
    (parafermionicCoverPortEdge c.1) h
  rw [parafermionicCoverPortEdge_eq_incident_pair] at he
  exact he _ (Sym2.mem_mk_right _ _)

/-- Closed exterior pairings preserve both primal endpoints, including sheet. -/
theorem exteriorPort_localPair_otherVertex (n : ℕ)
    (A : Configuration (ParafermionicAmbientGraph n)) (c : ParafermionicCoverFinitePort n)
    (hc : ¬ parafermionicCoverFinitePortOtherEndpointInBox n c) :
    parafermionicCoverPortOtherVertex (parafermionicCoverFiniteLocalPairPerm n A c).1 =
      parafermionicCoverPortOtherVertex c.1 := by
  change parafermionicCoverPortOtherVertex
    (parafermionicCoverLocalPair (parafermionicCoverConfigurationExtensionState n A) c.1) = _
  rw [parafermionicCoverLocalPair, exteriorPort_state_false n A c hc]
  rfl

/-- The exterior domain is invariant under the actual local pairing. -/
theorem exteriorPort_localPair_iff (n : ℕ)
    (A : Configuration (ParafermionicAmbientGraph n)) (c : ParafermionicCoverFinitePort n) :
    ¬ parafermionicCoverFinitePortOtherEndpointInBox n
        (parafermionicCoverFiniteLocalPairPerm n A c) ↔
      ¬ parafermionicCoverFinitePortOtherEndpointInBox n c := by
  constructor
  · intro hc
    have h := exteriorPort_localPair_otherVertex n A
      (parafermionicCoverFiniteLocalPairPerm n A c) hc
    rw [parafermionicCoverFiniteLocalPairPerm_involutive n A c] at h
    simpa only [parafermionicCoverFinitePortOtherEndpointInBox, h] using hc
  · intro hc
    simpa only [parafermionicCoverFinitePortOtherEndpointInBox,
      exteriorPort_localPair_otherVertex n A c hc] using hc

private theorem medialTurnPositive_closed_eq_flag (ω : LatticeBond → Bool)
    (p : LatticePort) (h : ω p.bond = false) :
    medialTurnPositive ω p = medialIncomingPrimalLeft p := by
  rcases p with ⟨⟨b, a⟩, t, s⟩
  cases a <;> cases t <;> cases s <;>
    simp [medialTurnPositive, medialIncomingPrimalLeft, h]

/-- An incoming exterior visit contributes one positive quarter turn, with no
bound or prescribed value on either individual suffix winding. -/
theorem pathWinding_exterior_pair_difference (n : ℕ) (hn : 1 ≤ n)
    (A : Configuration (ParafermionicAmbientGraph n)) (c : ParafermionicCoverFinitePort n)
    (hc : ¬ parafermionicCoverFinitePortOtherEndpointInBox n c)
    (hf : parafermionicCoverIncomingPrimalLeft c.1 = true) :
    parafermionicCoverPathWindingAtom n hn A (c, true) -
      parafermionicCoverPathWindingAtom n hn A
        (parafermionicCoverFiniteLocalPairPerm n A c, true) =
      if (c, false) ∈ (parafermionicCoverFiniteOriginExplorationPath n hn A).support
      then Real.pi / 2 else 0 := by
  rw [pathWinding_localPair_difference n hn A c hf]
  have hturn : parafermionicCoverMedialTurnExponent
      (parafermionicCoverConfigurationExtensionState n A) c.1 = 1 := by
    unfold parafermionicCoverMedialTurnExponent parafermionicCoverMedialTurnPositive
    rw [medialTurnPositive_closed_eq_flag _ _ (by
      rw [parafermionicCoverPortLocalBaseState_at, exteriorPort_state_false n A c hc])]
    change (if parafermionicCoverIncomingPrimalLeft c.1 then (1 : ℤ) else -1) = 1
    rw [hf]
    rfl
  rw [hturn]
  simp

/-- Exact exterior signed winding sum as the count of incoming exterior strands
visited by the actual exploration. This is pointwise in the configuration. -/
theorem exterior_signed_winding_sum (n : ℕ) (hn : 1 ≤ n)
    (A : Configuration (ParafermionicAmbientGraph n)) :
    (∑ c : ParafermionicCoverFinitePort n,
      if ¬ parafermionicCoverFinitePortOtherEndpointInBox n c then
        (if parafermionicCoverIncomingPrimalLeft c.1 then (1 : ℝ) else -1) *
          parafermionicCoverPathWindingAtom n hn A (c, true) else 0) =
    (Real.pi / 2) * ∑ c : ParafermionicCoverFinitePort n,
      if ¬ parafermionicCoverFinitePortOtherEndpointInBox n c ∧
        parafermionicCoverIncomingPrimalLeft c.1 = true ∧
        (c, false) ∈ (parafermionicCoverFiniteOriginExplorationPath n hn A).support
      then (1 : ℝ) else 0 := by
  classical
  let L := parafermionicCoverFiniteLocalPairPerm n A
  let P := fun c : ParafermionicCoverFinitePort n =>
    ¬ parafermionicCoverFinitePortOtherEndpointInBox n c
  have h := sum_signed_eq_incoming_pairs L
    (fun c => parafermionicCoverIncomingPrimalLeft c.1)
    (fun c => parafermionicCoverIncomingPrimalLeft_localPair _ c.1)
    P (exteriorPort_localPair_iff n A)
    (fun c => parafermionicCoverPathWindingAtom n hn A (c, true))
  simp only [ite_mul, one_mul, neg_one_mul] at ⊢
  rw [h, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c _
  by_cases hc : P c ∧ parafermionicCoverIncomingPrimalLeft c.1 = true
  · rw [ite_eq_left hc, pathWinding_exterior_pair_difference n hn A c hc.1 hc.2]
    by_cases hv : (c, false) ∈ (parafermionicCoverFiniteOriginExplorationPath n hn A).support
    all_goals simp [P] at hc
    all_goals simp [hc, hv]
  · have hnot : ¬ (¬ parafermionicCoverFinitePortOtherEndpointInBox n c ∧
        parafermionicCoverIncomingPrimalLeft c.1 = true ∧
        (c, false) ∈ (parafermionicCoverFiniteOriginExplorationPath n hn A).support) :=
      fun hbad => hc ⟨hbad.1, hbad.2.1⟩
    simp only [ite_eq_right hc, ite_eq_right hnot, mul_zero]

end
end PottsContinuity.Thm4
