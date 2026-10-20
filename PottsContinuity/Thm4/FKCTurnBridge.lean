module

public import PottsContinuity.Thm4.FKCExplorationBridge
public import PottsContinuity.Thm4.WalkTurn
public import PottsContinuity.FKC.Medial.ParafermionicCoverSourceTurning

@[expose] public section

namespace PottsContinuity.Thm4.FKCBridge
open PottsContinuity.Thm4.Medial SimpleGraph
noncomputable section

theorem turnExponent_eq (n : ℕ) (A : PottsContinuity.PD.FK.Configuration (ParafermionicAmbientGraph n))
    (c : ParafermionicCoverPort) :
    PottsContinuity.FKC.Medial.parafermionicCoverMedialTurnExponent
      (PottsContinuity.FKC.FiniteFK.parafermionicCoverConfigurationExtensionState n (fkcConfiguration n A)) (coverPortEquiv c) =
      parafermionicCoverMedialTurnExponent (parafermionicCoverConfigurationExtensionState n A) c := by
  have hstate := bondState_eq n A c
  generalize hB : parafermionicCoverPortBondState (parafermionicCoverConfigurationExtensionState n A) c = ω at hstate
  unfold parafermionicCoverMedialTurnExponent PottsContinuity.FKC.Medial.parafermionicCoverMedialTurnExponent
    parafermionicCoverMedialTurnPositive PottsContinuity.FKC.Medial.parafermionicCoverMedialTurnPositive
  rcases c with ⟨⟨⟨b, a⟩, t, s⟩, k⟩
  cases a <;> cases t <;> cases s <;>
    simp only [medialTurnPositive, PottsContinuity.FKC.Medial.medialTurnPositive, coverPortEquiv, portEquiv,
      bondEquiv, axisEquiv, Equiv.prodCongr_apply, Prod.map, Equiv.refl_apply,
      Equiv.coe_fn_mk, parafermionicCoverPortLocalBaseState,
      PottsContinuity.FKC.Medial.parafermionicCoverPortLocalBaseState, ↓reduceIte] at hstate ⊢ <;>
    rw [hstate, hB] <;> cases ω <;> rfl

theorem stepTurn_eq (n : ℕ) (A : PottsContinuity.PD.FK.Configuration (ParafermionicAmbientGraph n))
    (u v : ParafermionicCoverFinitePort n × Bool) :
    PottsContinuity.FKC.FiniteFK.parafermionicCoverFinitePairingStepTurn n (fkcConfiguration n A)
      (explorationVertexEquiv n u) (explorationVertexEquiv n v) =
      parafermionicCoverFinitePairingStepTurn n A u v := by
  change (if u.2 = false ∧ v.2 = false then
    PottsContinuity.FKC.Medial.parafermionicCoverMedialTurnExponent
      (PottsContinuity.FKC.FiniteFK.parafermionicCoverConfigurationExtensionState n (fkcConfiguration n A))
      (coverPortEquiv u.1.1) else 0) = _
  rw [turnExponent_eq]
  rfl

theorem walkTurn_map (n : ℕ) (hn : 1 ≤ n)
    (A : PottsContinuity.PD.FK.Configuration (ParafermionicAmbientGraph n))
    {u v : ParafermionicCoverFinitePort n × Bool}
    (p : (parafermionicCoverFiniteCornerCutPairingGraph n hn A).Walk u v) :
    PottsContinuity.FKC.FiniteFK.parafermionicCoverFinitePairingWalkTurn n hn (fkcConfiguration n A)
      (p.map (explorationGraphIso n hn A).toHom) =
      parafermionicCoverFinitePairingWalkTurn n hn A p := by
  unfold PottsContinuity.FKC.FiniteFK.parafermionicCoverFinitePairingWalkTurn parafermionicCoverFinitePairingWalkTurn
  rw [Walk.darts_map, List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro d _
  exact stepTurn_eq n A d.fst d.snd

/-- The actual exploration's total turn is four signed quarter turns. The FKC
source-cycle theorem is purely combinatorial and has no cluster-weight input. -/
theorem exploration_turn_eq_four (n : ℕ) (hn : 1 ≤ n)
    (A : PottsContinuity.PD.FK.Configuration (ParafermionicAmbientGraph n)) :
    parafermionicCoverFinitePairingWalkTurn n hn A
      (parafermionicCoverFiniteOriginExplorationPath n hn A) = 4 := by
  let E := explorationGraphIso n hn A
  let p := parafermionicCoverFiniteOriginExplorationPath n hn A
  have hs : E (parafermionicCoverFiniteOriginCornerPort n hn, true) =
      (PottsContinuity.FKC.FiniteFK.parafermionicCoverFiniteOriginCornerPort n hn, true) :=
    Prod.ext (finiteOrigin_eq n hn) rfl
  have ht : E (parafermionicCoverFiniteCornerPairPerm n
      (parafermionicCoverFiniteOriginCornerPort n hn), true) =
      (PottsContinuity.FKC.FiniteFK.parafermionicCoverFiniteCornerPairPerm n
        (PottsContinuity.FKC.FiniteFK.parafermionicCoverFiniteOriginCornerPort n hn), true) :=
    Prod.ext ((finiteCornerPair_eq n _).trans
      (congrArg (PottsContinuity.FKC.FiniteFK.parafermionicCoverFiniteCornerPairPerm n) (finiteOrigin_eq n hn))) rfl
  let q := (p.map E.toHom).copy hs ht
  have hq : q.IsPath := by
    simp only [q, Walk.isPath_def, Walk.support_copy, Walk.support_map]
    exact (parafermionicCoverFiniteOriginExplorationPath_isPath n hn A).support_nodup.map E.injective
  have heq : q = PottsContinuity.FKC.FiniteFK.parafermionicCoverFiniteOriginExplorationPath n hn (fkcConfiguration n A) := by
    obtain ⟨r, hr, huniq⟩ := PottsContinuity.FKC.FiniteFK.parafermionicCoverFiniteCornerCut_existsUnique_isPath
      n hn (fkcConfiguration n A)
    exact (huniq q hq).trans (huniq _
      (PottsContinuity.FKC.FiniteFK.parafermionicCoverFiniteOriginExplorationPath_isPath n hn (fkcConfiguration n A))).symm
  have hturn := PottsContinuity.FKC.Medial.parafermionicCoverFiniteOriginExplorationPath_turn_eq_four n hn (fkcConfiguration n A)
  rw [← heq] at hturn
  have hcopy : PottsContinuity.FKC.FiniteFK.parafermionicCoverFinitePairingWalkTurn n hn (fkcConfiguration n A) q =
      PottsContinuity.FKC.FiniteFK.parafermionicCoverFinitePairingWalkTurn n hn (fkcConfiguration n A) (p.map E.toHom) := by
    simp only [q, PottsContinuity.FKC.FiniteFK.parafermionicCoverFinitePairingWalkTurn, Walk.darts_copy]
  rw [hcopy, walkTurn_map] at hturn
  exact hturn

end
end PottsContinuity.Thm4.FKCBridge
