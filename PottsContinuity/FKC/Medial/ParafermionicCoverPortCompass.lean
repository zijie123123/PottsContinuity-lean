-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `Medial/ParafermionicCoverPortCompass.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.Medial.ParafermionicCoverTurn
public import PottsContinuity.FKC.Medial.FiniteCompassFan
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.Medial

open LatticeAxis

/-- The radial primal direction at a port, in the canonical compass order
`0=E, 1=N, 2=W, 3=S`. -/
def parafermionicCoverPortRadialCompass (c : ParafermionicCoverPort) : Fin 4 :=
  match c.1.bond.axis, c.1.tip with
  | horizontal, false => 0
  | horizontal, true => 2
  | vertical, false => 1
  | vertical, true => 3

/-- The unit-cell normal at a port, in the canonical compass order
`0=E, 1=N, 2=W, 3=S`. -/
def parafermionicCoverPortCellNormalCompass (c : ParafermionicCoverPort) : Fin 4 :=
  match c.1.bond.axis, c.1.side with
  | horizontal, false => 3
  | horizontal, true => 1
  | vertical, false => 2
  | vertical, true => 0

theorem parafermionicCoverPortRadialCompass_closedPair (c : ParafermionicCoverPort) :
    parafermionicCoverPortRadialCompass (parafermionicCoverClosedPair c) =
      parafermionicCoverPortRadialCompass c := by
  rcases c with ⟨⟨⟨⟨x,y⟩,ax⟩,tip,side⟩,k⟩
  cases ax <;> cases tip <;> cases side <;>
    simp [parafermionicCoverPortRadialCompass, parafermionicCoverClosedPair,
      LatticePort.closedPair]

theorem parafermionicCoverPortRadialCompass_openPair (c : ParafermionicCoverPort) :
    parafermionicCoverPortRadialCompass (parafermionicCoverOpenPair c) =
      parafermionicCoverPortRadialCompass c + 2 := by
  rcases c with ⟨⟨⟨⟨x,y⟩,ax⟩,tip,side⟩,k⟩
  cases ax <;> cases tip <;> cases side <;>
    simp [parafermionicCoverPortRadialCompass, parafermionicCoverOpenPair,
      LatticePort.openPair]

theorem parafermionicCoverPortRadialCompass_cornerPair (c : ParafermionicCoverPort) :
    parafermionicCoverPortRadialCompass (parafermionicCoverCornerPair c) =
      parafermionicCoverPortCellNormalCompass c := by
  rcases c with ⟨⟨⟨⟨x,y⟩,ax⟩,tip,side⟩,k⟩
  cases ax <;> cases tip <;> cases side <;>
    simp [parafermionicCoverPortRadialCompass,
      parafermionicCoverPortCellNormalCompass, parafermionicCoverCornerPair,
      LatticePort.cornerPair]

theorem parafermionicCoverPortCellNormalCompass_cornerPair (c : ParafermionicCoverPort) :
    parafermionicCoverPortCellNormalCompass (parafermionicCoverCornerPair c) =
      parafermionicCoverPortRadialCompass c := by
  rcases c with ⟨⟨⟨⟨x,y⟩,ax⟩,tip,side⟩,k⟩
  cases ax <;> cases tip <;> cases side <;>
    simp [parafermionicCoverPortRadialCompass,
      parafermionicCoverPortCellNormalCompass, parafermionicCoverCornerPair,
      LatticePort.cornerPair]

private theorem parafermionicCoverPortCompassTurnTable
    (c : ParafermionicCoverPort) (b : Bool) :
    (if medialTurnPositive (fun _ : LatticeBond => b) c.1 then (1 : ℤ) else -1) =
      if b then
        primalCompassQuarterTurn (parafermionicCoverPortRadialCompass c)
          (parafermionicCoverPortCellNormalCompass c)
      else -primalCompassQuarterTurn (parafermionicCoverPortRadialCompass c)
          (parafermionicCoverPortCellNormalCompass c) := by
  rcases c with ⟨⟨⟨⟨x,y⟩,ax⟩,tip,side⟩,k⟩
  cases ax <;> cases tip <;> cases side <;> cases b <;>
    simp [medialTurnPositive, parafermionicCoverPortRadialCompass,
      parafermionicCoverPortCellNormalCompass, primalCompassQuarterTurn]

theorem parafermionicCoverMedialTurnExponent_eq_portCompass (ω : ParafermionicCoverConfiguration)
    (c : ParafermionicCoverPort) :
    parafermionicCoverMedialTurnExponent ω c =
      if parafermionicCoverPortBondState ω c then
        primalCompassQuarterTurn (parafermionicCoverPortRadialCompass c)
          (parafermionicCoverPortCellNormalCompass c)
      else -primalCompassQuarterTurn (parafermionicCoverPortRadialCompass c)
          (parafermionicCoverPortCellNormalCompass c) := by
  have hpositive : medialTurnPositive (parafermionicCoverPortLocalBaseState ω c) c.1 =
      medialTurnPositive (fun _ : LatticeBond => parafermionicCoverPortBondState ω c) c.1 := by
    simp only [medialTurnPositive, parafermionicCoverPortLocalBaseState_at]
  change (if medialTurnPositive (parafermionicCoverPortLocalBaseState ω c) c.1
      then (1 : ℤ) else -1) = _
  rw [hpositive]
  exact parafermionicCoverPortCompassTurnTable c
    (parafermionicCoverPortBondState ω c)

end PottsContinuity.FKC.Medial
