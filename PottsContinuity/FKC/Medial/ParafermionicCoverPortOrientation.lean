-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `Medial/ParafermionicCoverPortOrientation.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.Medial.ParafermionicCoverTurn
public import PottsContinuity.FKC.Medial.ParafermionicCoverOriginCorner
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.Medial

open LatticeAxis LatticeBond LatticePort
noncomputable section

/-- Whether the incoming primal segment lies to the left of the oriented
incoming medial segment. -/
def medialIncomingPrimalLeft (p : LatticePort) : Bool :=
  match p.bond.axis with
  | horizontal => decide (p.tip = p.side)
  | vertical => decide (p.tip ≠ p.side)

theorem medialIncomingPrimalLeft_openPair (p : LatticePort) :
    medialIncomingPrimalLeft p.openPair = !medialIncomingPrimalLeft p := by
  rcases p with ⟨⟨b, ax⟩, t, s⟩
  cases ax <;> cases t <;> cases s <;>
    simp [medialIncomingPrimalLeft, LatticePort.openPair]

theorem medialIncomingPrimalLeft_closedPair (p : LatticePort) :
    medialIncomingPrimalLeft p.closedPair = !medialIncomingPrimalLeft p := by
  rcases p with ⟨⟨b, ax⟩, t, s⟩
  cases ax <;> cases t <;> cases s <;>
    simp [medialIncomingPrimalLeft, LatticePort.closedPair]

theorem medialIncomingPrimalLeft_cornerPair (p : LatticePort) :
    medialIncomingPrimalLeft p.cornerPair = !medialIncomingPrimalLeft p := by
  rcases p with ⟨⟨b, ax⟩, t, s⟩
  cases ax <;> cases t <;> cases s <;>
    simp [medialIncomingPrimalLeft, LatticePort.cornerPair]

theorem medialIncomingPrimalLeft_localPair (ω : LatticeBond → Bool)
    (p : LatticePort) :
    medialIncomingPrimalLeft (localPair ω p) = !medialIncomingPrimalLeft p := by
  unfold localPair
  split
  · exact medialIncomingPrimalLeft_openPair p
  · exact medialIncomingPrimalLeft_closedPair p

theorem medialIncomingPrimalLeft_origin :
    medialIncomingPrimalLeft parafermionicCoverOriginCornerPort.1 = true := by
  rfl

/-- The primal-left orientation of a genuine lifted port occurrence. -/
def parafermionicCoverIncomingPrimalLeft (c : ParafermionicCoverPort) : Bool :=
  medialIncomingPrimalLeft c.1

theorem parafermionicCoverIncomingPrimalLeft_openPair (c : ParafermionicCoverPort) :
    parafermionicCoverIncomingPrimalLeft (parafermionicCoverOpenPair c) =
      !parafermionicCoverIncomingPrimalLeft c := by
  simpa [parafermionicCoverIncomingPrimalLeft,
    parafermionicCoverOpenPair_projection] using
    medialIncomingPrimalLeft_openPair c.1

theorem parafermionicCoverIncomingPrimalLeft_closedPair (c : ParafermionicCoverPort) :
    parafermionicCoverIncomingPrimalLeft (parafermionicCoverClosedPair c) =
      !parafermionicCoverIncomingPrimalLeft c := by
  simpa [parafermionicCoverIncomingPrimalLeft,
    parafermionicCoverClosedPair_projection] using
    medialIncomingPrimalLeft_closedPair c.1

theorem parafermionicCoverIncomingPrimalLeft_cornerPair (c : ParafermionicCoverPort) :
    parafermionicCoverIncomingPrimalLeft (parafermionicCoverCornerPair c) =
      !parafermionicCoverIncomingPrimalLeft c := by
  simpa [parafermionicCoverIncomingPrimalLeft,
    parafermionicCoverCornerPair_projection] using
    medialIncomingPrimalLeft_cornerPair c.1

theorem parafermionicCoverIncomingPrimalLeft_localPair
    (ω : ParafermionicCoverConfiguration) (c : ParafermionicCoverPort) :
    parafermionicCoverIncomingPrimalLeft (parafermionicCoverLocalPair ω c) =
      !parafermionicCoverIncomingPrimalLeft c := by
  simpa [parafermionicCoverIncomingPrimalLeft,
    parafermionicCoverLocalPair_projection] using
    medialIncomingPrimalLeft_localPair (parafermionicCoverPortLocalBaseState ω c) c.1

theorem parafermionicCoverIncomingPrimalLeft_origin :
    parafermionicCoverIncomingPrimalLeft parafermionicCoverOriginCornerPort = true := by
  exact medialIncomingPrimalLeft_origin

end
end PottsContinuity.FKC.Medial
