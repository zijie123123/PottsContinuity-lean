-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `Medial/MedialPortTurn.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.Medial.LatticePorts

@[expose] public section

namespace PottsContinuity.FKC.Medial

open LatticePort

noncomputable section

/-- The actual signed quarter-turn at a medial port. `true` means `+i` and
`false` means `-i`; the table is indexed by the original edge state. -/
def medialTurnPositive (ω : LatticeBond → Bool) (p : LatticePort) : Bool :=
  match p.bond.axis, p.tip, p.side, ω p.bond with
  | .horizontal, false, false, false => true
  | .horizontal, false, false, true => false
  | .horizontal, false, true, false => false
  | .horizontal, false, true, true => true
  | .horizontal, true, false, false => false
  | .horizontal, true, false, true => true
  | .horizontal, true, true, false => true
  | .horizontal, true, true, true => false
  | .vertical, false, false, false => false
  | .vertical, false, false, true => true
  | .vertical, false, true, false => true
  | .vertical, false, true, true => false
  | .vertical, true, false, false => true
  | .vertical, true, false, true => false
  | .vertical, true, true, false => false
  | .vertical, true, true, true => true

end
end PottsContinuity.FKC.Medial
