module

public import PottsContinuity.Thm3.OuterCircuit.FiniteSourceSelector

@[expose] public section

namespace PottsContinuity.OuterCircuit

open PottsContinuity.PD.FK
open PottsContinuity.RSW

noncomputable section

/-- Selector indices include source polygons and finite region unions used
when the geometric envelope premise is unavailable. -/
abbrev OuterCircuitSelectorIndex (n : ℕ) :=
  Sum (OuterCircuitPolygonCode n) (Finset (OuterCircuitHostVertex n))

noncomputable instance outerCircuitSelectorIndexFintype (n : ℕ) :
    Fintype (OuterCircuitSelectorIndex n) := Fintype.ofFinite _

noncomputable instance outerCircuitSelectorIndexDecidableEq (n : ℕ) :
    DecidableEq (OuterCircuitSelectorIndex n) := Classical.decEq _

/-- A chosen finite order on the polygon and region codes. -/
noncomputable instance outerCircuitSelectorIndexLinearOrder (n : ℕ) :
    LinearOrder (OuterCircuitSelectorIndex n) :=
  LinearOrder.lift' (Fintype.equivFin (OuterCircuitSelectorIndex n))
    (Fintype.equivFin (OuterCircuitSelectorIndex n)).injective

/-- Region of a source polygon, or the explicitly stored union region. -/
def outerCircuitSelectorInside {n : ℕ} (i : OuterCircuitSelectorIndex n) :
    Finset (OuterCircuitHostVertex n) :=
  match i with
  | .inl p => outerCircuitCandidateInside p
  | .inr S => S

/-- Recognition edges are empty on the auxiliary region indices. -/
def outerCircuitSelectorSupport {n : ℕ} (i : OuterCircuitSelectorIndex n) :
    Finset (lemma4AmbientGraph n).edgeSet :=
  match i with
  | .inl p => outerCircuitCandidateSupport p
  | .inr _ => ∅

/-- Only actual source polygons can be selected as open outer circuits. -/
def outerCircuitSelectorValid {n : ℕ}
    (C : Configuration (lemma4AmbientGraph n))
    (i : OuterCircuitSelectorIndex n) : Prop :=
  match i with
  | .inl p => outerCircuitCandidateValid C p
  | .inr _ => False

end
end PottsContinuity.OuterCircuit
