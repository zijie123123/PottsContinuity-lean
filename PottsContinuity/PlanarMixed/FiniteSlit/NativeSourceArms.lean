module

public import PottsContinuity.PlanarMixed.FiniteSlit.OpenSourceTip
public import PottsContinuity.PlanarMixed.FiniteSlit.ClippedReveals
public import PottsContinuity.PlanarMixed.FiniteSlit.SourceRecordGeometry
public import PottsContinuity.PlanarMixed.RecordedArcBonds
public import PottsContinuity.BD12.CriticalValueConditional
public import PottsContinuity.BD12.CriticalValue
public import PottsContinuity.PlanarMixed.FiniteSlit.SourceExteriorReveals

@[expose] public section

namespace PottsContinuity.PlanarMixed.FiniteSlit
open PD.FK BD12 Exploration
noncomputable section
local instance nativeSourceArmsEdgeDecidableEq {U : Type*} (H : SimpleGraph U) :
    DecidableEq H.edgeSet := Classical.decEq _

/-- Witnesses for disjoint source arms and the retained first-contact crop.
These are sample-wise witnesses, not an observed full-path record: the full
first arm may vary after its discarded suffix is changed. -/
structure SourceWalkPair {V : Type*} (G : SimpleGraph V) where
  firstStart : V
  secondStart : V
  firstEnd : V
  secondEnd : V
  first : G.Walk firstStart firstEnd
  second : G.Walk secondStart secondEnd

/-- Source-arm geometry for a pair of actual open walks. All conditions are
ordinary lattice geometry and the literal first-contact characterization. -/
structure NativeSourceArms (n : ℕ)
    (C : Configuration (rectangleGraph (0,0) (2*n) (2*n)))
    (I J : Set (RectangleVertex (0,0) (2*n) (2*n))) where
  column : ℤ
  rightColumn : ℤ
  column_pos : 1 ≤ column
  column_le : column ≤ ((2*n:ℕ):ℤ)
  paths : SourceWalkPair (openGraph (rectangleGraph (0,0) (2*n) (2*n)) C)
  first_bottom : paths.firstStart.val.2 = 0
  second_bottom : paths.secondStart.val.2 = 0
  first_end_column : paths.firstEnd.val.1 = rightColumn
  second_end_column : paths.secondEnd.val.1 = column
  first_start_right : column ≤ paths.firstStart.val.1
  starts_order : paths.firstStart.val.1 < paths.secondStart.val.1
  first_bounds : ∀ w ∈ paths.first.support, w.val.1 ≤ rightColumn
  second_bounds : ∀ w ∈ paths.second.support, column ≤ w.val.1 ∧ w.val.1 ≤ rightColumn
  disjoint : ∀ w ∈ paths.first.support, w ∉ paths.second.support
  first_in : paths.firstStart ∈ I
  second_in : paths.secondStart ∈ J
  cropIndex : ℕ
  first_contact : IsFirstContact paths.first
    {w | w.val.1 = column-1 ∧ paths.secondEnd.val.2 ≤ w.val.2} cropIndex

namespace NativeSourceArms
variable {n : ℕ} {C : Configuration (rectangleGraph (0,0) (2*n) (2*n))}
  {I J : Set (RectangleVertex (0,0) (2*n) (2*n))} (D : NativeSourceArms n C I J)

/-- Literal retained source-coordinate trace; no suffix is included. -/
def croppedTrace : Set LatticeVertex :=
  Subtype.val '' {w | w ∈ (D.paths.first.take D.cropIndex).support}

/-- The original source Gamma1 trace ending at the slit tip. -/
def tipTrace : Set LatticeVertex := Subtype.val '' {w | w ∈ D.paths.second.support}

end NativeSourceArms
end
end PottsContinuity.PlanarMixed.FiniteSlit
