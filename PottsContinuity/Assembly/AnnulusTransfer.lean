module

public import PottsContinuity.Assembly.Links
public import PottsContinuity.DualityExt.PositiveBoundaryMergePDTransfer
public import PottsContinuity.PD.FK.IncreasingEvents

/-!
# Assembly of the conditional annulus transfer

The finite two-block estimate is proved in `DualityExt.PositiveBoundaryMergePDTransfer`.
This module records the exact finite carrier, law/event identifications, dual P5a estimate,
and comparison needed to apply it to the wired box annulus of the P5 ⇒ P1 argument
(Lemma 1) in `Thm3/Easy`.
-/

@[expose] public section

namespace PottsContinuity.Assembly

open PottsContinuity.PD.FK
open PottsContinuity.DualityExt
open MeasureTheory

noncomputable section

universe u

/-- Finite-volume data for the two-block dual transfer at dyadic annulus scale.
The dual event lower bound is the P5a input on its exact corner-identified
carrier; the remaining fields identify the law, the complementary event, and
the comparison to the wired `boxMeasure` event. -/
structure P5AnnulusFiniteInput (q : Set.Ici (1 : ℝ)) (j : ℕ) (c : ℝ) where
  V : Type u
  [instFiniteV : Finite V]
  W : Type u
  [instFiniteW : Finite W]
  G : SimpleGraph V
  H : SimpleGraph W
  I : Set V
  O : Set V
  hIO : Disjoint I O
  u : V
  v : V
  hu : u ∈ I
  hv : v ∈ O
  η : BoundaryCondition W
  d : Configuration G ≃ Configuration H
  S : Set (Configuration H)
  T : Set (Configuration G)
  hlaw :
    (law G (criticalParameters q) (positiveTwoBlockBoundary I O hIO)).map d =
      law H (criticalParameters q) η
  hevent : positiveBoundaryDisconnectedEvent
      (G := G) (positiveTwoBlockBoundary I O hIO)
      u v = d ⁻¹' S
  hdual : c ≤ (measure H (criticalParameters q) η S).toReal
  hdisjoint : Disjoint T
    (positiveBoundaryDisconnectedEvent
      (G := G) (positiveTwoBlockBoundary I O hIO)
      u v)
  hbox :
    (PottsContinuity.PD.RCInfinite.boxMeasure
      (criticalParameters q) 1 (0, 0) (2 ^ j) :
      Measure PottsContinuity.PD.FK.LatticeConfiguration).real
      {ω | annulusOpenCrossing (2 ^ (j - 1)) ω} ≤
      (measure G (criticalParameters q)
        (BoundaryCondition.wired (I ∪ O)) T).toReal

end
end PottsContinuity.Assembly
