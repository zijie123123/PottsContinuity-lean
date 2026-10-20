module

public import PottsContinuity.Assembly.AnnulusTransfer
public import PottsContinuity.DualityExt.PositiveFreeDomainComparison
public import Mathlib
public import PottsContinuity.PD.FK.FrozenBridge
public import PottsContinuity.Thm3.Easy.P5FourFrameConditional
public import PottsContinuity.Thm3.RSW.FiniteBoundary

@[expose] public section

namespace PottsContinuity.Assembly

open PottsContinuity
open PottsContinuity.DualityExt
open PottsContinuity.PD.FK
open PottsContinuity.RSW
open PottsContinuity.PD.RCInfinite
open MeasureTheory

universe u

noncomputable section

/-- Finite annulus data where the P5a lower bound is transported from its
source annulus through an explicit graph embedding into the dual carrier. -/
structure P5AnnulusEmbeddedP5aFiniteInput
    (q : Set.Ici (1 : ℝ)) (j : ℕ) (c : ℝ) where
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
  annulusEmbedding :
    (Thm3.Easy.p5aAnnulusVertexSet (2 ^ (j - 1) - 1) :
      Set (ℤ × ℤ)) ↪ W
  annulusGraph_le :
      (squareLattice.induce
        (Thm3.Easy.p5aAnnulusVertexSet (2 ^ (j - 1) - 1) :
          Set (ℤ × ℤ))).map annulusEmbedding ≤ H
  hη : (BoundaryCondition.free ∅ : BoundaryCondition W).partition ≤ η.partition
  hS : S =
    {A | embeddedConfigurationRestriction
      (squareLattice.induce
        (Thm3.Easy.p5aAnnulusVertexSet (2 ^ (j - 1) - 1) :
          Set (ℤ × ℤ))) H annulusEmbedding annulusGraph_le A ∈
      PottsContinuity.RSW.finiteBoolEvent
        (Thm3.Easy.p5aAnnulusVertexSet (2 ^ (j - 1) - 1))
        (Thm3.Easy.p5aAnnulusCircuitEvent (2 ^ (j - 1) - 1))}

end
end PottsContinuity.Assembly
