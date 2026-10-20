module

public import PottsContinuity.DualityExt.PositiveP5aJordanAnnulusTransfer
public import PottsContinuity.Thm3.Easy.P5FourFrameConditional

@[expose] public section

namespace PottsContinuity.DualityExt

open PottsContinuity.PD.FK
open MeasureTheory

noncomputable section

local instance p5aSourceHostConfigFintype (N : ℕ) :
    Fintype (Configuration
      (rectangleDualGraph (p5aAnnulusHostAnchor N) (4 * N) (4 * N))) :=
  Fintype.ofFinite _

/-- The source P5a annulus graph on the source module's exact vertex carrier. -/
def p5aAnnulusSourceFaceGraph (N : ℕ) :
    SimpleGraph
      {v : LatticeVertex // v ∈
        PottsContinuity.Thm3.Easy.p5aAnnulusVertexSet (N - 1)} :=
  squareLattice.induce
    (PottsContinuity.Thm3.Easy.p5aAnnulusVertexSet (N - 1) :
      Set LatticeVertex)

local instance p5aSourceConfigFintype (N : ℕ) :
    Fintype (Configuration
      (p5aAnnulusSourceFaceGraph N)) := Fintype.ofFinite _

/-- The source event on the exact P5a graph carrier. -/
def p5aAnnulusSourceJordanCircuitEvent (N : ℕ) :
    Set (Configuration (p5aAnnulusSourceFaceGraph N)) :=
  PottsContinuity.RSW.finiteBoolEvent
    (PottsContinuity.Thm3.Easy.p5aAnnulusVertexSet (N - 1))
    (PottsContinuity.RSW.annulusCircuitEvent
      (PottsContinuity.Thm3.Easy.p5aAnnulusVertexSet (N - 1))
      (0, 0) (N - 1))

theorem p5aAnnulusSourceJordanCircuitEvent_upper (N : ℕ) :
    IsUpperSet (p5aAnnulusSourceJordanCircuitEvent N) := by
  intro A B hAB hA
  change (PottsContinuity.PD.FK.boolConfigurationEquiv
      (p5aAnnulusSourceFaceGraph N)).symm A ∈
    PottsContinuity.RSW.annulusCircuitEvent
      (PottsContinuity.Thm3.Easy.p5aAnnulusVertexSet (N - 1))
      (0, 0) (N - 1) at hA
  change (PottsContinuity.PD.FK.boolConfigurationEquiv
      (p5aAnnulusSourceFaceGraph N)).symm B ∈
    PottsContinuity.RSW.annulusCircuitEvent
      (PottsContinuity.Thm3.Easy.p5aAnnulusVertexSet (N - 1))
      (0, 0) (N - 1)
  exact PottsContinuity.RSW.annulusCircuitEvent_isUpperSet
    (PottsContinuity.Thm3.Easy.p5aAnnulusVertexSet (N - 1))
    (0, 0) (N - 1)
    (PottsContinuity.RSW.boolConfigurationEquiv_symm_mono
      (PottsContinuity.Thm3.Easy.p5aAnnulusVertexSet (N - 1)) hAB) hA

theorem p5aAnnulusProbability_eq_sourceFaceMeasure (N : ℕ)
    (q : Set.Ici (1 : ℝ)) :
    PottsContinuity.Thm3.Easy.p5aAnnulusProbability
        (criticalParameters q) (N - 1) =
      (measure (p5aAnnulusSourceFaceGraph N) (criticalParameters q)
        (BoundaryCondition.free ∅) (p5aAnnulusSourceJordanCircuitEvent N)).toReal := by
  let V := PottsContinuity.Thm3.Easy.p5aAnnulusVertexSet (N - 1)
  let G := p5aAnnulusSourceFaceGraph N
  let S := p5aAnnulusSourceJordanCircuitEvent N
  have hpart :
      (frozenBoundaryCondition V 0).partition =
        (BoundaryCondition.free ∅ : BoundaryCondition (V : Set LatticeVertex)).partition := by
    simp [frozenBoundaryCondition, BoundaryCondition.free]
  have hlaw := law_eq_of_boundary_partition_eq
    (G := G) (criticalParameters q)
    (frozenBoundaryCondition V 0) (BoundaryCondition.free ∅) hpart
  have hsource :
      PottsContinuity.Thm3.Easy.p5aAnnulusProbability
          (criticalParameters q) (N - 1) =
        (measure G (criticalParameters q) (frozenBoundaryCondition V 0) S).toReal := by
    unfold PottsContinuity.Thm3.Easy.p5aAnnulusProbability
      PottsContinuity.RSW.finiteBoundaryEventProbability
    rfl
  calc
    PottsContinuity.Thm3.Easy.p5aAnnulusProbability
        (criticalParameters q) (N - 1) =
      (measure G (criticalParameters q) (frozenBoundaryCondition V 0) S).toReal := hsource
    _ = (measure G (criticalParameters q) (BoundaryCondition.free ∅) S).toReal := by
      unfold PottsContinuity.PD.FK.measure
      let : MeasurableSpace (Configuration G) :=
        PottsContinuity.PD.FK.configurationMeasurableSpace G
      have hμ : (law G (criticalParameters q) (frozenBoundaryCondition V 0)).toMeasure =
          (law G (criticalParameters q) (BoundaryCondition.free ∅)).toMeasure :=
        congrArg PMF.toMeasure hlaw
      exact congrArg
        (fun μ : MeasureTheory.Measure (Configuration G) => ENNReal.toReal (μ S)) hμ

end
end PottsContinuity.DualityExt
