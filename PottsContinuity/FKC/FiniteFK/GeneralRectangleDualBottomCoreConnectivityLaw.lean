-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/GeneralRectangleDualBottomCoreConnectivityLaw.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.GeneralRectangleDualBottomCoreAmbientConnectivity
public import PottsContinuity.FKC.FiniteFK.GeneralRectangleDualBottomCoreLaw
public import Mathlib.MeasureTheory.Measure.Portmanteau

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK
open PottsContinuity.FKC PottsContinuity.FKC.Medial MeasureTheory

noncomputable section

local instance coreLawAmbientCfgFintype (a : LatticeVertex) (w h : ℕ) :
    Fintype (Configuration (rectangleGraph (a.1 - 1, a.2) (w + 1) h)) := Fintype.ofFinite _
local instance coreLawDualCfgFintype (a : LatticeVertex) (w h : ℕ) :
    Fintype (Configuration (rectangleDualGraph a w h)) := Fintype.ofFinite _
local instance coreLawCoreCfgFintype (a : LatticeVertex) (w h : ℕ) :
    Fintype (Configuration (generalRectangleDualBottomCoreGraph a w h)) := Fintype.ofFinite _

/-- The actual core connectivity event: some selected retained seed reaches
one of the retained true-dual three sides. -/
def generalRectangleDualBottomCoreSeedBoundaryEvent
    (a : LatticeVertex) (w h : ℕ)
    (S : Set (generalRectangleDualBottomCoreVertex a w h)) :
    Set (Configuration (generalRectangleDualBottomCoreGraph a w h)) :=
  {C | ∃ u ∈ S, ∃ v,
    generalRectangleDualBottomCoreInclusion a w h v ∈
      generalRectangleDualBottomCollarInnerThreeSides a w h ∧
    ActualConnected (generalRectangleDualBottomCoreGraph a w h) C u v}

/-- In the ordinary rectangle, the seeds are the literal images of the chosen
core vertices and the target is the full left/right/top boundary. -/
def generalRectangleDualBottomCoreAmbientSeedBoundaryEvent
    (a : LatticeVertex) (w h : ℕ)
    (S : Set (generalRectangleDualBottomCoreVertex a w h)) :
    Set (Configuration (rectangleGraph (a.1 - 1, a.2) (w + 1) h)) :=
  {A | ∃ u ∈ S, ∃ z : RectangleVertex (a.1 - 1, a.2) (w + 1) h,
    z ∈ generalRectangleDualBottomCoreAmbientBoundary a w h ∧
    ActualConnected (rectangleGraph (a.1 - 1, a.2) (w + 1) h) A
      (generalRectangleDualBottomCoreVertexEquiv a w h u) z}

/-- In the true expanded dual graph, the target is the full actual three-side
boundary, not a wired identification or a replacement rectangle boundary. -/
def generalRectangleDualBottomCoreTrueDualSeedBoundaryEvent
    (a : LatticeVertex) (w h : ℕ)
    (S : Set (generalRectangleDualBottomCoreVertex a w h)) :
    Set (Configuration (rectangleDualGraph a w h)) :=
  {D | ∃ u ∈ S, ∃ z : RectangleDualVertex a w h,
    z ∈ generalRectangleDualBottomCollarInnerThreeSides a w h ∧
    ActualConnected (rectangleDualGraph a w h) D
      (generalRectangleDualBottomCoreInclusion a w h u) z}

private theorem generalRectangleDualBottomCore_ambientEvent_preimage
    (a : LatticeVertex) (w h : ℕ)
    (S : Set (generalRectangleDualBottomCoreVertex a w h)) :
    {A | generalRectangleDualBottomCoreConfigurationRestrictionAmbient a w h A ∈
      generalRectangleDualBottomCoreSeedBoundaryEvent a w h S} =
      generalRectangleDualBottomCoreAmbientSeedBoundaryEvent a w h S := by
  ext A
  constructor
  · rintro ⟨u, hu, v, hv, hconn⟩
    have hiff := generalRectangleDualBottomCoreAmbient_connected_to_boundary_iff a w h A
      (generalRectangleDualBottomCoreVertexEquiv a w h u)
    rcases hiff.mpr ⟨v, hv, by simpa using hconn⟩ with ⟨z, hz, hconn⟩
    exact ⟨u, hu, z, hz, hconn⟩
  · rintro ⟨u, hu, z, hz, hconn⟩
    have hiff := generalRectangleDualBottomCoreAmbient_connected_to_boundary_iff a w h A
      (generalRectangleDualBottomCoreVertexEquiv a w h u)
    rcases hiff.mp ⟨z, hz, hconn⟩ with ⟨v, hv, hconn⟩
    exact ⟨u, hu, v, hv, by simpa using hconn⟩

private theorem generalRectangleDualBottomCore_trueDualEvent_preimage
    (a : LatticeVertex) (w h : ℕ)
    (S : Set (generalRectangleDualBottomCoreVertex a w h)) :
    {D | generalRectangleDualBottomCoreConfigurationRestriction a w h D ∈
      generalRectangleDualBottomCoreSeedBoundaryEvent a w h S} =
      generalRectangleDualBottomCoreTrueDualSeedBoundaryEvent a w h S := by
  ext D
  constructor
  · rintro ⟨u, hu, v, hv, hconn⟩
    rcases (generalRectangleDualBottomCore_connected_to_fullThreeSides_iff a w h D u).mpr
        ⟨v, hv, hconn⟩ with ⟨z, hz, hconn⟩
    exact ⟨u, hu, z, hz, hconn⟩
  · rintro ⟨u, hu, z, hz, hconn⟩
    rcases (generalRectangleDualBottomCore_connected_to_fullThreeSides_iff a w h D u).mp
        ⟨z, hz, hconn⟩ with ⟨v, hv, hconn⟩
    exact ⟨u, hu, v, hv, hconn⟩

/-- The actual ordinary-rectangle and expanded-true-dual three-side
connectivity probabilities agree for every selected set of retained seeds. -/
theorem generalRectangleDualBottomCore_threeSideConnectivity_probability_eq
    (a : LatticeVertex) (w h : ℕ) (q : ClusterWeight)
    (S : Set (generalRectangleDualBottomCoreVertex a w h)) :
    (measure (rectangleGraph (a.1 - 1, a.2) (w + 1) h) q
      (BoundaryCondition.wired (generalRectangleDualBottomCoreAmbientBoundary a w h))
      (generalRectangleDualBottomCoreAmbientSeedBoundaryEvent a w h S)).toReal =
    (measure (rectangleDualGraph a w h) q
      (BoundaryCondition.wired (generalRectangleDualBottomCollarInnerThreeSides a w h))
      (generalRectangleDualBottomCoreTrueDualSeedBoundaryEvent a w h S)).toReal := by
  classical
  let C := generalRectangleDualBottomCoreGraph a w h
  let H := rectangleGraph (a.1 - 1, a.2) (w + 1) h
  let D := rectangleDualGraph a w h
  let ρH := embeddedConfigurationRestriction C H
    (generalRectangleDualBottomCoreVertexEquiv a w h).toEmbedding
    (by
      intro u v huv
      rcases (SimpleGraph.map_adj _ _ _ _).mp huv with ⟨u₀, v₀, hC, rfl, rfl⟩
      exact generalRectangleDualBottomCoreGraph_le_rectangle a w h hC)
  let ρD := embeddedConfigurationRestriction C D
    (generalRectangleDualBottomCoreInclusion a w h)
    (generalRectangleDualBottomCoreGraph_map_le a w h)
  let η := BoundaryCondition.wired
    {u : generalRectangleDualBottomCoreVertex a w h |
      generalRectangleDualBottomCoreInclusion a w h u ∈
        generalRectangleDualBottomCollarInnerThreeSides a w h}
  let E := generalRectangleDualBottomCoreSeedBoundaryEvent a w h S
  have hHlaw : (law H q (BoundaryCondition.wired
      (generalRectangleDualBottomCoreAmbientBoundary a w h))).map ρH = law C q η := by
    simpa [H, C, ρH, η, generalRectangleDualBottomCoreAmbientBoundary] using
      generalRectangleDualBottomCoreAmbient_law_restrict a w h q
  have hDlaw : (law D q (BoundaryCondition.wired
      (generalRectangleDualBottomCollarInnerThreeSides a w h))).map ρD = law C q η := by
    simpa [D, C, ρD, η] using generalRectangleDualBottomCoreGraph_law_map a w h q
  have hHset : {A | ρH A ∈ E} =
      generalRectangleDualBottomCoreAmbientSeedBoundaryEvent a w h S := by
    change {A | generalRectangleDualBottomCoreConfigurationRestrictionAmbient a w h A ∈ E} = _
    simpa [E] using generalRectangleDualBottomCore_ambientEvent_preimage a w h S
  have hDset : {A | ρD A ∈ E} =
      generalRectangleDualBottomCoreTrueDualSeedBoundaryEvent a w h S := by
    change {A | generalRectangleDualBottomCoreConfigurationRestriction a w h A ∈ E} = _
    simpa [E] using generalRectangleDualBottomCore_trueDualEvent_preimage a w h S
  have hHmeasure : measure H q (BoundaryCondition.wired
      (generalRectangleDualBottomCoreAmbientBoundary a w h))
      (generalRectangleDualBottomCoreAmbientSeedBoundaryEvent a w h S) =
      measure C q η E := by
    have hm := congrArg (fun p : PMF (Configuration C) => p.toMeasure E) hHlaw
    change ((law H q (BoundaryCondition.wired
      (generalRectangleDualBottomCoreAmbientBoundary a w h))).map ρH).toMeasure E =
      (law C q η).toMeasure E at hm
    rw [PMF.toMeasure_map_apply _ _ _ measurable_from_top
      (MeasurableSet.of_discrete (s := E))] at hm
    change measure H q (BoundaryCondition.wired
      (generalRectangleDualBottomCoreAmbientBoundary a w h)) {A | ρH A ∈ E} = _
      at hm
    rw [hHset] at hm
    simpa [measure] using hm
  have hDmeasure : measure D q (BoundaryCondition.wired
      (generalRectangleDualBottomCollarInnerThreeSides a w h))
      (generalRectangleDualBottomCoreTrueDualSeedBoundaryEvent a w h S) =
      measure C q η E := by
    have hm := congrArg (fun p : PMF (Configuration C) => p.toMeasure E) hDlaw
    change ((law D q (BoundaryCondition.wired
      (generalRectangleDualBottomCollarInnerThreeSides a w h))).map ρD).toMeasure E =
      (law C q η).toMeasure E at hm
    rw [PMF.toMeasure_map_apply _ _ _ measurable_from_top
      (MeasurableSet.of_discrete (s := E))] at hm
    change measure D q (BoundaryCondition.wired
      (generalRectangleDualBottomCollarInnerThreeSides a w h)) {A | ρD A ∈ E} = _
      at hm
    rw [hDset] at hm
    simpa [measure] using hm
  rw [hHmeasure, hDmeasure]

end
end PottsContinuity.FKC.FiniteFK
