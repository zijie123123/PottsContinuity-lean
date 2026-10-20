module

public import PottsContinuity.Thm3.Touch.FiniteSplitDomains
public import PottsContinuity.Thm3.RSW.FiniteBoundary
public import PottsContinuity.Thm3.Touch.FiniteStripPrimalEvents
public import PottsContinuity.Thm3.RSW.SelfDualSetup
public import PottsContinuity.Thm3.Prop4.TiltedCandidates
public import PottsContinuity.Thm3.Prop4.ClosedCutEnergy
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import PottsContinuity.Thm3.Touch.InfiniteTopEventCylinders
public import PottsContinuity.Thm3.Touch.FiniteStripSymmetry
public import PottsContinuity.Thm3.Prop4.TiltedBoundaryLimits
public import PottsContinuity.Thm3.Prop4.ArcIsolationEmbedding
public import PottsContinuity.Thm3.Prop4.TiltedClosedExtension
public import PottsContinuity.Thm3.Prop4.TouchHalfConsumer
public import PottsContinuity.PD.FK.Isomorphism

@[expose] public section

namespace PottsContinuity.Thm3.Touch

open Filter MeasureTheory Topology
open PottsContinuity.PD.FK
open PottsContinuity.RSW
open PottsContinuity.Thm3.Prop4

noncomputable section

attribute [local instance] configurationMeasurableSpace

local instance tiltedColumnSlopeSourceEdgeFintype (n L : ℕ) (t : ℝ) :
    Fintype (tiltedColumnGraph (2*n) L t).edgeSet := Fintype.ofFinite _
local instance tiltedColumnSlopeTargetEdgeFintype (n L : ℕ) (t : ℝ) :
    Fintype (tiltedColumnGraph (2*n) L (-t)).edgeSet := Fintype.ofFinite _
local instance tiltedColumnSlopeSourceConfigurationFintype (n L : ℕ) (t : ℝ) :
    Fintype (Configuration (tiltedColumnGraph (2*n) L t)) := Fintype.ofFinite _
local instance tiltedColumnSlopeTargetConfigurationFintype (n L : ℕ) (t : ℝ) :
    Fintype (Configuration (tiltedColumnGraph (2*n) L (-t))) := Fintype.ofFinite _

theorem tiltedHeight_columnSlopeReflection (t : ℝ) (z : ℤ × ℤ) :
    tiltedHeight (-t) (-z.1,z.2) = tiltedHeight t z := by
  dsimp [tiltedHeight]
  push_cast
  ring

private theorem tiltedTop_columnSlopeReflection (N : ℕ) (t : ℝ)
    (ht : t ∈ Set.Icc (-1 : ℝ) 1) (z : ℤ × ℤ) :
    tiltedTop N (-t) (-z.1,z.2) ↔ tiltedTop N t z := by
  have ht' : -t ∈ Set.Icc (-1 : ℝ) 1 := by
    rcases ht with ⟨htlo, hthi⟩
    exact ⟨by linarith, by linarith⟩
  rw [tiltedTop_iff_height N ht', tiltedTop_iff_height N ht]
  rw [tiltedHeight_columnSlopeReflection]

/-- The digital top is carried to the digital top under slope reflection. -/
theorem tiltedTop_columnSlopeReflection_iff (N : ℕ) (t : ℝ)
    (ht : t ∈ Set.Icc (-1 : ℝ) 1) (z : ℤ × ℤ) :
    tiltedTop N (-t) (-z.1,z.2) ↔ tiltedTop N t z :=
  tiltedTop_columnSlopeReflection N t ht z

end

end PottsContinuity.Thm3.Touch
