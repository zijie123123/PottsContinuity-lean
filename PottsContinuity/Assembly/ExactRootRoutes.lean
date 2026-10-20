module

public import PottsContinuity.Thm3.Easy.P5FrameCycleExtract
public import PottsContinuity.PD.Duality.RayIndexSeparation
public import PottsContinuity.PlanarTopology.InterlacedPaths
public import PottsContinuity.FKC.Domains.LatticePolygonOfCycle
public import PottsContinuity.FKC.Domains.PolygonDomain
public import PottsContinuity.Thm3.RSW.AnnulusCircuit
public import PottsContinuity.Thm3.RSW.PolygonRayAnyLength
public import PottsContinuity.Thm3.Easy.P5FrameCircuitOfLocation
public import PottsContinuity.DualityExt.PositivePolygonRayIndex
public import PottsContinuity.Assembly.P5aEmbeddedInput
public import PottsContinuity.Thm3.Easy.P5ToP5aConditional
public import PottsContinuity.Assembly.AnnulusTransfer

@[expose] public section

namespace PottsContinuity.Assembly

open MeasureTheory
open PottsContinuity
open PottsContinuity.PD.FK

/-- The P4-to-P5 geometry inputs `P4toP5GeometryInputs` give the exact P4-to-P5 link. -/
theorem hP4toP5_of_geometryProvider
    (hP4P5geom : p4toP5GeometryProvider) :
    ∀ (q : Set.Ici (1 : ℝ)) (p : Set.Icc (0 : ℝ) 1)
      (μ₀ : Measure (squareLattice.edgeSet → Bool)),
      (p : ℝ) = Real.sqrt (q : ℝ) / (1 + Real.sqrt (q : ℝ)) →
      IsRCInfiniteVolumeLimit p
        ⟨(q : ℝ), Set.mem_Ioi.mpr (lt_of_lt_of_le one_pos q.property)⟩ 0 μ₀ →
      assertionP4 μ₀ →
      assertionP5 p
        ⟨(q : ℝ), Set.mem_Ioi.mpr (lt_of_lt_of_le one_pos q.property)⟩ := by
  intro q p μ₀ hp hμ₀ hP4
  exact p4_implies_p5_of_geometryInputs q p μ₀ hp hμ₀ hP4
    (hP4P5geom q p μ₀ hp hμ₀)

end PottsContinuity.Assembly
