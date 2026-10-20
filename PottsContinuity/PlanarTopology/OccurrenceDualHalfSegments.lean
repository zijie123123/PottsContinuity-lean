module

public import PottsContinuity.PlanarTopology.PolygonFourArcExistence
public import PottsContinuity.PlanarTopology.DobrushinDualProjection
public import PottsContinuity.PlanarTopology.DobrushinExteriorExtraction
public import PottsContinuity.FKC.Medial.DomainBondSides
public import Mathlib.Analysis.Convex.PathConnected
public import PottsContinuity.FKC.Medial.PrimalDualSegments

@[expose] public section

namespace PottsContinuity.PlanarTopology
open FKC FKC.Medial FKC.FiniteFK

/-- The original bond midpoint is the midpoint of its two adjacent face centers. -/
theorem bond_midpoint_eq_dual_midpoint (δ : PositiveMesh) (b : LatticeBond) :
    b.midpoint δ = midpoint ℝ (dualFaceCenter δ (dualBondOfPrimal b).source)
      (dualFaceCenter δ (dualBondOfPrimal b).target) := by
  rw [midpoint_eq_smul_add]
  rcases b with ⟨⟨x,y⟩, ax⟩
  cases ax <;> apply Complex.ext <;>
    simp [LatticeBond.midpoint, dualBondOfPrimal, LatticeBond.source,
      LatticeBond.target, dualFaceCenter, latticeEmbed, Complex.add_re,
      Complex.add_im, Complex.mul_re, Complex.mul_im] <;> ring

end PottsContinuity.PlanarTopology
