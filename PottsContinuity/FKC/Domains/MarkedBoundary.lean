-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `Domains/MarkedBoundary.lean`, with
-- module and namespace relocated (wrappers of the SLE development replaced by `PottsContinuity.FKC.SLEWrap`)
-- and declarations not used here removed.
module

public import PottsContinuity.FKC.Domains.JordanChart
public import PottsContinuity.FKC.Domains.JordanOrientation

/-!
# A counterclockwise parametrization of a marked Jordan boundary

This is the boundary datum of a marked Jordan domain: a continuous simple
closed path based at the first mark, passing through the second mark at one-half,
with image exactly the domain frontier and positive geometric winding throughout
its actual interior. All such parametrizations are allowed; none is selected
canonically. Mesh approximations and their uniform convergence are recorded
separately, in `MarkedApproximationSequence` (`FKC.Domains.MarkedApproximation`).
-/

@[expose] public section

namespace PottsContinuity.FKC

open Set OAI.SLEExactGauge
open scoped unitInterval

/-- The actual midpoint of the unit parameter interval. -/
noncomputable def midpointUnitInterval : I := ⟨1 / 2, by norm_num, by norm_num⟩

@[simp] theorem midpointUnitInterval_coe : (midpointUnitInterval : ℝ) = 1 / 2 := rfl

/-- Every parametrization of the marked boundary satisfying the source's
simplicity, marking, and actual geometric counterclockwise conditions. -/
structure MarkedBoundaryParametrization (D : MarkedJordanDomain) where
  path : Path D.a D.a
  simple : InjOn path (Ico (0 : I) 1)
  midpoint_eq : path midpointUnitInterval = D.b
  range_eq_frontier : range path = frontier D.domain
  counterclockwise : ∀ z (hz : z ∈ complexInside (range path)),
    windingNumber path z (complexInside_subset_complement _ hz) = 1

/-- The actual inside of any simple parametrization of this boundary is the
original bounded Jordan domain, not a separately supplied interior. -/
theorem inside_eq_domain_of_boundary_path (D : MarkedJordanDomain) (γ : Path D.a D.a)
    (hγ : InjOn γ (Ico (0 : I) 1)) (hrange : range γ = frontier D.domain) :
    complexInside (range γ) = D.domain :=
  complexInside_eq_open (isJordanCurve_coordinates_range γ hγ)
    D.isJordanDomain.isOpen D.isJordanDomain.isConnected.isPreconnected
    D.isJordanDomain.nonempty D.isJordanDomain.isBounded hrange.symm

namespace MarkedBoundaryParametrization

variable {D : MarkedJordanDomain}

/-- The bounded interior determined by the path is exactly the specified domain. -/
theorem inside_eq_domain (β : MarkedBoundaryParametrization D) :
    complexInside (range β.path) = D.domain :=
  inside_eq_domain_of_boundary_path D β.path β.simple β.range_eq_frontier

/-- Every point of the domain is outside the boundary path's image. -/
theorem domain_subset_complement_range (β : MarkedBoundaryParametrization D) :
    D.domain ⊆ (range β.path)ᶜ := by
  rw [← β.inside_eq_domain]
  exact complexInside_subset_complement _

/-- The chosen positive orientation has winding one at each actual domain point. -/
theorem windingNumber_domain_eq_one (β : MarkedBoundaryParametrization D)
    {z : ℂ} (hz : z ∈ D.domain) :
    windingNumber β.path z (β.domain_subset_complement_range hz) = 1 := by
  have hzinside : z ∈ complexInside (range β.path) := by
    rwa [β.inside_eq_domain]
  exact β.counterclockwise z hzinside

end MarkedBoundaryParametrization

/-- Starting from any simple correctly marked boundary path, one of its two
orientations is a counterclockwise marked boundary parametrization. The actual
path, all its points, and both marks are retained, with only reversal allowed. -/
theorem exists_markedBoundaryParametrization_of_path (D : MarkedJordanDomain)
    (γ : Path D.a D.a) (hγ : InjOn γ (Ico (0 : I) 1))
    (hmid : γ midpointUnitInterval = D.b) (hrange : range γ = frontier D.domain) :
    ∃ β : MarkedBoundaryParametrization D, β.path = γ ∨ β.path = γ.symm := by
  obtain ⟨η, horientation, hη, hrangeη, hmidη, hpositive⟩ :=
    exists_positive_jordan_orientation γ hγ
  refine ⟨{
    path := η
    simple := hη
    midpoint_eq := (hmidη midpointUnitInterval midpointUnitInterval_coe).trans hmid
    range_eq_frontier := hrangeη.trans hrange
    counterclockwise := hpositive }, horientation⟩

end PottsContinuity.FKC
