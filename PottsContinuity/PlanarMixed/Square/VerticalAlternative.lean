module

public import PottsContinuity.PlanarMixed.Square.DualSwap
public import PottsContinuity.PlanarMixed.Square.RectangleDualCornerMarginal
public import PottsContinuity.PlanarMixed.Square.RectangleDualCornerConnectivity
public import PottsContinuity.PlanarMixed.Square.SubgraphIncreasingEventComparison
public import PottsContinuity.BD12.TwoBlockBoundaryMerge
public import PottsContinuity.PlanarMixed.Square.RectangleMixedCoordinateSwap
public import PottsContinuity.PlanarMixed.Square.RectangleMixedCrossingAlternative
public import PottsContinuity.PD.FK.IncreasingEvents
public import Mathlib.Tactic
public import PottsContinuity.PlanarMixed.Square.Extras
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# Vertical primal noncrossing and actual horizontal dual crossing on squares

The direction of the event changes while the bottom/top boundary convention
stays fixed. This is the additional direction needed for WIRED-ARC RSW.
-/

@[expose] public section

namespace PottsContinuity.PlanarMixed.Square
open PD.FK PD.FK.Medial PD.Duality BD12 MeasureTheory
open scoped PottsContinuity.PlanarMixed.Square
noncomputable section

/-- Actual crossing between the left/right face-base columns of the dual square.
No virtual boundary connections are used in the event. -/
def squareDualHorizontalCrossingEvent (z : ℤ) (N : ℕ) :
    Set (Configuration (rectangleDualGraph (z,z) N N)) :=
  {A | ∃ u v : RectangleDualVertex (z,z) N N,
    u.val.1 = z-1 ∧ v.val.1 = z+(N:ℤ) ∧
      ActualConnected (rectangleDualGraph (z,z) N N) A u v}

theorem squarePrimalConfigurationSwap_twice (z : ℤ) (N : ℕ)
    (A : Configuration (rectangleGraph (z,z) N N)) :
    configurationIso (squarePrimalGraphSwapIso z N)
      (configurationIso (squarePrimalGraphSwapIso z N) A) = A := by
  change (configurationIso (squarePrimalGraphSwapIso z N)).symm
    (configurationIso (squarePrimalGraphSwapIso z N) A) = A
  exact (configurationIso (squarePrimalGraphSwapIso z N)).symm_apply_apply A

/-- Failure of the actual vertical primal crossing produces an actual
horizontal complementary-dual crossing on the SAME dual configuration. -/
theorem squareVerticalNoncrossing_subset_dualHorizontal (z : ℤ) (N : ℕ) :
    (rectangleVerticalCrossingEvent (z,z) N N)ᶜ ⊆
      (rectanglePrimalDualConfigurationEquiv (z,z) N N) ⁻¹'
        squareDualHorizontalCrossingEvent z N := by
  intro A hnotV
  have hnotH : configurationIso (squarePrimalGraphSwapIso z N) A ∉
      rectangleHorizontalCrossingEvent (z,z) N N := by
    intro hH
    have hV := (rectangleHorizontalCrossingEvent_coordinateSwap_iff (z,z) N N
      (configurationIso (squarePrimalGraphSwapIso z N) A)).mp hH
    change configurationIso (squarePrimalGraphSwapIso z N)
      (configurationIso (squarePrimalGraphSwapIso z N) A) ∈
        rectangleVerticalCrossingEvent (z,z) N N at hV
    rw [squarePrimalConfigurationSwap_twice] at hV
    exact hnotV hV
  have hD := rectangleHorizontalNoncrossing_subset_dualBottomTopCrossing_preimage
    (z,z) N N hnotH
  change rectanglePrimalDualConfigurationEquiv (z,z) N N
    (configurationIso (squarePrimalGraphSwapIso z N) A) ∈
      rectangleDualBottomTopCrossingEvent (z,z) N N at hD
  rw [← squarePrimalDualConfiguration_swap_commute] at hD
  rcases hD with ⟨b, hb, t, ht, hconn⟩
  rcases Finset.mem_image.mp hb with ⟨i, hi, rfl⟩
  rcases Finset.mem_image.mp ht with ⟨j, hj, rfl⟩
  let u := (squareDualSwapVertexEquiv z N).symm (rectangleDualBottomPortVertex (z,z) N N i)
  let v := (squareDualSwapVertexEquiv z N).symm (rectangleDualTopPortVertex (z,z) N N j)
  have hu : u.val.1 = z-1 := by rfl
  have hv : v.val.1 = z+(N:ℤ) := by rfl
  have hconn' : ActualConnected (rectangleDualGraph (z,z) N N)
      (rectanglePrimalDualConfigurationEquiv (z,z) N N A) u v := by
    apply (actualConnected_configurationIso (squareDualGraphSwapIso z N)
      (rectanglePrimalDualConfigurationEquiv (z,z) N N A) u v).mp
    change ActualConnected (rectangleDualGraph (z,z) N N)
      (configurationIso (squareDualGraphSwapIso z N)
        (rectanglePrimalDualConfigurationEquiv (z,z) N N A))
      ((squareDualSwapVertexEquiv z N)
        ((squareDualSwapVertexEquiv z N).symm (rectangleDualBottomPortVertex (z,z) N N i)))
      ((squareDualSwapVertexEquiv z N)
        ((squareDualSwapVertexEquiv z N).symm (rectangleDualTopPortVertex (z,z) N N j)))
    simpa only [Equiv.apply_symm_apply] using hconn
  exact ⟨u, v, hu, hv, hconn'⟩

attribute [local instance] configurationMeasurableSpace

/-- Under separate bottom/top wiring, the two relevant actual crossing
probabilities have sum at least one. The second law wires left/right together. -/
theorem squareMixed_vertical_add_dualHorizontal_ge_one
    (q : Set.Ici (1 : ℝ)) (z : ℤ) (N : ℕ) (hN : 1 ≤ N) :
    1 ≤ (measure (rectangleGraph (z,z) N N) (criticalParameters q)
      (twoBlockBoundary (rectangleDoubleCollarInnerBottom (z,z) N N)
        (rectangleDoubleCollarInnerTop (z,z) N N)
        (rectangleDoubleCollarInnerBottom_disjoint_top (z,z) N N hN))
      (rectangleVerticalCrossingEvent (z,z) N N)).toReal +
      (measure (rectangleDualGraph (z,z) N N) (criticalParameters q)
        (BoundaryCondition.wired (rectangleDoubleCollarDualInnerVerticalSides (z,z) N N))
        (squareDualHorizontalCrossingEvent z N)).toReal := by
  let ξ := twoBlockBoundary (rectangleDoubleCollarInnerBottom (z,z) N N)
    (rectangleDoubleCollarInnerTop (z,z) N N)
    (rectangleDoubleCollarInnerBottom_disjoint_top (z,z) N N hN)
  have hsum := probReal_add_probReal_compl
    (μ := measure (rectangleGraph (z,z) N N) (criticalParameters q) ξ)
    (s := rectangleVerticalCrossingEvent (z,z) N N) MeasurableSpace.measurableSet_top
  have hmono := ENNReal.toReal_mono
    (measure_ne_top (measure (rectangleGraph (z,z) N N) (criticalParameters q) ξ) _)
    (measure_mono (μ := measure (rectangleGraph (z,z) N N) (criticalParameters q) ξ)
      (squareVerticalNoncrossing_subset_dualHorizontal z N))
  have htransfer := rectangleDoubleCollar_mixedLaw_measure_preimage q (z,z) N N hN
    (squareDualHorizontalCrossingEvent z N)
  change _ ≤ _ + _
  change (measure (rectangleGraph (z,z) N N) (criticalParameters q) ξ
    (rectangleVerticalCrossingEvent (z,z) N N)).toReal +
      (measure (rectangleGraph (z,z) N N) (criticalParameters q) ξ
        (rectangleVerticalCrossingEvent (z,z) N N)ᶜ).toReal = 1 at hsum
  change (measure (rectangleGraph (z,z) N N) (criticalParameters q) ξ
    (rectangleVerticalCrossingEvent (z,z) N N)ᶜ).toReal ≤
      (measure (rectangleGraph (z,z) N N) (criticalParameters q) ξ
        ((rectanglePrimalDualConfigurationEquiv (z,z) N N) ⁻¹'
          squareDualHorizontalCrossingEvent z N)).toReal at hmono
  rw [htransfer] at hmono
  dsimp only [ξ] at hsum hmono
  linarith only [hsum, hmono]

end
end PottsContinuity.PlanarMixed.Square
