/- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
accessible (see `related_formalizations` in formalization.yaml): file
`FiniteFK/RectangleMixedDuality.lean`.
Adaptation: namespace/import relocation; reuse existing PD/BD12 carriers.
Explicit self-dual parameter for every real q>=1 via the scoped coercion.
No upper bound q<4 is used in this finite proof. -/
module

public import PottsContinuity.BD12.SelfDualRectangle
public import PottsContinuity.PlanarMixed.Square.RectangleDoubleCollarLaw
public import PottsContinuity.PlanarMixed.Square.RectangleDoubleCollarDualLaw
public import PottsContinuity.PD.Duality.FiniteDuality
public import PottsContinuity.PlanarMixed.Square.PMFConditioningEquiv
public import PottsContinuity.PlanarMixed.Square.Extras
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Probability.ProbabilityMassFunction.Constructions

@[expose] public section

namespace PottsContinuity.PlanarMixed.Square
open PD.FK PD.FK.Medial PD.Duality BD12
open scoped PottsContinuity.PlanarMixed.Square
open PD.FK PD.FK.Medial
noncomputable section

local instance rmd_pout (a : LatticeVertex) (w h : ℕ) :
    DecidableEq (rectangleDoubleCollarOuterGraph a w h).edgeSet := Classical.decEq _
local instance rmd_dout (a : LatticeVertex) (w h : ℕ) :
    DecidableEq (rectangleDoubleCollarDualOuterGraph a w h).edgeSet := Classical.decEq _
local instance rmd_pin (a : LatticeVertex) (w h : ℕ) :
    DecidableEq (rectangleDoubleCollarInnerGraph a w h).edgeSet := Classical.decEq _
local instance rmd_din (a : LatticeVertex) (w h : ℕ) :
    DecidableEq (rectangleDoubleCollarDualInnerGraph a w h).edgeSet := Classical.decEq _

/-- The genuine finite mixed-boundary primal law, mapped by complementary-edge
transport, is the actual inner dual law with the two exposed vertical sides
wired together. -/
theorem rectangleDoubleCollar_mixedDuality_law_map
    (a : LatticeVertex) (w h : ℕ) (hh : 1 ≤ h) (q : Set.Ici (1 : ℝ)) :
    (law (rectangleGraph a w h) q
      (twoBlockBoundary (rectangleDoubleCollarInnerBottom a w h)
        (rectangleDoubleCollarInnerTop a w h)
        (rectangleDoubleCollarInnerBottom_disjoint_top a w h hh))).map
      (rectanglePrimalDualConfigurationEquiv a w h) =
      law (rectangleDualGraph a w h) q
        (BoundaryCondition.wired (rectangleDoubleCollarDualInnerVerticalSides a w h)) := by
  classical
  let Pout := rectangleDoubleCollarOuterGraph a w h
  let Pin := rectangleDoubleCollarInnerGraph a w h
  let Dout := rectangleDoubleCollarDualOuterGraph a w h
  let Din := rectangleDoubleCollarDualInnerGraph a w h
  let ep := rectangleDoubleCollarEmbedding a w h
  let ed := rectangleDoubleCollarDual_vertexEmbedding a w h
  let eout := rectanglePrimalDualConfigurationEquiv (a.1, a.2 - 1) w (h + 2)
  let ein := rectanglePrimalDualConfigurationEquiv a w h
  let erp := embeddedConfigurationRestriction Pin Pout ep
    (rectangleDoubleCollar_map_le a w h)
  let erd := embeddedConfigurationRestriction Din Dout ed
    (rectangleDoubleCollarDual_map_le a w h)
  let Rp := rectangleDoubleCollarRemoved a w h
  let Kp := rectangleDoubleCollarState a w h
  let Rd := rectangleDoubleCollarRemovedDualEdges a w h
  let Kd := rectangleDoubleCollarDualClosedState a w h
  let ξp := BoundaryCondition.free (∅ : Set (rectangleDoubleCollarOuterVertex a w h))
  let ξd := rectangleDualBoundaryCondition (a.1, a.2 - 1) w (h + 2)
  let outerPrimalLaw := law Pout q ξp
  have hdual := BD12.rectangleLaw_selfDual q
    (a.1, a.2 - 1) w (h + 2)
  have himage : eout '' frozenStateEvent Rp Kp = frozenStateEvent Rd Kd := by
    apply Set.ext
    intro B
    constructor
    · rintro ⟨A, hA, rfl⟩
      exact (rectangleDoubleCollar_collar_event a w h A).mp hA
    · intro hB
      refine ⟨eout.symm B, ?_, eout.apply_symm_apply B⟩
      exact (rectangleDoubleCollar_collar_event a w h (eout.symm B)).mpr
        (by simpa [eout, Rd, Kd] using hB)
  have hfiltered :
      (outerPrimalLaw.filter (frozenStateEvent Rp Kp)
        (frozenStateEvent_support q ξp Rp Kp)).map eout =
      (law Dout q ξd).filter (frozenStateEvent Rd Kd)
        (frozenStateEvent_support q ξd Rd Kd) := by
    have hfm := pmf_filter_map_equiv outerPrimalLaw eout
      (frozenStateEvent Rp Kp) (frozenStateEvent_support q ξp Rp Kp)
    have hsupportImage := pmf_map_equiv_filter_witness outerPrimalLaw eout
      (frozenStateEvent Rp Kp) (frozenStateEvent_support q ξp Rp Kp)
    have hsupportDual : ∃ B ∈ frozenStateEvent Rd Kd,
        B ∈ (outerPrimalLaw.map eout).support := by
      simpa [himage] using hsupportImage
    have himageFilter :
        (outerPrimalLaw.map eout).filter (eout '' frozenStateEvent Rp Kp) hsupportImage =
        (outerPrimalLaw.map eout).filter (frozenStateEvent Rd Kd) hsupportDual := by
      ext B
      rw [PMF.filter_apply, PMF.filter_apply]
      have hnum : (eout '' frozenStateEvent Rp Kp).indicator
          (outerPrimalLaw.map eout) B =
          (frozenStateEvent Rd Kd).indicator (outerPrimalLaw.map eout) B := by rw [himage]
      rw [hnum]
      have hnumAll (B : Configuration Dout) :
          (eout '' frozenStateEvent Rp Kp).indicator (outerPrimalLaw.map eout) B =
            (frozenStateEvent Rd Kd).indicator (outerPrimalLaw.map eout) B := by rw [himage]
      rw [show (∑' B : Configuration Dout,
          (eout '' frozenStateEvent Rp Kp).indicator (outerPrimalLaw.map eout) B) =
          ∑' B : Configuration Dout,
            (frozenStateEvent Rd Kd).indicator (outerPrimalLaw.map eout) B from tsum_congr hnumAll]
    have hdual' : outerPrimalLaw.map eout = law Dout q ξd := by
      simpa [outerPrimalLaw, ξp, ξd, Pout, Dout, eout] using hdual
    have hdualFilter :
        (outerPrimalLaw.map eout).filter (frozenStateEvent Rd Kd) hsupportDual =
        (law Dout q ξd).filter (frozenStateEvent Rd Kd)
          (frozenStateEvent_support q ξd Rd Kd) := by
      ext B
      rw [PMF.filter_apply, PMF.filter_apply]
      have hv (B : Configuration Dout) := congrArg (fun μ : PMF (Configuration Dout) => μ B) hdual'
      have hnum (B : Configuration Dout) :
          (frozenStateEvent Rd Kd).indicator (outerPrimalLaw.map eout) B =
          (frozenStateEvent Rd Kd).indicator (law Dout q ξd) B := by
        rw [Set.indicator_apply, Set.indicator_apply, hv B]
      rw [hnum B]
      rw [show (∑' B : Configuration Dout,
          (frozenStateEvent Rd Kd).indicator (outerPrimalLaw.map eout) B) =
          ∑' B : Configuration Dout,
            (frozenStateEvent Rd Kd).indicator (law Dout q ξd) B from tsum_congr hnum]
    exact hfm.trans (himageFilter.trans hdualFilter)
  have hprimalConditional := rectangleDoubleCollar_conditional_law_map a w h hh q
  have hdualConditional := rectangleDoubleCollar_dualConditional_map a w h q
  have hfun : erd ∘ eout = ein ∘ erp := by
    funext A
    exact rectangleDoubleCollar_primalDual_restriction_square a w h A
  calc
    (law Pin q
      (twoBlockBoundary (rectangleDoubleCollarInnerBottom a w h)
        (rectangleDoubleCollarInnerTop a w h)
        (rectangleDoubleCollarInnerBottom_disjoint_top a w h hh))).map ein
        = ((outerPrimalLaw.filter (frozenStateEvent Rp Kp)
            (frozenStateEvent_support q ξp Rp Kp)).map erp).map ein := by
          rw [hprimalConditional]
    _ = ((outerPrimalLaw.filter (frozenStateEvent Rp Kp)
            (frozenStateEvent_support q ξp Rp Kp)).map eout).map erd := by
          rw [PMF.map_comp, PMF.map_comp, ← hfun]
    _ = ((law Dout q ξd).filter (frozenStateEvent Rd Kd)
            (frozenStateEvent_support q ξd Rd Kd)).map erd := by rw [hfiltered]
    _ = law Din q (BoundaryCondition.wired
          (rectangleDoubleCollarDualInnerVerticalSides a w h)) := by
          simpa [erd, Din, Dout] using hdualConditional

end
end PottsContinuity.PlanarMixed.Square
