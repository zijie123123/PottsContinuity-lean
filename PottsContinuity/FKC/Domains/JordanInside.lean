-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `Domains/JordanInside.lean`, with
-- module and namespace relocated (wrappers of the SLE development replaced by `PottsContinuity.FKC.SLEWrap`)
-- and declarations not used here removed.
module

public import PottsContinuity.FKC.Domains.JordanBridge
public import PottsContinuity.FKC.Domains.JordanChart
public import PottsContinuity.FKC.Domains.LatticeGraph
public import PottsContinuity.FKC.SLEWrap.Geometry.ComplexJordanRegions

/-!
# The actual bounded interior of a Jordan curve

The existing topological inside construction and Jordan separation theorem
supply the domain, its frontier, boundedness and finite closure lattice graph.
The two libraries' Jordan predicates are connected by a proved bridge, not
stored as independent assumptions on the domain.
-/

@[expose] public section

namespace PottsContinuity.FKC

open Set OAI.SLEExactGauge

theorem isOpen_complexInside {C : Set ℂ}
    (hC : Schoenflies.IsJordanCurve (complexPlaneCoordinates '' C)) :
    IsOpen (complexInside C) :=
  (Schoenflies.jordan_curve_theorem hC).isOpen_inside.preimage
    complexPlaneCoordinates.continuous

theorem isConnected_complexInside {C : Set ℂ}
    (hC : Schoenflies.IsJordanCurve (complexPlaneCoordinates '' C)) :
    IsConnected (complexInside C) := by
  have h := (Schoenflies.jordan_curve_theorem hC).isConnected_inside.image
    complexPlaneCoordinates.symm complexPlaneCoordinates.symm.continuous.continuousOn
  rw [complexPlaneCoordinates.image_symm] at h
  exact h

theorem isBounded_complexInside {C : Set ℂ}
    (hC : Schoenflies.IsJordanCurve (complexPlaneCoordinates '' C)) :
    Bornology.IsBounded (complexInside C) := by
  have hb := (Schoenflies.jordan_curve_theorem hC).isBounded_inside
  have h := (hb.isCompact_closure.image complexPlaneCoordinates.symm.continuous).isBounded
  have h' := h.subset (Set.image_mono
    (subset_closure : Schoenflies.inside (complexPlaneCoordinates '' C) ⊆
      closure (Schoenflies.inside (complexPlaneCoordinates '' C))))
  rw [complexPlaneCoordinates.image_symm] at h'
  exact h'

theorem frontier_complexInside {C : Set ℂ}
    (hC : Schoenflies.IsJordanCurve (complexPlaneCoordinates '' C)) :
    frontier (complexInside C) = C := by
  apply complexPlaneCoordinates.injective.image_injective
  rw [complexPlaneCoordinates.image_frontier, complexInside_image]
  exact (Schoenflies.jordan_curve_theorem hC).frontier_inside

/-- The bounded interior has exactly the source's Jordan-domain properties. -/
theorem isJordanDomain_complexInside {C : Set ℂ}
    (hC : Schoenflies.IsJordanCurve (complexPlaneCoordinates '' C)) :
    TauCeti.IsJordanDomain (complexInside C) where
  isOpen := isOpen_complexInside hC
  isConnected := isConnected_complexInside hC
  isBounded := isBounded_complexInside hC
  isJordanCurve_frontier := by
    rw [frontier_complexInside hC]
    exact (TauCeti.isJordanCurve_image_homeomorph_iff complexPlaneCoordinates).mp
      (isJordanCurve_of_schoenflies hC)

/-- Actual distinct boundary points give source-valid marked Jordan data;
no conformal-coordinate or probabilistic hypothesis is needed. -/
def markedComplexInside {C : Set ℂ}
    (hC : Schoenflies.IsJordanCurve (complexPlaneCoordinates '' C))
    (a b : ℂ) (ha : a ∈ C) (hb : b ∈ C) (hab : a ≠ b) : MarkedJordanDomain where
  domain := complexInside C
  isJordanDomain := isJordanDomain_complexInside hC
  a := a
  b := b
  a_mem_frontier := (frontier_complexInside hC).symm ▸ ha
  b_mem_frontier := (frontier_complexInside hC).symm ▸ hb
  a_ne_b := hab

end PottsContinuity.FKC
