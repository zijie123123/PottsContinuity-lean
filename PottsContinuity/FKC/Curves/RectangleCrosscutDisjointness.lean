-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `Curves/RectangleCrosscutDisjointness.lean`, with
-- module and namespace relocated (wrappers of the SLE development replaced by `PottsContinuity.FKC.SLEWrap`)
-- and declarations not used here removed.
module

public import PottsContinuity.FKC.Curves.RectangleLowerClosureAvoidance
public import PottsContinuity.FKC.FiniteFK.RectangleOpenWalkInterpolation
public import PottsContinuity.FKC.Curves.UpperCrosscutWinding
public import PottsContinuity.FKC.Curves.DualWalkAvoidance

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

open PottsContinuity.FKC PottsContinuity.FKC.Curves PottsContinuity.FKC.Medial Set
open scoped unitInterval

noncomputable section

/-- Convert a rectangle primal-edge carrier to the configuration on its actual graph. -/
def rectanglePrimalCarrierConfiguration (n : ℕ)
    (A : Finset (rectanglePrimalEdgeCarrier (-((n : ℤ)), 0) (2*n) n)) :
    Configuration (rectangleGraph (-((n : ℤ)), 0) (2*n) n) := by
  simpa [rectanglePrimalEdgeCarrier] using A

private theorem unitEmbed_bottom_sub_I (x : ℤ) :
    latticeEmbed rectangleInterpolationUnitMesh (x, 0) - Complex.I =
      latticeEmbed rectangleInterpolationUnitMesh (x, -1) := by
  apply Complex.ext <;> simp [latticeEmbed_re, latticeEmbed_im, rectangleInterpolationUnitMesh]

/-- The actual finite complementary-dual walk avoids the full closed polygon
obtained by closing an open-primal walk along the lower boundary of the
rectangle. The top and all three literal closure segments are treated in the
same open-outside extension. -/
theorem rectangleLowerClosureDualPath_disjoint_upperCrosscutClosure
    (n : ℕ)
    (A : Finset (rectanglePrimalEdgeCarrier (-((n : ℤ)), 0) (2*n) n))
    {u v : RectangleVertex (-(n : ℤ), 0) (2*n) n}
    (p : (openGraph (rectangleGraph (-(n : ℤ), 0) (2*n) n)
      (rectanglePrimalCarrierConfiguration n A)).Walk u v)
    (hu : u.val.2 = 0) (hv : v.val.2 = 0)
    {s t : RectangleDualVertex (-(n : ℤ), 0) (2*n) n}
    (q : (openGraph (rectangleDualGraph (-(n : ℤ), 0) (2*n) n)
      (rectangleDualConfiguration (-(n : ℤ), 0) (2*n) n A)).Walk s t) :
    Disjoint (Set.range (rectangleLowerClosureDualPath n A q))
      (Set.range (upperCrosscutClosure
        (latticeWalkPath rectangleInterpolationUnitMesh
          (rectangleOpenOutsideWalkToLatticeWalk (rectanglePrimalCarrierConfiguration n A) p)))) := by
  let top := latticeWalkPath rectangleInterpolationUnitMesh
    (rectangleOpenOutsideWalkToLatticeWalk (rectanglePrimalCarrierConfiguration n A) p)
  let ext := rectangleLowerClosureExtension n A
  let dualWalk := q.map (rectangleOpenOutsideDualGraphHom (-(n : ℤ), 0) (2*n) n
    (rectanglePrimalCarrierConfiguration n A))
  have hExt : ext = rectangleOpenOutsideExtension (-(n : ℤ), 0) (2*n) n
      (rectanglePrimalCarrierConfiguration n A) := rfl
  have hMesh : rectangleLowerClosureMesh = rectangleInterpolationUnitMesh := by
    apply Subtype.ext
    rfl
  cases hMesh
  have hTop := closedDualWalkPath_range_disjoint_openPrimalWalk
    rectangleLowerClosureMesh ext dualWalk
    (p.map (rectangleOpenOutsidePrimalGraphHom (-(n : ℤ), 0) (2*n) n
      (rectanglePrimalCarrierConfiguration n A)))
  have hDualPath' : rectangleLowerClosureDualPath n A q =
      closedDualWalkPath rectangleLowerClosureMesh ext dualWalk := rfl
  have hTopWalk : latticeWalkPath rectangleLowerClosureMesh
      (openPrimalWalkToLatticeWalk
        (p.map (rectangleOpenOutsidePrimalGraphHom (-(n : ℤ), 0) (2*n) n
          (rectanglePrimalCarrierConfiguration n A)))) = top := by
    rfl
  have hTopRange : Set.range top = Set.range
      (latticeWalkPath rectangleLowerClosureMesh
        (openPrimalWalkToLatticeWalk
          (p.map (rectangleOpenOutsidePrimalGraphHom (-(n : ℤ), 0) (2*n) n
            (rectanglePrimalCarrierConfiguration n A))))) := by
    exact congrArg (fun γ : Path (latticeEmbed rectangleLowerClosureMesh u.val)
      (latticeEmbed rectangleLowerClosureMesh v.val) => Set.range γ) hTopWalk.symm
  have hTop' : Disjoint (Set.range (rectangleLowerClosureDualPath n A q))
      (Set.range top) := by
    rw [hDualPath', hTopRange]
    exact hTop
  have hSource := rectangleOpenOutsideWalkPath_source
    (-(n : ℤ), 0) (2*n) n (rectanglePrimalCarrierConfiguration n A) p
  have hTarget := rectangleOpenOutsideWalkPath_target
    (-(n : ℤ), 0) (2*n) n (rectanglePrimalCarrierConfiguration n A) p
  have hSource' : top 0 = latticeEmbed rectangleInterpolationUnitMesh u.val := by
    simp [top]
  have hTarget' : top 1 = latticeEmbed rectangleInterpolationUnitMesh v.val := by
    simp [top]
  have hLeft := rectangleLowerClosureDualPath_disjoint_lowerVertical n A q u.val.1
  have hRight := rectangleLowerClosureDualPath_disjoint_lowerVertical n A q v.val.1
  have hBottom := rectangleLowerClosureDualPath_disjoint_bottomSegment n A q
    u.val.1 v.val.1
  rw [Set.disjoint_left] at hTop' hLeft hRight hBottom ⊢
  intro z hzD hzClosure
  have hzClosure' : z ∈ Set.range (upperCrosscutClosure top) := by
    simpa [top] using hzClosure
  have huPair : u.val = (u.val.1, 0) := by ext <;> simp [hu]
  have hvPair : v.val = (v.val.1, 0) := by ext <;> simp [hv]
  unfold upperCrosscutClosure balancedFourPath at hzClosure'
  rw [Path.trans_range, Path.trans_range, Path.trans_range] at hzClosure'
  simp only [Set.mem_union] at hzClosure'
  rcases hzClosure' with h | h
  · rcases h with hztop | hzright
    · exact hTop' hzD hztop
    · have hseg : z ∈ segment ℝ
          (latticeEmbed rectangleInterpolationUnitMesh v.val)
          (latticeEmbed rectangleInterpolationUnitMesh v.val - Complex.I) := by
        simpa [upperCrosscutRight, Path.range_segment] using hzright
      have hvs : latticeEmbed rectangleInterpolationUnitMesh v.val - Complex.I =
          latticeEmbed rectangleLowerClosureMesh (v.val.1, -1) := by
        rw [hvPair]
        exact unitEmbed_bottom_sub_I v.val.1
      have hv0 : latticeEmbed rectangleInterpolationUnitMesh v.val =
          latticeEmbed rectangleLowerClosureMesh (v.val.1, 0) := by
        rw [hvPair]
        rfl
      rw [hvs, hv0] at hseg
      rw [segment_symm ℝ] at hseg
      exact hRight hzD hseg
  · rcases h with hzbottom | hzleft
    · have hseg : z ∈ segment ℝ
          (latticeEmbed rectangleInterpolationUnitMesh v.val - Complex.I)
          (latticeEmbed rectangleInterpolationUnitMesh u.val - Complex.I) := by
        simpa [upperCrosscutBottom, Path.range_segment] using hzbottom
      have hvs : latticeEmbed rectangleInterpolationUnitMesh v.val - Complex.I =
          latticeEmbed rectangleLowerClosureMesh (v.val.1, -1) := by
        rw [hvPair]
        exact unitEmbed_bottom_sub_I v.val.1
      have hus : latticeEmbed rectangleInterpolationUnitMesh u.val - Complex.I =
          latticeEmbed rectangleLowerClosureMesh (u.val.1, -1) := by
        rw [huPair]
        exact unitEmbed_bottom_sub_I u.val.1
      rw [hvs, hus] at hseg
      have hseg' : z ∈ segment ℝ
          (latticeEmbed rectangleLowerClosureMesh (u.val.1, -1))
          (latticeEmbed rectangleLowerClosureMesh (v.val.1, -1)) := by
        rw [segment_symm ℝ]
        exact hseg
      exact hBottom hzD hseg'
    · have hseg : z ∈ segment ℝ
          (latticeEmbed rectangleInterpolationUnitMesh u.val - Complex.I)
          (latticeEmbed rectangleInterpolationUnitMesh u.val) := by
        simpa [upperCrosscutLeft, Path.range_segment] using hzleft
      have hus : latticeEmbed rectangleInterpolationUnitMesh u.val - Complex.I =
          latticeEmbed rectangleLowerClosureMesh (u.val.1, -1) := by
        rw [huPair]
        exact unitEmbed_bottom_sub_I u.val.1
      have hu0 : latticeEmbed rectangleInterpolationUnitMesh u.val =
          latticeEmbed rectangleLowerClosureMesh (u.val.1, 0) := by
        rw [huPair]
        rfl
      rw [hus, hu0] at hseg
      exact hLeft hzD hseg

end
end PottsContinuity.FKC.FiniteFK
