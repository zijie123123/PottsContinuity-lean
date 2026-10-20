module

public import PottsContinuity.PlanarMixed.Thm4SideFactor.RightOuterRoutes
public import PottsContinuity.PlanarMixed.Thm4SideFactor.RightReducedEmbedding

@[expose] public section

namespace PottsContinuity.PlanarMixed.Thm4SideFactor
open PD.FK PD.FK.Medial Thm4Side DualityExt
noncomputable section

/-- The native rectangle's three wired sides are already joined in the exact host dual boundary. -/
theorem right_native_boundary_le_induced (m : ℕ)
    (X : Configuration (FKC.FiniteFK.slitBoxGraph (16*m))) :
    (nativeSideFullBoundary m).partition ≤
      (isolatedExtensionPullbackBoundary (rightNativeToHostDual m)
        (frozenBoundary
          (rectangleDualBoundaryCondition (-((16*m+1:ℕ):ℤ),-((16*m+1:ℕ):ℤ))
            (2*(16*m+1)) (2*(16*m+1))) (rightDualExterior m X))).partition := by
  intro u v huv
  rcases huv with huv | ⟨hu,hv⟩
  · subst v
    exact (isolatedExtensionPullbackBoundary (rightNativeToHostDual m)
      (frozenBoundary
        (rectangleDualBoundaryCondition (-((16*m+1:ℕ):ℤ),-((16*m+1:ℕ):ℤ))
          (2*(16*m+1)) (2*(16*m+1))) (rightDualExterior m X))).partition.refl u
  · obtain ⟨bu,hbu,hcu⟩ := right_native_outer_routes m X u hu
    obtain ⟨bv,hbv,hcv⟩ := right_native_outer_routes m X v hv
    change (componentSetoid (sideDualGraph m)
      (rectangleDualBoundaryCondition (-((16*m+1:ℕ):ℤ),-((16*m+1:ℕ):ℤ))
        (2*(16*m+1)) (2*(16*m+1))) (rightDualExterior m X)).r
          (rightNativeToHostDual m u) (rightNativeToHostDual m v)
    apply Setoid.trans' _ (actualConnected_component _ _ _ hcu)
    apply Setoid.trans' _ ?_ (Setoid.symm' _ (actualConnected_component _ _ _ hcv))
    apply boundary_component
    exact (rectangleDualBoundaryCondition_rel _ _ _ bu bv).mpr (Or.inr ⟨hbu,hbv⟩)

/-- Freezing any further native-dual exterior only strengthens the required wiring. -/
theorem right_native_further_boundary_le (m : ℕ)
    (X : Configuration (FKC.FiniteFK.slitBoxGraph (16*m)))
    (K : Configuration (rectangleSubgraphDualGraph
      (sideExactLawHostSubgraph_le m (slitRightDualRectangleReveal m X)))) :
    (nativeSideFullBoundary m).partition ≤
      (isolatedExtensionPullbackBoundary (rightNativeToHostDual m)
        (frozenBoundary
          (frozenBoundary
            (rectangleDualBoundaryCondition (-((16*m+1:ℕ):ℤ),-((16*m+1:ℕ):ℤ))
              (2*(16*m+1)) (2*(16*m+1))) (rightDualExterior m X)) K)).partition := by
  intro u v huv
  exact boundary_component _ _ K (right_native_boundary_le_induced m X huv)

end
end PottsContinuity.PlanarMixed.Thm4SideFactor
