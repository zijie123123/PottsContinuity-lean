module

public import PottsContinuity.Thm3.Prop4.SampledRectangleDualArms
public import PottsContinuity.Thm3.Prop4.ClusterFactorization

/-!
# Complementary-boundary-arc cut separation and the free product bound

Every arm step crosses a sampled original bond. Boundary hits may occur on
any of the literal lower or upper complementary arcs, with the two primal
marks kept at their own heights. No bottom/top replacement is made.
-/

@[expose] public section

open MeasureTheory

namespace PottsContinuity.Thm3.Prop4

open PD.FK
noncomputable section

/-- The literal sampled cut and actual complementary-arc arms separate the
prescribed original primal endpoints in that same configuration. -/
theorem sampled_cut_dual_arms_disconnect (a : LatticeVertex) (w h : ℕ)
    (u v : RectangleVertex a w h) (hu : u.val.1 = a.1) (hv : v.val.1 = a.1+(w : ℤ))
    (k lo hi : ℤ) (hlohi : lo ≤ hi)
    (A : Configuration (rectangleGraph a w h))
    (hclosed : ∀ y ∈ Finset.Icc lo hi,
      PlanarTopology.rectangleSampledBondClosed a w h A ⟨(k,y),.horizontal⟩)
    (P Q : LatticeVertex → Prop)
    (harms : A ∈ sampledRectangleDualArmsEvent a w h {(k,lo-1)} {(k,hi)}
      (PlanarTopology.rectangleLowerDualArc a w h u.val v.val)
      (PlanarTopology.rectangleUpperDualArc a w h u.val v.val) P Q) :
    ¬ ActualConnected (rectangleGraph a w h) A u v := by
  obtain ⟨f,hf,g,hg,s,hs,t,ht,minus,plus,hm,hp⟩ := harms
  have hf' : f = (k,lo-1) := Set.mem_singleton_iff.mp hf
  have hg' : g = (k,hi) := Set.mem_singleton_iff.mp hg
  subst f
  subst g
  exact PlanarTopology.rectangle_disconnected_of_sampled_closed_cut_and_dual_arms
    a w h A u v hu hv k lo hi hlohi hclosed s t hs ht minus plus

/-- In the actual finite free law, the full sampled cut screen and endpoint
target arms have the upper product, including all side-boundary exits. -/
theorem sampled_cut_screen_target_probability_le_product (θ : Parameters)
    (a : LatticeVertex) (w h : ℕ) (u v : RectangleVertex a w h)
    (hu : u.val.1 = a.1) (hv : v.val.1 = a.1+(w : ℤ))
    (k lo hi : ℤ) (hlohi : lo ≤ hi) (P Q : LatticeVertex → Prop)
    (S T : Set (RectangleVertex a w h)) :
    (measure (rectangleGraph a w h) θ (BoundaryCondition.free ∅)
      ({A | (∀ y ∈ Finset.Icc lo hi,
          PlanarTopology.rectangleSampledBondClosed a w h A ⟨(k,y),.horizontal⟩) ∧
        A ∈ sampledRectangleDualArmsEvent a w h {(k,lo-1)} {(k,hi)}
          (PlanarTopology.rectangleLowerDualArc a w h u.val v.val)
          (PlanarTopology.rectangleUpperDualArc a w h u.val v.val) P Q} ∩
        targetConnectionEvent u S ∩ targetConnectionEvent v T)).toReal ≤
      (measure (rectangleGraph a w h) θ (BoundaryCondition.free ∅) (targetConnectionEvent u S)).toReal *
      (measure (rectangleGraph a w h) θ (BoundaryCondition.free ∅) (targetConnectionEvent v T)).toReal := by
  apply free_target_product_of_cluster_separation
  intro A hA
  exact sampled_cut_dual_arms_disconnect a w h u v hu hv k lo hi hlohi A hA.1 P Q hA.2

end
end PottsContinuity.Thm3.Prop4
