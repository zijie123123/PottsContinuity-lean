module

public import PottsContinuity.Thm3.Prop4.CentralDualFaceIncidence
public import PottsContinuity.Thm3.Prop4.FiniteDualSampledWalkMap
public import PottsContinuity.Thm3.Prop4.TubeSafeExteriorArcs
public import PottsContinuity.Thm3.Prop4.SampledArmCorrelation

/-!
# Actual complementary-arc arms from a restored reference exit path

A nontrivial sampled exit supplies its actual incident original bond. A
length-zero exit at the central root has the explicit central incident bond.
Thus safe physical height selects the correct complementary arc in all cases.
-/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4

open PD.FK
noncomputable section
local instance safeReferenceArmPrimalEq (a : LatticeVertex) (w h : ℕ) :
    DecidableEq (rectangleGraph a w h).edgeSet := Classical.decEq _

/-- A true sampled dual exit from a central physical root lies on the
appropriate complementary arc, including a length-zero boundary-root path. -/
theorem central_safe_dual_exit_mem_complementary_arc {n : ℕ} (hn : 1 ≤ n)
    (r : ℝ) (hr : 1 ≤ r) (u v : LatticeVertex) (huBox : u ∈ box n) (hvBox : v ∈ box n)
    (huX : u.1 = -(n : ℤ)) (hvX : v.1 = n) (t b : ℝ) (ht : |t| ≤ 1)
    (hu : (u.2 : ℝ) = t*u.1+b) (hv : (v.2 : ℝ) = t*v.1+b)
    (c : ℤ) (hc : -(n : ℤ)-1 ≤ c ∧ c ≤ n) (reflected : Bool)
    {G : SimpleGraph (RectangleDualVertex (-(n : ℤ),-(n : ℤ)) (2*n) (2*n))}
    (hG : G ≤ rectangleDualGraph (-(n : ℤ),-(n : ℤ)) (2*n) (2*n))
    {x y : RectangleDualVertex (-(n : ℤ),-(n : ℤ)) (2*n) (2*n)}
    (hx : x.val = (0,c)) (p : G.Walk x y)
    (hy : y.val ∈ rectangleDualBoundary (-(n : ℤ),-(n : ℤ)) (2*n) (2*n))
    (hsafe : if reflected then tiltedHeight t y.val ≤ b-2*r else b+2*r ≤ tiltedHeight t y.val) :
    y.val ∈ if reflected then
      PlanarTopology.rectangleLowerDualArc (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) u v else
      PlanarTopology.rectangleUpperDualArc (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) u v := by
  have hInc : ∃ d : RectangleDualEdgeCarrier (-(n : ℤ),-(n : ℤ)) (2*n) (2*n),
      y.val = d.crossingBond.source ∨ y.val = d.crossingBond.target := by
    by_cases hxy : x = y
    · have hyx : y.val = (0,c) := hxy ▸ hx
      obtain ⟨d,hd⟩ := central_dual_face_incident hn c hc
      exact ⟨d,hd.imp (fun h => hyx.trans h) (fun h => hyx.trans h)⟩
    · exact rectangle_dual_walk_end_incident _ _ _ hG p hxy
  obtain ⟨d,hd⟩ := hInc
  cases reflected
  · exact tube_safe_upper_exterior_arc n r hr u v huBox hvBox huX hvX t b ht hu hv d y.val hd hy hsafe
  · exact tube_safe_lower_exterior_arc n r hr u v huBox hvBox huX hvX t b ht hu hv d y.val hd hy hsafe

/-- A safely exiting literal reference dual walk supplies the actual sampled
complementary-arc arm in the SAME restored original primal configuration. -/
theorem restored_safe_dual_walk_gives_sampled_arm {n : ℕ} (hn : 1 ≤ n)
    (r : ℝ) (hr : 1 ≤ r) (u v : LatticeVertex) (huBox : u ∈ box n) (hvBox : v ∈ box n)
    (huX : u.1 = -(n : ℤ)) (hvX : v.1 = n) (t b : ℝ) (ht : |t| ≤ 1)
    (hu : (u.2 : ℝ) = t*u.1+b) (hv : (v.2 : ℝ) = t*v.1+b)
    (c : ℤ) (hc : -(n : ℤ)-1 ≤ c ∧ c ≤ n) (reflected : Bool)
    (R : Configuration (rectangleGraph (-(n : ℤ),-(n : ℤ)) (2*n) (2*n)))
    (A : RemainingConfiguration (rectangleGraph (-(n : ℤ),-(n : ℤ)) (2*n) (2*n)) R)
    {x y : RectangleDualVertex (-(n : ℤ),-(n : ℤ)) (2*n) (2*n)}
    (hx : x.val = (0,c)) (p : (openGraph _ (frozenReferenceDualSample _ _ _ R A)).Walk x y)
    (hy : y.val ∈ rectangleDualBoundary (-(n : ℤ),-(n : ℤ)) (2*n) (2*n))
    (hsafe : if reflected then tiltedHeight t y.val ≤ b-2*r else b+2*r ≤ tiltedHeight t y.val) :
    A.val ∪ R ∈ sampledRectangleDualArmEvent (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) {(0,c)}
      (if reflected then PlanarTopology.rectangleLowerDualArc (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) u v else
        PlanarTopology.rectangleUpperDualArc (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) u v) (fun _ => True) := by
  have hG : openGraph _ (frozenReferenceDualSample _ _ _ R A) ≤
      rectangleDualGraph (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) := by
    intro a d had
    exact edgeRestriction_le _ _ (openGraph_le _ _ had)
  have hArc := central_safe_dual_exit_mem_complementary_arc hn r hr u v huBox hvBox huX hvX
    t b ht hu hv c hc reflected hG hx p hy hsafe
  obtain ⟨q,_⟩ := frozenReferenceDualSample_walk_sampled _ _ _ R A p
  refine ⟨x.val,?_,y.val,hArc,q.reverse,fun _ _ => True.intro⟩
  exact hx

end
end PottsContinuity.Thm3.Prop4
