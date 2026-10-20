module

public import PottsContinuity.Thm3.Prop4.RectangleCutSurvival
public import PottsContinuity.Thm3.Prop4.ClosingImage

/-!
# Closing cost and the full complementary-arc cut product

The original connection may be destroyed by closing the cut. Both endpoint
arms survive in the same closing image, where the sampled dual arms and
actual closed cut separate the endpoints. No planar interface remains here.
-/

@[expose] public section

open MeasureTheory

namespace PottsContinuity.Thm3.Prop4

open PD.FK
noncomputable section

local instance sampledCutClosingEdgeDecidableEq (a : LatticeVertex) (w h : ℕ) :
    DecidableEq (rectangleGraph a w h).edgeSet := Classical.decEq _

/-- The exact closing cost times an actual source event is bounded by the
free endpoint-arm product, for the full sampled complementary boundary arcs. -/
theorem sampled_cut_closing_probability_le_free_product (θ : Parameters)
    (a : LatticeVertex) (w h : ℕ) (u v : RectangleVertex a w h)
    (hu : u.val.1 = a.1) (hv : v.val.1 = a.1+(w : ℤ))
    (k lo hi : ℤ) (hlohi : lo ≤ hi) (huCut : u.val.1 ≤ k) (hvCut : k < v.val.1)
    (K : Configuration (rectangleGraph a w h))
    (hcolumn : ∀ e ∈ K, ∃ y : ℤ, Sym2.map Subtype.val e.val = s((k,y),(k+1,y)))
    (hrows : ∀ y ∈ Finset.Icc lo hi, ∃ c : RectanglePrimalBond a w h,
      c.val = ⟨(k,y),.horizontal⟩ ∧ rectanglePrimalBondToEdge a w h c ∈ K)
    (P Q : LatticeVertex → Prop) (B : Set (Configuration (rectangleGraph a w h)))
    (hB : ∀ A ∈ B,
      A ∈ sampledRectangleDualArmsEvent a w h {(k,lo-1)} {(k,hi)}
        (PlanarTopology.rectangleLowerDualArc a w h u.val v.val)
        (PlanarTopology.rectangleUpperDualArc a w h u.val v.val) P Q ∧
      ActualConnected (rectangleGraph a w h) A u v) :
    (1-edgeParameter θ)^K.card*(measure (rectangleGraph a w h) θ (BoundaryCondition.free ∅) B).toReal ≤
      (measure (rectangleGraph a w h) θ (BoundaryCondition.free ∅)
        (targetConnectionEvent u {z | z.val.1 = k})).toReal *
      (measure (rectangleGraph a w h) θ (BoundaryCondition.free ∅)
        (targetConnectionEvent v {z | z.val.1 = k+1})).toReal := by
  classical
  apply (finite_closing_image_energy (rectangleGraph a w h) θ (BoundaryCondition.free ∅) K B).trans
  apply le_trans _ (sampled_cut_screen_target_probability_le_product θ a w h u v hu hv k lo hi hlohi
    P Q {z | z.val.1 = k} {z | z.val.1 = k+1})
  apply measureReal_mono _ (measure_ne_top _ _)
  rintro C ⟨A,hA,rfl⟩
  have hAB := hB A hA
  obtain ⟨hleft,hright⟩ := rectangle_cut_surviving_endpoint_targets a w h A K k hcolumn u v huCut hvCut hAB.2
  refine ⟨⟨⟨?_,isLowerSet_sampledRectangleDualArmsEvent a w h _ _ _ _ P Q Finset.sdiff_subset hAB.1⟩,
    hleft⟩,hright⟩
  intro y hy
  obtain ⟨c,hc,hcK⟩ := hrows y hy
  refine ⟨c,hc,?_⟩
  intro he
  let e : (rectangleGraph a w h).edgeSet := rectanglePrimalBondToEdge a w h c
  have he' : e ∈ A \ K := he
  have hcK' : e ∈ K := hcK
  exact (@Finset.mem_sdiff (rectangleGraph a w h).edgeSet
    (sampledCutClosingEdgeDecidableEq a w h) A K e).mp he' |>.2 <| hcK'


end
end PottsContinuity.Thm3.Prop4
