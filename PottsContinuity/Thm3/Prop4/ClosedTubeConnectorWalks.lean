module

public import PottsContinuity.Thm3.Prop4.RetainedCentralRowEdge
public import PottsContinuity.Thm3.Prop4.TubeReferenceConnectorWalks

/-!
# Retained connectors in a single restored random sample

Closing exactly the retained central rows supplies a genuine sampled walk.
All its vertices and its length are retained, including empty connectors.
-/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4

open PD.FK
noncomputable section
local instance closedConnectorOriginalEq (n : ℕ) :
    DecidableEq (rectangleGraph (-(n : ℤ),-(n : ℤ)) (2*n) (2*n)).edgeSet := Classical.decEq _

/-- Closing the actual retained row interval produces the literal sampled
vertical connector in the same restored configuration. -/
theorem closed_rows_sampled_vertical_connector {n : ℕ} (hn : 1 ≤ n) (r : ℝ)
    (u v : LatticeVertex) (lo hi a b : ℤ)
    (hrows : radiusTubeCutRows n r u v 0 = Finset.Icc lo hi)
    (hab : a ≤ b) (ha : -(n : ℤ)-1 ≤ a) (hb : b ≤ n)
    (hout : b < lo ∨ hi ≤ a)
    (C : Configuration (tubePrimalRemainingGraph n r u v))
    (hC : Disjoint C (tubeRemainingCentralRows n r u v (a+1) b)) :
    ∃ p : (PlanarTopology.rectangleSampledClosedDualGraph (-(n : ℤ),-(n : ℤ))
      (2*n) (2*n) ((edgeRestrictionConfigurationEquiv _ (rectangleTubeRevealedEdges n r u v) C).val ∪
        rectangleTubeRevealedEdges n r u v)).Walk (0,a) (0,b),
      p.length = (b-a).toNat ∧ ∀ z ∈ p.support, z.1=0 ∧ a ≤ z.2 ∧ z.2 ≤ b := by
  apply vertical_graph_walk_of_row_steps _ a b hab
  intro y hya hyb
  apply tubeRemainingCentralRows_closed_dual_step hn r u v (a+1) b y (by omega) _
    (Finset.mem_Icc.mpr (by omega)) C hC
  rw [hrows,Finset.mem_Icc]
  omega

/-- The lower and upper short connectors coexist in a single restored sample
when their union of retained original row edges is closed. -/
theorem closed_rows_sampled_cut_connectors {n : ℕ} (hn : 1 ≤ n) (r : ℝ)
    (u v : LatticeVertex) (lo hi L U : ℤ) (hlohi : lo ≤ hi)
    (hrows : radiusTubeCutRows n r u v 0 = Finset.Icc lo hi)
    (hL : -(n : ℤ)-1 ≤ L ∧ L ≤ lo-1) (hU : hi ≤ U ∧ U ≤ n)
    (C : Configuration (tubePrimalRemainingGraph n r u v))
    (hC : Disjoint C (tubeRemainingCentralRows n r u v (L+1) (lo-1) ∪
      tubeRemainingCentralRows n r u v (hi+1) U)) :
    let H := PlanarTopology.rectangleSampledClosedDualGraph (-(n : ℤ),-(n : ℤ))
      (2*n) (2*n) ((edgeRestrictionConfigurationEquiv _ (rectangleTubeRevealedEdges n r u v) C).val ∪
        rectangleTubeRevealedEdges n r u v);
    ∃ minus : H.Walk (0,L) (0,lo-1), ∃ plus : H.Walk (0,hi) (0,U),
      minus.length = (lo-1-L).toNat ∧ plus.length = (U-hi).toNat := by
  have hbox (y : ℤ) (hy : y ∈ Finset.Icc lo hi) : -(n : ℤ) ≤ y ∧ y ≤ n := by
    have hm : y ∈ radiusTubeCutRows n r u v 0 := by rwa [hrows]
    exact Finset.mem_Icc.mp (Finset.mem_filter.mp hm).1
  have hlo := hbox lo (Finset.mem_Icc.mpr ⟨le_rfl,hlohi⟩)
  have hhi := hbox hi (Finset.mem_Icc.mpr ⟨hlohi,le_rfl⟩)
  have hdis := Finset.disjoint_union_right.mp hC
  obtain ⟨minus,hminus,_⟩ := closed_rows_sampled_vertical_connector hn r u v lo hi L (lo-1)
    hrows hL.2 hL.1 (by omega) (Or.inl (by omega)) C hdis.1
  obtain ⟨plus,hplus,_⟩ := closed_rows_sampled_vertical_connector hn r u v lo hi hi U
    hrows hU.1 (by omega) hU.2 (Or.inr le_rfl) C hdis.2
  exact ⟨minus,plus,hminus,hplus⟩

end
end PottsContinuity.Thm3.Prop4
