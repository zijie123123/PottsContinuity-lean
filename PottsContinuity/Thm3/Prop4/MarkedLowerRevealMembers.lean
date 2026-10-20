module

public import PottsContinuity.Thm3.Prop4.MarkedLowerDualReveal
public import PottsContinuity.Thm3.Prop4.LowerDualEndpointColumns

/-! # Actual lower-dual access and columns of every marked revealed bond -/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4
open PD.FK PlanarTopology
noncomputable section
local instance markedRevealMembersEdgeEq (a : LatticeVertex) (w h : ℕ) :
    DecidableEq (rectangleGraph a w h).edgeSet := Classical.decEq _

/-- Every bond in the actual raw marked reveal has an incident face reached
from the literal lower arc by closed sampled bonds in the ORIGINAL sample. -/
theorem markedLowerDualReveal_mem_gives_sampled_lower_access
    (a : LatticeVertex) (w h : ℕ) (u v : LatticeVertex)
    (A : Configuration (rectangleGraph a w h)) (f : (rectangleGraph a w h).edgeSet)
    (hf : f ∈ markedLowerDualReveal a w h u v A) :
    (∃ s ∈ rectangleLowerDualArc a w h u v,
      (rectangleSampledClosedDualGraph a w h A).Reachable s (rectangleCrossingDualBond a w h f).source) ∨
    (∃ s ∈ rectangleLowerDualArc a w h u v,
      (rectangleSampledClosedDualGraph a w h A).Reachable s (rectangleCrossingDualBond a w h f).target) := by
  classical
  obtain ⟨z,hz,s,hs,hconn⟩ := (Push.mem_closedClusterReveal_iff_endpoint _ _ A f).mp hf
  have hsL : s.val ∈ rectangleLowerDualArc a w h u v := (Finset.mem_filter.mp hs).2
  have hfin : ActualConnected (rectangleDualGraph a w h) (rectangleDualConfiguration a w h A) s z := by
    rw [← Push.auxiliaryClosedConfiguration_rectangle_eq]
    exact hconn
  have hreach := (rectangle_finite_closed_dual_reachable_iff_sampled a w h A s z).mp hfin
  have hpair : (DualityExt.rectangleDualEdgeEquiv a w h f).val =
      s(rectangleDualEdgeSource a w h (rectanglePrimalDualEdgeEquiv a w h f),
        rectangleDualEdgeTarget a w h (rectanglePrimalDualEdgeEquiv a w h f)) := rfl
  rw [hpair,Sym2.mem_iff] at hz
  rcases hz with rfl | rfl
  · exact Or.inl ⟨s.val,hsL,hreach⟩
  · exact Or.inr ⟨s.val,hsL,hreach⟩

/-- The raw marked reveal's two literal original-bond endpoint columns are
bounded by ANY actual prescribed open crossing trace, with no source-fit
column assumption remaining. -/
theorem markedLowerDualReveal_bond_columns (n : ℕ)
    (A : Configuration (rectangleGraph (-(n : ℤ),-(n : ℤ)) (2*n) (2*n)))
    (u v : RectangleVertex (-(n : ℤ),-(n : ℤ)) (2*n) (2*n))
    (hu : u.val.1 = -(n : ℤ)) (hv : v.val.1 = (n : ℤ))
    (p : PD.squareLattice.Walk u.val v.val) (hPB : ∀ z ∈ p.support, z ∈ box n)
    (htrace : rectangleTraceConfiguration (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) p ⊆ A) :
    ∀ e ∈ markedLowerDualReveal (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) u.val v.val A,
      (∃ z ∈ p.support.toFinset,
        (rectanglePrimalEdgeBond (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) e).source.1 = z.1 ∧
        (rectanglePrimalEdgeBond (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) e).source.2 ≤ z.2) ∧
      (∃ z ∈ p.support.toFinset,
        (rectanglePrimalEdgeBond (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) e).target.1 = z.1 ∧
        (rectanglePrimalEdgeBond (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) e).target.2 ≤ z.2) := by
  intro e he
  let d := rectanglePrimalDualEdgeEquiv (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) e
  have hreach := markedLowerDualReveal_mem_gives_sampled_lower_access
    (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) u.val v.val A e he
  have hmem := rectanglePrimalEdgeBond_endpoints_mem_public (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) e
  exact ⟨lower_dual_reached_endpoint_column_witness n A u v hu hv p hPB htrace d
      ⟨_,hmem.1⟩ (Or.inl rfl) hreach,
    lower_dual_reached_endpoint_column_witness n A u v hu hv p hPB htrace d
      ⟨_,hmem.2⟩ (Or.inr rfl) hreach⟩

end
end PottsContinuity.Thm3.Prop4
