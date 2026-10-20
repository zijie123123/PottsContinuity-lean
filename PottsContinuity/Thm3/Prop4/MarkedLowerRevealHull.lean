module

public import PottsContinuity.Thm3.Prop4.MarkedLowerRevealMembers

/-! # Filled-region membership of the actual marked raw query endpoints -/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4
open PD.FK PlanarTopology
noncomputable section
local instance markedLowerHullEdgeEq (a : LatticeVertex) (w h : ℕ) :
    DecidableEq (rectangleGraph a w h).edgeSet := Classical.decEq _

/-- BOTH endpoints of every actual lower raw query are inaccessible from the
top while avoiding any actual prescribed open crossing trace. -/
theorem markedLowerDualReveal_endpoints_mem_lowerTraceHull (n : ℕ)
    (A : Configuration (rectangleGraph (-(n : ℤ),-(n : ℤ)) (2*n) (2*n)))
    (u v : RectangleVertex (-(n : ℤ),-(n : ℤ)) (2*n) (2*n))
    (hu : u.val.1 = -(n : ℤ)) (hv : v.val.1 = (n : ℤ))
    (p : PD.squareLattice.Walk u.val v.val) (hPB : ∀ z ∈ p.support, z ∈ box n)
    (htrace : rectangleTraceConfiguration (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) p ⊆ A)
    (e : (rectangleGraph (-(n : ℤ),-(n : ℤ)) (2*n) (2*n)).edgeSet)
    (he : e ∈ markedLowerDualReveal (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) u.val v.val A) :
    (rectanglePrimalEdgeBond (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) e).source ∈
      lowerTraceHull n p.support.toFinset ∧
    (rectanglePrimalEdgeBond (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) e).target ∈
      lowerTraceHull n p.support.toFinset := by
  let d := rectanglePrimalDualEdgeEquiv (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) e
  have hreach := markedLowerDualReveal_mem_gives_sampled_lower_access
    (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) u.val v.val A e he
  have hmem := rectanglePrimalEdgeBond_endpoints_mem_public (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) e
  exact ⟨lower_dual_reached_endpoint_mem_lowerTraceHull n A u v hu hv p hPB htrace d
      ⟨_,hmem.1⟩ (Or.inl rfl) hreach,
    lower_dual_reached_endpoint_mem_lowerTraceHull n A u v hu hv p hPB htrace d
      ⟨_,hmem.2⟩ (Or.inr rfl) hreach⟩

end
end PottsContinuity.Thm3.Prop4
