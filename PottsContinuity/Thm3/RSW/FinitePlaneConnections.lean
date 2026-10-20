module

public import PottsContinuity.Thm3.RSW.FinitePlaneComparison
public import PottsContinuity.Thm3.RSW.FreeArmTranslation
public import PottsContinuity.Thm3.RSW.AnnulusLongConnection

@[expose] public section

namespace PottsContinuity.RSW
open PD.FK PD.RCInfinite
noncomputable section

/-- Literal restriction of plane states preserves actual sampled connections. -/
theorem finitePlaneBoolRestriction_connection
    (V : Finset LatticeVertex) (ω : LatticeConfiguration) (x y : LatticeVertex)
    (hconn : finitePlaneBoolRestriction V ω ∈ finiteConnectionEvent V x y) :
    ω ∈ PD.CorrLength.connectionEvent x y := by
  let φ : rcOpenGraph V (finitePlaneBoolRestriction V ω) →g PD.rcInfiniteOpenGraph ω := {
    toFun := Subtype.val
    map_rel' := by
      intro u v huv
      obtain ⟨⟨he,hstate⟩,_hne⟩ :=
        (SimpleGraph.fromEdgeSet_adj _).mp huv
      have hadj : squareLattice.Adj u.val v.val :=
        (squareLattice.induce (V : Set LatticeVertex)).mem_edgeSet.mp he
      apply (PD.RCInfinite.rcInfiniteOpenGraph_adj ω u.val v.val).mpr
      refine ⟨squareLattice.mem_edgeSet.mpr hadj,?_⟩
      exact hstate
  }
  obtain ⟨hx,hy,p⟩ := hconn
  apply (PD.CorrLength.connectionEvent_iff_rcInfiniteReachable x y ω).mpr
  exact p.map φ

/-- The actual annulus event read from the plane is covered by genuine
translated boundary arms rooted in the finite box of radius 2n. -/
theorem plane_annulus_subset_oneArm_union (V : Finset LatticeVertex) (n : ℕ) :
    {ω : LatticeConfiguration | finitePlaneBoolRestriction V ω ∈
      annulusCircuitEvent V (0,0) n} ⊆
    ⋃ x : {x : LatticeVertex // x ∈ box (2*n)},
      Thm3.Easy.oneArmBoundaryEvent x.val n := by
  intro ω hω
  obtain ⟨x,hx,y,_hy,hconn,hspan⟩ :=
    annulusCircuitEvent_has_long_connection V n (finitePlaneBoolRestriction V ω) hω
  have hyout : y ∉ latticeBox x n := by
    intro hy
    rw [mem_latticeBox] at hy
    omega
  have hinf := finitePlaneBoolRestriction_connection V ω x y hconn
  have harm := connectionEvent_subset_oneArmBoundaryEvent x y n hyout hinf
  exact Set.mem_iUnion.mpr ⟨⟨x,hx⟩,harm⟩

end
end PottsContinuity.RSW
