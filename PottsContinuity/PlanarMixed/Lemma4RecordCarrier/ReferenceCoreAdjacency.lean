module

public import PottsContinuity.PlanarMixed.Lemma4RecordCarrier.ReferenceWindowNoncrossing
public import PottsContinuity.PD.Duality.RectangleDualAmbient
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Basic

@[expose] public section

namespace PottsContinuity.PlanarMixed.Lemma4Connectors
open PD.FK Square
noncomputable section

/-- Inside the true-dual horizontal core, the only missing ordinary lattice
edges are vertical edges lying entirely on an outer side column. -/
theorem referenceDualCore_adj_of_lattice_adj
    (z : ℤ) (N : ℕ) (hN : 1 ≤ N)
    (u v : rectangleDualHorizontalCoreVertex (z,z) N N)
    (huv : PD.FK.squareLattice.Adj u.val.val v.val.val)
    (hleft : ¬ (u.val.val.1=z-1 ∧ v.val.val.1=z-1))
    (hright : ¬ (u.val.val.1=z+(N:ℤ) ∧ v.val.val.1=z+(N:ℤ))) :
    (rectangleDualHorizontalCoreGraph (z,z) N N).Adj u v := by
  have hu := (PD.FK.mem_latticeRectangle (z-1,z-1) u.val.val (N+1) (N+1)).mp u.val.property
  have hv := (PD.FK.mem_latticeRectangle (z-1,z-1) v.val.val (N+1) (N+1)).mp v.val.property
  have huy := u.property
  have hvy := v.property
  change z ≤ u.val.val.2 ∧ u.val.val.2 ≤ z+(N:ℤ)-1 at huy
  change z ≤ v.val.val.2 ∧ v.val.val.2 ≤ z+(N:ℤ)-1 at hvy
  norm_num only [Nat.cast_add,Nat.cast_one,Prod.fst,Prod.snd] at hu hv
  have hstep := (PD.FK.squareLattice_adj_iff u.val.val v.val.val).mp huv
  have hi : (z ≤ u.val.val.1 ∧ u.val.val.1 < z+(N:ℤ)) ∨
      (z ≤ v.val.val.1 ∧ v.val.val.1 < z+(N:ℤ)) := by omega
  have hamb : (rectangleDualAmbientGraph (z,z) N N).Adj u.val v.val :=
    (rectangleDualAmbientGraph_adj_iff _ _ _ _ _).mpr huv
  change (rectangleDualGraph (z,z) N N).Adj u.val v.val
  rcases hi with hi | hi
  · apply rectangleDualAmbient_adj_actual_of_left_interior _ _ _ _ _ _ hamb
    exact Finset.mem_filter.mpr ⟨u.val.property,hi.1,hi.2,huy.1,by omega⟩
  · exact (rectangleDualAmbient_adj_actual_of_left_interior _ _ _ _ _
      (Finset.mem_filter.mpr ⟨v.val.property,hi.1,hi.2,hvy.1,by omega⟩) hamb.symm).symm

end
end PottsContinuity.PlanarMixed.Lemma4Connectors
