module

public import PottsContinuity.Thm3.Push.IntervalArmFilledExploration
public import PottsContinuity.Thm3.Push.AuxiliaryIndexInvariance
public import PottsContinuity.PD.Duality.RayIndexSeparation
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

@[expose] public section

namespace PottsContinuity.Push
open PottsContinuity.PD.FK PottsContinuity.PD.Duality
noncomputable section
local instance intervalIndexPropDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-- All three exterior port sides used by the source explorations have zero
index for every closed walk confined to the original primal square. -/
theorem rayIndex_square_left_right_bottom_port_zero (N : ℕ)
    {z : LatticeVertex} (p : squareLattice.Walk z z)
    (hp : ∀ x ∈ p.support, x ∈ latticeRectangle (0,0) N N)
    (v : RectangleDualVertex (0,0) N N)
    (hv : v.val.1 = -1 ∨ v.val.1 = (N : ℤ) ∨ v.val.2 = -1) :
    rayIndex (faceIndexMark v.val) p = 0 := by
  rcases hv with hleft | hright | hbottom
  · rw [rayIndex_left_telescope (faceIndexMark v.val) p]
    · omega
    · intro x hx
      have h := (mem_latticeRectangle (0,0) x N N).mp (hp x hx)
      simp only [faceIndexMark,hleft]
      omega
  · apply rayIndex_zero_of_right
    intro x hx
    have h := (mem_latticeRectangle (0,0) x N N).mp (hp x hx)
    simp only [faceIndexMark,hright]
    omega
  · apply rayIndex_zero_of_level _ p 0
    intro x hx
    have h := (mem_latticeRectangle (0,0) x N N).mp (hp x hx)
    simp only [faceIndexMark,hbottom]
    rw [ite_eq_right (by omega)]

/-- Left-arc seed marks have zero index, independently of the interval size. -/
theorem rayIndex_interval_left_seed_zero (N : ℕ) (l : ℤ)
    {z : LatticeVertex} (p : squareLattice.Walk z z)
    (hp : ∀ x ∈ p.support, x ∈ latticeRectangle (0,0) N N)
    (v : RectangleDualVertex (0,0) N N) (hv : v ∈ intervalArmLeftDualPorts N l) :
    rayIndex (faceIndexMark v.val) p = 0 := by
  apply rayIndex_square_left_right_bottom_port_zero N p hp v
  rcases (mem_intervalArmLeftDualPorts N l v).mp hv with h | ⟨h,_⟩
  · exact Or.inl h
  · exact Or.inr (Or.inr h)

/-- Opposite exterior seed marks also have zero index. -/
theorem rayIndex_interval_right_seed_zero (N : ℕ) (r : ℤ)
    {z : LatticeVertex} (p : squareLattice.Walk z z)
    (hp : ∀ x ∈ p.support, x ∈ latticeRectangle (0,0) N N)
    (v : RectangleDualVertex (0,0) N N) (hv : v ∈ intervalArmRightDualPorts N r) :
    rayIndex (faceIndexMark v.val) p = 0 := by
  apply rayIndex_square_left_right_bottom_port_zero N p hp v
  rcases (mem_intervalArmRightDualPorts N r v).mp hv with h | ⟨h,_⟩
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

/-- Index zero propagates from the actual reached left seeds along closed-dual
paths when the primal closed walk is supported on the filled source frontier. -/
theorem rayIndex_zero_on_interval_left_reached (N : ℕ) (l r : ℤ)
    (A : Configuration (rectangleGraph (0,0) N N)) {z : LatticeVertex}
    (p : squareLattice.Walk z z)
    (hinside : ∀ x ∈ p.support, x ∈ latticeRectangle (0,0) N N)
    (hedges : ∀ f : (rectangleGraph (0,0) N N).edgeSet,
      (rectanglePrimalEdgeBond (0,0) N N f).toSym2 ∈ p.edges →
        f ∈ intervalArmFilledLeftFrontier N l r A)
    (v : RectangleDualVertex (0,0) N N) (hv : v ∈ intervalArmLeftReached N l A) :
    rayIndex (faceIndexMark v.val) p = 0 := by
  obtain ⟨b,hb,⟨q⟩⟩ := hv
  let S := intervalArmLeftReached N l A
  let H := rectangleDualGraph (0,0) N N
  let σ := fun x => decide (x ∉ intervalArmRightRegion N l r A)
  let qH := q.mapLe (openGraph_le H _)
  have hsupport : ∀ x ∈ qH.support, x ∈ S := by
    intro x hx
    have hx' : x ∈ q.support := by simpa only [qH,SimpleGraph.Walk.support_mapLe_eq_support] using hx
    exact ⟨b,hb,(q.takeUntil x hx').reachable⟩
  let qS := qH.induce S hsupport
  have hlabel : ∀ x ∈ S, σ x = true := by
    intro x hxs
    apply decide_eq_true
    exact fun hright => (outsideSeedRegion_subset_compl _ _ _ hright) hxs
  have hidx := rectangle_constant_region_index_eq (0,0) N N σ p hedges S true hlabel qS.reachable
  exact hidx.symm.trans (rayIndex_interval_left_seed_zero N l p hinside b hb)

/-- Index zero propagates through the geometric opposite-region paths.
Those paths are not required to consist of closed dual edges. -/
theorem rayIndex_zero_on_interval_right_region (N : ℕ) (l r : ℤ)
    (A : Configuration (rectangleGraph (0,0) N N)) {z : LatticeVertex}
    (p : squareLattice.Walk z z)
    (hinside : ∀ x ∈ p.support, x ∈ latticeRectangle (0,0) N N)
    (hedges : ∀ f : (rectangleGraph (0,0) N N).edgeSet,
      (rectanglePrimalEdgeBond (0,0) N N f).toSym2 ∈ p.edges →
        f ∈ intervalArmFilledLeftFrontier N l r A)
    (v : RectangleDualVertex (0,0) N N) (hv : v ∈ intervalArmRightRegion N l r A) :
    rayIndex (faceIndexMark v.val) p = 0 := by
  obtain ⟨b,hb,hbs,hvs,⟨q⟩⟩ := hv
  let S := intervalArmLeftReached N l A
  let C := intervalArmRightRegion N l r A
  let H := rectangleDualGraph (0,0) N N
  let σ := fun x => decide (x ∉ C)
  let inclusion : H.induce Sᶜ →g H := {toFun := Subtype.val,map_rel' := fun h => h}
  let qH := q.map inclusion
  have hsupport : ∀ x ∈ qH.support, x ∈ C := by
    intro x hx
    rw [SimpleGraph.Walk.support_map] at hx
    obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hx
    exact ⟨b,hb,hbs,t.property,(q.takeUntil t ht).reachable⟩
  let qC := qH.induce C hsupport
  have hlabel : ∀ x ∈ C, σ x = false := by
    intro x hxc
    exact decide_eq_false (not_not_intro hxc)
  have hidx := rectangle_constant_region_index_eq (0,0) N N σ p hedges C false hlabel qC.reachable
  exact hidx.symm.trans (rayIndex_interval_right_seed_zero N r p hinside b hb)

end
end PottsContinuity.Push
