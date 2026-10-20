module

public import PottsContinuity.Thm3.RSW.TiltedStripTopEdgeIndependence
public import PottsContinuity.DualityExt.PositiveConnectedBoundaryPartition
public import PottsContinuity.FKC.FiniteFK.RectangleConnectivity
public import PottsContinuity.Thm3.RSW.BottomCollarSourceState

@[expose] public section

namespace PottsContinuity.RSW
open PD.FK Thm3.Prop4 DualityExt
noncomputable section

private theorem corridor_rectangle_reachable (a : LatticeVertex) (w h : ℕ)
    (u v : RectangleVertex a w h) : (rectangleGraph a w h).Reachable u v := by
  rw [rectangleGraph_eq_FKC]
  exact FKC.FiniteFK.rectangleGraph_reachable_all a w h u v

/-- Open precisely the host bonds whose two endpoints lie above the reduced
strip's upper supporting threshold. -/
def tiltedUpperCorridorState (a : LatticeVertex) (w h N : ℕ) (t : ℝ) :
    Configuration (rectangleGraph a w h) := by
  classical
  letI corridorEdgeFinite : Fintype (rectangleGraph a w h).edgeSet := Fintype.ofFinite _
  exact Finset.univ.filter (fun e => ∀ z ∈ e.val, (N : ℝ) < tiltedHeight t z.val + 1)

private theorem corridor_subrectangle_reachable
    (a b : LatticeVertex) (w h u v N : ℕ) (t : ℝ)
    (hsub : ∀ z : RectangleVertex b u v, z.val ∈ PD.FK.latticeRectangle a w h)
    (hupper : ∀ z : RectangleVertex b u v, (N : ℝ) < tiltedHeight t z.val+1)
    (x y : RectangleVertex b u v) :
    (openGraph (rectangleGraph a w h) (tiltedUpperCorridorState a w h N t)).Reachable
      ⟨x.val,hsub x⟩ ⟨y.val,hsub y⟩ := by
  classical
  let f : RectangleVertex b u v → RectangleVertex a w h := fun z => ⟨z.val,hsub z⟩
  let φ : rectangleGraph b u v →g
      openGraph (rectangleGraph a w h) (tiltedUpperCorridorState a w h N t) := by
    refine ⟨f,?_⟩
    intro x y hxy
    have hadj : (rectangleGraph a w h).Adj (f x) (f y) := hxy
    rw [openGraph_adj]
    refine ⟨⟨s(f x,f y),(rectangleGraph a w h).mem_edgeSet.mpr hadj⟩,?_,rfl⟩
    simp only [tiltedUpperCorridorState,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_coe]
    intro z hz
    rcases (Sym2.mem_iff').mp hz with rfl | rfl
    · exact hupper x
    · exact hupper y
  exact (corridor_rectangle_reachable b u v x y).map φ

/-- Every upper-corridor vertex connects vertically to the host's top row. -/
theorem tiltedUpperCorridor_reachable_cap
    (a : LatticeVertex) (w h N : ℕ) (t : ℝ)
    (u : RectangleVertex a w h) (hu : (N : ℝ) < tiltedHeight t u.val+1) :
    (openGraph (rectangleGraph a w h) (tiltedUpperCorridorState a w h N t)).Reachable u
      ⟨(u.val.1,a.2+(h:ℤ)),by
        have hb := (mem_latticeRectangle a u.val w h).mp u.property
        rw [mem_latticeRectangle]
        exact ⟨hb.1,by omega,by omega⟩⟩ := by
  let d := (a.2+(h:ℤ)-u.val.2).toNat
  have hb := (mem_latticeRectangle a u.val w h).mp u.property
  have hd : (d : ℤ) = a.2+(h:ℤ)-u.val.2 := by
    dsimp [d]
    exact Int.toNat_of_nonneg (by omega)
  have hsub (z : RectangleVertex u.val 0 d) : z.val ∈ PD.FK.latticeRectangle a w h := by
    have hz := (mem_latticeRectangle u.val z.val 0 d).mp z.property
    rw [mem_latticeRectangle]
    constructor <;> constructor <;> omega
  have hupper (z : RectangleVertex u.val 0 d) : (N : ℝ) < tiltedHeight t z.val+1 := by
    have hz := (mem_latticeRectangle u.val z.val 0 d).mp z.property
    have hx : z.val.1 = u.val.1 := by omega
    have hy : (u.val.2 : ℝ) ≤ z.val.2 := by exact_mod_cast hz.2.1
    dsimp [tiltedHeight] at hu ⊢
    rw [hx]
    linarith
  let x : RectangleVertex u.val 0 d := ⟨u.val,by
    rw [mem_latticeRectangle]
    constructor <;> constructor <;> omega⟩
  let y : RectangleVertex u.val 0 d := ⟨(u.val.1,a.2+(h:ℤ)),by
    rw [mem_latticeRectangle]
    constructor <;> constructor <;> omega⟩
  exact corridor_subrectangle_reachable a u.val w h 0 d N t hsub hupper x y

/-- If the top cap is above the upper threshold, the entire open upper
corridor forms one connected class, for arbitrary real slopes. -/
theorem tiltedUpperCorridor_connected
    (a : LatticeVertex) (w h N : ℕ) (t : ℝ)
    (hcap : ∀ z : RectangleVertex a w h, z.val.2 = a.2+(h:ℤ) →
      (N : ℝ) < tiltedHeight t z.val+1)
    (u v : RectangleVertex a w h)
    (hu : (N : ℝ) < tiltedHeight t u.val+1)
    (hv : (N : ℝ) < tiltedHeight t v.val+1) :
    (componentSetoid (rectangleGraph a w h) (BoundaryCondition.free ∅)
      (tiltedUpperCorridorState a w h N t)).r u v := by
  let cap (z : RectangleVertex a w h) : RectangleVertex a w h :=
    ⟨(z.val.1,a.2+(h:ℤ)),by
      have hz := (mem_latticeRectangle a z.val w h).mp z.property
      rw [mem_latticeRectangle]
      exact ⟨hz.1,by omega,by omega⟩⟩
  have hsub (z : RectangleVertex (a.1,a.2+(h:ℤ)) w 0) :
      z.val ∈ PD.FK.latticeRectangle a w h := by
    have hz := (mem_latticeRectangle _ z.val w 0).mp z.property
    rw [mem_latticeRectangle]
    constructor <;> constructor <;> omega
  have hupper (z : RectangleVertex (a.1,a.2+(h:ℤ)) w 0) :
      (N : ℝ) < tiltedHeight t z.val+1 := by
    apply hcap ⟨z.val,hsub z⟩
    change z.val.2 = a.2+(h:ℤ)
    have hz := (mem_latticeRectangle _ z.val w 0).mp z.property
    omega
  let top (z : RectangleVertex a w h) : RectangleVertex (a.1,a.2+(h:ℤ)) w 0 :=
    ⟨(cap z).val,by
      have hz := (mem_latticeRectangle a z.val w h).mp z.property
      rw [mem_latticeRectangle]
      exact ⟨hz.1,by rfl,by simp [cap]⟩⟩
  have hrow : (openGraph (rectangleGraph a w h) (tiltedUpperCorridorState a w h N t)).Reachable
      (cap u) (cap v) :=
    corridor_subrectangle_reachable a (a.1,a.2+(h:ℤ)) w h w 0 N t hsub hupper (top u) (top v)
  exact actualConnected_component _ _ _
    (((tiltedUpperCorridor_reachable_cap a w h N t u hu).trans hrow).trans
      (tiltedUpperCorridor_reachable_cap a w h N t v hv).symm)

/-- Freezing the upper corridor gives exactly one upper wired class. -/
theorem tiltedUpperCorridor_partition
    (a : LatticeVertex) (w h N : ℕ) (t : ℝ)
    (hcap : ∀ z : RectangleVertex a w h, z.val.2 = a.2+(h:ℤ) →
      (N : ℝ) < tiltedHeight t z.val+1) :
    (frozenBoundary (BoundaryCondition.free ∅) (tiltedUpperCorridorState a w h N t)).partition =
      (BoundaryCondition.wired {z : RectangleVertex a w h |
        (N : ℝ) < tiltedHeight t z.val+1}).partition := by
  classical
  apply frozenBoundary_partition_eq_wired_of_boundary_connected
  · intro e he u hu
    simp only [tiltedUpperCorridorState,Finset.mem_filter,Finset.mem_univ,true_and] at he
    exact he u hu
  · exact Set.empty_subset _
  · intro u v hu hv
    exact tiltedUpperCorridor_connected a w h N t hcap u v hu hv

end
end PottsContinuity.RSW
