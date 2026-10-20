module

public import PottsContinuity.Thm3.Prop4.TubeHalfPlaneEdges

/-!
# Safe affine connector heights and their true lengths

The endpoints of the actual cut lie within the tube's proved width.
Rounded safe affine heights can therefore be reached with linear-in-radius
vertical connectors. Physical exterior stopping is a separate construction.
-/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4

/-- The two actual extremal central cut rows have the literal width bound. -/
theorem central_cut_endpoint_deviation (n : ℕ) (r : ℝ) (u v : PD.FK.LatticeVertex)
    (t b : ℝ) (ht : |t| ≤ 1) (hu : (u.2 : ℝ) = t*u.1+b)
    (hv : (v.2 : ℝ) = t*v.1+b) (lo hi : ℤ) (hlohi : lo ≤ hi)
    (hrows : radiusTubeCutRows n r u v 0 = Finset.Icc lo hi) :
    |(lo : ℝ)-b| < 2*r ∧ |(hi : ℝ)-b| < 2*r := by
  have hmem (y : ℤ) (hy : y ∈ Finset.Icc lo hi) :=
    ((mem_radiusTubeCutRows_iff n r u v 0 y).mp (by rwa [hrows])).1
  constructor
  · have h := tube_vertical_deviation_lt u v (0,lo) t b r ht hu hv
      ((mem_radiusTube n r u v _).mp (hmem lo (Finset.mem_Icc.mpr ⟨le_rfl,hlohi⟩))).2
    simpa only [Int.cast_zero,mul_zero,zero_add] using h
  · have h := tube_vertical_deviation_lt u v (0,hi) t b r ht hu hv
      ((mem_radiusTube n r u v _).mp (hmem hi (Finset.mem_Icc.mpr ⟨hlohi,le_rfl⟩))).2
    simpa only [Int.cast_zero,mul_zero,zero_add] using h

/-- The lower safe integer height lies below the actual lower root, at a
vertical distance strictly below four radii. -/
theorem central_cut_lower_connector_length (n : ℕ) (r : ℝ) (u v : PD.FK.LatticeVertex)
    (t b : ℝ) (ht : |t| ≤ 1) (hu : (u.2 : ℝ) = t*u.1+b)
    (hv : (v.2 : ℝ) = t*v.1+b) (lo hi : ℤ) (hlohi : lo ≤ hi)
    (hrows : radiusTubeCutRows n r u v 0 = Finset.Icc lo hi) :
    ⌊b-2*r⌋ ≤ lo-1 ∧
      ((lo-1-⌊b-2*r⌋ : ℤ) : ℝ) < 4*r ∧ (⌊b-2*r⌋ : ℝ) ≤ b-2*r := by
  have hd := abs_lt.mp (central_cut_endpoint_deviation n r u v t b ht hu hv lo hi hlohi hrows).1
  have hl : ⌊b-2*r⌋ < lo := Int.floor_lt.mpr (by linarith only [hd.1])
  have hf := Int.sub_one_lt_floor (b-2*r)
  refine ⟨by omega,?_,Int.floor_le _⟩
  push_cast
  linarith only [hd.2,hf]

/-- The upper safe integer height lies above the actual upper root, at a
vertical distance strictly below four radii plus one. -/
theorem central_cut_upper_connector_length (n : ℕ) (r : ℝ) (u v : PD.FK.LatticeVertex)
    (t b : ℝ) (ht : |t| ≤ 1) (hu : (u.2 : ℝ) = t*u.1+b)
    (hv : (v.2 : ℝ) = t*v.1+b) (lo hi : ℤ) (hlohi : lo ≤ hi)
    (hrows : radiusTubeCutRows n r u v 0 = Finset.Icc lo hi) :
    hi ≤ ⌈b+2*r⌉ ∧
      ((⌈b+2*r⌉-hi : ℤ) : ℝ) < 4*r+1 ∧ b+2*r ≤ (⌈b+2*r⌉ : ℝ) := by
  have hd := abs_lt.mp (central_cut_endpoint_deviation n r u v t b ht hu hv lo hi hlohi hrows).2
  have hh : hi < ⌈b+2*r⌉ := Int.lt_ceil.mpr (by linarith only [hd.2])
  have hc := Int.ceil_lt_add_one (b+2*r)
  refine ⟨by omega,?_,Int.le_ceil _⟩
  push_cast
  linarith only [hd.1,hc]


/-- Stop the lower connector at the physical exterior if it is reached before
its safe affine height. The actual root and linear length bound are retained. -/
theorem central_cut_lower_connector_stopped {n : ℕ} (hn : 1 ≤ n) (r : ℝ)
    (u v : PD.FK.LatticeVertex) (t b : ℝ) (ht : |t| ≤ 1)
    (hu : (u.2 : ℝ) = t*u.1+b) (hv : (v.2 : ℝ) = t*v.1+b)
    (lo hi : ℤ) (hlohi : lo ≤ hi)
    (hrows : radiusTubeCutRows n r u v 0 = Finset.Icc lo hi) :
    let L := max (-(n : ℤ)-1) ⌊b-2*r⌋;
    -(n : ℤ)-1 ≤ L ∧ L ≤ lo-1 ∧ ((lo-1-L : ℤ) : ℝ) < 4*r ∧
      ((0,L) ∈ PlanarTopology.rectangleLowerDualArc (-(n : ℤ),-(n : ℤ))
        (2*n) (2*n) u v ∨ (L : ℝ) ≤ b-2*r) := by
  dsimp only
  have hr := central_cut_lower_connector_length n r u v t b ht hu hv lo hi hlohi hrows
  have hm : lo ∈ radiusTubeCutRows n r u v 0 := by
    rw [hrows]; exact Finset.mem_Icc.mpr ⟨le_rfl,hlohi⟩
  have hbnd := Finset.mem_Icc.mp (Finset.mem_filter.mp hm).1
  refine ⟨le_max_left _ _,max_le (by omega) hr.1,?_,?_⟩
  · have hh : ((lo-1-max (-(n : ℤ)-1) ⌊b-2*r⌋ : ℤ) : ℝ) ≤
        ((lo-1-⌊b-2*r⌋ : ℤ) : ℝ) := by exact_mod_cast sub_le_sub_left (le_max_right _ _) (lo-1)
    exact hh.trans_lt hr.2.1
  · by_cases h : -(n : ℤ)-1 ≤ ⌊b-2*r⌋
    · right
      rw [max_eq_right h]
      exact hr.2.2
    · left
      rw [max_eq_left (by omega)]
      apply Or.inl
      dsimp
      omega

/-- Stop the upper connector at the actual top exterior if reached first. -/
theorem central_cut_upper_connector_stopped {n : ℕ} (hn : 1 ≤ n) (r : ℝ)
    (u v : PD.FK.LatticeVertex) (t b : ℝ) (ht : |t| ≤ 1)
    (hu : (u.2 : ℝ) = t*u.1+b) (hv : (v.2 : ℝ) = t*v.1+b)
    (lo hi : ℤ) (hlohi : lo ≤ hi)
    (hrows : radiusTubeCutRows n r u v 0 = Finset.Icc lo hi) :
    let U := min (n : ℤ) ⌈b+2*r⌉;
    hi ≤ U ∧ U ≤ (n : ℤ) ∧ ((U-hi : ℤ) : ℝ) < 4*r+1 ∧
      ((0,U) ∈ PlanarTopology.rectangleUpperDualArc (-(n : ℤ),-(n : ℤ))
        (2*n) (2*n) u v ∨ b+2*r ≤ (U : ℝ)) := by
  dsimp only
  have hr := central_cut_upper_connector_length n r u v t b ht hu hv lo hi hlohi hrows
  have hm : hi ∈ radiusTubeCutRows n r u v 0 := by
    rw [hrows]; exact Finset.mem_Icc.mpr ⟨hlohi,le_rfl⟩
  have hbnd := Finset.mem_Icc.mp (Finset.mem_filter.mp hm).1
  refine ⟨le_min hbnd.2 hr.1,min_le_left _ _,?_,?_⟩
  · have hh : ((min (n : ℤ) ⌈b+2*r⌉-hi : ℤ) : ℝ) ≤
        ((⌈b+2*r⌉-hi : ℤ) : ℝ) := by exact_mod_cast sub_le_sub_right (min_le_right _ _) hi
    exact hh.trans_lt hr.2.1
  · by_cases h : ⌈b+2*r⌉ ≤ (n : ℤ)
    · right
      rw [min_eq_right h]
      exact hr.2.2
    · left
      rw [min_eq_left (by omega)]
      apply Or.inl
      dsimp
      omega

end PottsContinuity.Thm3.Prop4
