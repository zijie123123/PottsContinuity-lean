module

public import PottsContinuity.Thm3.Prop4.SplitRadius
public import PottsContinuity.Thm3.Prop4.TiltedCandidates

/-!
# Radius-parametrized tubes for the corrected split proof

The source Euclidean tube is retained unchanged. A separate radius parameter
allows the proof to use radius 4n^ε so that square arms of radius n^ε survive
the removal of the edges incident to its farthest vertex.
-/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4

/-- The literal Euclidean sublevel tube for every real radius, including an empty negative sublevel. -/
noncomputable def radiusTube (n : ℕ) (r : ℝ) (u v : ℤ × ℤ) : Finset (ℤ × ℤ) := by
  classical
  exact (box n).filter (fun z => tubeDistance u v z < r)

@[simp] theorem mem_radiusTube (n : ℕ) (r : ℝ) (u v z : ℤ × ℤ) :
    z ∈ radiusTube n r u v ↔ z ∈ box n ∧ tubeDistance u v z < r := by
  classical
  simp [radiusTube]

/-- The original definition is exactly the original-radius instance; it is not changed. -/
theorem inductionTube_eq_radiusTube (n : ℕ) (ε : ℝ) (u v : ℤ × ℤ) :
    inductionTube n ε u v = radiusTube n ((n : ℝ)^ε) u v := rfl

/-- The corrected proof tube, enlarged by a fixed absolute factor. -/
noncomputable def widenedInductionTube (n : ℕ) (ε : ℝ) (u v : ℤ × ℤ) : Finset (ℤ × ℤ) :=
  radiusTube n (4*(n : ℝ)^ε) u v

/-- The actual original cut edges indexed by their integer row. -/
noncomputable def radiusTubeCutRows (n : ℕ) (r : ℝ) (u v : ℤ × ℤ)
    (k : ℤ) : Finset ℤ := by
  classical
  exact (Finset.Icc (-(n : ℤ)) n).filter
    (fun y => (k,y) ∈ radiusTube n r u v ∧ (k+1,y) ∈ radiusTube n r u v)

/-- The literal unoriented edges crossing the chosen column gap. -/
noncomputable def radiusTubeCut (n : ℕ) (r : ℝ) (u v : ℤ × ℤ)
    (k : ℤ) : Finset (Sym2 (ℤ × ℤ)) := by
  classical
  exact (radiusTubeCutRows n r u v k).image (fun y => s((k,y),(k+1,y)))

/-- The full cut remains uniformly bounded by its real width, with rounding. -/
theorem radiusTubeCut_card_le (n : ℕ) (r : ℝ) (u v : ℤ × ℤ)
    (t b : ℝ) (ht : |t| ≤ 1)
    (hu : (u.2 : ℝ) = t*(u.1 : ℝ)+b)
    (hv : (v.2 : ℝ) = t*(v.1 : ℝ)+b) (k : ℤ) :
    (radiusTubeCut n r u v k).card ≤ 4*⌈r⌉₊+1 := by
  classical
  let a := t*(k : ℝ)+b-2*r
  have hrad : r ≤ (⌈r⌉₊ : ℝ) := Nat.le_ceil _
  have hsubset : radiusTubeCutRows n r u v k ⊆ Finset.Icc ⌈a⌉ ⌊a+(4*⌈r⌉₊ : ℕ)⌋ := by
    intro y hy
    have hmem := (Finset.mem_filter.mp hy).2.1
    have hd := abs_lt.mp (tube_vertical_deviation_lt u v (k,y) t b r ht hu hv
      ((mem_radiusTube n r u v (k,y)).mp hmem).2)
    apply Finset.mem_Icc.mpr
    constructor
    · apply Int.ceil_le.mpr
      dsimp [a]
      linarith only [hd.1]
    · apply Int.le_floor.mpr
      dsimp [a]
      push_cast
      linarith only [hd.2,hrad]
  exact (Finset.card_image_le).trans
    ((Finset.card_le_card hsubset).trans (tilted_column_card_le _ a))

end PottsContinuity.Thm3.Prop4
