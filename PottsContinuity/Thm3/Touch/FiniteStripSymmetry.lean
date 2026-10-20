module

public import PottsContinuity.Thm3.Prop4.TiltedReflection
public import PottsContinuity.Foundations.BoxBoundary
public import PottsContinuity.PD.FK.Graph
public import PottsContinuity.PD.FK.Isomorphism
public import PottsContinuity.Thm3.RSW.SelfDualSetup

/-!
# Finite column truncations for the tilted-strip half-height event

The finite carrier is the strip cut by `|x| ≤ L`; the enclosing frozen box is
only used to represent this finite set as a `Finset`.  Its exact membership
criterion and the primal half-turn are proved below.  No probability statement
is proved here; the half-height bound for the tilted strip follows from
`PlanarMixed.TiltedHalfHeight.selfDualTiltedHalfHeight_ge_half` with the reduced
marginal identity `RSW.selfDual_tiltedStrip_reflected_marginal`.
-/

@[expose] public section

namespace PottsContinuity.Thm3.Touch

open PottsContinuity
open PottsContinuity.Thm3.Prop4
open PottsContinuity.PD.FK

/-- The finite strip cut at columns `-L` and `L`, represented inside a large
square only to obtain a finite carrier. -/
noncomputable def tiltedColumnWindow (N L : ℕ) (t : ℝ) : Finset (ℤ × ℤ) :=
  (tiltedWindow N (L + N + 2) t).filter (fun z => |z.1| ≤ (L : ℤ))

private theorem tiltedColumn_height_bound (N L : ℕ) (t : ℝ)
    (ht : t ∈ Set.Icc (-1 : ℝ) 1) (z : ℤ × ℤ)
    (hz : z ∈ tiltedStripVertices N t) (hx : |z.1| ≤ (L : ℤ)) :
    |(z.2 : ℝ)| ≤ (L : ℝ) + (N : ℝ) := by
  have hheight : 0 ≤ tiltedHeight t z ∧ tiltedHeight t z ≤ (N : ℝ) := hz
  have hheightLower : -(N : ℝ) ≤ tiltedHeight t z := by linarith
  have hheightAbs : |tiltedHeight t z| ≤ (N : ℝ) :=
    abs_le.mpr ⟨hheightLower, hheight.2⟩
  have hxR : |(z.1 : ℝ)| ≤ (L : ℝ) := by exact_mod_cast hx
  have htR : |t| ≤ 1 := abs_le.mpr ht
  have htx : |t| * |(z.1 : ℝ)| ≤ (L : ℝ) := by
    calc
      |t| * |(z.1 : ℝ)| ≤ 1 * |(z.1 : ℝ)| :=
        mul_le_mul_of_nonneg_right htR (abs_nonneg _)
      _ ≤ (L : ℝ) := by simpa using hxR
  calc
    |(z.2 : ℝ)| = |tiltedHeight t z + t * (z.1 : ℝ)| := by
      congr 1
      dsimp [tiltedHeight]
      ring
    _ ≤ |tiltedHeight t z| + |t * (z.1 : ℝ)| := abs_add_le _ _
    _ = |tiltedHeight t z| + |t| * |(z.1 : ℝ)| := by rw [abs_mul]
    _ ≤ (N : ℝ) + (L : ℝ) := add_le_add hheightAbs htx
    _ = (L : ℝ) + (N : ℝ) := by ring

/-- Exact equality with the requested unboxed column truncation. -/
theorem mem_tiltedColumnWindow_iff (N L : ℕ) (t : ℝ)
    (ht : t ∈ Set.Icc (-1 : ℝ) 1) (z : ℤ × ℤ) :
    z ∈ tiltedColumnWindow N L t ↔
      z ∈ tiltedStripVertices N t ∧ |z.1| ≤ (L : ℤ) := by
  classical
  rw [tiltedColumnWindow, Finset.mem_filter, mem_tiltedWindow]
  constructor
  · rintro ⟨⟨hbox, hstrip⟩, hx⟩
    exact ⟨hstrip, hx⟩
  · rintro ⟨hstrip, hx⟩
    refine ⟨⟨?_, hstrip⟩, hx⟩
    apply (Foundations.mem_box_iff_abs_le (L + N + 2) z).2
    constructor
    · exact le_trans hx (by exact_mod_cast (Nat.le_add_right L (N + 2)))
    · have hyR := tiltedColumn_height_bound N L t ht z hstrip hx
      have hyZ : |z.2| ≤ ((L + N : ℕ) : ℤ) := by exact_mod_cast hyR
      exact le_trans hyZ (by exact_mod_cast (Nat.le_add_right (L + N) 2))

/-- The point reflection preserves the exact finite column carrier at every
slope in the source range. -/
theorem tiltedColumnWindow_reflection_mem_iff (N L : ℕ) (t : ℝ)
    (ht : t ∈ Set.Icc (-1 : ℝ) 1) (z : ℤ × ℤ) :
    tiltedReflection N z ∈ tiltedColumnWindow N L t ↔
      z ∈ tiltedColumnWindow N L t := by
  rw [mem_tiltedColumnWindow_iff N L t ht,
    mem_tiltedColumnWindow_iff N L t ht, tiltedReflection_mem_strip_iff]
  simp [tiltedReflection]

/-- The induced finite graph on the column truncation. -/
abbrev tiltedColumnGraph (N L : ℕ) (t : ℝ) :=
  squareLattice.induce (tiltedColumnWindow N L t : Set (ℤ × ℤ))

/-- The actual point half-turn on the finite column graph. -/
def tiltedColumnReflectionIso (N L : ℕ) (t : ℝ)
    (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
    tiltedColumnGraph N L t ≃g tiltedColumnGraph N L t where
  toEquiv :=
    { toFun := fun z => ⟨tiltedReflection N z.1,
        (tiltedColumnWindow_reflection_mem_iff N L t ht z.1).2 z.2⟩
      invFun := fun z => ⟨tiltedReflection N z.1,
        (tiltedColumnWindow_reflection_mem_iff N L t ht z.1).2 z.2⟩
      left_inv := fun z => Subtype.ext (tiltedReflection_involutive N z.1)
      right_inv := fun z => Subtype.ext (tiltedReflection_involutive N z.1) }
  map_rel_iff' := by
    intro u v
    change |(-u.1.1)-(-v.1.1)| +
        |((N : ℤ)-u.1.2)-((N : ℤ)-v.1.2)| = 1 ↔
      |u.1.1-v.1.1| + |u.1.2-v.1.2| = 1
    rw [neg_sub_neg, sub_sub_sub_cancel_left,
      abs_sub_comm v.1.1 u.1.1, abs_sub_comm v.1.2 u.1.2]

end PottsContinuity.Thm3.Touch
