module

public import PottsContinuity.Thm3.RSW.SquarePair
public import PottsContinuity.Foundations.BoxBoundary

/-!
# Explicit bounding-square indices for Lemma 5

There are two orientations: left-to-right and bottom-to-top. Each index records
an anchor in box m and both endpoint heights in Fin(m+1). The index includes
all corner cases, and its cardinality is bounded by the source's 72m^4.
-/

@[expose] public section

namespace PottsContinuity.RSW

/-- An anchor, an orientation, and the two offsets on opposite square sides. -/
abbrev SquareLocalizationIndex (m : ℕ) :=
  {a : ℤ × ℤ // a ∈ box m} × Bool × Fin (m + 1) × Fin (m + 1)

/-- Lower left corner of the square indexed by its left or bottom anchor. -/
def localizationCorner {m : ℕ} (t : SquareLocalizationIndex m) : ℤ × ℤ :=
  if t.2.1 then (t.1.val.1 - (t.2.2.1.val : ℤ), t.1.val.2)
  else (t.1.val.1, t.1.val.2 - (t.2.2.1.val : ℤ))

/-- The vertex on the opposite side, including either endpoint of that side. -/
def localizationPartner {m : ℕ} (t : SquareLocalizationIndex m) : ℤ × ℤ :=
  if t.2.1 then
    (t.1.val.1 - (t.2.2.1.val : ℤ) + (t.2.2.2.val : ℤ), t.1.val.2 + m)
  else (t.1.val.1 + m, t.1.val.2 - (t.2.2.1.val : ℤ) + (t.2.2.2.val : ℤ))

/-- The entire induced lattice square belonging to an index. -/
def localizationSquare {m : ℕ} (t : SquareLocalizationIndex m) : Finset (ℤ × ℤ) :=
  latticeRectangle (localizationCorner t).1 ((localizationCorner t).1 + m)
    (localizationCorner t).2 ((localizationCorner t).2 + m)

/-- Both indexed vertices lie in the indicated square. -/
theorem localization_endpoints_mem {m : ℕ} (t : SquareLocalizationIndex m) :
    t.1.val ∈ localizationSquare t ∧ localizationPartner t ∈ localizationSquare t := by
  obtain ⟨a, o, i, j⟩ := t
  have hi := i.is_lt
  have hj := j.is_lt
  cases o <;>
    simp only [localizationSquare, localizationCorner, localizationPartner, Bool.false_eq_true,
      ↓reduceIte, latticeRectangle, Finset.mem_product, Finset.mem_Icc] <;> omega

/-- The indexed pair has exact infinity distance m. -/
theorem localization_endpoints_distance {m : ℕ} (t : SquareLocalizationIndex m) :
    max |t.1.val.1 - (localizationPartner t).1|
      |t.1.val.2 - (localizationPartner t).2| = (m : ℤ) := by
  obtain ⟨a, o, i, j⟩ := t
  have hi := i.is_lt
  have hj := j.is_lt
  have hoffset : |(i.val : ℤ) - j.val| ≤ (m : ℤ) := by
    rw [abs_le]
    constructor <;> omega
  cases o <;>
    simp only [localizationPartner, Bool.false_eq_true, ↓reduceIte,
      sub_add_eq_sub_sub, sub_sub_cancel, sub_self, zero_sub, abs_neg, Int.abs_natCast]
  · exact max_eq_left hoffset
  · exact max_eq_right hoffset

/-- Exact cardinality of this explicit, nonempty enumeration. -/
theorem card_squareLocalizationIndex (m : ℕ) :
    Fintype.card (SquareLocalizationIndex m) =
      (2 * m + 1)^2 * 2 * (m + 1)^2 := by
  have hcard : (box m).card = (2 * m + 1)^2 := by
    simp only [box, Finset.card_product, Int.card_Icc]
    have h : ((m : ℤ) + 1 - -(m : ℤ)).toNat = 2 * m + 1 := by omega
    rw [h]
    ring
  simp only [SquareLocalizationIndex, Fintype.card_prod, Fintype.card_coe,
    Fintype.card_bool, Fintype.card_fin, hcard]
  ring

/-- The explicit enumeration preserves the universal source coefficient 72. -/
theorem card_squareLocalizationIndex_le (m : ℕ) (hm : 1 ≤ m) :
    (Fintype.card (SquareLocalizationIndex m) : ℝ) ≤ 72 * (m : ℝ)^4 := by
  rw [card_squareLocalizationIndex]
  push_cast
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  calc
    (2 * (m : ℝ) + 1)^2 * 2 * (m + 1)^2 ≤ (3 * m)^2 * 2 * (2 * m)^2 := by
      gcongr <;> linarith only [hmR]
    _ = 72 * (m : ℝ)^4 := by ring

end PottsContinuity.RSW
