module

public import PottsContinuity.Thm3.RSW.SquareEnumeration

/-!
# Bounding squares for finite clusters

The square is built from coordinate extrema of the entire finite cloud. One
coordinate span is maximal; its two extrema provide the opposite-side pair.
The other coordinate offsets index SquareLocalizationIndex without any choice
of a default square or any planar argument.
-/

@[expose] public section

namespace PottsContinuity.RSW

/-- Every finite cloud containing the origin is contained in an indexed square,
with both indexed opposite-side endpoints belonging to the cloud. -/
theorem finiteCloud_boundingSquare (C : Finset (ℤ × ℤ)) (h0 : (0, 0) ∈ C) :
    ∃ m : ℕ, ∃ t : SquareLocalizationIndex m,
      t.1.val ∈ C ∧ localizationPartner t ∈ C ∧ C ⊆ localizationSquare t := by
  classical
  have hC : C.Nonempty := ⟨(0, 0), h0⟩
  let lx := C.inf' hC Prod.fst
  let ux := C.sup' hC Prod.fst
  let ly := C.inf' hC Prod.snd
  let uy := C.sup' hC Prod.snd
  have hb (z : ℤ × ℤ) (hz : z ∈ C) :
      lx ≤ z.1 ∧ z.1 ≤ ux ∧ ly ≤ z.2 ∧ z.2 ≤ uy :=
    ⟨Finset.inf'_le _ hz, Finset.le_sup' _ hz,
      Finset.inf'_le _ hz, Finset.le_sup' _ hz⟩
  have hz := hb (0, 0) h0
  let m := (max (ux - lx) (uy - ly)).toNat
  have hnonneg : 0 ≤ max (ux - lx) (uy - ly) := by
    have := le_max_left (ux - lx) (uy - ly)
    omega
  have hm : (m : ℤ) = max (ux - lx) (uy - ly) := Int.toNat_of_nonneg hnonneg
  have hmx : ux - lx ≤ (m : ℤ) := by rw [hm]; exact le_max_left _ _
  have hmy : uy - ly ≤ (m : ℤ) := by rw [hm]; exact le_max_right _ _
  have hbox (z : ℤ × ℤ) (hzC : z ∈ C) : z ∈ box m := by
    have := hb z hzC
    rw [Foundations.mem_box_iff_interval]
    constructor <;> constructor <;> omega
  by_cases hspan : uy - ly ≤ ux - lx
  · obtain ⟨a, ha, hax⟩ := Finset.exists_mem_eq_inf' hC Prod.fst
    obtain ⟨b, hbC, hbx⟩ := Finset.exists_mem_eq_sup' hC Prod.fst
    have ha' := hb a ha
    have hb' := hb b hbC
    have hwidth : (m : ℤ) = ux - lx := by rw [hm, max_eq_left hspan]
    have hi : (a.2 - ly).toNat < m + 1 := by omega
    have hj : (b.2 - ly).toNat < m + 1 := by omega
    let i : Fin (m + 1) := ⟨(a.2 - ly).toNat, hi⟩
    let j : Fin (m + 1) := ⟨(b.2 - ly).toNat, hj⟩
    let t : SquareLocalizationIndex m := ⟨⟨a, hbox a ha⟩, false, i, j⟩
    have hia : (i.val : ℤ) = a.2 - ly := Int.toNat_of_nonneg (by omega)
    have hjb : (j.val : ℤ) = b.2 - ly := Int.toNat_of_nonneg (by omega)
    have hcorner : localizationCorner t = (lx, ly) := by
      apply Prod.ext <;> simp only [t, localizationCorner, Bool.false_eq_true, ↓reduceIte]
      · exact hax.symm
      · omega
    have hpartner : localizationPartner t = b := by
      apply Prod.ext <;> simp only [t, localizationPartner, Bool.false_eq_true, ↓reduceIte]
      · change lx = a.1 at hax
        change ux = b.1 at hbx
        omega
      · omega
    refine ⟨m, t, ha, hpartner ▸ hbC, ?_⟩
    intro z hzC
    have := hb z hzC
    simp only [localizationSquare, hcorner, latticeRectangle, Finset.mem_product, Finset.mem_Icc]
    constructor <;> constructor <;> omega
  · obtain ⟨a, ha, hay⟩ := Finset.exists_mem_eq_inf' hC Prod.snd
    obtain ⟨b, hbC, hby⟩ := Finset.exists_mem_eq_sup' hC Prod.snd
    have ha' := hb a ha
    have hb' := hb b hbC
    have hwidth : (m : ℤ) = uy - ly := by rw [hm, max_eq_right (le_of_not_ge hspan)]
    have hi : (a.1 - lx).toNat < m + 1 := by omega
    have hj : (b.1 - lx).toNat < m + 1 := by omega
    let i : Fin (m + 1) := ⟨(a.1 - lx).toNat, hi⟩
    let j : Fin (m + 1) := ⟨(b.1 - lx).toNat, hj⟩
    let t : SquareLocalizationIndex m := ⟨⟨a, hbox a ha⟩, true, i, j⟩
    have hia : (i.val : ℤ) = a.1 - lx := Int.toNat_of_nonneg (by omega)
    have hjb : (j.val : ℤ) = b.1 - lx := Int.toNat_of_nonneg (by omega)
    have hcorner : localizationCorner t = (lx, ly) := by
      apply Prod.ext <;> simp only [t, localizationCorner, ↓reduceIte]
      · omega
      · exact hay.symm
    have hpartner : localizationPartner t = b := by
      apply Prod.ext <;> simp only [t, localizationPartner, ↓reduceIte]
      · omega
      · change ly = a.2 at hay
        change uy = b.2 at hby
        omega
    refine ⟨m, t, ha, hpartner ▸ hbC, ?_⟩
    intro z hzC
    have := hb z hzC
    simp only [localizationSquare, hcorner, latticeRectangle, Finset.mem_product, Finset.mem_Icc]
    constructor <;> constructor <;> omega

end PottsContinuity.RSW
