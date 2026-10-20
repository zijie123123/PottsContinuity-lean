module

public import PottsContinuity.PlanarMixed.FiniteSlit.Domain

/-! Exact finite slit corners and the excluded terminal crossing bond.
These record the lattice offsets needed by the Case 2 Omega comparison. -/

@[expose] public section

namespace PottsContinuity.PlanarMixed.FiniteSlit
open PD.FK PD.FK.Medial BD12
noncomputable section

/-- The wired right endpoint of the same physical tip bond. -/
def rightTip (M : ℕ) (x y : ℤ) (hM : 2 ≤ M) (hy : 0 < y) (hyM : y < (M : ℤ)) :
    Vertex M x :=
  ⟨(x,y),(mem_rectangle_iff M x (by omega) _).mpr ⟨by omega,by omega,hy.le,hyM.le⟩⟩

theorem rightTip_mem_beta (M : ℕ) (x y : ℤ)
    (hM : 2 ≤ M) (hy : 0 < y) (hyM : y < (M : ℤ)) :
    rightTip M x y hM hy hyM ∈ beta M x y := Or.inr (Or.inr ⟨rfl,le_refl _⟩)

theorem dualBottom_subset_alpha (M : ℕ) (x : ℤ) : dualBottom M x ⊆ alpha M x := by
  rintro v ⟨h0,_,hx⟩
  exact Or.inl ⟨h0,by omega⟩

theorem dualRay_subset_beta (M : ℕ) (x y : ℤ) : dualRay M x y ⊆ beta M x y := by
  rintro v ⟨hx,hy⟩
  exact Or.inr (Or.inr ⟨hx,by omega⟩)

/-- A fixed slightly larger box strictly contains the whole source square,
so none of its three outer sides meets the source Omega domain. -/
theorem sourceSquare_strictly_inside (n : ℕ) (x : ℤ)
    (hx0 : 0 ≤ x) (hxn : x ≤ (2*n : ℕ)) (z : LatticeVertex)
    (hz : z ∈ PD.FK.latticeRectangle (0,0) (2*n) (2*n)) :
    x-((2*n+2 : ℕ) : ℤ) < z.1 ∧ z.1 < x+((2*n+2 : ℕ) : ℤ)-1 ∧
      0 ≤ z.2 ∧ z.2 < ((2*n+2 : ℕ) : ℤ) := by
  have h := (PD.FK.mem_latticeRectangle _ _ _ _).mp hz
  simp only [zero_add] at h
  simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] at hxn ⊢
  omega

/-- Source placement in that fixed finite box, with no limit or extra case. -/
theorem sourceSquare_subset_box (n : ℕ) (x : ℤ)
    (hx0 : 0 ≤ x) (hxn : x ≤ (2*n : ℕ)) :
    (PD.FK.latticeRectangle (0,0) (2*n) (2*n) : Set LatticeVertex) ⊆
      PD.FK.latticeRectangle (x-((2*n+2 : ℕ) : ℤ),0) (2*(2*n+2)-1) (2*n+2) := by
  intro z hz
  have hs := sourceSquare_strictly_inside n x hx0 hxn z hz
  exact (mem_rectangle_iff (2*n+2) x (by omega) z).mpr
    ⟨hs.1.le,hs.2.1.le,hs.2.2.1,hs.2.2.2.le⟩

end
end PottsContinuity.PlanarMixed.FiniteSlit
