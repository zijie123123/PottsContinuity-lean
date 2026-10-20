module

public import PottsContinuity.Thm3.RSW.Lemma4MiddleBandProduct

@[expose] public section

namespace PottsContinuity.RSW
open PD.FK
noncomputable section

/-- The original vertices on one side of the closed middle band. -/
def lemma4SideVertices (n : ℕ) (σ : ℤ) : Set {z : LatticeVertex // z ∈ box (56*n)} :=
  {v | 2*(n:ℤ) ≤ σ*v.val.2}

/-- The exact unobserved graph on a side carrier. In particular the already
recorded horizontal bonds on its base row are absent. -/
abbrev lemma4SideResidualGraph (n : ℕ) (σ : ℤ) :=
  (edgeRestriction (lemma4AmbientGraph n) (lemma4MiddleReveal n)).induce (lemma4SideVertices n σ)

/-- The original base row at which the middle record can induce wiring. -/
def lemma4SideBase (n : ℕ) (σ : ℤ) : Set (lemma4SideVertices n σ) :=
  {v | σ*v.val.val.2 = 2*(n:ℤ)}

/-- Every residual neighbour of a side vertex away from the base remains
inside that side. The claim is for each of the two actual orientations. -/
theorem lemma4SideResidual_closed (n : ℕ) (σ : ℤ) (hσ : σ = 1 ∨ σ = -1) :
    ∀ ⦃x : lemma4SideVertices n σ⦄, x ∉ lemma4SideBase n σ →
    ∀ ⦃y : {z : LatticeVertex // z ∈ box (56*n)}⦄,
      (edgeRestriction (lemma4AmbientGraph n) (lemma4MiddleReveal n)).Adj x.val y →
      ∃ z : lemma4SideVertices n σ, z.val = y ∧ (lemma4SideResidualGraph n σ).Adj x z := by
  intro x hx y hxy
  have hadj := edgeRestriction_le (lemma4AmbientGraph n) (lemma4MiddleReveal n) hxy
  change squareLattice.Adj x.val.val y.val at hadj
  have hcoord := (PD.FK.squareLattice_adj_iff _ _).mp hadj
  have hside : 2*(n:ℤ) ≤ σ*x.val.val.2 := x.property
  change σ*x.val.val.2 ≠ 2*(n:ℤ) at hx
  have hy : y ∈ lemma4SideVertices n σ := by
    change 2*(n:ℤ) ≤ σ*y.val.2
    rcases hσ with rfl | rfl
    · simp only [one_mul] at hside hx ⊢
      omega
    · simp only [neg_one_mul] at hside hx ⊢
      omega
  exact ⟨⟨y,hy⟩,rfl,hxy⟩

/-- Away from its base row, each actual side avoids every vertex touched by
the middle reveal. No law or path estimate is assumed. -/
theorem lemma4SideResidual_avoids_middle (n : ℕ) (σ : ℤ) (hσ : σ = 1 ∨ σ = -1) :
    ∀ ⦃x : lemma4SideVertices n σ⦄, x ∉ lemma4SideBase n σ →
      x.val ∉ lemma4MiddleVertices n := by
  intro x hx hm
  have hside : 2*(n:ℤ) ≤ σ*x.val.val.2 := x.property
  change σ*x.val.val.2 ≠ 2*(n:ℤ) at hx
  change |x.val.val.2| ≤ 2*(n:ℤ) at hm
  rw [abs_le] at hm
  rcases hσ with rfl | rfl
  · simp only [one_mul] at hside hx
    omega
  · simp only [neg_one_mul] at hside hx
    omega

end
end PottsContinuity.RSW
