module

public import PottsContinuity.PlanarTopology.LowerBoundaryArcExtension

@[expose] public section

namespace PottsContinuity.PlanarTopology
noncomputable section

/-- An upper complementary-arc point admits the reflected exterior approach
from the expanded top row, above the two respective primal endpoint spokes. -/
theorem upper_boundary_arc_extension (l r b t uy vy : ℝ) (c : ℝ × ℝ)
    (hc : l ≤ c.1 ∧ c.1 ≤ r ∧ b ≤ c.2 ∧ c.2 ≤ t)
    (hArc : c.2 = t ∨ (c.1 = l ∧ uy < c.2) ∨ (c.1 = r ∧ vy < c.2)) :
    ∃ s : ℝ × ℝ, ∃ U : Path s c, s.2 = t+1 ∧
      (∀ z ∈ Set.range U, l-1 ≤ z.1 ∧ z.1 ≤ r+1 ∧ b-1 ≤ z.2 ∧ z.2 ≤ t+1) ∧
      ∀ z ∈ Set.range U, z = c ∨ t < z.2 ∨
        (z.1 < l ∧ uy < z.2) ∨ (r < z.1 ∧ vy < z.2) := by
  let f : ℝ × ℝ → ℝ × ℝ := fun z => (z.1,-z.2)
  have hf : Continuous f := by fun_prop
  have hfc : l ≤ (f c).1 ∧ (f c).1 ≤ r ∧ -t ≤ (f c).2 ∧ (f c).2 ≤ -b :=
    ⟨hc.1,hc.2.1,by dsimp [f]; linarith [hc.2.2.2],by dsimp [f]; linarith [hc.2.2.1]⟩
  have hArc' : (f c).2 = -t ∨ ((f c).1 = l ∧ (f c).2 < -uy) ∨
      ((f c).1 = r ∧ (f c).2 < -vy) := by
    rcases hArc with h | ⟨hx,hy⟩ | ⟨hx,hy⟩
    · left; dsimp [f]; rw [h]
    · exact Or.inr (Or.inl ⟨hx,by dsimp [f]; linarith⟩)
    · exact Or.inr (Or.inr ⟨hx,by dsimp [f]; linarith⟩)
  obtain ⟨s,L,hs,hL,hOut⟩ := lower_boundary_arc_extension l r (-t) (-b) (-uy) (-vy) (f c) hfc hArc'
  have hcc : c = f (f c) := by ext <;> simp [f]
  let U : Path (f s) c := (L.map hf).cast rfl hcc
  refine ⟨f s,U,by dsimp [f]; linarith,?_,?_⟩
  · rintro z ⟨a,rfl⟩
    have hh := hL _ ⟨a,rfl⟩
    change l-1 ≤ (L a).1 ∧ (L a).1 ≤ r+1 ∧ b-1 ≤ -(L a).2 ∧ -(L a).2 ≤ t+1
    exact ⟨hh.1,hh.2.1,by linarith [hh.2.2.2],by linarith [hh.2.2.1]⟩
  · rintro z ⟨a,rfl⟩
    change f (L a) = c ∨ t < -(L a).2 ∨
      ((L a).1 < l ∧ uy < -(L a).2) ∨ (r < (L a).1 ∧ vy < -(L a).2)
    rcases hOut _ ⟨a,rfl⟩ with he | hy | ⟨hx,hy⟩ | ⟨hx,hy⟩
    · left; rw [he]; exact hcc.symm
    · exact Or.inr (Or.inl (by linarith))
    · exact Or.inr (Or.inr (Or.inl ⟨hx,by linarith⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨hx,by linarith⟩))

end
end PottsContinuity.PlanarTopology
