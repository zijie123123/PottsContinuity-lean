module

public import PottsContinuity.PD.Duality.RectanglePathIntersection

@[expose] public section

namespace PottsContinuity.PlanarTopology
noncomputable section

private theorem pair_segment_parameter {s t z : ℝ × ℝ}
    (hz : z ∈ Set.range (Path.segment s t)) :
    ∃ θ : ℝ, 0 ≤ θ ∧ θ ≤ 1 ∧
      z.1 = (1-θ)*s.1+θ*t.1 ∧ z.2 = (1-θ)*s.2+θ*t.2 := by
  rw [Path.range_segment,segment_eq_image] at hz
  obtain ⟨θ,hθ,rfl⟩ := hz
  exact ⟨θ,hθ.1,hθ.2,rfl,rfl⟩

/-- Straight real planar segments stay in every closed coordinate rectangle
containing their endpoints. -/
theorem pair_segment_box {s t z : ℝ × ℝ} {l r b u : ℝ}
    (hs : l ≤ s.1 ∧ s.1 ≤ r ∧ b ≤ s.2 ∧ s.2 ≤ u)
    (ht : l ≤ t.1 ∧ t.1 ≤ r ∧ b ≤ t.2 ∧ t.2 ≤ u)
    (hz : z ∈ Set.range (Path.segment s t)) :
    l ≤ z.1 ∧ z.1 ≤ r ∧ b ≤ z.2 ∧ z.2 ≤ u := by
  obtain ⟨θ,h0,h1,hx,hy⟩ := pair_segment_parameter hz
  constructor
  · nlinarith [hs.1,ht.1]
  constructor
  · nlinarith [hs.2.1,ht.2.1]
  constructor
  · nlinarith [hs.2.2.1,ht.2.2.1]
  · nlinarith [hs.2.2.2,ht.2.2.2]

/-- A continuous extension from the expanded left side to a point of the
left complementary three-piece boundary arc. Except at its endpoint it stays
outside the original rectangle, and never travels right of that endpoint. -/
theorem continuous_left_boundary_extension (l r b t : ℝ) (u : ℝ × ℝ)
    (hu : l ≤ u.1 ∧ u.1 ≤ r ∧ b ≤ u.2 ∧ u.2 ≤ t)
    (hb : u.1 = l ∨ u.2 = b ∨ u.2 = t) :
    ∃ s : ℝ × ℝ, ∃ L : Path s u, s.1 = l-1 ∧
      (∀ z ∈ Set.range L, l-1 ≤ z.1 ∧ z.1 ≤ r+1 ∧ b-1 ≤ z.2 ∧ z.2 ≤ t+1) ∧
      ∀ z ∈ Set.range L, z = u ∨ z.1 < l ∨
        (z.1 ≤ u.1 ∧ (z.2 < b ∨ t < z.2)) := by
  rcases hb with hx | hy | hy
  · refine ⟨(l-1,u.2),Path.segment _ _,rfl,?_,?_⟩
    · intro z hz
      apply pair_segment_box (s := (l-1,u.2)) (t := u) _ _ hz <;>
        constructor <;> first | linarith [hu.1,hu.2.1,hu.2.2.1,hu.2.2.2] |
          (constructor <;> first | linarith [hu.1,hu.2.1,hu.2.2.1,hu.2.2.2] |
            (constructor <;> linarith [hu.1,hu.2.1,hu.2.2.1,hu.2.2.2]))
    · intro z hz
      obtain ⟨θ,h0,h1,hzx,hzy⟩ := pair_segment_parameter hz
      dsimp at hzx hzy
      rw [hx] at hzx
      by_cases hθ : θ = 1
      · left
        apply Prod.ext <;> nlinarith
      · have hθlt : θ < 1 := lt_of_le_of_ne h1 hθ
        exact Or.inr (Or.inl (by nlinarith))
  · let c : ℝ × ℝ := (u.1,b-1)
    refine ⟨(l-1,b-1),(Path.segment (l-1,b-1) c).trans (Path.segment c u),rfl,?_,?_⟩
    · intro z hz
      rw [Path.trans_range] at hz
      rcases hz with hz | hz
      all_goals
        apply pair_segment_box _ _ hz <;>
          refine ⟨by linarith [hu.1],by linarith [hu.2.1],
            by linarith [hu.2.2.1],by linarith [hu.2.2.2]⟩
    · intro z hz
      rw [Path.trans_range] at hz
      rcases hz with hz | hz
      · obtain ⟨θ,h0,h1,hzx,hzy⟩ := pair_segment_parameter hz
        dsimp [c] at hzx hzy
        right; right
        constructor
        · nlinarith [hu.1]
        · left; nlinarith
      · obtain ⟨θ,h0,h1,hzx,hzy⟩ := pair_segment_parameter hz
        dsimp [c] at hzx hzy
        rw [hy] at hzy
        by_cases hθ : θ = 1
        · left; apply Prod.ext <;> nlinarith
        · have hθlt : θ < 1 := lt_of_le_of_ne h1 hθ
          right; right
          exact ⟨by nlinarith,Or.inl (by nlinarith)⟩
  · let c : ℝ × ℝ := (u.1,t+1)
    refine ⟨(l-1,t+1),(Path.segment (l-1,t+1) c).trans (Path.segment c u),rfl,?_,?_⟩
    · intro z hz
      rw [Path.trans_range] at hz
      rcases hz with hz | hz
      all_goals
        apply pair_segment_box _ _ hz <;>
          refine ⟨by linarith [hu.1],by linarith [hu.2.1],
            by linarith [hu.2.2.1],by linarith [hu.2.2.2]⟩
    · intro z hz
      rw [Path.trans_range] at hz
      rcases hz with hz | hz
      · obtain ⟨θ,h0,h1,hzx,hzy⟩ := pair_segment_parameter hz
        dsimp [c] at hzx hzy
        right; right
        constructor
        · nlinarith [hu.1]
        · right; nlinarith
      · obtain ⟨θ,h0,h1,hzx,hzy⟩ := pair_segment_parameter hz
        dsimp [c] at hzx hzy
        rw [hy] at hzy
        by_cases hθ : θ = 1
        · left; apply Prod.ext <;> nlinarith
        · have hθlt : θ < 1 := lt_of_le_of_ne h1 hθ
          right; right
          exact ⟨by nlinarith,Or.inr (by nlinarith)⟩

/-- The reflected continuous extension to the expanded right side. -/
theorem continuous_right_boundary_extension (l r b t : ℝ) (u : ℝ × ℝ)
    (hu : l ≤ u.1 ∧ u.1 ≤ r ∧ b ≤ u.2 ∧ u.2 ≤ t)
    (hb : u.1 = r ∨ u.2 = b ∨ u.2 = t) :
    ∃ s : ℝ × ℝ, ∃ R : Path s u, s.1 = r+1 ∧
      (∀ z ∈ Set.range R, l-1 ≤ z.1 ∧ z.1 ≤ r+1 ∧ b-1 ≤ z.2 ∧ z.2 ≤ t+1) ∧
      ∀ z ∈ Set.range R, z = u ∨ r < z.1 ∨
        (u.1 ≤ z.1 ∧ (z.2 < b ∨ t < z.2)) := by
  let f : ℝ × ℝ → ℝ × ℝ := fun z => (-z.1,z.2)
  have hf : Continuous f := by fun_prop
  have hfu : -r ≤ (f u).1 ∧ (f u).1 ≤ -l ∧ b ≤ (f u).2 ∧ (f u).2 ≤ t :=
    ⟨by dsimp [f]; linarith [hu.2.1],by dsimp [f]; linarith [hu.1],hu.2.2⟩
  have hfb : (f u).1 = -r ∨ (f u).2 = b ∨ (f u).2 = t := by
    rcases hb with hb | hb | hb
    · exact Or.inl (by dsimp [f]; rw [hb])
    · exact Or.inr (Or.inl hb)
    · exact Or.inr (Or.inr hb)
  obtain ⟨s,L,hs,hL,hLo⟩ := continuous_left_boundary_extension (-r) (-l) b t (f u) hfu hfb
  have huu : u = f (f u) := by ext <;> simp [f]
  let R : Path (f s) u := (L.map hf).cast rfl huu
  refine ⟨f s,R,by dsimp [f]; linarith,?_,?_⟩
  · rintro z ⟨θ,rfl⟩
    have hh := hL _ (show L θ ∈ Set.range L from ⟨θ,rfl⟩)
    change l-1 ≤ -(L θ).1 ∧ -(L θ).1 ≤ r+1 ∧ b-1 ≤ (L θ).2 ∧ (L θ).2 ≤ t+1
    exact ⟨by linarith [hh.2.1],by linarith [hh.1],hh.2.2⟩
  · rintro z ⟨θ,rfl⟩
    have hh := hLo _ (show L θ ∈ Set.range L from ⟨θ,rfl⟩)
    change f (L θ) = u ∨ r < -(L θ).1 ∨
      (u.1 ≤ -(L θ).1 ∧ ((L θ).2 < b ∨ t < (L θ).2))
    rcases hh with hh | hh | ⟨hx,hy⟩
    · left; rw [hh]; exact huu.symm
    · exact Or.inr (Or.inl (by linarith))
    · exact Or.inr (Or.inr ⟨by dsimp [f] at hx; linarith,hy⟩)

end
end PottsContinuity.PlanarTopology
