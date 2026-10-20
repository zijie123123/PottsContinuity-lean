module

public import PottsContinuity.PlanarTopology.ContinuousBoundaryExtension

@[expose] public section

namespace PottsContinuity.PlanarTopology
noncomputable section

private theorem segment_parameter {s t z : ℝ × ℝ}
    (hz : z ∈ Set.range (Path.segment s t)) :
    ∃ θ : ℝ, 0 ≤ θ ∧ θ ≤ 1 ∧
      z.1 = (1-θ)*s.1+θ*t.1 ∧ z.2 = (1-θ)*s.2+θ*t.2 := by
  rw [Path.range_segment,segment_eq_image] at hz
  obtain ⟨θ,hθ,rfl⟩ := hz
  exact ⟨θ,hθ.1,hθ.2,rfl,rfl⟩

/-- An exterior approach from the lower expanded row to a left-side point
stays strictly below the height of the left primal mark. -/
theorem lower_left_boundary_extension (l r b t uy : ℝ) (c : ℝ × ℝ)
    (hc : l ≤ c.1 ∧ c.1 ≤ r ∧ b ≤ c.2 ∧ c.2 ≤ t)
    (hx : c.1 = l) (hy : c.2 < uy) :
    ∃ s : ℝ × ℝ, ∃ L : Path s c, s.2 = b-1 ∧
      (∀ z ∈ Set.range L, l-1 ≤ z.1 ∧ z.1 ≤ r+1 ∧ b-1 ≤ z.2 ∧ z.2 ≤ t+1) ∧
      ∀ z ∈ Set.range L, z = c ∨ z.1 < l ∧ z.2 < uy := by
  let k : ℝ × ℝ := (l-1,c.2)
  refine ⟨(l-1,b-1),(Path.segment (l-1,b-1) k).trans (Path.segment k c),rfl,?_,?_⟩
  · intro z hz
    rw [Path.trans_range] at hz
    rcases hz with hz | hz
    all_goals
      apply pair_segment_box _ _ hz <;>
        refine ⟨?_,?_,?_,?_⟩ <;>
        (try dsimp only [k,Prod.fst,Prod.snd]) <;>
        linarith [hc.1,hc.2.1,hc.2.2.1,hc.2.2.2]
  · intro z hz
    rw [Path.trans_range] at hz
    rcases hz with hz | hz
    · have hh := pair_segment_box
        (l := l-1) (r := l-1) (b := b-1) (u := c.2)
        (s := (l-1,b-1)) (t := k)
        ⟨le_rfl,le_rfl,le_rfl,by linarith [hc.2.2.1]⟩
        ⟨le_rfl,le_rfl,by change b-1 ≤ c.2; linarith [hc.2.2.1],le_rfl⟩ hz
      exact Or.inr ⟨by linarith [hh.2.1],by linarith [hh.2.2.2]⟩
    · obtain ⟨θ,h0,h1,hzx,hzy⟩ := segment_parameter hz
      dsimp [k] at hzx hzy
      by_cases hθ : θ = 1
      · left; apply Prod.ext <;> nlinarith
      · have hθlt : θ < 1 := lt_of_le_of_ne h1 hθ
        exact Or.inr ⟨by rw [hx] at hzx; nlinarith,by nlinarith⟩

/-- A lower complementary-arc point can be approached from the expanded
bottom without entering the rectangle or either primal endpoint spoke. -/
theorem lower_boundary_arc_extension (l r b t uy vy : ℝ) (c : ℝ × ℝ)
    (hc : l ≤ c.1 ∧ c.1 ≤ r ∧ b ≤ c.2 ∧ c.2 ≤ t)
    (hArc : c.2 = b ∨ (c.1 = l ∧ c.2 < uy) ∨ (c.1 = r ∧ c.2 < vy)) :
    ∃ s : ℝ × ℝ, ∃ L : Path s c, s.2 = b-1 ∧
      (∀ z ∈ Set.range L, l-1 ≤ z.1 ∧ z.1 ≤ r+1 ∧ b-1 ≤ z.2 ∧ z.2 ≤ t+1) ∧
      ∀ z ∈ Set.range L, z = c ∨ z.2 < b ∨
        (z.1 < l ∧ z.2 < uy) ∨ (r < z.1 ∧ z.2 < vy) := by
  rcases hArc with hb | ⟨hx,hy⟩ | ⟨hx,hy⟩
  · refine ⟨(c.1,b-1),Path.segment _ _,rfl,?_,?_⟩
    · intro z hz
      apply pair_segment_box _ _ hz <;>
        refine ⟨by linarith [hc.1],by linarith [hc.2.1],
          by linarith [hc.2.2.1],by linarith [hc.2.2.2]⟩
    · intro z hz
      obtain ⟨θ,h0,h1,hzx,hzy⟩ := segment_parameter hz
      dsimp at hzx hzy
      by_cases hθ : θ = 1
      · left; apply Prod.ext <;> nlinarith
      · have hθlt : θ < 1 := lt_of_le_of_ne h1 hθ
        right; left
        rw [hb] at hzy
        nlinarith
  · obtain ⟨s,L,hs,hL,hOut⟩ := lower_left_boundary_extension l r b t uy c hc hx hy
    exact ⟨s,L,hs,hL,fun z hz => (hOut z hz).imp_right (fun h => Or.inr (Or.inl h))⟩
  · let f : ℝ × ℝ → ℝ × ℝ := fun z => (-z.1,z.2)
    have hf : Continuous f := by fun_prop
    have hfc : -r ≤ (f c).1 ∧ (f c).1 ≤ -l ∧ b ≤ (f c).2 ∧ (f c).2 ≤ t :=
      ⟨by dsimp [f]; linarith [hc.2.1],by dsimp [f]; linarith [hc.1],hc.2.2⟩
    obtain ⟨s,L,hs,hL,hOut⟩ := lower_left_boundary_extension (-r) (-l) b t vy (f c) hfc
      (by dsimp [f]; rw [hx]) hy
    have hcc : c = f (f c) := by ext <;> simp [f]
    let R : Path (f s) c := (L.map hf).cast rfl hcc
    refine ⟨f s,R,hs,?_,?_⟩
    · rintro z ⟨a,rfl⟩
      have hh := hL _ ⟨a,rfl⟩
      change l-1 ≤ -(L a).1 ∧ -(L a).1 ≤ r+1 ∧ b-1 ≤ (L a).2 ∧ (L a).2 ≤ t+1
      exact ⟨by linarith [hh.2.1],by linarith [hh.1],hh.2.2⟩
    · rintro z ⟨a,rfl⟩
      change f (L a) = c ∨ (L a).2 < b ∨
        (-(L a).1 < l ∧ (L a).2 < uy) ∨ (r < -(L a).1 ∧ (L a).2 < vy)
      rcases hOut _ ⟨a,rfl⟩ with he | ⟨hleft,hlow⟩
      · left; rw [he]; exact hcc.symm
      · exact Or.inr (Or.inr (Or.inr ⟨by linarith,hlow⟩))

end
end PottsContinuity.PlanarTopology
