module

public import PottsContinuity.PlanarTopology.ContinuousThreeArc

@[expose] public section

namespace PottsContinuity.Push
open PottsContinuity.PlanarTopology
noncomputable section

/-- A bottom-to-top curve meets every curve joining the complementary left
and right boundary arcs around its starting point. The top endpoint is free
to lie anywhere on the top side. -/
theorem interval_arm_complementary_curves_intersect
    (l r b t : ℝ) {s u x y : ℝ × ℝ} (P : Path s u) (Q : Path x y)
    (hP : ∀ z ∈ Set.range P, l ≤ z.1 ∧ z.1 ≤ r ∧ b ≤ z.2 ∧ z.2 ≤ t)
    (hQ : ∀ z ∈ Set.range Q, l ≤ z.1 ∧ z.1 ≤ r ∧ b ≤ z.2 ∧ z.2 ≤ t)
    (hs : s.2 = b) (hu : u.2 = t)
    (hx : x.1 < s.1 ∧ (x.1 = l ∨ x.2 = b))
    (hy : s.1 < y.1 ∧ (y.1 = r ∨ y.2 = b)) :
    ∃ z, z ∈ Set.range P ∧ z ∈ Set.range Q := by
  have hsB := hP s P.source_mem_range
  have huB := hP u P.target_mem_range
  let a : ℝ × ℝ := (s.1,t+1)
  let c : ℝ × ℝ := (u.1,t+1)
  let W : Path a s := (Path.segment a c).trans ((Path.segment c u).trans P.symm)
  have haB : l ≤ a.1 ∧ a.1 ≤ r ∧ b ≤ a.2 ∧ a.2 ≤ t+1 :=
    ⟨hsB.1,hsB.2.1,by dsimp [a]; linarith [hsB.2.2.1,hsB.2.2.2],le_rfl⟩
  have hcB : l ≤ c.1 ∧ c.1 ≤ r ∧ b ≤ c.2 ∧ c.2 ≤ t+1 :=
    ⟨huB.1,huB.2.1,by dsimp [c]; linarith [huB.2.2.1,huB.2.2.2],le_rfl⟩
  have huB' : l ≤ u.1 ∧ u.1 ≤ r ∧ b ≤ u.2 ∧ u.2 ≤ t+1 :=
    ⟨huB.1,huB.2.1,huB.2.2.1,by linarith [huB.2.2.2]⟩
  have hW : ∀ z ∈ Set.range W, l ≤ z.1 ∧ z.1 ≤ r ∧ b ≤ z.2 ∧ z.2 ≤ t+1 := by
    intro z hz
    change z ∈ Set.range ((Path.segment a c).trans ((Path.segment c u).trans P.symm)) at hz
    rw [Path.trans_range,Path.trans_range,Path.symm_range] at hz
    rcases hz with hz | hz | hz
    · exact pair_segment_box haB hcB hz
    · exact pair_segment_box hcB huB' hz
    · have h := hP z hz
      exact ⟨h.1,h.2.1,h.2.2.1,by linarith [h.2.2.2]⟩
  obtain ⟨z,hzW,hzQ⟩ := continuous_three_arc_paths_intersect l r b (t+1) s.1 s.1 W Q
    hW (fun z hz => ⟨(hQ z hz).1,(hQ z hz).2.1,(hQ z hz).2.2.1,
      by linarith [(hQ z hz).2.2.2]⟩)
    rfl hs ⟨le_rfl,le_rfl⟩ ⟨le_rfl,le_rfl⟩
    ⟨hx.1,hx.2.elim (fun h => Or.inl h) (fun h => Or.inr (Or.inl h))⟩
    ⟨hy.1,hy.2.elim (fun h => Or.inl h) (fun h => Or.inr (Or.inl h))⟩
  refine ⟨z,?_,hzQ⟩
  change z ∈ Set.range ((Path.segment a c).trans ((Path.segment c u).trans P.symm)) at hzW
  rw [Path.trans_range,Path.trans_range,Path.symm_range] at hzW
  rcases hzW with hz | hz | hz
  · have hzTop := pair_segment_box (l := l) (r := r) (b := t+1) (u := t+1)
      ⟨haB.1,haB.2.1,le_rfl,le_rfl⟩ ⟨hcB.1,hcB.2.1,le_rfl,le_rfl⟩ hz
    linarith [hzTop.2.2.1,(hQ z hzQ).2.2.2]
  · have hzLine := pair_segment_box (l := u.1) (r := u.1) (b := t) (u := t+1)
      (s := c) (t := u)
      ⟨le_rfl,le_rfl,by dsimp [c]; linarith,le_rfl⟩
      ⟨le_rfl,le_rfl,by rw [hu],by rw [hu]; linarith⟩ hz
    have heq : z = u := Prod.ext (by linarith [hzLine.1,hzLine.2.1])
      (by linarith [hzLine.2.2.1,(hQ z hzQ).2.2.2])
    exact heq ▸ P.target_mem_range
  · exact hz

end
end PottsContinuity.Push
