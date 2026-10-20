module

public import PottsContinuity.PD.Duality.RectanglePathIntersection

/-!
# Interlaced paths in the upper half-plane

Two paths with alternating endpoints on the boundary line intersect. The proof
extends them below that line to opposite-side crossings of a larger rectangle,
then uses the already proved rectangle path intersection theorem. No simple-path
or generic-position assumption is imposed on the original paths.
-/

@[expose] public section

namespace PottsContinuity.RSW

open Set unitInterval

/-- A straight segment stays in every coordinate rectangle containing its endpoints. -/
theorem segment_xy_bounds {a b z : ℝ × ℝ} {l r bot top : ℝ}
    (ha : l ≤ a.1 ∧ a.1 ≤ r ∧ bot ≤ a.2 ∧ a.2 ≤ top)
    (hb : l ≤ b.1 ∧ b.1 ≤ r ∧ bot ≤ b.2 ∧ b.2 ≤ top)
    (hz : z ∈ Set.range (Path.segment a b)) :
    l ≤ z.1 ∧ z.1 ≤ r ∧ bot ≤ z.2 ∧ z.2 ≤ top := by
  rw [Path.range_segment] at hz
  have hc : Convex ℝ (Set.Icc (l, bot) (r, top)) := convex_Icc _ _
  have h := hc.segment_subset ⟨⟨ha.1, ha.2.2.1⟩, ⟨ha.2.1, ha.2.2.2⟩⟩
    ⟨⟨hb.1, hb.2.2.1⟩, ⟨hb.2.1, hb.2.2.2⟩⟩ hz
  exact ⟨h.1.1, h.2.1, h.1.2, h.2.2⟩

/-- Strictly interlaced bottom endpoints force intersection for arbitrary
continuous paths confined to a bounded part of the upper half-plane. -/
theorem path_intersection_of_strict_interlacing
    (a b c d l r H : ℝ) (hab : a < b) (hbc : b < c) (hcd : c < d)
    (hla : l ≤ a) (hdr : d ≤ r) (hH : 0 ≤ H)
    (P : Path (a, (0 : ℝ)) (c, 0)) (Q : Path (b, (0 : ℝ)) (d, 0))
    (hP : ∀ z ∈ Set.range P, l ≤ z.1 ∧ z.1 ≤ r ∧ 0 ≤ z.2 ∧ z.2 ≤ H)
    (hQ : ∀ z ∈ Set.range Q, l ≤ z.1 ∧ z.1 ≤ r ∧ 0 ≤ z.2 ∧ z.2 ≤ H) :
    ∃ z, z ∈ Set.range P ∧ z ∈ Set.range Q := by
  let P' := (Path.segment (l - 1, (-2 : ℝ)) (a, -2)).trans
    ((Path.segment (a, (-2 : ℝ)) (a, 0)).trans
      (P.trans ((Path.segment (c, (0 : ℝ)) (c, -2)).trans
        (Path.segment (c, (-2 : ℝ)) (r + 1, -2)))))
  let Q' := (Path.segment (b, (-3 : ℝ)) (b, 0)).trans
    (Q.trans ((Path.segment (d, (0 : ℝ)) (d, -1)).trans
      ((Path.segment (d, (-1 : ℝ)) (r + 1 / 2, -1)).trans
        (Path.segment (r + 1 / 2, (-1 : ℝ)) (r + 1 / 2, H + 1)))))
  have hpdesc (z : ℝ × ℝ) (hz : z ∈ Set.range P') :
      z ∈ Set.range P ∨
      (z.2 = -2 ∧ z.1 ≤ a) ∨
      (z.1 = a ∧ -2 ≤ z.2 ∧ z.2 ≤ 0) ∨
      (z.1 = c ∧ -2 ≤ z.2 ∧ z.2 ≤ 0) ∨
      (z.2 = -2 ∧ c ≤ z.1) := by
    simp only [P', Path.trans_range, Set.mem_union] at hz
    rcases hz with hz | hz | hz | hz | hz
    · have h := segment_xy_bounds (l := l - 1) (r := a) (bot := -2) (top := -2)
        (by dsimp; refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith) (by dsimp; refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith) hz
      exact Or.inr (Or.inl ⟨by linarith, h.2.1⟩)
    · have h := segment_xy_bounds (l := a) (r := a) (bot := -2) (top := 0)
        (by norm_num) (by norm_num) hz
      exact Or.inr (Or.inr (Or.inl ⟨by linarith, h.2.2⟩))
    · exact Or.inl hz
    · have h := segment_xy_bounds (l := c) (r := c) (bot := -2) (top := 0)
        (by norm_num) (by norm_num) hz
      exact Or.inr (Or.inr (Or.inr (Or.inl ⟨by linarith, h.2.2⟩)))
    · have h := segment_xy_bounds (l := c) (r := r + 1) (bot := -2) (top := -2)
        (by dsimp; refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith) (by dsimp; refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith) hz
      exact Or.inr (Or.inr (Or.inr (Or.inr ⟨by linarith, h.1⟩)))
  have hqdesc (z : ℝ × ℝ) (hz : z ∈ Set.range Q') :
      z ∈ Set.range Q ∨
      (z.1 = b ∧ -3 ≤ z.2 ∧ z.2 ≤ 0) ∨
      (z.1 = d ∧ -1 ≤ z.2 ∧ z.2 ≤ 0) ∨
      (z.2 = -1 ∧ d ≤ z.1) ∨
      (z.1 = r + 1 / 2 ∧ -1 ≤ z.2) := by
    simp only [Q', Path.trans_range, Set.mem_union] at hz
    rcases hz with hz | hz | hz | hz | hz
    · have h := segment_xy_bounds (l := b) (r := b) (bot := -3) (top := 0)
        (by norm_num) (by norm_num) hz
      exact Or.inr (Or.inl ⟨by linarith, h.2.2⟩)
    · exact Or.inl hz
    · have h := segment_xy_bounds (l := d) (r := d) (bot := -1) (top := 0)
        (by norm_num) (by norm_num) hz
      exact Or.inr (Or.inr (Or.inl ⟨by linarith, h.2.2⟩))
    · have h := segment_xy_bounds (l := d) (r := r + 1 / 2) (bot := -1) (top := -1)
        (by dsimp; refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith) (by dsimp; refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith) hz
      exact Or.inr (Or.inr (Or.inr (Or.inl ⟨by linarith, h.1⟩)))
    · have h := segment_xy_bounds (l := r + 1 / 2) (r := r + 1 / 2)
        (bot := -1) (top := H + 1)
        (by dsimp; refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith) (by dsimp; refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith) hz
      exact Or.inr (Or.inr (Or.inr (Or.inr ⟨by linarith, h.2.2.1⟩)))
  have hpbox : ∀ z ∈ Set.range P',
      l - 1 ≤ z.1 ∧ z.1 ≤ r + 1 ∧ -3 ≤ z.2 ∧ z.2 ≤ H + 1 := by
    intro z hz
    simp only [P', Path.trans_range, Set.mem_union] at hz
    rcases hz with hz | hz | hz | hz | hz
    all_goals first
      | (have h := hP z hz; refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith)
      | (apply segment_xy_bounds (hz := hz) <;> dsimp <;> refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith)
  have hqbox : ∀ z ∈ Set.range Q',
      l - 1 ≤ z.1 ∧ z.1 ≤ r + 1 ∧ -3 ≤ z.2 ∧ z.2 ≤ H + 1 := by
    intro z hz
    simp only [Q', Path.trans_range, Set.mem_union] at hz
    rcases hz with hz | hz | hz | hz | hz
    all_goals first
      | (have h := hQ z hz; refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith)
      | (apply segment_xy_bounds (hz := hz) <;> dsimp <;> refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith)
  obtain ⟨s, t, heq⟩ := PD.FK.Curves.pathRectangle_crossing_intersection
    (a := (l - 1, (-3 : ℝ))) (b := (r + 1, H + 1)) P' Q'
    (by dsimp; linarith) (by dsimp; linarith)
    (fun s => hpbox _ ⟨s, rfl⟩) (fun t => hqbox _ ⟨t, rfl⟩)
    (by simp [P']) (by simp [P']) (by simp [Q']) (by simp [Q'])
  let z := P' s
  have hzp : z ∈ Set.range P' := ⟨s, rfl⟩
  have hzq : z ∈ Set.range Q' := ⟨t, heq.symm⟩
  have hzn : 0 ≤ z.2 := by
    by_contra hn
    have hn' : z.2 < 0 := lt_of_not_ge hn
    rcases hpdesc z hzp with h | h | h | h | h
    · exact (not_lt_of_ge (hP z h).2.2.1) hn'
    all_goals rcases hqdesc z hzq with hq | hq | hq | hq | hq
    all_goals first
      | (exact (not_lt_of_ge (hQ z hq).2.2.1) hn')
      | (rcases h with ⟨h1, h2⟩; rcases hq with ⟨h3, h4⟩; linarith)
  have hporig : z ∈ Set.range P := by
    rcases hpdesc z hzp with h | h | h | h | h
    · exact h
    · exfalso; linarith [h.1]
    · have he : z = (a, 0) := Prod.ext h.1 (by linarith [h.2.2])
      exact he.symm ▸ (show (a, (0 : ℝ)) ∈ Set.range P from ⟨0, by simp⟩)
    · have he : z = (c, 0) := Prod.ext h.1 (by linarith [h.2.2])
      exact he.symm ▸ (show (c, (0 : ℝ)) ∈ Set.range P from ⟨1, by simp⟩)
    · exfalso; linarith [h.1]
  refine ⟨z, hporig, ?_⟩
  have hzx := (hP z hporig).2.1
  rcases hqdesc z hzq with h | h | h | h | h
  · exact h
  · have he : z = (b, 0) := Prod.ext h.1 (by linarith [h.2.2])
    exact he.symm ▸ (show (b, (0 : ℝ)) ∈ Set.range Q from ⟨0, by simp⟩)
  · have he : z = (d, 0) := Prod.ext h.1 (by linarith [h.2.2])
    exact he.symm ▸ (show (d, (0 : ℝ)) ∈ Set.range Q from ⟨1, by simp⟩)
  · exfalso; linarith [h.1]
  · exfalso; linarith [h.1]

end PottsContinuity.RSW
