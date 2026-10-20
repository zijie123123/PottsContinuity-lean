module

public import PottsContinuity.PlanarTopology.UpperBoundaryArcExtension

@[expose] public section

namespace PottsContinuity.PlanarTopology
noncomputable section

/-- A left-to-right path meets a path between the complementary lower and
upper boundary arcs. Each side arc is cut at its OWN primal endpoint height;
paths may revisit any boundary point and need not be simple. -/
theorem rectangle_boundary_arc_paths_intersect (l r b t : ℝ) {a d u v : ℝ × ℝ}
    (P : Path a d) (Q : Path u v) (hlr : l ≤ r)
    (hP : ∀ z ∈ Set.range P, l ≤ z.1 ∧ z.1 ≤ r ∧ b ≤ z.2 ∧ z.2 ≤ t)
    (hQ : ∀ z ∈ Set.range Q, l ≤ z.1 ∧ z.1 ≤ r ∧ b ≤ z.2 ∧ z.2 ≤ t)
    (ha : a.1 = l) (hd : d.1 = r)
    (hu : u.2 = b ∨ (u.1 = l ∧ u.2 < a.2) ∨ (u.1 = r ∧ u.2 < d.2))
    (hv : v.2 = t ∨ (v.1 = l ∧ a.2 < v.2) ∨ (v.1 = r ∧ d.2 < v.2)) :
    ∃ z, z ∈ Set.range P ∧ z ∈ Set.range Q := by
  by_contra hn
  have haB := hP a P.source_mem_range
  have hdB := hP d P.target_mem_range
  obtain ⟨s,L,hs,hL,hLo⟩ := lower_boundary_arc_extension l r b t a.2 d.2 u
    (hQ u Q.source_mem_range) hu
  obtain ⟨w,U,hw,hU,hUo⟩ := upper_boundary_arc_extension l r b t a.2 d.2 v
    (hQ v Q.target_mem_range) hv
  let A : ℝ × ℝ := (l-1,a.2)
  let D : ℝ × ℝ := (r+1,d.2)
  let P' : Path A D := (Path.segment A a).trans (P.trans (Path.segment d D))
  let Q' : Path s w := L.trans (Q.trans U.symm)
  have hwide : ∀ z ∈ Set.range P',
      (l-1 ≤ z.1 ∧ z.1 ≤ r+1 ∧ b ≤ z.2 ∧ z.2 ≤ t) ∧
      (z ∈ Set.range P ∨ (z.1 ≤ l ∧ z.2 = a.2) ∨ (r ≤ z.1 ∧ z.2 = d.2)) := by
    intro z hz
    change z ∈ Set.range ((Path.segment A a).trans (P.trans (Path.segment d D))) at hz
    rw [Path.trans_range,Path.trans_range] at hz
    rcases hz with hz | hz | hz
    · have hh := pair_segment_box (l := l-1) (r := l) (b := a.2) (u := a.2)
        (s := A) (t := a) ⟨le_rfl,by dsimp [A]; linarith,le_rfl,le_rfl⟩
        ⟨by linarith [ha],ha.le,le_rfl,le_rfl⟩ hz
      have hy : z.2 = a.2 := le_antisymm hh.2.2.2 hh.2.2.1
      exact ⟨⟨hh.1,by linarith [hh.2.1],by rw [hy]; exact haB.2.2.1,
        by rw [hy]; exact haB.2.2.2⟩,Or.inr (Or.inl ⟨hh.2.1,hy⟩)⟩
    · have hh := hP z hz
      exact ⟨⟨by linarith [hh.1],by linarith [hh.2.1],hh.2.2⟩,Or.inl hz⟩
    · have hh := pair_segment_box (l := r) (r := r+1) (b := d.2) (u := d.2)
        (s := d) (t := D) ⟨hd.ge,by linarith [hd],le_rfl,le_rfl⟩
        ⟨by dsimp [D]; linarith,le_rfl,le_rfl,le_rfl⟩ hz
      have hy : z.2 = d.2 := le_antisymm hh.2.2.2 hh.2.2.1
      exact ⟨⟨by linarith [hh.1],hh.2.1,by rw [hy]; exact hdB.2.2.1,
        by rw [hy]; exact hdB.2.2.2⟩,Or.inr (Or.inr ⟨hh.1,hy⟩)⟩
  have hleft : ∀ z ∈ Set.range P', z.1 < l → z.2 = a.2 := by
    intro z hz hzl
    rcases (hwide z hz).2 with hzP | ⟨_,hy⟩ | ⟨hx,_⟩
    · exact (not_lt_of_ge (hP z hzP).1 hzl).elim
    · exact hy
    · linarith
  have hright : ∀ z ∈ Set.range P', r < z.1 → z.2 = d.2 := by
    intro z hz hzr
    rcases (hwide z hz).2 with hzP | ⟨hx,_⟩ | ⟨_,hy⟩
    · exact (not_lt_of_ge (hP z hzP).2.1 hzr).elim
    · linarith
    · exact hy
  have hdisQ : Disjoint (Set.range P') (Set.range Q) := by
    apply Set.disjoint_left.mpr
    intro z hz hzQ
    rcases (hwide z hz).2 with hzP | ⟨hx,hy⟩ | ⟨hx,hy⟩
    · exact hn ⟨z,hzP,hzQ⟩
    · have he : z = a := Prod.ext (by linarith [(hQ z hzQ).1]) hy
      exact hn ⟨a,P.source_mem_range,he ▸ hzQ⟩
    · have he : z = d := Prod.ext (by linarith [(hQ z hzQ).2.1]) hy
      exact hn ⟨d,P.target_mem_range,he ▸ hzQ⟩
  have hdisL : Disjoint (Set.range P') (Set.range L) := by
    apply Set.disjoint_left.mpr
    intro z hz hzL
    rcases hLo z hzL with he | hy | ⟨hx,hy⟩ | ⟨hx,hy⟩
    · exact Set.disjoint_left.mp hdisQ hz (he.symm ▸ Q.source_mem_range)
    · linarith [(hwide z hz).1.2.2.1]
    · have he := hleft z hz hx; linarith
    · have he := hright z hz hx; linarith
  have hdisU : Disjoint (Set.range P') (Set.range U) := by
    apply Set.disjoint_left.mpr
    intro z hz hzU
    rcases hUo z hzU with he | hy | ⟨hx,hy⟩ | ⟨hx,hy⟩
    · exact Set.disjoint_left.mp hdisQ hz (he.symm ▸ Q.target_mem_range)
    · linarith [(hwide z hz).1.2.2.2]
    · have he := hleft z hz hx; linarith
    · have he := hright z hz hx; linarith
  have hPbox : ∀ θ, l-1 ≤ (P' θ).1 ∧ (P' θ).1 ≤ r+1 ∧ b-1 ≤ (P' θ).2 ∧ (P' θ).2 ≤ t+1 := by
    intro θ
    have hh := (hwide _ ⟨θ,rfl⟩).1
    exact ⟨hh.1,hh.2.1,by linarith [hh.2.2.1],by linarith [hh.2.2.2]⟩
  have hQbox : ∀ θ, l-1 ≤ (Q' θ).1 ∧ (Q' θ).1 ≤ r+1 ∧ b-1 ≤ (Q' θ).2 ∧ (Q' θ).2 ≤ t+1 := by
    intro θ
    have hz : Q' θ ∈ Set.range L ∪ (Set.range Q ∪ Set.range U) := by
      simpa only [Q',Path.trans_range,Path.symm_range] using
        (show Q' θ ∈ Set.range Q' from ⟨θ,rfl⟩)
    rcases hz with hz | hz | hz
    · exact hL _ hz
    · have hh := hQ _ hz
      exact ⟨by linarith [hh.1],by linarith [hh.2.1],by linarith [hh.2.2.1],by linarith [hh.2.2.2]⟩
    · exact hU _ hz
  obtain ⟨α,β,he⟩ := PD.FK.Curves.pathRectangle_crossing_intersection
    (a := (l-1,b-1)) (b := (r+1,t+1)) P' Q' (by dsimp; linarith)
    (by dsimp; linarith [haB.2.2.1,haB.2.2.2]) hPbox hQbox
    (by simpa only [A] using congrArg Prod.fst P'.source)
    (by simpa only [D] using congrArg Prod.fst P'.target)
    ((congrArg Prod.snd Q'.source).trans hs) ((congrArg Prod.snd Q'.target).trans hw)
  have hzP : Q' β ∈ Set.range P' := ⟨α,he⟩
  have hzQ : Q' β ∈ Set.range L ∪ (Set.range Q ∪ Set.range U) := by
    simpa only [Q',Path.trans_range,Path.symm_range] using
      (show Q' β ∈ Set.range Q' from ⟨β,rfl⟩)
  rcases hzQ with hz | hz | hz
  · exact Set.disjoint_left.mp hdisL hzP hz
  · exact Set.disjoint_left.mp hdisQ hzP hz
  · exact Set.disjoint_left.mp hdisU hzP hz

end
end PottsContinuity.PlanarTopology
