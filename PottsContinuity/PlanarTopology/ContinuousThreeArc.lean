module

public import PottsContinuity.PlanarTopology.ContinuousBoundaryExtension

@[expose] public section

namespace PottsContinuity.PlanarTopology
noncomputable section

private theorem segment_fixed_fst {a b z : ℝ × ℝ} (hab : a.1 = b.1)
    (hz : z ∈ Set.range (Path.segment a b)) : z.1 = a.1 := by
  rw [Path.range_segment,segment_eq_image] at hz
  obtain ⟨θ,_,rfl⟩ := hz
  change (1-θ)*a.1+θ*b.1 = a.1
  rw [← hab]
  ring

/-- Continuous four-arc intersection in a rectangle, with the top and bottom
central targets disjoint from the complementary endpoint arcs. No injectivity
or lattice-path hypothesis is required for either curve. -/
theorem continuous_three_arc_paths_intersect
    (l r b t cL cR : ℝ) {a d u v : ℝ × ℝ}
    (p : Path a d) (q : Path u v)
    (hp : ∀ z ∈ Set.range p, l ≤ z.1 ∧ z.1 ≤ r ∧ b ≤ z.2 ∧ z.2 ≤ t)
    (hq : ∀ z ∈ Set.range q, l ≤ z.1 ∧ z.1 ≤ r ∧ b ≤ z.2 ∧ z.2 ≤ t)
    (ha : a.2 = t) (hd : d.2 = b)
    (hax : cL ≤ a.1 ∧ a.1 ≤ cR) (hdx : cL ≤ d.1 ∧ d.1 ≤ cR)
    (hu : u.1 < cL ∧ (u.1 = l ∨ u.2 = b ∨ u.2 = t))
    (hv : cR < v.1 ∧ (v.1 = r ∨ v.2 = b ∨ v.2 = t)) :
    ∃ z, z ∈ Set.range p ∧ z ∈ Set.range q := by
  by_contra hno
  have haB := hp a p.source_mem_range
  have hdB := hp d p.target_mem_range
  have huB := hq u q.source_mem_range
  have hvB := hq v q.target_mem_range
  obtain ⟨s,L,hs,hL,hLo⟩ := continuous_left_boundary_extension l r b t u huB hu.2
  obtain ⟨w,R,hw,hR,hRo⟩ := continuous_right_boundary_extension l r b t v hvB hv.2
  let A : ℝ × ℝ := (a.1,t+1)
  let D : ℝ × ℝ := (d.1,b-1)
  let P : Path A D := (Path.segment A a).trans (p.trans (Path.segment d D))
  let Q : Path s w := L.trans (q.trans R.symm)
  have hP : ∀ z ∈ Set.range P,
      (l ≤ z.1 ∧ z.1 ≤ r ∧ b-1 ≤ z.2 ∧ z.2 ≤ t+1) ∧
      (z ∈ Set.range p ∨ (cL ≤ z.1 ∧ z.1 ≤ cR) ∧ (z.2 < b ∨ t < z.2)) := by
    intro z hz
    change z ∈ Set.range ((Path.segment A a).trans (p.trans (Path.segment d D))) at hz
    rw [Path.trans_range,Path.trans_range] at hz
    rcases hz with hz | hz | hz
    · have hx : z.1 = a.1 := segment_fixed_fst (a := A) (b := a) rfl hz
      have hbox := pair_segment_box (l := l) (r := r) (b := b-1) (u := t+1)
        (s := A) (t := a)
        ⟨haB.1,haB.2.1,by dsimp [A]; linarith [haB.2.2.1],by dsimp [A]; rfl⟩
        ⟨haB.1,haB.2.1,by linarith [haB.2.2.1],by linarith [haB.2.2.2]⟩ hz
      refine ⟨hbox,?_⟩
      by_cases hzt : t < z.2
      · exact Or.inr ⟨hx ▸ hax,Or.inr hzt⟩
      · have hy := pair_segment_box (l := l) (r := r) (b := t) (u := t+1)
          (s := A) (t := a)
          ⟨haB.1,haB.2.1,by dsimp [A]; linarith,by dsimp [A]; rfl⟩
          ⟨haB.1,haB.2.1,by rw [ha],by rw [ha]; linarith⟩ hz
        have he : z = a := Prod.ext hx (by linarith [hy.2.2.1])
        exact Or.inl (he ▸ p.source_mem_range)
    · have hb := hp z hz
      exact ⟨⟨hb.1,hb.2.1,by linarith [hb.2.2.1],by linarith [hb.2.2.2]⟩,Or.inl hz⟩
    · have hx : z.1 = d.1 := segment_fixed_fst (a := d) (b := D) rfl hz
      have hbox := pair_segment_box (l := l) (r := r) (b := b-1) (u := t+1)
        (s := d) (t := D)
        ⟨hdB.1,hdB.2.1,by linarith [hdB.2.2.1],by linarith [hdB.2.2.2]⟩
        ⟨hdB.1,hdB.2.1,by dsimp [D]; rfl,by dsimp [D]; linarith [hdB.2.2.2]⟩ hz
      refine ⟨hbox,?_⟩
      by_cases hzb : z.2 < b
      · exact Or.inr ⟨hx ▸ hdx,Or.inl hzb⟩
      · have hy := pair_segment_box (l := l) (r := r) (b := b-1) (u := b)
          (s := d) (t := D)
          ⟨hdB.1,hdB.2.1,by rw [hd]; linarith,by rw [hd]⟩
          ⟨hdB.1,hdB.2.1,by dsimp [D]; rfl,by dsimp [D]; linarith⟩ hz
        have he : z = d := Prod.ext hx (by linarith [hy.2.2.2])
        exact Or.inl (he ▸ p.target_mem_range)
  have hQbox : ∀ z ∈ Set.range Q,
      l-1 ≤ z.1 ∧ z.1 ≤ r+1 ∧ b-1 ≤ z.2 ∧ z.2 ≤ t+1 := by
    intro z hz
    change z ∈ Set.range (L.trans (q.trans R.symm)) at hz
    rw [Path.trans_range,Path.trans_range,Path.symm_range] at hz
    rcases hz with hz | hz | hz
    · exact hL z hz
    · have h := hq z hz
      exact ⟨by linarith [h.1],by linarith [h.2.1],by linarith [h.2.2.1],
        by linarith [h.2.2.2]⟩
    · exact hR z hz
  have hdis : ∀ z ∈ Set.range P, z ∉ Set.range Q := by
    intro z hzP hzQ
    obtain ⟨hzBox,hzP⟩ := hP z hzP
    change z ∈ Set.range (L.trans (q.trans R.symm)) at hzQ
    rw [Path.trans_range,Path.trans_range,Path.symm_range] at hzQ
    rcases hzQ with hzL | hzQ | hzR
    · rcases hLo z hzL with he | he | ⟨hx,hy⟩
      · subst z
        rcases hzP with hzP | ⟨hx,_⟩
        · exact hno ⟨u,hzP,q.source_mem_range⟩
        · linarith [hu.1,hx.1]
      · linarith [hzBox.1]
      · rcases hzP with hzP | ⟨hc,_⟩
        · have hb := hp z hzP
          rcases hy with hy | hy <;> linarith [hb.2.2.1,hb.2.2.2]
        · linarith [hu.1,hc.1]
    · rcases hzP with hzP | ⟨_,hy⟩
      · exact hno ⟨z,hzP,hzQ⟩
      · have hb := hq z hzQ
        rcases hy with hy | hy <;> linarith [hb.2.2.1,hb.2.2.2]
    · rcases hRo z hzR with he | he | ⟨hx,hy⟩
      · subst z
        rcases hzP with hzP | ⟨hx,_⟩
        · exact hno ⟨v,hzP,q.target_mem_range⟩
        · linarith [hv.1,hx.2]
      · linarith [hzBox.2.1]
      · rcases hzP with hzP | ⟨hc,_⟩
        · have hb := hp z hzP
          rcases hy with hy | hy <;> linarith [hb.2.2.1,hb.2.2.2]
        · linarith [hv.1,hc.2]
  obtain ⟨s₀,t₀,hst⟩ := PD.FK.Curves.pathRectangle_crossing_intersection
    (a := (l-1,b-1)) (b := (r+1,t+1)) Q P.symm
    (by dsimp; linarith [haB.1,haB.2.1]) (by dsimp; linarith [haB.2.2.1,haB.2.2.2])
    (fun θ => hQbox _ ⟨θ,rfl⟩)
    (fun θ => by
      have hh := (hP _ (show P.symm θ ∈ Set.range P from
        (Path.symm_range P) ▸ ⟨θ,rfl⟩)).1
      exact ⟨by linarith [hh.1],by linarith [hh.2.1],hh.2.2⟩)
    (by simpa using (congrArg Prod.fst Q.source').trans hs)
    (by simpa using (congrArg Prod.fst Q.target').trans hw)
    (by simp [D]) (by simp [A])
  exact hdis _ ((Path.symm_range P) ▸ (show P.symm t₀ ∈ Set.range P.symm from ⟨t₀,rfl⟩))
    ⟨s₀,hst⟩

end
end PottsContinuity.PlanarTopology
