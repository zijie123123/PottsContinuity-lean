module

public import PottsContinuity.PlanarMixed.FiniteSlit.CanonicalSourceArms
public import PottsContinuity.Thm3.RSW.SlitCrosscutHit

@[expose] public section

namespace PottsContinuity.PlanarMixed.FiniteSlit
open PD.FK RSW
noncomputable section

/-- Disjoint bottom-to-right source walks force an actual first LEFT-slit
contact on every original rectangular carrier. No crop index is an input. -/
theorem disjoint_openSourceRectangle_firstContact_exists
    (w h : ℕ) (x B : ℤ) (hx : 1 ≤ x)
    (C : Configuration (rectangleGraph (0,0) w h))
    (D : SourceWalkPair (openGraph (rectangleGraph (0,0) w h) C))
    (ha : D.firstStart.val.2 = 0) (hb : D.secondStart.val.2 = 0)
    (hu : D.firstEnd.val.1 = B) (hv : D.secondEnd.val.1 = x)
    (hxa : x ≤ D.firstStart.val.1) (hab : D.firstStart.val.1 < D.secondStart.val.1)
    (hp : ∀ z ∈ D.first.support, z.val.1 ≤ B)
    (hq : ∀ z ∈ D.second.support, x ≤ z.val.1 ∧ z.val.1 ≤ B)
    (hdis : ∀ z ∈ D.first.support, z ∉ D.second.support) :
    ∃ k, IsFirstContact D.first
      {z | z.val.1 = x-1 ∧ D.secondEnd.val.2 ≤ z.val.2} k := by
  let φ : openGraph (rectangleGraph (0,0) w h) C →g PD.FK.squareLattice := {
    toFun := Subtype.val
    map_rel' := fun e => (openGraph_le _ C) e }
  let p := (D.first.map φ).copy
    (show D.firstStart.val = (D.firstStart.val.1,0) from Prod.ext rfl ha)
    (show D.firstEnd.val = (B,D.firstEnd.val.2) from Prod.ext hu rfl)
  let q := (D.second.map φ).copy
    (show D.secondStart.val = (D.secondStart.val.1,0) from Prod.ext rfl hb)
    (show D.secondEnd.val = (x,D.secondEnd.val.2) from Prod.ext hv rfl)
  have hpS : p.support = D.first.support.map Subtype.val := by
    simp only [p,SimpleGraph.Walk.support_copy,SimpleGraph.Walk.support_map]
    rfl
  have hqS : q.support = D.second.support.map Subtype.val := by
    simp only [q,SimpleGraph.Walk.support_copy,SimpleGraph.Walk.support_map]
    rfl
  have hpB : ∀ z ∈ p.support,
      0 ≤ z.1 ∧ z.1 ≤ B ∧ 0 ≤ z.2 ∧ z.2 ≤ (h:ℤ) := by
    intro z hz
    rw [hpS] at hz
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hz
    have hrect := (mem_latticeRectangle _ _ _ _).mp a.property
    exact ⟨hrect.1.1,hp a ha,hrect.2.1,(by simpa using hrect.2.2)⟩
  have hqB : ∀ z ∈ q.support,
      0 ≤ z.1 ∧ z.1 ≤ B ∧ 0 ≤ z.2 ∧ z.2 ≤ (h:ℤ) := by
    intro z hz
    rw [hqS] at hz
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hz
    have hrect := (mem_latticeRectangle _ _ _ _).mp a.property
    exact ⟨hrect.1.1,(hq a ha).2,hrect.2.1,(by simpa using hrect.2.2)⟩
  have hPd : ∀ z ∈ p.support, z ∉ q.support := by
    intro z hz hzq
    rw [hpS] at hz
    rw [hqS] at hzq
    obtain ⟨a,ha,hea⟩ := List.mem_map.mp hz
    obtain ⟨b,hb,heb⟩ := List.mem_map.mp hzq
    have he : a = b := Subtype.ext (hea.trans heb.symm)
    exact hdis a ha (he.symm ▸ hb)
  have hy : 0 < D.secondEnd.val.2 := disjoint_bottom_right_walk_tip_pos
    D.firstStart.val.1 D.secondStart.val.1 B D.firstEnd.val.2 x D.secondEnd.val.2
    hxa hab.le (hq _ D.second.start_mem_support).2 p q
    (fun z hz => (hpB z hz).2.2.1)
    (fun z hz => ⟨(hqB z hz).2.1,(hqB z hz).2.2.1⟩) hPd
  have ha0 : 0 ≤ D.firstStart.val.1 := by
    have hh := (mem_latticeRectangle _ _ _ _).mp D.firstStart.property
    exact hh.1.1
  have hyh : D.secondEnd.val.2 ≤ (h:ℤ) := by
    have hh := (mem_latticeRectangle _ _ _ _).mp D.secondEnd.property
    simpa using hh.2.2
  obtain ⟨z,hzp,hzx,hzy⟩ := disjoint_bottom_right_walk_hits_left_slit
    D.firstStart.val.1 D.secondStart.val.1 B D.firstEnd.val.2 x D.secondEnd.val.2 (h:ℤ)
    ha0 hab (hq _ D.second.start_mem_support).2 hx hxa hy hyh p q hpB hqB hPd
  rw [hpS] at hzp
  obtain ⟨a,ha,hea⟩ := List.mem_map.mp hzp
  obtain ⟨k,hka,hklen⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp ha
  have hhit : ∃ k, k ≤ D.first.length ∧ D.first.getVert k ∈
      {z | z.val.1 = x-1 ∧ D.secondEnd.val.2 ≤ z.val.2} := by
    refine ⟨k,hklen,?_⟩
    rw [hka]
    exact ⟨by simpa only [← hea] using hzx,by simpa only [← hea] using hzy⟩
  exact ⟨firstContactIndex D.first _ hhit,isFirstContact_firstContactIndex D.first _ hhit⟩

end
end PottsContinuity.PlanarMixed.FiniteSlit
