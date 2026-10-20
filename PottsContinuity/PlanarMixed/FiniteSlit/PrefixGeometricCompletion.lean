module

public import PottsContinuity.Thm3.RSW.SlitRayApproach
public import PottsContinuity.Thm3.RSW.SlitTipPositive
public import PottsContinuity.Thm3.RSW.SlitContactOrder

@[expose] public section

namespace PottsContinuity.PlanarMixed.FiniteSlit
open PD.FK PlanarTopology RSW
noncomputable section

/-- A retained left-contact prefix has a geometric continuation above the
source rectangle, disjoint from the later bottom-to-tip walk. This does not
extend a random configuration or require any additional open bond. -/
theorem leftContact_geometric_completion
    (a b x y t B H : ℤ) (hx : 1 ≤ x) (hxB : x-1 ≤ B)
    (p : PD.FK.squareLattice.Walk (a,0) (x-1,t))
    (q : PD.FK.squareLattice.Walk (b,0) (x,y))
    (hp : ∀ z ∈ p.support, 0 ≤ z.1 ∧ z.1 ≤ B ∧ 0 ≤ z.2 ∧ z.2 ≤ H)
    (hq : ∀ z ∈ q.support, x ≤ z.1 ∧ z.1 ≤ B ∧ 0 ≤ z.2 ∧ z.2 ≤ H)
    (hdis : ∀ z ∈ p.support, z ∉ q.support) :
    ∃ P : PD.FK.squareLattice.Walk (a,0) (B,H+1),
      p.length ≤ P.length ∧
      (∀ i ≤ p.length, P.getVert i = p.getVert i) ∧
      (∀ z ∈ P.support, 0 ≤ z.1 ∧ z.1 ≤ B ∧ 0 ≤ z.2 ∧ z.2 ≤ H+1) ∧
      (∀ z ∈ P.support, z ∉ q.support) := by
  obtain ⟨V,hV⟩ := vertical_walk_between (x-1) t (H+1)
  obtain ⟨T,hT⟩ := horizontal_walk_between (x-1) B (H+1)
  have ht := hp _ p.end_mem_support
  have hH : 0 ≤ H := (hp _ p.start_mem_support).2.2.1.trans
    (hp _ p.start_mem_support).2.2.2
  have hV' : ∀ z ∈ V.support,
      z.1 = x-1 ∧ 0 ≤ z.2 ∧ z.2 ≤ H+1 := by
    intro z hz
    have hh := hV z hz
    rw [min_eq_left (by omega : t ≤ H+1),max_eq_right (by omega : t ≤ H+1)] at hh
    exact ⟨hh.1,by omega,hh.2.2⟩
  have hT' : ∀ z ∈ T.support, x-1 ≤ z.1 ∧ z.1 ≤ B ∧ z.2 = H+1 := by
    intro z hz
    simpa only [min_eq_left hxB,max_eq_right hxB] using hT z hz
  refine ⟨p.append (V.append T),by simp,?_,?_,?_⟩
  · intro i hi
    rw [SimpleGraph.Walk.getVert_append']; simp only [hi,ite_true]
  · intro z hz
    rw [SimpleGraph.Walk.mem_support_append_iff] at hz
    rcases hz with hz | hz
    · have hh := hp z hz
      exact ⟨hh.1,hh.2.1,hh.2.2.1,by omega⟩
    · rw [SimpleGraph.Walk.mem_support_append_iff] at hz
      rcases hz with hz | hz
      · have hh := hV' z hz
        exact ⟨by omega,by omega,hh.2⟩
      · have hh := hT' z hz
        exact ⟨by omega,hh.2.1,by omega,by omega⟩
  · intro z hz hzq
    rw [SimpleGraph.Walk.mem_support_append_iff] at hz
    rcases hz with hz | hz
    · exact hdis z hz hzq
    · rw [SimpleGraph.Walk.mem_support_append_iff] at hz
      rcases hz with hz | hz
      · have hh := hV' z hz
        have hhq := hq z hzq
        omega
      · have hh := hT' z hz
        have hhq := hq z hzq
        omega

/-- First marked-ray approaches depend only on the left-contact prefix.
The unused suffix is supplied geometrically outside the source rectangle. -/
theorem leftContact_prefix_first_markedRay_approaches_left
    (a b x y t B H : ℤ) (hx : 1 ≤ x) (hxB : x-1 ≤ B) (hab : a < b)
    (p : PD.FK.squareLattice.Walk (a,0) (x-1,t))
    (q : PD.FK.squareLattice.Walk (b,0) (x,y))
    (hp : ∀ z ∈ p.support, 0 ≤ z.1 ∧ z.1 ≤ B ∧ 0 ≤ z.2 ∧ z.2 ≤ H)
    (hq : ∀ z ∈ q.support, x ≤ z.1 ∧ z.1 ≤ B ∧ 0 ≤ z.2 ∧ z.2 ≤ H)
    (hdis : ∀ z ∈ p.support, z ∉ q.support)
    (m : ℕ) (hmpos : 0 < m) (hmle : m ≤ p.length)
    (hmhit : (p.getVert m).1 = x ∧ y ≤ (p.getVert m).2)
    (hmfirst : ∀ j < m, ¬ ((p.getVert j).1 = x ∧ y ≤ (p.getVert j).2)) :
    (p.getVert (m-1)).1 = x-1 ∧
      (p.getVert (m-1)).2 = (p.getVert m).2 ∧ y < (p.getVert (m-1)).2 := by
  obtain ⟨P,hlen,hget,hP,hPd⟩ := leftContact_geometric_completion
    a b x y t B H hx hxB p q hp hq hdis
  have hQ : ∀ z ∈ q.support, x ≤ z.1 ∧ z.1 ≤ B ∧ 0 ≤ z.2 ∧ z.2 ≤ H+1 := by
    intro z hz
    have hh := hq z hz
    exact ⟨hh.1,hh.2.1,hh.2.2.1,by omega⟩
  have hh := first_markedRay_contact_approaches_left a b B (H+1) x y (H+1)
    hab P q hP hQ hPd m hmpos (hmle.trans hlen)
    (by rw [hget m hmle]; exact hmhit)
    (by intro j hj; rw [hget j (by omega)]; exact hmfirst j hj)
  rw [hget (m-1) (by omega),hget m hmle] at hh
  exact hh

/-- The later tip is strictly above the bottom using only the retained
left-contact prefix and its geometric continuation. -/
theorem disjoint_leftContact_prefix_tip_pos
    (a b x y t B H : ℤ) (hx : 1 ≤ x) (hxB : x-1 ≤ B)
    (hxa : x ≤ a) (hab : a < b)
    (p : PD.FK.squareLattice.Walk (a,0) (x-1,t))
    (q : PD.FK.squareLattice.Walk (b,0) (x,y))
    (hp : ∀ z ∈ p.support, 0 ≤ z.1 ∧ z.1 ≤ B ∧ 0 ≤ z.2 ∧ z.2 ≤ H)
    (hq : ∀ z ∈ q.support, x ≤ z.1 ∧ z.1 ≤ B ∧ 0 ≤ z.2 ∧ z.2 ≤ H)
    (hdis : ∀ z ∈ p.support, z ∉ q.support) : 0 < y := by
  obtain ⟨P,_,_,hP,hPd⟩ := leftContact_geometric_completion
    a b x y t B H hx hxB p q hp hq hdis
  exact disjoint_bottom_right_walk_tip_pos a b B (H+1) x y hxa hab.le
    (hq _ q.start_mem_support).2.1 P q
    (fun z hz => (hP z hz).2.2.1)
    (fun z hz => ⟨(hq z hz).2.1,(hq z hz).2.2.1⟩) hPd

/-- A first left-contact prefix avoids the right marked ray on its entire
support. Only the two retained source walks are input. -/
theorem disjoint_leftContact_prefix_avoids_markedRay
    (a b x y t B H : ℤ) (hx : 1 ≤ x) (hxB : x-1 ≤ B)
    (hxa : x ≤ a) (hab : a < b)
    (p : PD.FK.squareLattice.Walk (a,0) (x-1,t))
    (q : PD.FK.squareLattice.Walk (b,0) (x,y))
    (hp : ∀ z ∈ p.support, 0 ≤ z.1 ∧ z.1 ≤ B ∧ 0 ≤ z.2 ∧ z.2 ≤ H)
    (hq : ∀ z ∈ q.support, x ≤ z.1 ∧ z.1 ≤ B ∧ 0 ≤ z.2 ∧ z.2 ≤ H)
    (hdis : ∀ z ∈ p.support, z ∉ q.support)
    (hfirst : ∀ j < p.length, ¬ ((p.getVert j).1 = x-1 ∧ y ≤ (p.getVert j).2)) :
    ∀ z ∈ p.support, ¬ (z.1 = x ∧ y ≤ z.2) := by
  have hy := disjoint_leftContact_prefix_tip_pos a b x y t B H hx hxB hxa hab p q hp hq hdis
  have hav := walk_prefix_avoids_ray_of_rayApproach Prod.fst Prod.snd x y p
    (by dsimp; omega) p.length le_rfl hfirst
    (fun m hmp hml hmh hmf =>
      let hh := leftContact_prefix_first_markedRay_approaches_left
        a b x y t B H hx hxB hab p q hp hq hdis m hmp hml hmh hmf
      ⟨hh.1,hh.2.2.le⟩)
  intro z hz
  obtain ⟨i,hi,hile⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hz
  exact hi ▸ hav i hile

end
end PottsContinuity.PlanarMixed.FiniteSlit
