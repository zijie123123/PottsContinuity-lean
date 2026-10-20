module

public import PottsContinuity.PlanarMixed.FiniteSlit.PrefixGeometricCompletion
public import PottsContinuity.PlanarMixed.FiniteSlit.SourceRectanglePadding
public import PottsContinuity.PlanarMixed.FiniteSlit.CrosscutBand
public import PottsContinuity.PlanarMixed.RetainedWalk

@[expose] public section

namespace PottsContinuity.PlanarMixed.FiniteSlit
open PD.FK RSW
noncomputable section

/-- Crosscuts are constructed from the retained source prefix itself. No open
continuation to the right boundary, nor its geometric trace, is required. -/
theorem sourceRectangle_crosscutData_of_leftContactPrefix
    (w h : ℕ) (x y : ℤ) (hx : 1 ≤ x) (hxw : x ≤ (w:ℤ))
    {a b u v : RectangleVertex (0,0) w h}
    (p : (rectangleGraph (0,0) w h).Walk a u)
    (q : (rectangleGraph (0,0) w h).Walk b v)
    (ha : a.val.2 = 0) (hb : b.val.2 = 0)
    (hxa : x ≤ a.val.1) (hab : a.val.1 < b.val.1)
    (hu : u.val.1 = x-1 ∧ y ≤ u.val.2) (hv : v.val = (x,y))
    (hq : ∀ z ∈ q.support, x ≤ z.val.1)
    (hdis : ∀ z ∈ p.support, z ∉ q.support)
    (hfirst : ∀ i < p.length,
      ¬ ((p.getVert i).val.1 = x-1 ∧ y ≤ (p.getVert i).val.2)) :
    let f := paddedRectangleReference w h x hx hxw
    0 < y ∧ ∃ D : CrosscutData (2*(w+h)+2) x y,
      D.firstStart = f a ∧ D.secondStart = f b ∧
      D.firstEnd = f u ∧ D.secondEnd = f v ∧
      D.first.support = p.support.map f ∧ D.second.support = q.support.map f ∧
      D.first.edges = p.edges.map (Sym2.map f) ∧
      D.second.edges = q.edges.map (Sym2.map f) := by
  let f := paddedRectangleReference w h x hx hxw
  let φ : rectangleGraph (0,0) w h →g PD.FK.squareLattice := {
    toFun := Subtype.val
    map_rel' := fun hh => hh }
  let P := (p.map φ).copy (show a.val = (a.val.1,0) from Prod.ext rfl ha)
    (show u.val = (x-1,u.val.2) from Prod.ext hu.1 rfl)
  let Q := (q.map φ).copy (show b.val = (b.val.1,0) from Prod.ext rfl hb) hv
  have hsP : P.support = p.support.map Subtype.val := by
    simp only [P,SimpleGraph.Walk.support_copy,SimpleGraph.Walk.support_map]; rfl
  have hsQ : Q.support = q.support.map Subtype.val := by
    simp only [Q,SimpleGraph.Walk.support_copy,SimpleGraph.Walk.support_map]; rfl
  have hbounds (z : RectangleVertex (0,0) w h) :
      0 ≤ z.val.1 ∧ z.val.1 ≤ (w:ℤ) ∧ 0 ≤ z.val.2 ∧ z.val.2 ≤ (h:ℤ) := by
    have hh := (PD.FK.mem_latticeRectangle _ _ _ _).mp z.property
    dsimp at hh
    omega
  have hP : ∀ z ∈ P.support, 0 ≤ z.1 ∧ z.1 ≤ (w:ℤ) ∧ 0 ≤ z.2 ∧ z.2 ≤ (h:ℤ) := by
    intro z hz
    rw [hsP] at hz
    obtain ⟨r,_,rfl⟩ := List.mem_map.mp hz
    exact hbounds r
  have hQ : ∀ z ∈ Q.support, x ≤ z.1 ∧ z.1 ≤ (w:ℤ) ∧ 0 ≤ z.2 ∧ z.2 ≤ (h:ℤ) := by
    intro z hz
    rw [hsQ] at hz
    obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hz
    exact ⟨hq r hr,(hbounds r).2⟩
  have hPd : ∀ z ∈ P.support, z ∉ Q.support := by
    intro z hz hzq
    rw [hsP] at hz
    rw [hsQ] at hzq
    obtain ⟨r,hr,he⟩ := List.mem_map.mp hz
    obtain ⟨s,hs,he'⟩ := List.mem_map.mp hzq
    have hh : r = s := Subtype.ext (he.trans he'.symm)
    exact hdis r hr (hh.symm ▸ hs)
  have hget (i : ℕ) : P.getVert i = (p.getVert i).val := by
    simp only [P,SimpleGraph.Walk.getVert_copy,SimpleGraph.Walk.getVert_map]; rfl
  have hlen : P.length = p.length := by
    simp only [P,SimpleGraph.Walk.length_copy,SimpleGraph.Walk.length_map]
  have hfirstP : ∀ i < P.length, ¬ ((P.getVert i).1 = x-1 ∧ y ≤ (P.getVert i).2) := by
    intro i hi
    rw [hget]
    exact hfirst i (by omega)
  have hy := disjoint_leftContact_prefix_tip_pos a.val.1 b.val.1 x y u.val.2 w h
    hx (by omega) hxa hab P Q hP hQ hPd
  have hav := disjoint_leftContact_prefix_avoids_markedRay a.val.1 b.val.1 x y u.val.2 w h
    hx (by omega) hxa hab P Q hP hQ hPd hfirstP
  have hpavoid : ∀ z ∈ p.support, ¬ (z.val.1 = x ∧ y ≤ z.val.2) := by
    intro z hz
    apply hav z.val
    rw [hsP]
    exact List.mem_map.mpr ⟨z,hz,rfl⟩
  have hpret : ∀ {r s : RectangleVertex (0,0) w h},
      s(r,s) ∈ p.edges → (graph (2*(w+h)+2) x y).Adj (f r) (f s) := by
    intro r s he
    refine ⟨p.adj_of_mem_edges he,?_⟩
    change ¬ (y < r.val.2 ∧ y < s.val.2 ∧
      ((r.val.1 = x-1 ∧ s.val.1 = x) ∨ (s.val.1 = x-1 ∧ r.val.1 = x)))
    have hr := hpavoid r (p.fst_mem_support_of_mem_edges he)
    have hs := hpavoid s (p.snd_mem_support_of_mem_edges he)
    omega
  have hqret : ∀ {r s : RectangleVertex (0,0) w h},
      s(r,s) ∈ q.edges → (graph (2*(w+h)+2) x y).Adj (f r) (f s) := by
    intro r s he
    refine ⟨q.adj_of_mem_edges he,?_⟩
    change ¬ (y < r.val.2 ∧ y < s.val.2 ∧
      ((r.val.1 = x-1 ∧ s.val.1 = x) ∨ (s.val.1 = x-1 ∧ r.val.1 = x)))
    have hr := hq r (q.fst_mem_support_of_mem_edges he)
    have hs := hq s (q.snd_mem_support_of_mem_edges he)
    omega
  let R := retainedWalk (graph (2*(w+h)+2) x y) f p hpret
  let T := retainedWalk (graph (2*(w+h)+2) x y) f q hqret
  have hsR : R.support = p.support.map f := retainedWalk_support _ _ _ _
  have hsT : T.support = q.support.map f := retainedWalk_support _ _ _ _
  have hinside (z : RectangleVertex (0,0) w h) :
      x-((2*(w+h)+2:ℕ):ℤ) < z.val.1 ∧
      z.val.1 < x+((2*(w+h)+2:ℕ):ℤ)-1 ∧
      0 ≤ z.val.2 ∧ z.val.2 < ((2*(w+h)+2:ℕ):ℤ) := by
    have hz := hbounds z
    omega
  let D : CrosscutData (2*(w+h)+2) x y := {
    firstStart := f a
    secondStart := f b
    firstEnd := f u
    secondEnd := f v
    first := R
    second := T
    first_bottom := ha
    second_bottom := hb
    first_start_right := hxa
    starts_order := hab
    first_end_column := hu.1
    first_end_height := hu.2
    second_end := hv
    first_bounds := by
      intro z hz
      rw [hsR] at hz
      obtain ⟨r,_,rfl⟩ := List.mem_map.mp hz
      exact hinside r
    second_bounds := by
      intro z hz
      rw [hsT] at hz
      obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hz
      exact ⟨hq r hr,(hinside r).2⟩
    disjoint := by
      intro z hz hzt
      rw [hsR] at hz
      rw [hsT] at hzt
      obtain ⟨r,hr,hrz⟩ := List.mem_map.mp hz
      obtain ⟨s,hs,hsz⟩ := List.mem_map.mp hzt
      have he : r = s := f.injective (hrz.trans hsz.symm)
      exact hdis r hr (he.symm ▸ hs) }
  exact ⟨hy,D,rfl,rfl,rfl,rfl,hsR,hsT,
    retainedWalk_edges _ f p hpret,retainedWalk_edges _ f q hqret⟩

end
end PottsContinuity.PlanarMixed.FiniteSlit
