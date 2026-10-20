module

public import PottsContinuity.PlanarMixed.FiniteSlit.CrosscutBand
public import PottsContinuity.PlanarMixed.RetainedWalk
public import PottsContinuity.Thm3.RSW.SlitRetainedExistence

@[expose] public section

namespace PottsContinuity.PlanarMixed.FiniteSlit
open PD.FK BD12 RSW
noncomputable section

/-- Every disjoint source realization gives actual finite crosscut data.
The first trace is the WHOLE prefix through its first left-slit contact;
the second trace is the original bottom-to-tip path. Support and bond lists
are literal images, so no terminal edge or boundary contact is silently added. -/
theorem sourceSquare_exists_crosscutData
    (n : ℕ) (x y B : ℤ) (hx : 1 ≤ x) (hxn : x ≤ (2*n:ℕ))
    {a b u v : RectangleVertex (0,0) (2*n) (2*n)}
    (p : (rectangleGraph (0,0) (2*n) (2*n)).Walk a u)
    (q : (rectangleGraph (0,0) (2*n) (2*n)).Walk b v)
    (ha : a.val.2 = 0) (hb : b.val.2 = 0) (hu : u.val.1 = B)
    (hxa : x ≤ a.val.1) (hab : a.val.1 < b.val.1) (hv : v.val = (x,y))
    (hp : ∀ w ∈ p.support, w.val.1 ≤ B)
    (hq : ∀ w ∈ q.support, x ≤ w.val.1 ∧ w.val.1 ≤ B)
    (hdis : ∀ w ∈ p.support, w ∉ q.support) :
    let f := sourceSquareSlitEmbedding n x (by omega) hxn
    ∃ k : ℕ, 0 < k ∧ k ≤ p.length ∧
      ((p.getVert k).val.1 = x-1 ∧ y ≤ (p.getVert k).val.2) ∧
      (∀ j : ℕ, j < k → ¬ ((p.getVert j).val.1 = x-1 ∧ y ≤ (p.getVert j).val.2)) ∧
      ∃ D : CrosscutData (2*n+2) x y,
        D.firstStart = f a ∧ D.secondStart = f b ∧
        D.firstEnd = f (p.getVert k) ∧ D.secondEnd = f v ∧
        D.first.support = (p.take k).support.map f ∧
        D.second.support = q.support.map f ∧
        D.first.edges = (p.take k).edges.map (Sym2.map f) ∧
        D.second.edges = q.edges.map (Sym2.map f) := by
  let f := sourceSquareSlitEmbedding n x (by omega) hxn
  let φ : rectangleGraph (0,0) (2*n) (2*n) →g PD.FK.squareLattice := {
    toFun := Subtype.val
    map_rel' := fun h => h }
  let Q := (q.map φ).copy (show b.val = (b.val.1,0) from Prod.ext rfl hb) hv
  have hsQ : Q.support = q.support.map Subtype.val := by
    calc
      Q.support = (q.map φ).support := SimpleGraph.Walk.support_copy _ _ _
      _ = q.support.map Subtype.val := SimpleGraph.Walk.support_map _ _
  have hbounds (w : RectangleVertex (0,0) (2*n) (2*n)) :
      0 ≤ w.val.1 ∧ w.val.1 ≤ ((2*n:ℕ):ℤ) ∧
        0 ≤ w.val.2 ∧ w.val.2 ≤ ((2*n:ℕ):ℤ) := by
    have hh := (PD.FK.mem_latticeRectangle _ _ _ _).mp w.property
    dsimp at hh
    omega
  have hQ : ∀ w ∈ Q.support,
      x ≤ w.1 ∧ w.1 ≤ B ∧ 0 ≤ w.2 ∧ w.2 ≤ ((2*n:ℕ):ℤ) := by
    intro w hw
    rw [hsQ] at hw
    obtain ⟨z,hz,rfl⟩ := List.mem_map.mp hw
    exact ⟨(hq z hz).1,(hq z hz).2,(hbounds z).2.2⟩
  have hpQ : ∀ w ∈ p.support, w.val ∉ Q.support := by
    intro w hw hwQ
    rw [hsQ] at hwQ
    obtain ⟨z,hz,he⟩ := List.mem_map.mp hwQ
    exact hdis w hw (Subtype.ext he ▸ hz)
  obtain ⟨k,hkpos,hkle,hkhit,hfirst,r,hredges,_,_⟩ :=
    sourceSquare_exists_retained_leftSlit_prefix_of_disjoint_walks n x y B b.val.1 hx hxn
      p ha hu hxa hab Q
      (fun w hw => ⟨(hbounds w).1,hp w hw,(hbounds w).2.2⟩) hQ hpQ
  have hpret : ∀ {u v : RectangleVertex (0,0) (2*n) (2*n)},
      s(u,v) ∈ (p.take k).edges → (graph (2*n+2) x y).Adj (f u) (f v) := by
    intro u v he
    apply r.adj_of_mem_edges
    rw [hredges]
    exact List.mem_map.mpr ⟨s(u,v),he,rfl⟩
  have hqret : ∀ {u v : RectangleVertex (0,0) (2*n) (2*n)},
      s(u,v) ∈ q.edges → (graph (2*n+2) x y).Adj (f u) (f v) := by
    intro u v he
    refine ⟨q.adj_of_mem_edges he,?_⟩
    change ¬ (y < u.val.2 ∧ y < v.val.2 ∧
      ((u.val.1 = x-1 ∧ v.val.1 = x) ∨ (v.val.1 = x-1 ∧ u.val.1 = x)))
    have hu := (hq u (q.fst_mem_support_of_mem_edges he)).1
    have hv := (hq v (q.snd_mem_support_of_mem_edges he)).1
    omega
  let P := retainedWalk (graph (2*n+2) x y) f (p.take k) hpret
  let T := retainedWalk (graph (2*n+2) x y) f q hqret
  have hsP : P.support = (p.take k).support.map f := retainedWalk_support _ _ _ _
  have hsT : T.support = q.support.map f := retainedWalk_support _ _ _ _
  let D : CrosscutData (2*n+2) x y := {
    firstStart := f a
    secondStart := f b
    firstEnd := f (p.getVert k)
    secondEnd := f v
    first := P
    second := T
    first_bottom := ha
    second_bottom := hb
    first_start_right := hxa
    starts_order := hab
    first_end_column := hkhit.1
    first_end_height := hkhit.2
    second_end := hv
    first_bounds := by
      intro w hw
      rw [hsP] at hw
      obtain ⟨z,hz,rfl⟩ := List.mem_map.mp hw
      exact sourceSquare_strictly_inside n x (by omega) hxn z.val z.property
    second_bounds := by
      intro w hw
      rw [hsT] at hw
      obtain ⟨z,hz,rfl⟩ := List.mem_map.mp hw
      have hz' := sourceSquare_strictly_inside n x (by omega) hxn z.val z.property
      exact ⟨(hq z hz).1,hz'.2⟩
    disjoint := by
      intro w hw hwt
      rw [hsP] at hw
      rw [hsT] at hwt
      obtain ⟨z,hz,hzw⟩ := List.mem_map.mp hw
      obtain ⟨t,ht,htw⟩ := List.mem_map.mp hwt
      have he : z = t := f.injective (hzw.trans htw.symm)
      exact hdis z ((p.isSubwalk_take k).support_subset hz) (he.symm ▸ ht)
  }
  refine ⟨k,hkpos,hkle,hkhit,hfirst,D,rfl,rfl,rfl,rfl,hsP,hsT,?_,?_⟩
  · exact retainedWalk_edges _ f (p.take k) hpret
  · exact retainedWalk_edges _ f q hqret

end
end PottsContinuity.PlanarMixed.FiniteSlit
