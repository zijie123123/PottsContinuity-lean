module

public import PottsContinuity.PlanarMixed.FiniteSlit.SourceRectanglePadding
public import PottsContinuity.PlanarMixed.FiniteSlit.FirstContactCrop

@[expose] public section

namespace PottsContinuity.PlanarMixed.FiniteSlit
open PD.FK RSW
noncomputable section

/-- Original open rectangle walks construct actual finite slit crosscuts.
The auxiliary square is used only for deterministic contact existence;
every output trace and bond is the image of an original rectangle walk. -/
theorem openSourceRectangle_exists_crosscutData
    (w h : ℕ) (x y B : ℤ) (hx : 1 ≤ x) (hxw : x ≤ (w:ℤ))
    (C : Configuration (rectangleGraph (0,0) w h))
    {a b u v : RectangleVertex (0,0) w h}
    (p : (openGraph (rectangleGraph (0,0) w h) C).Walk a u)
    (q : (openGraph (rectangleGraph (0,0) w h) C).Walk b v)
    (ha : a.val.2 = 0) (hb : b.val.2 = 0) (hu : u.val.1 = B)
    (hxa : x ≤ a.val.1) (hab : a.val.1 < b.val.1) (hv : v.val = (x,y))
    (hp : ∀ z ∈ p.support, z.val.1 ≤ B)
    (hq : ∀ z ∈ q.support, x ≤ z.val.1 ∧ z.val.1 ≤ B)
    (hdis : ∀ z ∈ p.support, z ∉ q.support) :
    let f := paddedRectangleReference w h x hx hxw
    ∃ k, IsFirstContact p {z | z.val.1 = x-1 ∧ y ≤ z.val.2} k ∧
      ∃ D : CrosscutData (2*(w+h)+2) x y,
        D.firstStart = f a ∧ D.secondStart = f b ∧
        D.firstEnd = f (p.getVert k) ∧ D.secondEnd = f v ∧
        D.first.support = (p.take k).support.map f ∧ D.second.support = q.support.map f ∧
        D.first.edges = (p.take k).edges.map (Sym2.map f) ∧
        D.second.edges = q.edges.map (Sym2.map f) := by
  let φ : openGraph (rectangleGraph (0,0) w h) C →g
      rectangleGraph (0,0) (2*(w+h)) (2*(w+h)) := {
    toFun := rectangleToPaddedSquare w h
    map_rel' := fun hab => openGraph_le _ C hab }
  let P := p.map φ
  let Q := q.map φ
  have hP : ∀ z ∈ P.support, z.val.1 ≤ B := by
    intro z hz
    rw [SimpleGraph.Walk.support_map] at hz
    obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hz
    exact hp t ht
  have hQ : ∀ z ∈ Q.support, x ≤ z.val.1 ∧ z.val.1 ≤ B := by
    intro z hz
    rw [SimpleGraph.Walk.support_map] at hz
    obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hz
    exact hq t ht
  have hdis' : ∀ z ∈ P.support, z ∉ Q.support := by
    intro z hz hzQ
    rw [SimpleGraph.Walk.support_map] at hz hzQ
    obtain ⟨r,hr,hrz⟩ := List.mem_map.mp hz
    obtain ⟨s,hs,hsz⟩ := List.mem_map.mp hzQ
    have he : r = s := (rectangleToPaddedSquare w h).injective (hrz.trans hsz.symm)
    exact hdis r hr (he ▸ hs)
  obtain ⟨k,_,hkle,hhit,hfirst,D,hDa,hDb,hDt,hDu,hPs,hQs,hPe,hQe⟩ :=
    sourceSquare_exists_crosscutData (w+h) x y B hx (by omega) P Q
      ha hb hu hxa hab hv hP hQ hdis'
  let sf := sourceSquareSlitEmbedding (w+h) x (by omega) (by omega : x ≤ ((2*(w+h):ℕ):ℤ))
  have hcomp : (fun z => sf (φ z)) =
      (paddedRectangleReference w h x hx hxw : RectangleVertex (0,0) w h → _) := by
    funext z
    exact paddedSquare_reference_comp w h x hx hxw z
  have hget (i : ℕ) : (P.getVert i).val = (p.getVert i).val := by
    rw [SimpleGraph.Walk.getVert_map]
    rfl
  have hcontact : IsFirstContact p {z | z.val.1 = x-1 ∧ y ≤ z.val.2} k := by
    refine ⟨?_,?_,?_⟩
    · simpa only [P,SimpleGraph.Walk.length_map] using hkle
    · change (p.getVert k).val.1 = x-1 ∧ y ≤ (p.getVert k).val.2
      rw [hget k] at hhit
      exact hhit
    · intro i hi
      change ¬ ((p.getVert i).val.1 = x-1 ∧ y ≤ (p.getVert i).val.2)
      have hi' := hfirst i hi
      rw [hget i] at hi'
      exact hi'
  change D.firstStart = sf (φ a) at hDa
  change D.secondStart = sf (φ b) at hDb
  change D.secondEnd = sf (φ v) at hDu
  change D.firstStart = (fun z => sf (φ z)) a at hDa
  change D.secondStart = (fun z => sf (φ z)) b at hDb
  change D.secondEnd = (fun z => sf (φ z)) v at hDu
  rw [hcomp] at hDa hDb hDu
  rw [SimpleGraph.Walk.getVert_map] at hDt
  change D.firstEnd = (fun z => sf (φ z)) (p.getVert k) at hDt
  rw [hcomp] at hDt
  change D.first.support = (P.take k).support.map sf at hPs
  simp only [P,SimpleGraph.Walk.support_take,SimpleGraph.Walk.support_map,
    ← List.map_take,List.map_map,Function.comp_def] at hPs
  rw [hcomp] at hPs
  change D.second.support = Q.support.map sf at hQs
  simp only [Q,SimpleGraph.Walk.support_map,List.map_map,Function.comp_def] at hQs
  rw [hcomp] at hQs
  change D.first.edges = (P.take k).edges.map (Sym2.map sf) at hPe
  simp only [P,SimpleGraph.Walk.edges_take,SimpleGraph.Walk.edges_map,
    ← List.map_take,List.map_map,Function.comp_def,Sym2.map_map] at hPe
  change D.first.edges = (p.edges.take k).map (Sym2.map (fun z => sf (φ z))) at hPe
  rw [hcomp] at hPe
  change D.second.edges = Q.edges.map (Sym2.map sf) at hQe
  simp only [Q,SimpleGraph.Walk.edges_map,List.map_map,Function.comp_def,Sym2.map_map] at hQe
  change D.second.edges = q.edges.map (Sym2.map (fun z => sf (φ z))) at hQe
  rw [hcomp] at hQe
  exact ⟨k,hcontact,D,hDa,hDb,hDt,hDu,
    by simpa only [SimpleGraph.Walk.support_take] using hPs,hQs,
    by simpa only [SimpleGraph.Walk.edges_take] using hPe,hQe⟩

end
end PottsContinuity.PlanarMixed.FiniteSlit
