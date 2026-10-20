module

public import PottsContinuity.Thm3.Push.PrefixExteriorClosure
public import PottsContinuity.PlanarMixed.FiniteSlit.SourceExteriorReveals

@[expose] public section

namespace PottsContinuity.PlanarMixed.StripRSWSelectors
open PD.FK Push PlanarTopology PlanarMixed.FiniteSlit
noncomputable section

/-- The upward ray above the first-contact endpoint belongs to the left
source exterior, even though the recorded prefix itself stops at that endpoint. -/
theorem source_upper_ray_mem_leftExterior (w h : ℕ) (a x y t : ℤ) (hyt : y ≤ t)
    (p : PD.FK.squareLattice.Walk (a,0) (x-1,t))
    (hfirst : firstContactTrace {z | z.1=x-1 ∧ y ≤ z.2} p.support=some p.support)
    (u : RectangleVertex (0,0) w h) (hux : u.val.1=x-1) (htu : t ≤ u.val.2) :
    u ∈ sourceLeftExterior w h x y (sourceCoordinateTrace w h {z | z ∈ p.support}) := by
  classical
  by_cases he : u.val.2=t
  · right
    refine ⟨u,?_,rfl⟩
    change u.val ∈ p.support
    have heu : u.val=(x-1,t) := Prod.ext hux he
    exact heu.symm ▸ p.end_mem_support
  · have hstrict : t<u.val.2 := by omega
    have hub := (PD.FK.mem_latticeRectangle _ _ _ _).mp u.property
    dsimp at hub
    obtain ⟨r,hr⟩ := vertical_walk_between u.val.1 u.val.2 (h:ℤ)
    let S : Set LatticeVertex := {z | z ∈ PD.FK.latticeRectangle (0,0) w h ∧
      z.1=u.val.1 ∧ u.val.2 ≤ z.2}
    have hrs : ∀ z ∈ r.support, z ∈ S := by
      intro z hz
      have hh := hr z hz
      refine ⟨?_,hh.1,by omega⟩
      rw [PD.FK.mem_latticeRectangle]
      dsimp
      constructor <;> constructor <;> omega
    let f : (PD.FK.squareLattice.induce S) →g sourceExteriorGraph w h x y := {
      toFun := fun z => Sum.inl ⟨z.val,z.property.1⟩
      map_rel' := by
        intro z v hzv
        change (slitRetainedBondGraph x y).Adj z.val v.val
        rw [slitRetainedBondGraph_adj_iff]
        have hz0 := ((PD.FK.mem_latticeRectangle _ _ _ _).mp z.property.1).2.1
        have hv0 := ((PD.FK.mem_latticeRectangle _ _ _ _).mp v.property.1).2.1
        refine ⟨hzv,hz0,hv0,?_⟩
        have hz := z.property.2.1
        have hv := v.property.2.1
        omega }
    let q := (r.induce S hrs).map f
    let top : RectangleVertex (0,0) w h := ⟨(u.val.1,h), (hrs _ r.end_mem_support).1⟩
    have htop : (sourceExteriorGraph w h x y).Adj (Sum.inl top) (Sum.inr false) :=
      Or.inr ⟨rfl,by change u.val.1<x; omega⟩
    let Q := (q.copy (show f ⟨_,hrs _ r.start_mem_support⟩=Sum.inl u from rfl)
      (show f ⟨_,hrs _ r.end_mem_support⟩=Sum.inl top from rfl)).append htop.toWalk
    left
    refine ⟨Sum.inr false,rfl,Q.reverse,?_⟩
    intro z hz hzcut
    simp only [SimpleGraph.Walk.support_reverse,List.mem_reverse] at hz
    dsimp only [Q] at hz
    rw [SimpleGraph.Walk.mem_support_append_iff] at hz
    rcases hz with hz | hz
    · rw [SimpleGraph.Walk.support_copy] at hz
      change z ∈ ((r.induce S hrs).map f).support at hz
      rw [SimpleGraph.Walk.support_map] at hz
      obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hz
      obtain ⟨c,hc,hec⟩ := hzcut
      have hecv : c.val=v.val := congrArg Subtype.val (Sum.inl.inj hec)
      have hvp : v.val ∈ p.support := hecv ▸ hc
      have heend := firstContact_prefix_upper_ray_unique a x y t hyt p hfirst v.val hvp
        (v.property.2.1.trans hux) (by have := v.property.2.2; omega)
      have hey := congrArg Prod.snd heend
      have hvy := v.property.2.2
      omega
    · have hz' : z=Sum.inl top ∨ z=Sum.inr false := by simpa using hz
      rcases hz' with rfl | rfl
      · obtain ⟨c,hc,hec⟩ := hzcut
        have hec' : c=top := Sum.inl.inj hec
        have heend := firstContact_prefix_upper_ray_unique a x y t hyt p hfirst top.val
          (hec' ▸ hc) hux (by dsimp [top]; omega)
        have hey := congrArg Prod.snd heend
        dsimp [top] at hey
        omega
      · rcases hzcut with ⟨c,hc,hec⟩
        cases hec

end
end PottsContinuity.PlanarMixed.StripRSWSelectors
