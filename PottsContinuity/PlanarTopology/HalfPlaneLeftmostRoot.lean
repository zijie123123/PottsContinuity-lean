module

public import PottsContinuity.PlanarTopology.HalfPlaneClusterEvents
public import Mathlib.Data.Int.LeastGreatest
public import Mathlib.Tactic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Data.Int.Star

@[expose] public section

namespace PottsContinuity.PlanarTopology
open PD.FK PD.RCInfinite
noncomputable section

/-- Every infinite component in a right half-plane has a leftmost column.
After an actual translation it gives an infinite component at the boundary origin. -/
theorem halfPlane_infinite_has_translated_boundary_root (ω : LatticeConfiguration)
    (u : {z : LatticeVertex // 0 ≤ z.1}) (hu : ω ∈ halfPlaneInfiniteAt u) :
    ∃ a : LatticeVertex, edgeTranslate a ω ∈ halfPlaneInfiniteAt ⟨(0,0),by norm_num⟩ := by
  classical
  let G := (PD.rcInfiniteOpenGraph ω).induce {z : LatticeVertex | 0 ≤ z.1}
  let C := {v | G.Reachable u v}
  have hC : C.Infinite := hu
  let P := fun k : ℤ => ∃ v : {z : LatticeVertex // 0 ≤ z.1}, v ∈ C ∧ v.val.1 = k
  obtain ⟨l,⟨v,hv,hvl⟩,hl⟩ := Int.exists_least_of_bdd
    (P := P) ⟨0,by rintro k ⟨z,hz,rfl⟩; exact z.property⟩
    ⟨u.val.1,u,SimpleGraph.Reachable.refl u,rfl⟩
  let a : LatticeVertex := (-l,-v.val.2)
  let e := openGraphTranslationIso a ω
  have he : e v.val = (0,0) := by
    change (v.val.1 + -l,v.val.2 + -v.val.2) = (0,0)
    rw [hvl]
    simp
  have hconn (z : {z : LatticeVertex // 0 ≤ z.1}) (hz : z ∈ C) :
      ((PD.rcInfiniteOpenGraph (edgeTranslate a ω)).induce {z : LatticeVertex | 0 ≤ z.1}).Reachable
        ⟨(0,0),by norm_num⟩ ⟨e z.val,by change 0 ≤ z.val.1 + -l; have := hl _ ⟨z,hz,rfl⟩; omega⟩ := by
    obtain ⟨p⟩ := hv.symm.trans hz
    let f := e.toHom.comp
      (SimpleGraph.Embedding.induce (G := PD.rcInfiniteOpenGraph ω) {z : LatticeVertex | 0 ≤ z.1}).toHom
    have hstart : f v = (0,0) := he
    let q := (p.map f).copy hstart rfl
    have hq : ∀ w ∈ q.support, 0 ≤ w.1 := by
      intro w hw
      have hs : q.support = p.support.map f := by
        dsimp [q]
        rw [SimpleGraph.Walk.support_copy]
        exact SimpleGraph.Walk.support_map f p
      have hw' := Eq.mp (congrArg (fun xs : List LatticeVertex => w ∈ xs) hs) hw
      obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hw'
      have hut : t ∈ C := hv.trans (p.takeUntil t ht).reachable
      have hlt := hl _ ⟨t,hut,rfl⟩
      change 0 ≤ t.val.1 + -l
      omega
    exact ⟨q.induce _ hq⟩
  refine ⟨a,?_⟩
  change {z | ((PD.rcInfiniteOpenGraph (edgeTranslate a ω)).induce {z : LatticeVertex | 0 ≤ z.1}).Reachable
    ⟨(0,0),by norm_num⟩ z}.Infinite
  intro hfin
  have hCL := hC.image Subtype.val_injective.injOn
  apply hCL
  apply ((hfin.image Subtype.val).image e.symm).subset
  rintro w ⟨z,hz,rfl⟩
  refine ⟨e z.val,?_,e.symm_apply_apply z.val⟩
  exact ⟨_,hconn z hz,rfl⟩

end
end PottsContinuity.PlanarTopology
