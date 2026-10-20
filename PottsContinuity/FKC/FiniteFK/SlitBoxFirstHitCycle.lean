-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/SlitBoxFirstHitCycle.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.SlitBoxFirstHitPathGeometry
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

open PottsContinuity.FKC

/- The exterior witness is essential: at n=1, u=(0,-1), t=(0,0), and p=r
the single bond give a two-edge backtrack rather than a simple cycle. -/

/-- A first-hit slit path closes to a simple cycle with a simple exterior
return walk whose only in-box vertices lie on the slit path's start or the
wired arc. The explicit exterior witness rules out the two-edge backtrack. -/
theorem slitBox_firstHit_path_append_exterior_return_isCycle
    (n : ℕ) (hn : 1 ≤ n) (A : Configuration (slitBoxGraph n))
    (u : SlitBoxVertex n) (huY : u.val.2 = -(n : ℤ))
    (t : SlitBoxVertex n) (ht : t ∈ slitBoxWiredArc n)
    (p : (openGraph (slitBoxGraph n) A).Walk u t)
    (hp : p.IsPath)
    (hfirst : ∀ x ∈ p.support, x ∈ slitBoxWiredArc n → x = t)
    (r : squareLattice.Walk t.val u.val) (hr : r.IsPath)
    (hreturn : ∀ x ∈ r.support,
      x ∈ latticeRectangle (-(n : ℤ), -(n : ℤ)) (2 * n) (2 * n) →
        x = u.val ∨ (x.1 = 0 ∧ 0 ≤ x.2 ∧ x.2 ≤ n))
    (hExterior : ∃ x ∈ r.support,
      x ∉ latticeRectangle (-(n : ℤ), -(n : ℤ)) (2 * n) (2 * n)) :
    ((p.map (slitBoxOpenGraphToSquareLatticeHom n A)).append r).IsCycle := by
  classical
  have htCoords := (mem_slitBoxWiredArc_iff n t).mp ht
  have htu : t.val ≠ u.val := by
    intro heq
    have : t.val.2 = u.val.2 := congrArg Prod.snd heq
    rw [huY] at this
    omega
  have huBox : u.val ∈ latticeRectangle (-(n : ℤ), -(n : ℤ)) (2 * n) (2 * n) :=
    u.property
  have htBox : t.val ∈ latticeRectangle (-(n : ℤ), -(n : ℤ)) (2 * n) (2 * n) :=
    t.property
  have hrLong : 1 < r.length := by
    by_contra hnot
    have hlen : r.length ≤ 1 := by omega
    rcases hExterior with ⟨x, hx, hxout⟩
    have hpos : 0 < r.length := by
      by_contra hzero
      have hzero' : r.length = 0 := by omega
      exact htu (r.eq_of_length_eq_zero hzero')
    have hlen1 : r.length = 1 := by omega
    have hadj : squareLattice.Adj t.val u.val :=
      SimpleGraph.Walk.adj_of_length_eq_one hlen1
    have hrEq : r = hadj.toWalk := by
      apply SimpleGraph.Walk.eq_of_length_le_one hlen
      simp
    rw [hrEq, hadj.support_toWalk] at hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact hxout htBox
    · exact hxout huBox
  let H := p.map (slitBoxOpenGraphToSquareLatticeHom n A)
  have hHpath : H.IsPath := hp.map (slitBoxOpenGraphToSquareLatticeHom_injective n A)
  have hdis : H.support.tail.Disjoint r.support.tail := by
    apply List.disjoint_left.mpr
    intro x hxH hxR
    have hxHsupport : x ∈ H.support := List.mem_of_mem_tail hxH
    have hxRsupport : x ∈ r.support := List.mem_of_mem_tail hxR
    have hxMapped : x ∈ p.support.map (slitBoxOpenGraphToSquareLatticeHom n A) := by
      change x ∈ (p.map (slitBoxOpenGraphToSquareLatticeHom n A)).support at hxHsupport
      rw [SimpleGraph.Walk.support_map] at hxHsupport
      exact hxHsupport
    rcases List.mem_map.mp hxMapped with ⟨a, ha, hax⟩
    have hax' : a.val = x := hax
    have hxBox : x ∈ latticeRectangle (-(n : ℤ), -(n : ℤ)) (2 * n) (2 * n) := by
      rw [← hax']
      exact a.property
    rcases hreturn x hxRsupport hxBox with hxu | hxArc
    ·
      have hHnodup : H.support.Nodup := hHpath.support_nodup
      rw [← SimpleGraph.Walk.cons_tail_support] at hHnodup
      change (u.val :: H.support.tail).Nodup at hHnodup
      have huNot : u.val ∉ H.support.tail := (List.nodup_cons.mp hHnodup).1
      exact huNot (by simpa [hxu] using hxH)
    · have haArc : a ∈ slitBoxWiredArc n := by
        rw [mem_slitBoxWiredArc_iff]
        constructor
        · simpa [hax'] using hxArc.1
        · simpa [hax'] using hxArc.2
      have hat : a = t := hfirst a ha haArc
      have hxt : x = t.val := by simpa [hax'] using congrArg Subtype.val hat
      have hrnodup : r.support.Nodup := hr.support_nodup
      rw [← SimpleGraph.Walk.cons_tail_support] at hrnodup
      change (t.val :: r.support.tail).Nodup at hrnodup
      have htNot : t.val ∉ r.support.tail := (List.nodup_cons.mp hrnodup).1
      exact htNot (by simpa [hxt] using hxR)
  exact hHpath.isCycle_append hr hdis (Or.inr hrLong)

end PottsContinuity.FKC.FiniteFK
