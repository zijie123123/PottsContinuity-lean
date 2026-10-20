module

public import PottsContinuity.Thm4Records.TraceInterior
public import PottsContinuity.Thm4Records.ScreenIndex
public import PottsContinuity.PlanarTopology.RectangleIntersection
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Paths
public import Mathlib.Order.CompletePartialOrder

@[expose] public section

namespace PottsContinuity.Thm4Records
open PD.FK PD.Duality PlanarTopology
noncomputable section

/-- Between the full side screens, each step of a left-right square crossing
has an endpoint in the central index region. No square crop replaces a screen. -/
theorem crossing_full_screens_central_segment (m : ℕ) (hm : 1 ≤ m)
    {lb lt rb rt a b : LatticeVertex}
    (pL : squareLattice.Walk lb lt) (pR : squareLattice.Walk rb rt)
    (p : squareLattice.Walk a b)
    (hL : ∀ z ∈ pL.support,
      -(5*(m:ℤ)) ≤ z.1 ∧ z.1 ≤ -(m:ℤ)-1 ∧
      -(16*(m:ℤ))-1 ≤ z.2 ∧ z.2 ≤ 16*(m:ℤ))
    (hR : ∀ z ∈ pR.support,
      (m:ℤ) ≤ z.1 ∧ z.1 ≤ 5*(m:ℤ)-1 ∧
      -(16*(m:ℤ))-1 ≤ z.2 ∧ z.2 ≤ 16*(m:ℤ))
    (hlb : lb.2=-(16*(m:ℤ))-1) (hlt : lt.2=16*(m:ℤ))
    (hrb : rb.2=-(16*(m:ℤ))-1) (hrt : rt.2=16*(m:ℤ))
    (hp : ∀ z ∈ p.support,
      -(5*(m:ℤ)) ≤ z.1 ∧ z.1 ≤ 5*(m:ℤ)-1 ∧
      -(12*(m:ℤ)) ≤ z.2 ∧ z.2 ≤ -(2*(m:ℤ))-1)
    (ha : a.1=-(5*(m:ℤ))) (hb : b.1=5*(m:ℤ)-1) :
    ∃ u ∈ pL.support, ∃ v ∈ pR.support, ∃ q : squareLattice.Walk u v,
      q.support ⊆ p.support ∧ q.edges ⊆ p.edges ∧
      ∀ x y, s(x,y) ∈ q.edges →
        ∃ z, (z=x ∨ z=y) ∧ z ∉ pL.support ∧ z ∉ pR.support ∧
          rayIndex z pL=0 ∧ rayIndex z pR=1 := by
  have hpb : ∀ z ∈ p.support,
      -(5*(m:ℤ)) ≤ z.1 ∧ z.1 ≤ 5*(m:ℤ)-1 ∧
      -(16*(m:ℤ))-1 ≤ z.2 ∧ z.2 ≤ 16*(m:ℤ) := by
    intro z hz
    have hc := hp z hz
    exact ⟨hc.1,hc.2.1,by omega,by omega⟩
  have hLb : ∀ z ∈ pL.support,
      -(5*(m:ℤ)) ≤ z.1 ∧ z.1 ≤ 5*(m:ℤ)-1 ∧
      -(16*(m:ℤ))-1 ≤ z.2 ∧ z.2 ≤ 16*(m:ℤ) := by
    intro z hz
    have hc := hL z hz
    exact ⟨hc.1,by omega,hc.2.2⟩
  have hRb : ∀ z ∈ pR.support,
      -(5*(m:ℤ)) ≤ z.1 ∧ z.1 ≤ 5*(m:ℤ)-1 ∧
      -(16*(m:ℤ))-1 ≤ z.2 ∧ z.2 ≤ 16*(m:ℤ) := by
    intro z hz
    have hc := hR z hz
    exact ⟨by omega,hc.2⟩
  obtain ⟨l,hlp,hlL⟩ := rectangle_walks_common_vertex p pL (by omega) (by omega)
    hpb hLb ha hb hlb hlt
  obtain ⟨r,hrp,hrR⟩ := rectangle_walks_common_vertex p pR (by omega) (by omega)
    hpb hRb ha hb hrb hrt
  let P := (p.takeUntil l hlp).reverse.append (p.takeUntil r hrp)
  have hPsupp : P.support ⊆ p.support := by
    intro z hz
    rcases (SimpleGraph.Walk.mem_support_append_iff _ _).mp hz with hz | hz
    · exact (p.isSubwalk_takeUntil hlp).support_subset
        (by simpa only [SimpleGraph.Walk.support_reverse,List.mem_reverse] using hz)
    · exact (p.isSubwalk_takeUntil hrp).support_subset hz
  have hPedges : P.edges ⊆ p.edges := by
    intro e he
    simp only [P,SimpleGraph.Walk.edges_append,SimpleGraph.Walk.edges_reverse,List.mem_append,
      List.mem_reverse] at he
    rcases he with he | he
    · exact (p.isSubwalk_takeUntil hlp).edges_subset he
    · exact (p.isSubwalk_takeUntil hrp).edges_subset he
  have hdis : Disjoint {z | z ∈ pL.support} {z | z ∈ pR.support} := by
    apply Set.disjoint_left.mpr
    intro z hzL hzR
    have h₁ := hL z hzL
    have h₂ := hR z hzR
    omega
  have hn : ∀ u ∈ pL.support, ∀ v ∈ pR.support, ¬ squareLattice.Adj u v := by
    intro u hu v hv huv
    have h₁ := hL u hu
    have h₂ := hR v hv
    have hstep := (squareLattice_adj_iff _ _).mp huv
    omega
  obtain ⟨u,hu,v,hv,q,c,d,I,hq,hqs,hqe,hs,hI,hcover⟩ :=
    walk_between_full_traces_with_interior {z | z ∈ pL.support} {z | z ∈ pR.support}
      hdis hn P hlL hrR
  have hqSupp : q.support ⊆ p.support := fun _ hz => hPsupp (hqs hz)
  have hISupp : I.support ⊆ p.support := by
    intro z hz
    apply hqSupp
    rw [hs]
    simp [hz]
  have hstep : ∀ x y, squareLattice.Adj x y → |x.1-y.1| ≤ 1 := by
    intro x y hxy
    have hc := (squareLattice_adj_iff _ _).mp hxy
    rw [abs_le]
    omega
  obtain ⟨z,t,k,hz,hqsplit,_⟩ := walk_prefix_at_level Prod.fst hstep q 0
    (by have := hL u hu; omega) (by have := hR v hv; omega)
  have hzq : z ∈ q.support := by
    rw [hqsplit]
    exact (SimpleGraph.Walk.mem_support_append_iff _ _).mpr (Or.inl t.end_mem_support)
  have hzI : z ∈ I.support := by
    rw [hs] at hzq
    simp only [List.mem_cons,List.mem_append,List.not_mem_nil,or_false] at hzq
    have hu' := hL u hu
    have hv' := hR v hv
    rcases hzq with he | hzq | he
    · subst z; omega
    · exact hzq
    · subst z; omega
  have hrowsL : ∀ z ∈ I.support, lb.2 < z.2 ∧ z.2 < lt.2 := by
    intro z hz
    have hc := hp z (hISupp hz)
    rw [hlb,hlt]
    omega
  have hrowsR : ∀ z ∈ I.support, rb.2 < z.2 ∧ z.2 < rt.2 := by
    intro z hz
    have hc := hp z (hISupp hz)
    rw [hrb,hrt]
    omega
  have hLz : rayIndex z pL=0 := rayIndex_zero_of_right z pL (by
    intro w hw
    have hc := hL w hw
    omega)
  have hRz : rayIndex z pR=1 := by
    have hi := rayIndex_left_telescope z pR (by intro w hw; have := hR w hw; omega)
    have hc := hp z (hISupp hzI)
    rw [hrb,hrt,ite_eq_left (by omega),ite_eq_right (by omega)] at hi
    exact hi
  have hidxL : ∀ w ∈ I.support, rayIndex w pL=0 := by
    intro w hw
    have index (v : LatticeVertex) (hv : v ∈ I.support) : rayIndex c pL=rayIndex v pL :=
      screenIndex_eq_of_dual_walk_off_trace pL (I.takeUntil v hv)
        (fun a ha => (hI a ((I.isSubwalk_takeUntil hv).support_subset ha)).1)
        (fun a ha => hrowsL a ((I.isSubwalk_takeUntil hv).support_subset ha))
    exact (index w hw).symm.trans ((index z hzI).trans hLz)
  have hidxR : ∀ w ∈ I.support, rayIndex w pR=1 := by
    intro w hw
    have index (v : LatticeVertex) (hv : v ∈ I.support) : rayIndex c pR=rayIndex v pR :=
      screenIndex_eq_of_dual_walk_off_trace pR (I.takeUntil v hv)
        (fun a ha => (hI a ((I.isSubwalk_takeUntil hv).support_subset ha)).2)
        (fun a ha => hrowsR a ((I.isSubwalk_takeUntil hv).support_subset ha))
    exact (index w hw).symm.trans ((index z hzI).trans hRz)
  refine ⟨u,hu,v,hv,q,hqSupp,(fun _ he => hPedges (hqe he)),?_⟩
  intro x y hxy
  rcases hcover x y hxy with hx | hy
  · exact ⟨x,Or.inl rfl,(hI x hx).1,(hI x hx).2,hidxL x hx,hidxR x hx⟩
  · exact ⟨y,Or.inr rfl,(hI y hy).1,(hI y hy).2,hidxL y hy,hidxR y hy⟩

end
end PottsContinuity.Thm4Records
