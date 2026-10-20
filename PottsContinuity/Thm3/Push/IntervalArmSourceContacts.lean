module

public import PottsContinuity.Thm3.Push.IntervalArmLowerCollarIndex
public import PottsContinuity.Thm3.Push.IntervalArmFilledForest
public import PottsContinuity.Thm3.Push.IntervalArmRecord
public import PottsContinuity.Thm3.Push.BottomCappedCycle

@[expose] public section

namespace PottsContinuity.Push
open PottsContinuity.PD.FK PottsContinuity.PlanarTopology
noncomputable section

/-- One actual filled-frontier component contains at most ONE vertex of the
original source interval. The lower cap remains inside its source columns;
no assertion is made about bottom contacts outside that interval. -/
theorem intervalArmFilled_frontier_source_contacts_eq
    (N : ℕ) (l r : ℤ) (A : Configuration (rectangleGraph (0,0) N N))
    (u v : RectangleVertex (0,0) N N)
    (huI : u ∈ intervalArmBottomArc N l r) (hvI : v ∈ intervalArmBottomArc N l r)
    (hconn : ActualConnected (rectangleGraph (0,0) N N) (intervalArmFilledLeftFrontier N l r A) u v) :
    u = v := by
  classical
  have hu : u.val.2=0 := huI.1
  have hv : v.val.2=0 := hvI.1
  by_contra hne
  have hxy : u.val.1 ≠ v.val.1 := by
    intro he
    exact hne (Subtype.ext (Prod.ext he (hu.trans hv.symm)))
  obtain ⟨q,hq⟩ := hconn.exists_isPath
  let F := intervalArmFilledLeftFrontier N l r A
  let j := rectangleOpenGraphToSquare (0,0) N N F
  have huEq : u.val=(u.val.1,(0 : ℤ)) := Prod.ext rfl hu
  have hvEq : v.val=(v.val.1,(0 : ℤ)) := Prod.ext rfl hv
  let p := (q.map j).copy huEq hvEq
  have hp : p.IsPath := by
    apply ((q.map j).isPath_copy huEq hvEq).mpr
    exact hq.map (by
      intro a b h
      change a.val=b.val at h
      exact Subtype.ext h)
  have hbox : ∀ x ∈ p.support, x ∈ PD.FK.latticeRectangle (0,0) N N := by
    intro x hx
    have hcopy := (q.map j).support_copy huEq hvEq
    have hxmap : x ∈ (q.map j).support := hcopy ▸ hx
    rw [SimpleGraph.Walk.support_map] at hxmap
    obtain ⟨z,_,rfl⟩ := List.mem_map.mp hxmap
    exact z.property
  have htrace := rectangle_open_walk_trace_subset (0,0) N N F q
  have hP : ∀ f : (rectangleGraph (0,0) N N).edgeSet,
      (rectanglePrimalEdgeBond (0,0) N N f).toSym2 ∈ p.edges → f ∈ F := by
    intro f hf
    apply htrace
    apply (mem_rectangleTraceConfiguration (0,0) N N (q.map j) f).mpr
    have hcopy := (q.map j).edges_copy huEq hvEq
    have hfmap : (rectanglePrimalEdgeBond (0,0) N N f).toSym2 ∈ (q.map j).edges := hcopy ▸ hf
    erw [rectanglePrimalEdgeBond_toSym2_public] at hfmap
    exact hfmap
  obtain ⟨c,hc,hPC,hstrip,hbelow,hCP⟩ := exists_bottom_capped_cycle N u.val.1 v.val.1 hxy p hp hbox
  have hC : ∀ f : (rectangleGraph (0,0) N N).edgeSet,
      (rectanglePrimalEdgeBond (0,0) N N f).toSym2 ∈ c.edges → f ∈ F := by
    intro f hf
    let a := f.val.out.1
    let b := f.val.out.2
    have hpair : s(a,b)=f.val := Quot.out_eq _
    have heq : (rectanglePrimalEdgeBond (0,0) N N f).toSym2 = s(a.val,b.val) := by
      erw [rectanglePrimalEdgeBond_toSym2_public]
      change Sym2.map Subtype.val f.val = _
      rw [← hpair]
      rfl
    have ha := (mem_latticeRectangle (0,0) a.val N N).mp a.property
    have hb := (mem_latticeRectangle (0,0) b.val N N).mp b.property
    apply hP
    rw [heq] at hf ⊢
    exact hCP a.val b.val (by dsimp at ha; omega) (by dsimp at hb; omega) hf
  have hpne : p.edges ≠ [] := by
    intro he
    have heq : (u.val.1,(0 : ℤ))=(v.val.1,(0 : ℤ)) :=
      (SimpleGraph.Walk.edges_eq_nil.mp he).eq
    have hxyeq := congrArg (fun z : LatticeVertex => z.1) heq
    exact hxy hxyeq
  obtain ⟨e,he⟩ := List.exists_mem_of_ne_nil p.edges hpne
  let a := e.out.1
  let b := e.out.2
  have hpair : s(a,b)=e := Quot.out_eq _
  have hea : a ∈ e := by rw [← hpair]; exact (Sym2.mem_iff').mpr (Or.inl rfl)
  have heb : b ∈ e := by rw [← hpair]; exact (Sym2.mem_iff').mpr (Or.inr rfl)
  let a' : RectangleVertex (0,0) N N := ⟨a,hbox a (SimpleGraph.Walk.mem_support_of_mem_edges he hea)⟩
  let b' : RectangleVertex (0,0) N N := ⟨b,hbox b (SimpleGraph.Walk.mem_support_of_mem_edges he heb)⟩
  have hab : (rectangleGraph (0,0) N N).Adj a' b' := by
    apply (rectangleGraph_adj_iff (0,0) N N a' b').mpr
    exact p.adj_of_mem_edges (by rw [hpair]; exact he)
  let f : (rectangleGraph (0,0) N N).edgeSet :=
    ⟨s(a',b'),(rectangleGraph (0,0) N N).mem_edgeSet.mpr hab⟩
  have hfe : (rectanglePrimalEdgeBond (0,0) N N f).toSym2=e := by
    erw [rectanglePrimalEdgeBond_toSym2_public]
    exact hpair
  have hbelowI : ∀ z ∈ c.support, z.2 < 0 → l ≤ z.1 ∧ z.1 ≤ r := by
    intro z hz hz0
    have hh := hbelow z hz hz0
    have huBounds := huI.2
    have hvBounds := hvI.2
    exact ⟨by omega,by omega⟩
  exact lower_collar_closed_trail_avoids_interval_square_bonds N l r A c
    hc.isTrail.edges_nodup hstrip hbelowI hC f (by rw [hfe]; exact hPC he)

end
end PottsContinuity.Push
