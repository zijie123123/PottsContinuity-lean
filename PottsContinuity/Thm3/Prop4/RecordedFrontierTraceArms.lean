module

public import PottsContinuity.Thm3.Prop4.RecordedDualFaceFrontier

/-! # Literal recorded lower arms along a frontier walk -/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4
open PD.FK
noncomputable section

private theorem adjacent_of_mem_walk_ne_start {V : Type*} {G : SimpleGraph V}
    {u v : V} (p : G.Walk u v) (z : V) (hz : z ∈ p.support) (hne : z ≠ u) :
    ∃ y : V, G.Adj z y := by
  induction p with
  | nil => exact (hne (List.mem_singleton.mp hz)).elim
  | @cons u w v huw p ih =>
    rcases List.mem_cons.mp hz with hzu | hz
    · exact (hne hzu).elim
    · by_cases hzw : z = w
      · subst z
        exact ⟨u,huw.symm⟩
      · exact ih hz hzw

/-- At every visited vertex except the initial mark, a literal recorded
frontier walk supplies a lower sampled-dual arm in the same record. This
includes boundary vertices, corners and repeated visits. -/
theorem recorded_frontier_walk_vertex_has_lower_arm (a : LatticeVertex) (w h : ℕ)
    (R B : Configuration (rectangleGraph a w h)) (L : Set LatticeVertex)
    {u v : RectangleVertex a w h}
    (p : (openGraph _ (recordedDualFaceFrontier a w h R B L)).Walk u v)
    (z : RectangleVertex a w h) (hz : z ∈ p.support) (hne : z ≠ u) :
    ∃ f ∈ sampledStarFacePorts a w h z, ∃ s ∈ L,
      Nonempty ((recordedSampledClosedDualGraph a w h R B).Walk s f) := by
  obtain ⟨y,hzy⟩ := adjacent_of_mem_walk_ne_start p z hz hne
  obtain ⟨e,he,hexy⟩ := (openGraph_adj _ _ z y).mp hzy
  have hbond : (rectanglePrimalEdgeBond a w h e).toSym2 = s(z.val,y.val) := by
    erw [rectanglePrimalEdgeBond_toSym2_public,hexy]
    rfl
  have hzBond : (rectanglePrimalEdgeBond a w h e).source = z.val ∨
      (rectanglePrimalEdgeBond a w h e).target = z.val := by
    change s((rectanglePrimalEdgeBond a w h e).source,
      (rectanglePrimalEdgeBond a w h e).target) = s(z.val,y.val) at hbond
    rcases Sym2.eq_iff.mp hbond with ⟨hs,_⟩ | ⟨_,ht⟩
    · exact Or.inl hs
    · exact Or.inr ht
  exact recorded_dual_arm_at_frontier_bond a w h R B L e he z hzBond

/-- The same frontier path is an actual open path in the recorded state. -/
theorem recorded_frontier_walk_open_in_record (a : LatticeVertex) (w h : ℕ)
    (R B : Configuration (rectangleGraph a w h)) (L : Set LatticeVertex)
    {u v : RectangleVertex a w h}
    (p : (openGraph _ (recordedDualFaceFrontier a w h R B L)).Walk u v) :
    ∃ q : (openGraph _ B).Walk u v, q.support = p.support := by
  refine ⟨p.mapLe (openGraph_mono (recordedDualFaceFrontier_subset_recorded a w h R B L)),?_⟩
  exact SimpleGraph.Walk.support_mapLe_eq_support _ _

end
end PottsContinuity.Thm3.Prop4
