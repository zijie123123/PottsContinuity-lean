module

public import PottsContinuity.PlanarTopology.RectangleTrace
public import PottsContinuity.PD.Duality.RectangleCrossingExclusion
public import Mathlib.Tactic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Combinatorics.SimpleGraph.Walk.Maps
public import Mathlib.Order.CompletePartialOrder

/-!
# Label-preserving dual walk interpolation

The interpolation and edge-label lemmas below are adapted from the private
helpers in PD/Duality/RectangleCrossingExclusion.lean. Unlike a set of all
segments between visited neighbours, the actual-edge range statement keeps
the original walk's edge labels. This is essential for restricted traces.
-/

@[expose] public section

namespace PottsContinuity.PlanarTopology
open PD.FK PD.FK.Medial PD.FK.Curves unitInterval
noncomputable section

def rectangleDualOpenGraphToSquare (a : LatticeVertex) (w h : ℕ)
    (D : Configuration (rectangleDualGraph a w h)) :
    openGraph (rectangleDualGraph a w h) D →g squareLattice where
  toFun := fun v => v.1
  map_rel' := by
    intro u v huv
    exact (rectangleDualAmbientGraph_adj_iff a w h _ _).mp
      (rectangleDualGraph_le_ambient a w h (openGraph_le _ _ huv))

private theorem walk_edge_mem_step {V : Type*} {G : SimpleGraph V} {u v : V}
    (p : G.Walk u v) {e : Sym2 V} (he : e ∈ p.edges) :
    ∃ x y : V, G.Adj x y ∧ e = s(x,y) := by
  induction p with
  | @nil u => simp at he
  | @cons u v w hadj p ih =>
      simp only [SimpleGraph.Walk.edges_cons, List.mem_cons] at he
      rcases he with he | he
      · exact ⟨u,v,hadj,he⟩
      · obtain ⟨x,y,hxy,heq⟩ := ih he
        exact ⟨x,y,hxy,heq⟩

private theorem mapped_walk_edge_mem_step {V W : Type*} {G : SimpleGraph V}
    {H : SimpleGraph W} (f : G →g H) {u v : V} (p : G.Walk u v)
    {x y : W} (he : s(x,y) ∈ (p.map f).edges) :
    ∃ x' y' : V, G.Adj x' y' ∧ s(x',y') ∈ p.edges ∧
      (f x' = x ∧ f y' = y ∨ f x' = y ∧ f y' = x) := by
  rw [SimpleGraph.Walk.edges_map] at he
  rcases List.mem_map.mp he with ⟨e, he, hemap⟩
  obtain ⟨x',y',hadj,heq⟩ := walk_edge_mem_step p he
  rw [heq] at he
  have hpair : s(f x', f y') = s(x,y) := by
    simpa [heq] using hemap
  rcases Sym2.eq_iff.mp hpair with ⟨h₁,h₂⟩ | ⟨h₁,h₂⟩
  · exact ⟨x',y',hadj,he,Or.inl ⟨h₁,h₂⟩⟩
  · exact ⟨x',y',hadj,he,Or.inr ⟨h₁,h₂⟩⟩

theorem latticeWalkPath_range_actual_segment (δ : PositiveMesh)
    {u v : LatticeVertex} (p : squareLattice.Walk u v) (hne : 0 < p.length)
    {z : ℂ} (hz : z ∈ Set.range (latticeWalkPath δ p)) :
    ∃ x y : LatticeVertex, x ∈ p.support ∧ y ∈ p.support ∧
      s(x,y) ∈ p.edges ∧ squareLattice.Adj x y ∧
      z ∈ Set.range (Path.segment (latticeEmbed δ x)
        (latticeEmbed δ y)) := by
  induction p with
  | @nil u => simp at hne
  | @cons u v w hadj p ih =>
      change z ∈ Set.range
        ((Path.segment (latticeEmbed δ u) (latticeEmbed δ v)).trans
          (latticeWalkPath δ p)) at hz
      rw [Path.trans_range] at hz
      rcases hz with hfirst | htail
      · refine ⟨u,v,by simp, ?_⟩
        refine ⟨List.mem_cons.mpr (Or.inr (SimpleGraph.Walk.start_mem_support p)), ?_⟩
        exact ⟨by simp, hadj, hfirst⟩
      · by_cases hlen : p.length = 0
        · have hvw : v = w := SimpleGraph.Walk.eq_of_length_eq_zero hlen
          subst w
          have hpNil : p = SimpleGraph.Walk.nil :=
            (SimpleGraph.Walk.eq_nil_iff_nil).2 (SimpleGraph.Walk.length_eq_zero_iff.mp hlen)
          subst p
          have hvz : z = latticeEmbed δ v := by
            rcases htail with ⟨t, ht⟩
            simpa [latticeWalkPath] using ht.symm
          subst z
          refine ⟨u,v,by simp, by simp, ?_⟩
          refine ⟨by simp, hadj, ?_⟩
          rw [Path.range_segment]
          exact right_mem_segment ℝ _ _
        · obtain ⟨x,y,hx,hy,he,hxy,hseg⟩ := ih (by omega) htail
          refine ⟨x,y,List.mem_cons.mpr (Or.inr hx), ?_⟩
          refine ⟨List.mem_cons.mpr (Or.inr hy), ?_⟩
          exact ⟨List.mem_cons.mpr (Or.inr he), hxy, hseg⟩

private theorem rectangleDualWalk_segment_edge_label
    (a : LatticeVertex) (w h : ℕ) (A : Configuration (rectangleGraph a w h))
    {u v : RectangleDualVertex a w h}
    (q : (openGraph (rectangleDualGraph a w h)
      (rectangleDualConfiguration a w h A)).Walk u v)
    {x y : LatticeVertex}
    (he : s(x,y) ∈ (q.map (rectangleDualOpenGraphToSquare a w h
      (rectangleDualConfiguration a w h A))).edges) :
    ∃ e : RectangleDualEdgeCarrier a w h,
      e.primalEdge ∉ A ∧ e.crossingBond.toSym2 = s(x,y) := by
  let D := rectangleDualConfiguration a w h A
  obtain ⟨X,Y,hXY,hEdge,hmap⟩ :=
    mapped_walk_edge_mem_step (rectangleDualOpenGraphToSquare a w h D) q he
  have hOpen : s(X,Y) ∈ openEdges (rectangleDualGraph a w h) D := by
    rw [← openGraph_edgeSet]
    exact q.edges_subset_edgeSet hEdge
  change ∃ g : (rectangleDualGraph a w h).edgeSet,
    g ∈ (D : Set (rectangleDualGraph a w h).edgeSet) ∧ (g : Sym2 _) = s(X,Y) at hOpen
  rcases hOpen with ⟨g,hg,hgval⟩
  let e := (rectangleDualGraphEdgeEquiv a w h).symm g
  have heq : rectangleDualGraphEdgeEquiv a w h e = g := Equiv.apply_symm_apply _ _
  have hmem : rectangleDualGraphEdgeEquiv a w h e ∈ D := by simpa [heq] using hg
  have hclosed : e.primalEdge ∉ A := (mem_rectangleDualConfiguration a w h A e).mp hmem
  have hpair : e.crossingBond.toSym2 = s(X.val,Y.val) := by
    have hpair' := congrArg Subtype.val heq
    change rectangleDualCarrierPair a w h e = (g : Sym2 _) at hpair'
    rw [hgval] at hpair'
    have hm := congrArg (Sym2.map (fun z : RectangleDualVertex a w h => z.1)) hpair'
    simpa [rectangleDualCarrierPair, LatticeBond.toSym2,
      rectangleDualEdgeSource_val, rectangleDualEdgeTarget_val] using hm
  rcases hmap with hmap | hmap
  · rcases hmap with ⟨hX,hY⟩
    change X.val = x at hX
    change Y.val = y at hY
    exact ⟨e,hclosed,hpair.trans (by rw [hX,hY])⟩
  · rcases hmap with ⟨hX,hY⟩
    change X.val = y at hX
    change Y.val = x at hY
    exact ⟨e,hclosed,hpair.trans (by rw [hX,hY]; exact Sym2.eq_swap)⟩

theorem dualCenterSegment_subset_label (δ : PositiveMesh)
    (d : LatticeBond) {x y : LatticeVertex}
    (hpair : d.toSym2 = s(x,y)) :
    Set.range (Path.segment (dualFaceCenter δ x)
      (dualFaceCenter δ y)) ⊆ dualBondSegment δ d := by
  have hends : (d.source = x ∧ d.target = y) ∨
      (d.source = y ∧ d.target = x) := by
    simpa [LatticeBond.toSym2] using Sym2.eq_iff.mp hpair
  rw [Path.range_segment]
  rcases hends with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · intro z hz
    exact hz
  · intro z hz
    exact (segment_symm ℝ _ _).subset hz

theorem latticeSegment_subset_primalBond (δ : PositiveMesh)
    (b : LatticeBond) {x y : LatticeVertex}
    (hpair : b.toSym2 = s(x,y)) :
    Set.range (Path.segment (latticeEmbed δ x)
      (latticeEmbed δ y)) ⊆ primalBondSegment δ b := by
  have hends : (b.source = x ∧ b.target = y) ∨
      (b.source = y ∧ b.target = x) := by
    simpa [LatticeBond.toSym2] using Sym2.eq_iff.mp hpair
  rw [Path.range_segment, primalBondSegment]
  rcases hends with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · intro z hz
    exact hz
  · intro z hz
    exact (segment_symm ℝ _ _).subset hz

def dualWalkCurve (δ : PositiveMesh) : {u v : LatticeVertex} →
    squareLattice.Walk u v → Path (dualFaceCenter δ u)
      (dualFaceCenter δ v)
  | _, _, .nil => Path.refl _
  | u, _, .cons (v := v) _ p =>
      (Path.segment (dualFaceCenter δ u)
        (dualFaceCenter δ v)).trans (dualWalkCurve δ p)

theorem dualWalkCurve_range_actual_segment (δ : PositiveMesh)
    {u v : LatticeVertex} (p : squareLattice.Walk u v) (hne : 0 < p.length)
    {z : ℂ} (hz : z ∈ Set.range (dualWalkCurve δ p)) :
    ∃ x y : LatticeVertex, x ∈ p.support ∧ y ∈ p.support ∧
      s(x,y) ∈ p.edges ∧ squareLattice.Adj x y ∧
      z ∈ Set.range (Path.segment (dualFaceCenter δ x)
        (dualFaceCenter δ y)) := by
  induction p with
  | @nil u => simp at hne
  | @cons u v w hadj p ih =>
      change z ∈ Set.range
        ((Path.segment (dualFaceCenter δ u)
          (dualFaceCenter δ v)).trans (dualWalkCurve δ p)) at hz
      rw [Path.trans_range] at hz
      rcases hz with hfirst | htail
      · refine ⟨u,v,by simp, ?_⟩
        refine ⟨List.mem_cons.mpr (Or.inr (SimpleGraph.Walk.start_mem_support p)), ?_⟩
        exact ⟨by simp, hadj, hfirst⟩
      · by_cases hlen : p.length = 0
        · have hvw : v = w := SimpleGraph.Walk.eq_of_length_eq_zero hlen
          subst w
          have hpNil : p = SimpleGraph.Walk.nil :=
            (SimpleGraph.Walk.eq_nil_iff_nil).2 (SimpleGraph.Walk.length_eq_zero_iff.mp hlen)
          subst p
          have hvz : z = dualFaceCenter δ v := by
            rcases htail with ⟨t, ht⟩
            simpa [dualWalkCurve] using ht.symm
          subst z
          refine ⟨u,v,by simp, by simp, ?_⟩
          refine ⟨by simp, hadj, ?_⟩
          rw [Path.range_segment]
          exact right_mem_segment ℝ _ _
        · obtain ⟨x,y,hx,hy,he,hxy,hseg⟩ := ih (by omega) htail
          refine ⟨x,y,List.mem_cons.mpr (Or.inr hx), ?_⟩
          refine ⟨List.mem_cons.mpr (Or.inr hy), ?_⟩
          exact ⟨List.mem_cons.mpr (Or.inr he), hxy, hseg⟩

theorem rectangleDualWalkPath_point_on_dualBond (δ : PositiveMesh)
    (a : LatticeVertex) (w h : ℕ) (A : Configuration (rectangleGraph a w h))
    {u v : RectangleDualVertex a w h}
    (q : (openGraph (rectangleDualGraph a w h)
      (rectangleDualConfiguration a w h A)).Walk u v)
    (hqpos : 0 < (q.map (rectangleDualOpenGraphToSquare a w h
      (rectangleDualConfiguration a w h A))).length)
    {z : ℂ} (hz : z ∈ Set.range (dualWalkCurve δ
      (q.map (rectangleDualOpenGraphToSquare a w h
        (rectangleDualConfiguration a w h A))))) :
    ∃ e : RectangleDualEdgeCarrier a w h,
      e.primalEdge ∉ A ∧ z ∈ dualBondSegment δ e.crossingBond := by
  let qs := q.map (rectangleDualOpenGraphToSquare a w h
    (rectangleDualConfiguration a w h A))
  obtain ⟨x,y,hx,hy,hedge,hadj,hseg⟩ :=
    dualWalkCurve_range_actual_segment δ qs hqpos hz
  obtain ⟨e,heclosed,hpair⟩ :=
    rectangleDualWalk_segment_edge_label a w h A q hedge
  exact ⟨e,heclosed,dualCenterSegment_subset_label δ e.crossingBond hpair hseg⟩


/-- A complementary dual segment misses the ENTIRE original walk whenever its
crossed rectangle edge is absent from the restricted trace. No confinement or
simplicity of the original walk is required. -/
theorem trace_closed_dualBond_disjoint_walk (δ : PositiveMesh)
    (a : LatticeVertex) (w h : ℕ) {u v : LatticeVertex}
    (p : PD.squareLattice.Walk u v) (d : RectangleDualEdgeCarrier a w h)
    (hd : d.primalEdge ∉ rectangleTraceConfiguration a w h p) :
    Disjoint (Set.range (latticeWalkPath δ p)) (dualBondSegment δ d.crossingBond) := by
  apply Set.disjoint_left.mpr
  intro z hzP hzD
  by_cases hzero : p.length = 0
  · have huv := SimpleGraph.Walk.eq_of_length_eq_zero hzero
    subst v
    have hp : p = .nil := (SimpleGraph.Walk.eq_nil_iff_nil).mpr
      (SimpleGraph.Walk.length_eq_zero_iff.mp hzero)
    subst p
    obtain ⟨t,rfl⟩ := hzP
    exact latticeVertex_not_mem_dualBondSegment δ u d.crossingBond hzD
  · obtain ⟨x,y,_,_,he,hxy,hseg⟩ :=
      latticeWalkPath_range_actual_segment δ p (Nat.pos_of_ne_zero hzero) hzP
    let b := wholePlaneBondEdgeEquiv.symm ⟨s(x,y),hxy⟩
    have hb : b.toSym2 = s(x,y) := congrArg Subtype.val
      (wholePlaneBondEdgeEquiv.apply_symm_apply ⟨s(x,y),hxy⟩)
    have hzB := latticeSegment_subset_primalBond δ b hb hseg
    have hcross := (primalDualSegments_intersect_iff δ b d.crossingBond).mp ⟨z,hzB,hzD⟩
    have hbond : rectanglePrimalEdgeBond a w h d.primalEdge = b := by
      have hh := congrArg primalBondOfDual hcross
      simpa only [rectangleDualEdge_crossedPrimalBond,
        primalBondOfDual_dualBondOfPrimal] using hh
    apply hd
    apply (mem_rectangleTraceConfiguration a w h p d.primalEdge).mpr
    rw [← rectanglePrimalEdgeBond_toSym2_public, hbond, hb]
    exact he

end
end PottsContinuity.PlanarTopology
