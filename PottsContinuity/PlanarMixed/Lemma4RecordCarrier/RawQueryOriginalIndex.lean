module

public import PottsContinuity.PlanarMixed.Lemma4StoppingRecords.OriginalClosedDualRead
public import PottsContinuity.Thm3.RSW.FiniteDualScreen
public import PottsContinuity.Thm3.Push.ClosedDualTraceIndex
public import PottsContinuity.Thm3.Push.DualCutCellBoundary

@[expose] public section

namespace PottsContinuity.PlanarMixed.Lemma4Connectors
open PD.FK PD.FK.Medial PD.Duality PD.RCInfinite Push
noncomputable section

/-- A raw query in the dual rectangle has an ORIGINAL primal endpoint with
the exterior seed index. The double-dual coordinate shift is explicit. -/
theorem raw_dual_query_original_endpoint_index
    (a : LatticeVertex) (w h : ℕ) (A : Configuration (rectangleGraph a w h))
    (seeds : Finset (RectangleDualVertex a w h))
    {z : LatticeVertex} (P : squareLattice.Walk z z)
    (hopen : ∀ f : (rectangleGraph a w h).edgeSet,
      (rectanglePrimalEdgeBond a w h f).toSym2 ∈ P.edges → f ∈ A)
    (k : ℤ) (hseed : ∀ s ∈ seeds, rayIndex (faceIndexMark s.val) P=k)
    (e : (rectangleGraph a w h).edgeSet)
    (he : e ∈ closedClusterReveal (DualityExt.rectangleDualEdgeEquiv a w h) seeds A) :
    ∃ v ∈ (primalBondOfDual (rectanglePrimalEdgeBond a w h e)).toSym2,
      rayIndex v P=k := by
  obtain ⟨v,hv,hidx⟩ := rectangle_raw_query_has_seed_index_of_open_trace a w h A seeds P hopen k hseed e he
  let d := rectanglePrimalDualEdgeEquiv a w h e
  let b := rectanglePrimalEdgeBond a w h e
  have hfaces : v.val=b.faceBase false ∨ v.val=b.faceBase true := by
    change v ∈ s(rectangleDualEdgeSource a w h d,rectangleDualEdgeTarget a w h d) at hv
    rcases Sym2.mem_iff'.mp hv with hv | hv
    · exact Or.inl ((congrArg Subtype.val hv).trans (rectangleDualEdgeSource_faceBase a w h d))
    · exact Or.inr ((congrArg Subtype.val hv).trans (rectangleDualEdgeTarget_faceBase a w h d))
  have hends := primalBondOfDual_endpoints_faceIndexMark b
  refine ⟨faceIndexMark v.val,?_,hidx⟩
  rcases hfaces with hv | hv
  · rw [hv,← hends.1]
    exact Sym2.mem_mk_left _ _
  · rw [hv,← hends.2]
    exact Sym2.mem_mk_right _ _

/-- Pulling the raw dual query back to an actually sampled source edge keeps
the original endpoint and its seed index, including queried closed chords. -/
theorem complementary_raw_query_original_endpoint_index
    (V : Finset LatticeVertex) (a : LatticeVertex) (w h : ℕ)
    (A : Configuration (PD.FK.squareLattice.induce (V : Set LatticeVertex)))
    (seeds : Finset (RectangleDualVertex a w h))
    {z : LatticeVertex} (P : squareLattice.Walk z z)
    (hopen : ∀ f : (rectangleGraph a w h).edgeSet,
      (rectanglePrimalEdgeBond a w h f).toSym2 ∈ P.edges →
        f ∈ originalClosedDualRectangleRead V a w h A)
    (k : ℤ) (hseed : ∀ s ∈ seeds, rayIndex (faceIndexMark s.val) P=k)
    (b : (PD.FK.squareLattice.induce (V : Set LatticeVertex)).edgeSet)
    (hb : b ∈ complementaryRevealPullback _ _ (rectangleDualOriginalEdge V a w h)
      (closedClusterReveal (DualityExt.rectangleDualEdgeEquiv a w h) seeds
        (originalClosedDualRectangleRead V a w h A))) :
    ∃ v ∈ b.val, rayIndex v.val P=k := by
  obtain ⟨e,he,heb⟩ := (mem_complementaryRevealPullback _ _ _ _ b).mp hb
  have hbond := (originalEdgeOfBond_eq_some_iff V _ b).mp heb
  have hpair : Sym2.map Subtype.val b.val=(primalBondOfDual (rectanglePrimalEdgeBond a w h e)).toSym2 :=
    congrArg Subtype.val hbond
  obtain ⟨v,hv,hidx⟩ := raw_dual_query_original_endpoint_index a w h _ seeds P hopen k hseed e he
  rw [← hpair] at hv
  obtain ⟨u,hu,rfl⟩ := Sym2.mem_map.mp hv
  exact ⟨u,hu,hidx⟩

/-- Every sampled edge of a genuinely closed source loop is open in its
literal complementary rectangle read. -/
theorem finite_closed_trace_rectangle_read_open
    (V : Finset LatticeVertex) (a : LatticeVertex) (w h : ℕ)
    (A : Configuration (PD.FK.squareLattice.induce (V : Set LatticeVertex)))
    {z : LatticeVertex} (P : squareLattice.Walk z z)
    (hclosed : RSW.finiteDualWalkClosed V A P)
    (e : (rectangleGraph a w h).edgeSet)
    (he : (rectanglePrimalEdgeBond a w h e).toSym2 ∈ P.edges) :
    e ∈ originalClosedDualRectangleRead V a w h A := by
  rw [originalClosedDualRectangleRead,mem_complementaryEdgeRead]
  intro b hb
  apply hclosed (primalBondOfDual (rectanglePrimalEdgeBond a w h e))
    (by convert! he using 1; simp only [dualBondOfPrimal_primalBondOfDual]) b
  exact congrArg Subtype.val ((originalEdgeOfBond_eq_some_iff V _ b).mp hb)

/-- No assertion about a geometrically highest path is needed: any genuine
closed source loop supplies the sampled-edge premise for raw-query transport. -/
theorem complementary_raw_query_endpoint_index_of_closed_trace
    (V : Finset LatticeVertex) (a : LatticeVertex) (w h : ℕ)
    (A : Configuration (PD.FK.squareLattice.induce (V : Set LatticeVertex)))
    (seeds : Finset (RectangleDualVertex a w h))
    {z : LatticeVertex} (P : squareLattice.Walk z z)
    (hclosed : RSW.finiteDualWalkClosed V A P)
    (k : ℤ) (hseed : ∀ s ∈ seeds, rayIndex (faceIndexMark s.val) P=k)
    (b : (PD.FK.squareLattice.induce (V : Set LatticeVertex)).edgeSet)
    (hb : b ∈ complementaryRevealPullback _ _ (rectangleDualOriginalEdge V a w h)
      (closedClusterReveal (DualityExt.rectangleDualEdgeEquiv a w h) seeds
        (originalClosedDualRectangleRead V a w h A))) :
    ∃ v ∈ b.val, rayIndex v.val P=k :=
  complementary_raw_query_original_endpoint_index V a w h A seeds P
    (finite_closed_trace_rectangle_read_open V a w h A P hclosed) k hseed b hb

/-- An open component with a different index cannot use a queried bond.
This is a bond statement, so it does not discard folds or unused chords. -/
theorem edge_not_query_of_component_index
    {V : Finset LatticeVertex} {z : LatticeVertex} (P : squareLattice.Walk z z)
    (A R : Configuration (PD.FK.squareLattice.induce (V : Set LatticeVertex)))
    (k i : ℤ) (hki : k ≠ i)
    (hquery : ∀ e ∈ R, ∃ v ∈ e.val, rayIndex v.val P=k)
    (u : (V : Set LatticeVertex))
    (hcomponent : ∀ v, ActualConnected _ A u v → rayIndex v.val P=i)
    (e : (PD.FK.squareLattice.induce (V : Set LatticeVertex)).edgeSet)
    (he : e ∈ A) (hroot : ∃ v ∈ e.val, ActualConnected _ A u v) : e ∉ R := by
  intro heR
  obtain ⟨v,hv,hidx⟩ := hquery e heR
  obtain ⟨t,ht,hut⟩ := hroot
  have huv : ActualConnected _ A t v := by
    induction heval : e.val using Sym2.inductionOn with
    | hf x y =>
      have hadj : (openGraph _ A).Adj x y := (openGraph_adj _ _ x y).mpr ⟨e,he,heval⟩
      rw [heval] at ht hv
      rcases Sym2.mem_iff'.mp ht with rfl | rfl
      all_goals rcases Sym2.mem_iff'.mp hv with rfl | rfl
      · exact SimpleGraph.Reachable.rfl
      · exact hadj.reachable
      · exact hadj.symm.reachable
      · exact SimpleGraph.Reachable.rfl
  exact hki (hidx.symm.trans (hcomponent v (hut.trans huv)))

end
end PottsContinuity.PlanarMixed.Lemma4Connectors
