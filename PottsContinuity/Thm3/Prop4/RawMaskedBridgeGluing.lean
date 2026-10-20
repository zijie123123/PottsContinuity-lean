module

public import PottsContinuity.Thm3.Prop4.RawReplayExitHeight
public import PottsContinuity.Thm3.Prop4.StrictBandDualExclusion

@[expose] public section

namespace PottsContinuity.Thm3.Prop4
open PD.FK PD.FK.Medial PlanarTopology Exploration
noncomputable section
local instance rawMaskedBridgeGluingEdgeEq (a : LatticeVertex) (w h : ℕ) :
    DecidableEq (rectangleGraph a w h).edgeSet := Classical.decEq _

/-- Original raw replay connects the marked vertices inside an induced mask
when a reference strict-core crossing and the two signed raw-query exit
bounds hold. The premises concern original bonds, not replay connectivity. -/
theorem sourceMarkedRaw_masked_connection_of_query_exit_heights
    (a : LatticeVertex) (w h : ℕ) (hw : 1 ≤ w) (hh : 1 ≤ h)
    (u v : RectangleVertex a w h) (hu : u.val.1 = a.1) (hv : v.val.1 = a.1+(w : ℤ))
    (A B : Configuration (rectangleGraph a w h))
    (hA : ActualConnected (rectangleGraph a w h) A u v)
    (T : Set LatticeVertex) (t b R : ℝ) (ht : |t| ≤ 1)
    (hLower : ∀ e ∈ sampledRawDualReveal a w h (rectangleLowerDualArc a w h u.val v.val) A,
      ∀ z : RectangleVertex a w h, z ∈ e.val → z.val ∉ T →
        (z.val.2 : ℝ)-(t*z.val.1+b) ≤ -R)
    (hUpper : ∀ e ∈ sampledRawDualReveal a w h (rectangleUpperDualArc a w h u.val v.val) A,
      ∀ z : RectangleVertex a w h, z ∈ e.val → z.val ∉ T →
        R ≤ (z.val.2 : ℝ)-(t*z.val.1+b))
    (l r : RectangleVertex a w h) (hl : l.val.1 = a.1) (hr : r.val.1 = a.1+(w : ℤ))
    (p : (openGraph (rectangleGraph a w h)
      (B ∩ RSW.inducedConfigurationErasure {z : RectangleVertex a w h | z.val ∈ T}
        (Finset.univ : Configuration (rectangleGraph a w h)))).Walk l r)
    (hp : ∀ z ∈ p.support, |(z.val.2 : ℝ)-(t*z.val.1+b)| < R-1) :
    ActualConnected (rectangleGraph a w h)
      (replayRevealedState (rectangleGraph a w h) (sourceMarkedRawReveal a w h u v A)
        (revealRecordConfiguration (sourceMarkedRawReveal a w h u v) A) B ∩
        RSW.inducedConfigurationErasure {z : RectangleVertex a w h | z.val ∈ T}
          (Finset.univ : Configuration (rectangleGraph a w h))) u v := by
  classical
  by_contra hdis
  obtain ⟨x,hx,y,hy,⟨q⟩⟩ := sourceMarkedRaw_dual_bridge_of_masked_disconnection a w h hw hh u v hu hv A B _ hdis
  have hne : x ≠ y := by
    intro he
    exact Set.disjoint_left.mp (sampledDualSeedRegions_disjoint_of_marked_connection a w h A u v hu hv hA)
      hx (he ▸ hy)
  have hLsub : sampledRawDualReveal a w h (rectangleLowerDualArc a w h u.val v.val) A ⊆
      sourceMarkedRawReveal a w h u v A := by
    rw [sourceMarkedRawReveal_eq_union]
    exact Finset.subset_union_left
  have hUsub : sampledRawDualReveal a w h (rectangleUpperDualArc a w h u.val v.val) A ⊆
      sourceMarkedRawReveal a w h u v A := by
    rw [sourceMarkedRawReveal_eq_union]
    exact Finset.subset_union_right
  have hxH : (rectangleClamp a w h (dualFaceCenter unitLatticeMesh x)).im-
      (t*(rectangleClamp a w h (dualFaceCenter unitLatticeMesh x)).re+b) ≤ -(R-1) := by
    cases q with
    | nil => exact (hne rfl).elim
    | @cons x z y hadj tail =>
      have hz : ¬sampledDualSeedRegion a w h A (rectangleLowerDualArc a w h u.val v.val) z :=
        fun hz => hadj.2.1 ⟨hx,hz⟩
      have h := sampledRawDual_masked_replay_exit_height_le a w h (rectangleLowerDualArc a w h u.val v.val) A B (sourceMarkedRawReveal a w h u v A) T hLsub t b (-R) ht hLower hx hz hadj.1
      linarith only [h]
  have hyH : R-1 ≤ (rectangleClamp a w h (dualFaceCenter unitLatticeMesh y)).im-
      (t*(rectangleClamp a w h (dualFaceCenter unitLatticeMesh y)).re+b) := by
    cases q.reverse with
    | nil => exact (hne rfl).elim
    | @cons y z x hadj tail =>
      have hz : ¬sampledDualSeedRegion a w h A (rectangleUpperDualArc a w h u.val v.val) z :=
        fun hz => hadj.2.2 ⟨hy,hz⟩
      exact sampledRawDual_masked_replay_exit_height_ge a w h (rectangleUpperDualArc a w h u.val v.val) A B (sourceMarkedRawReveal a w h u v A) T hUsub t b R ht hUpper hy hz hadj.1
  exact strict_affine_band_excludes_sampled_dual_bridge a w h _ hl hr p t b (R-1) hp x y hne
    (q.mapLe (sourceMarkedRaw_masked_dual_bridge_le_reference a w h u v A B _)) hxH hyH

end
end PottsContinuity.Thm3.Prop4
