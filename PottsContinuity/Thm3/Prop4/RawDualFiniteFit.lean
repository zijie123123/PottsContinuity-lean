module

public import PottsContinuity.Thm3.Prop4.SampledRawDualRegion

/-! # Literal sampled labels agree with the existing finite raw exploration -/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4
open PD.FK PD.FK.Medial
noncomputable section
local instance rawDualFiniteFitEdgeEq (a : LatticeVertex) (w h : ℕ) :
    DecidableEq (rectangleGraph a w h).edgeSet := Classical.decEq _

/-- The finite auxiliary cluster and the sampled face-label cluster coincide. -/
theorem sampledDualSeedRegion_iff_finite_reached (a : LatticeVertex) (w h : ℕ)
    (A : Configuration (rectangleGraph a w h)) (S : Finset (RectangleDualVertex a w h))
    (f : RectangleDualVertex a w h) :
    sampledDualSeedRegion a w h A (Subtype.val '' (S : Set (RectangleDualVertex a w h))) f.val ↔
      f ∈ Push.closedClusterReached (DualityExt.rectangleDualEdgeEquiv a w h) S A := by
  constructor
  · rintro ⟨s,⟨s',hs',rfl⟩,hp⟩
    refine ⟨s',hs',?_⟩
    rw [Push.auxiliaryClosedConfiguration_rectangle_eq]
    exact (rectangle_finite_closed_dual_reachable_iff_sampled a w h A s' f).mpr hp
  · rintro ⟨s,hs,hp⟩
    refine ⟨s.val,⟨s,hs,rfl⟩,?_⟩
    rw [Push.auxiliaryClosedConfiguration_rectangle_eq] at hp
    exact (rectangle_finite_closed_dual_reachable_iff_sampled a w h A s f).mp hp

/-- The face-defined reveal is EXACTLY the existing raw finite-cluster reveal. -/
theorem sampledRawDualReveal_eq_finite_raw (a : LatticeVertex) (w h : ℕ)
    (A : Configuration (rectangleGraph a w h)) (S : Finset (RectangleDualVertex a w h)) :
    sampledRawDualReveal a w h (Subtype.val '' (S : Set (RectangleDualVertex a w h))) A =
      Push.closedClusterReveal (DualityExt.rectangleDualEdgeEquiv a w h) S A := by
  classical
  ext e
  let d := rectanglePrimalDualEdgeEquiv a w h e
  have hpair : (DualityExt.rectangleDualEdgeEquiv a w h e).val =
      s(rectangleDualEdgeSource a w h d,rectangleDualEdgeTarget a w h d) := rfl
  rw [Push.mem_closedClusterReveal_iff_endpoint]
  change e ∈ rawFaceRegionReveal a w h _ ↔ _
  simp only [rawFaceRegionReveal,Finset.mem_filter,Finset.mem_univ,true_and]
  rw [hpair]
  constructor
  · rintro (hs | ht)
    · refine ⟨rectangleDualEdgeSource a w h d,Sym2.mem_iff.mpr (Or.inl rfl),?_⟩
      exact (sampledDualSeedRegion_iff_finite_reached a w h A S _).mp hs
    · refine ⟨rectangleDualEdgeTarget a w h d,Sym2.mem_iff.mpr (Or.inr rfl),?_⟩
      exact (sampledDualSeedRegion_iff_finite_reached a w h A S _).mp ht
  · rintro ⟨f,hf,hreach⟩
    rcases Sym2.mem_iff.mp hf with rfl | rfl
    · exact Or.inl ((sampledDualSeedRegion_iff_finite_reached a w h A S _).mpr hreach)
    · exact Or.inr ((sampledDualSeedRegion_iff_finite_reached a w h A S _).mpr hreach)

end
end PottsContinuity.Thm3.Prop4
