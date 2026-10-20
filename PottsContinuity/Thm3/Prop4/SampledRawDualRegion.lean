module

public import PottsContinuity.Thm3.Prop4.RawFaceEdgeDomain

/-! # The raw sampled closed-dual exploration on an edge-defined domain -/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4
open PD.FK PD.FK.Medial
noncomputable section
local instance sampledRawRegionEdgeEq (a : LatticeVertex) (w h : ℕ) :
    DecidableEq (rectangleGraph a w h).edgeSet := Classical.decEq _

/-- All face labels reached along actual sampled closed dual bonds from S. -/
def sampledDualSeedRegion (a : LatticeVertex) (w h : ℕ)
    (A : Configuration (rectangleGraph a w h)) (S : Set LatticeVertex) (f : LatticeVertex) : Prop :=
  ∃ s ∈ S, (PlanarTopology.rectangleSampledClosedDualGraph a w h A).Reachable s f

/-- The source raw reveal, with no exterior or trace-to-trace completion. -/
def sampledRawDualReveal (a : LatticeVertex) (w h : ℕ)
    (S : Set LatticeVertex) (A : Configuration (rectangleGraph a w h)) :
    Configuration (rectangleGraph a w h) :=
  rawFaceRegionReveal a w h (sampledDualSeedRegion a w h A S)

/-- A sampled closed step preserves the actual reached face region. -/
theorem sampledDualSeedRegion_step (a : LatticeVertex) (w h : ℕ)
    (A : Configuration (rectangleGraph a w h)) (S : Set LatticeVertex)
    {f g : LatticeVertex}
    (hfg : (PlanarTopology.rectangleSampledClosedDualGraph a w h A).Adj f g)
    (hf : sampledDualSeedRegion a w h A S f) : sampledDualSeedRegion a w h A S g := by
  obtain ⟨s,hs,hp⟩ := hf
  exact ⟨s,hs,hp.trans hfg.reachable⟩

/-- Closure of the actual raw region across every original closed bond. -/
theorem sampledDualSeedRegion_closed_iff (a : LatticeVertex) (w h : ℕ)
    (A : Configuration (rectangleGraph a w h)) (S : Set LatticeVertex)
    (e : (rectangleGraph a w h).edgeSet) (he : e ∉ A) :
    sampledDualSeedRegion a w h A S (rectangleCrossingDualBond a w h e).source ↔
      sampledDualSeedRegion a w h A S (rectangleCrossingDualBond a w h e).target := by
  have hstep : (PlanarTopology.rectangleSampledClosedDualGraph a w h A).Adj
      (rectangleCrossingDualBond a w h e).source (rectangleCrossingDualBond a w h e).target :=
    ⟨rectanglePrimalDualEdgeEquiv a w h e,he,Or.inl ⟨rfl,rfl⟩⟩
  exact ⟨sampledDualSeedRegion_step a w h A S hstep,
    sampledDualSeedRegion_step a w h A S hstep.symm⟩

/-- Source frontiers are sampled open bonds, even though interior queried
bonds may be open as well. -/
theorem sampledRawDual_frontier_open (a : LatticeVertex) (w h : ℕ)
    (A : Configuration (rectangleGraph a w h)) (S : Set LatticeVertex) :
    rawFaceRegionFrontier a w h (sampledDualSeedRegion a w h A S) ⊆ A :=
  rawFaceRegionFrontier_subset_open a w h _ A (sampledDualSeedRegion_closed_iff a w h A S)

/-- Every raw queried closed bond has both dual endpoints reached. -/
theorem sampledRawDual_closed_faces (a : LatticeVertex) (w h : ℕ)
    (A : Configuration (rectangleGraph a w h)) (S : Set LatticeVertex)
    (e : (rectangleGraph a w h).edgeSet)
    (he : e ∈ sampledRawDualReveal a w h S A) (hclosed : e ∉ A) :
    sampledDualSeedRegion a w h A S (rectangleCrossingDualBond a w h e).source ∧
      sampledDualSeedRegion a w h A S (rectangleCrossingDualBond a w h e).target :=
  rawFaceRegionReveal_closed_faces a w h _ A (sampledDualSeedRegion_closed_iff a w h A S) e he hclosed

/-- Any compatible sample preserves membership along a closed dual step
starting in the original explored region. -/
theorem sampledRawDual_compatible_step (a : LatticeVertex) (w h : ℕ)
    (S : Set LatticeVertex) (A C : Configuration (rectangleGraph a w h))
    (hagree : C ∩ sampledRawDualReveal a w h S A = A ∩ sampledRawDualReveal a w h S A)
    {x y : LatticeVertex}
    (hxy : (PlanarTopology.rectangleSampledClosedDualGraph a w h C).Adj x y)
    (hx : sampledDualSeedRegion a w h A S x) : sampledDualSeedRegion a w h A S y := by
  classical
  obtain ⟨d,hd,hends⟩ := hxy
  have heR : d.primalEdge ∈ sampledRawDualReveal a w h S A := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    rw [← d.crossingBond_eq]
    rcases hends with ⟨hxs,_⟩ | ⟨hxt,_⟩
    · exact Or.inl (hxs ▸ hx)
    · exact Or.inr (hxt ▸ hx)
  have hstate := Finset.ext_iff.mp hagree d.primalEdge
  erw [Finset.mem_inter,Finset.mem_inter] at hstate
  have hdA : d.primalEdge ∉ A := fun ha => hd (hstate.mpr ⟨ha,heR⟩).1
  exact sampledDualSeedRegion_step a w h A S ⟨d,hdA,hends⟩ hx

/-- Every original closed dual step starting in the explored region is
retained closed in a compatible sample. -/
theorem sampledRawDual_original_step_retained (a : LatticeVertex) (w h : ℕ)
    (S : Set LatticeVertex) (A C : Configuration (rectangleGraph a w h))
    (hagree : C ∩ sampledRawDualReveal a w h S A = A ∩ sampledRawDualReveal a w h S A)
    {x y : LatticeVertex}
    (hxy : (PlanarTopology.rectangleSampledClosedDualGraph a w h A).Adj x y)
    (hx : sampledDualSeedRegion a w h A S x) :
    (PlanarTopology.rectangleSampledClosedDualGraph a w h C).Adj x y := by
  classical
  obtain ⟨d,hd,hends⟩ := hxy
  have heR : d.primalEdge ∈ sampledRawDualReveal a w h S A := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    rw [← d.crossingBond_eq]
    rcases hends with ⟨hxs,_⟩ | ⟨hxt,_⟩
    · exact Or.inl (hxs ▸ hx)
    · exact Or.inr (hxt ▸ hx)
  have hstate := Finset.ext_iff.mp hagree d.primalEdge
  erw [Finset.mem_inter,Finset.mem_inter] at hstate
  exact ⟨d,(fun hc => hd (hstate.mp ⟨hc,heR⟩).1),hends⟩

/-- The entire raw reached face region is fixed by the recorded primal states. -/
theorem sampledRawDual_region_eq_of_agreement (a : LatticeVertex) (w h : ℕ)
    (S : Set LatticeVertex) (A C : Configuration (rectangleGraph a w h))
    (hagree : C ∩ sampledRawDualReveal a w h S A = A ∩ sampledRawDualReveal a w h S A) :
    sampledDualSeedRegion a w h C S = sampledDualSeedRegion a w h A S := by
  funext y
  apply propext
  constructor
  · rintro ⟨s,hs,⟨p⟩⟩
    have transfer {x y} (p : (PlanarTopology.rectangleSampledClosedDualGraph a w h C).Walk x y) :
        sampledDualSeedRegion a w h A S x → sampledDualSeedRegion a w h A S y := by
      induction p with
      | nil => exact id
      | cons hxy p ih =>
        exact fun hx => ih (sampledRawDual_compatible_step a w h S A C hagree hxy hx)
    exact transfer p ⟨s,hs,SimpleGraph.Reachable.refl s⟩
  · rintro ⟨s,hs,⟨p⟩⟩
    have liftWalk {x y} (p : (PlanarTopology.rectangleSampledClosedDualGraph a w h A).Walk x y) :
        sampledDualSeedRegion a w h A S x →
        (PlanarTopology.rectangleSampledClosedDualGraph a w h C).Reachable x y := by
      induction p with
      | nil => exact fun _ => SimpleGraph.Reachable.refl _
      | cons hxy p ih =>
        intro hx
        exact (sampledRawDual_original_step_retained a w h S A C hagree hxy hx).reachable.trans
          (ih (sampledDualSeedRegion_step a w h A S hxy hx))
    exact ⟨s,hs,liftWalk p ⟨s,hs,SimpleGraph.Reachable.refl s⟩⟩

/-- The uncompleted raw sampled exploration is a stopping set on all samples. -/
theorem sampledRawDualReveal_stable (a : LatticeVertex) (w h : ℕ)
    (S : Set LatticeVertex) (A C : Configuration (rectangleGraph a w h))
    (hagree : C ∩ sampledRawDualReveal a w h S A = A ∩ sampledRawDualReveal a w h S A) :
    sampledRawDualReveal a w h S C = sampledRawDualReveal a w h S A := by
  unfold sampledRawDualReveal
  rw [sampledRawDual_region_eq_of_agreement a w h S A C hagree]

/-- Simultaneously exploring two boundary arcs is exactly exploring their
union, with no extra original bond queried. -/
theorem sampledRawDualReveal_union (a : LatticeVertex) (w h : ℕ)
    (S T : Set LatticeVertex) (A : Configuration (rectangleGraph a w h)) :
    sampledRawDualReveal a w h (S ∪ T) A =
      sampledRawDualReveal a w h S A ∪ sampledRawDualReveal a w h T A := by
  classical
  have hregion (f) : sampledDualSeedRegion a w h A (S ∪ T) f ↔
      sampledDualSeedRegion a w h A S f ∨ sampledDualSeedRegion a w h A T f := by
    constructor
    · rintro ⟨s,hs,hp⟩
      rcases hs with hs | hs
      · exact Or.inl ⟨s,hs,hp⟩
      · exact Or.inr ⟨s,hs,hp⟩
    · rintro (⟨s,hs,hp⟩ | ⟨s,hs,hp⟩)
      · exact ⟨s,Or.inl hs,hp⟩
      · exact ⟨s,Or.inr hs,hp⟩
  ext e
  simp only [sampledRawDualReveal,rawFaceRegionReveal,Finset.mem_filter,Finset.mem_univ,
    true_and,Finset.mem_union,hregion]
  tauto

/-- On a genuine marked primal connection the two complementary sampled
closed-dual reached regions are disjoint. -/
theorem sampledDualSeedRegions_disjoint_of_marked_connection (a : LatticeVertex) (w h : ℕ)
    (A : Configuration (rectangleGraph a w h)) (u v : RectangleVertex a w h)
    (hu : u.val.1 = a.1) (hv : v.val.1 = a.1+(w : ℤ))
    (hconn : ActualConnected (rectangleGraph a w h) A u v) :
    Disjoint {f | sampledDualSeedRegion a w h A
        (PlanarTopology.rectangleLowerDualArc a w h u.val v.val) f}
      {f | sampledDualSeedRegion a w h A
        (PlanarTopology.rectangleUpperDualArc a w h u.val v.val) f} := by
  apply Set.disjoint_left.mpr
  rintro f ⟨s,hs,⟨p⟩⟩ ⟨t,ht,⟨q⟩⟩
  exact PlanarTopology.rectangle_sampled_dual_screen_excludes_primal
    a w h A u v hu hv s t hs ht (p.append q.reverse) hconn

end
end PottsContinuity.Thm3.Prop4
