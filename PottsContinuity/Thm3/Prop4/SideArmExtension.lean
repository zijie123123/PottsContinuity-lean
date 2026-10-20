module

public import PottsContinuity.Thm3.Prop4.SideArmGeometry
public import PottsContinuity.Infinite.Translation
public import PottsContinuity.PD.RCInfinite.FiniteModification

/-! # One-edge extension of actual side arms -/

@[expose] public section

open MeasureTheory

namespace PottsContinuity.Thm3.Prop4

open PD.FK PD.RCInfinite

/-- Every selected direction gives an actual original lattice edge. -/
theorem sideDirection_adj (d : Fin 4) : PottsContinuity.squareLattice.Adj (0,0) (sideDirection d) := by
  fin_cases d <;> norm_num [sideDirection, PottsContinuity.squareLattice]

/-- The original edge opened to extend the chosen face arm. -/
def sideDirectionEdge (d : Fin 4) : PottsContinuity.squareLattice.edgeSet :=
  ⟨s((0,0),sideDirection d),PottsContinuity.squareLattice.mem_edgeSet.mpr (sideDirection_adj d)⟩

/-- Exact configuration translation identity for the selected face. -/
theorem sideArmEvent_translation_preimage (n : ℕ) (d : Fin 4) :
    (latticeConfigurationTranslate (sideDirection d)) ⁻¹' shiftedSideArmEvent n d =
      sideArmEvent n d := by
  ext ω
  have hconn (z : ℤ × ℤ) :
      (PottsContinuity.rcInfiniteOpenGraph (latticeConfigurationTranslate (sideDirection d) ω)).Reachable
          (sideDirection d) (z+sideDirection d) ↔
        (PottsContinuity.rcInfiniteOpenGraph ω).Reachable (0,0) z := by
    change (PD.rcInfiniteOpenGraph (latticeConfigurationTranslate (sideDirection d) ω)).Reachable
      (sideDirection d) (z+sideDirection d) ↔ (PD.rcInfiniteOpenGraph ω).Reachable (0,0) z
    simpa only [PD.CorrLength.connectionEvent_iff_rcInfiniteReachable, latticeTranslate,
      Prod.add_def, add_comm, zero_add] using
      PD.CorrLength.connectionEvent_translation (sideDirection d) (0,0) z ω
  change (∃ z ∈ vertexBoundary (box n),
    z.1*(sideDirection d).1+z.2*(sideDirection d).2 = (n : ℤ) ∧
    (PottsContinuity.rcInfiniteOpenGraph
      (latticeConfigurationTranslate (sideDirection d) ω)).Reachable
      (sideDirection d) (z+sideDirection d)) ↔ _
  simp only [hconn]
  rfl

/-- Translation invariance preserves the full side event, with all endpoints
under the same measure; individual endpoint probabilities are not summed here. -/
theorem shiftedSideArm_probability_eq (θ : Parameters)
    (μ : Measure (PottsContinuity.squareLattice.edgeSet → Bool))
    (hμ : IsRCInfiniteVolumeLimit θ.toP θ.toQ 0 μ) (n : ℕ) (d : Fin 4) :
    μ.real (shiftedSideArmEvent n d) = μ.real (sideArmEvent n d) := by
  have hinv := Infinite.infinite_volume_translation_invariant θ.toP θ.toQ θ.property 0 μ hμ
    (sideDirection d)
  have h := congrArg (fun ν : Measure (PottsContinuity.squareLattice.edgeSet → Bool) =>
    ν (shiftedSideArmEvent n d)) hinv
  have hm := Measure.map_apply (μ := μ)
    (latticeConfigurationTranslate_measurable (sideDirection d))
    (shiftedSideArmEvent_isOpen n d).measurableSet
  have hpre := sideArmEvent_translation_preimage n d
  have hmass : μ (sideArmEvent n d) = μ (shiftedSideArmEvent n d) :=
    (congrArg μ hpre).symm.trans (hm.symm.trans h)
  change μ.real (shiftedSideArmEvent n d) = μ.real (sideArmEvent n d)
  exact (congrArg ENNReal.toReal hmass).symm

private theorem openEdge_graph_le (ω : PottsContinuity.squareLattice.edgeSet → Bool) (e : PottsContinuity.squareLattice.edgeSet) :
    PottsContinuity.rcInfiniteOpenGraph ω ≤ PottsContinuity.rcInfiniteOpenGraph (setEdge e true ω) := by
  intro x y hxy
  change (SimpleGraph.fromEdgeSet {e | ∃ h : e ∈ PottsContinuity.squareLattice.edgeSet,
    ω ⟨e,h⟩ = true}).Adj x y at hxy
  change (SimpleGraph.fromEdgeSet {f | ∃ h : f ∈ PottsContinuity.squareLattice.edgeSet,
    setEdge e true ω ⟨f,h⟩ = true}).Adj x y
  rw [SimpleGraph.fromEdgeSet_adj] at hxy ⊢
  obtain ⟨⟨he,hopen⟩,hne⟩ := hxy
  refine ⟨⟨he,?_⟩,hne⟩
  simp only [setEdge]
  split_ifs
  · rfl
  · exact hopen

/-- One opened original edge extends the translated arm to radius n+1. -/
theorem openSideEdge_image_subset_nextArm (n : ℕ) (d : Fin 4) :
    setEdge (sideDirectionEdge d) true '' shiftedSideArmEvent n d ⊆ RSW.infiniteArmEvent (n+1) := by
  rintro _ ⟨ω,⟨z,hz,hdot,hconn⟩,rfl⟩
  refine ⟨z+sideDirection d,shiftedSide_mem_nextBoundary n d z hz hdot,?_⟩
  have hedge : (PottsContinuity.rcInfiniteOpenGraph (setEdge (sideDirectionEdge d) true ω)).Adj
      (0,0) (sideDirection d) := by
    change (SimpleGraph.fromEdgeSet {f | ∃ h : f ∈ PottsContinuity.squareLattice.edgeSet,
      setEdge (sideDirectionEdge d) true ω ⟨f,h⟩ = true}).Adj (0,0) (sideDirection d)
    rw [SimpleGraph.fromEdgeSet_adj]
    exact ⟨⟨(sideDirectionEdge d).property,setEdge_self _ _ _⟩,(sideDirection_adj d).ne⟩
  exact hedge.reachable.trans (hconn.mono (openEdge_graph_le ω _))

/-- Uniform finite-energy side-arm extension for the genuine frozen free law. -/
theorem sideArm_probability_extension (θ : Parameters)
    (μ : Measure (PottsContinuity.squareLattice.edgeSet → Bool))
    (hμ : IsRCInfiniteVolumeLimit θ.toP θ.toQ 0 μ) (n : ℕ) (d : Fin 4) :
    energyBound θ*μ.real (sideArmEvent n d) ≤ RSW.oneArmProbability μ (n+1) := by
  let : IsProbabilityMeasure μ := hμ.1
  have hPD := RSW.free_limit_to_PD θ.toP θ.toQ μ hμ
  have h := setEdge_image_energy θ 0 μ hPD (sideDirectionEdge d) true
    (shiftedSideArmEvent_isOpen n d).measurableSet
  have heq := shiftedSideArm_probability_eq θ μ hμ n d
  have h' : energyBound θ*μ.real (sideArmEvent n d) ≤
      μ.real (setEdge (sideDirectionEdge d) true '' shiftedSideArmEvent n d) :=
    (congrArg (fun x : ℝ => energyBound θ*x) heq).ge.trans h
  exact h'.trans (measureReal_mono (openSideEdge_image_subset_nextArm n d))

end PottsContinuity.Thm3.Prop4
