module

public import PottsContinuity.Thm3.RSW.ArmOpen
public import PottsContinuity.Foundations.BoxBoundary

/-! # Monotonicity of the actual infinite-volume arm event -/

@[expose] public section

open MeasureTheory

namespace PottsContinuity.Thm3.Prop4

/-- Every open infinite-volume edge is an original lattice edge. -/
theorem infiniteOpenGraph_le_squareLattice (ω : squareLattice.edgeSet → Bool) :
    rcInfiniteOpenGraph ω ≤ squareLattice := by
  intro u v huv
  change (SimpleGraph.fromEdgeSet _).Adj u v at huv
  rw [SimpleGraph.fromEdgeSet_adj] at huv
  obtain ⟨⟨he,_⟩,_⟩ := huv
  exact squareLattice.mem_edgeSet.mp he

/-- An actual walk to a farther frozen boundary first crosses every smaller
box boundary. No infinite-cluster assumption is needed. -/
theorem infiniteArmEvent_antitone : Antitone RSW.infiniteArmEvent := by
  intro n m hnm ω hω
  by_cases heq : n = m
  · simpa only [heq] using hω
  obtain ⟨z,hz,⟨w⟩⟩ := hω
  have hnlt : n < m := lt_of_le_of_ne hnm heq
  have hzout : z ∉ box n := by
    have hzmax := hz
    rw [Foundations.vertexBoundary_box_eq] at hzmax
    change max |z.1| |z.2| = (m : ℤ) at hzmax
    intro hzin
    have hin := (Foundations.mem_box_iff_abs_le n z).mp hzin
    have hmax := max_le hin.1 hin.2
    have hlt : (n : ℤ) < m := by exact_mod_cast hnlt
    omega
  have hzero : (0,0) ∈ box n := by simp [box]
  obtain ⟨d,hd,hdin,hdout⟩ := w.exists_boundary_dart (box n : Set (ℤ × ℤ)) hzero hzout
  have hsupport := w.dart_fst_mem_support_of_mem_darts hd
  refine ⟨d.fst,?_,⟨w.takeUntil d.fst hsupport⟩⟩
  rw [Foundations.vertexBoundary_eq_PD]
  exact ⟨hdin,d.snd,infiniteOpenGraph_le_squareLattice ω d.adj,hdout⟩

/-- Real arm probabilities decrease with radius for every finite measure. -/
theorem oneArmProbability_antitone (μ : Measure (squareLattice.edgeSet → Bool))
    [IsFiniteMeasure μ] : Antitone (RSW.oneArmProbability μ) := by
  intro n m hnm
  exact measureReal_mono (infiniteArmEvent_antitone hnm)

end PottsContinuity.Thm3.Prop4
