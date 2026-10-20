module

public import PottsContinuity.Thm3.RSW.ClosedBlockEnergy
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef

@[expose] public section

namespace PottsContinuity.RSW
open PD.FK MeasureTheory Filter Topology
open scoped BigOperators
noncomputable section
local instance closedBlockFailureEdgeEq {V : Type*} (G : SimpleGraph V) :
    DecidableEq G.edgeSet := Classical.decEq _
local instance closedBlockFailureEdgeFintype {V : Type*} [Finite V] (G : SimpleGraph V) :
    Fintype G.edgeSet := Fintype.ofFinite _
attribute [local instance] configurationMeasurableSpace

/-- The existing exact first-closed-block selector has the all-parameter FK
failure estimate. Only the disjoint original-edge blocks are geometric input. -/
theorem firstClosedBlockScan_none_probability_le
    {V ι : Type*} [Finite V] [DecidableEq ι] {G : SimpleGraph V}
    (θ : Parameters) (ξ : BoundaryCondition V) (js : List ι) (F : ι → Finset G.edgeSet)
    (hdisj : ∀ i ∈ js.toFinset, ∀ j ∈ js.toFinset, i ≠ j → Disjoint (F i) (F j)) :
    (measure G θ ξ {A | (FKC.FiniteFK.firstClosedBlockScan F A js).2 = none}).toReal ≤
      ∏ i ∈ js.toFinset, (1-(1-edgeParameter θ)^(F i).card) := by
  have heq : {A : Configuration G | (FKC.FiniteFK.firstClosedBlockScan F A js).2 = none} =
      {A | ∀ i ∈ js.toFinset, ¬Disjoint A (F i)} := by
    ext A
    simp only [FKC.FiniteFK.firstClosedBlockScan_none_iff,List.mem_toFinset,Set.mem_ofPred_eq]
  rw [heq]
  exact measure_disjoint_closed_blocks_failure_le θ ξ js.toFinset F hdisj

/-- Equal-size blocks give an exponential scan-failure bound, with no
independence assumption and arbitrary original boundary conditions. -/
theorem firstClosedBlockScan_none_probability_le_constant_card
    {V ι : Type*} [Finite V] [DecidableEq ι] {G : SimpleGraph V}
    (θ : Parameters) (ξ : BoundaryCondition V) (js : List ι) (F : ι → Finset G.edgeSet)
    (H : ℕ)
    (hdisj : ∀ i ∈ js.toFinset, ∀ j ∈ js.toFinset, i ≠ j → Disjoint (F i) (F j))
    (hcard : ∀ i ∈ js.toFinset, (F i).card = H) :
    (measure G θ ξ {A | (FKC.FiniteFK.firstClosedBlockScan F A js).2 = none}).toReal ≤
      (1-(1-edgeParameter θ)^H)^js.toFinset.card := by
  apply (firstClosedBlockScan_none_probability_le θ ξ js F hdisj).trans_eq
  calc
    _ = ∏ i ∈ js.toFinset, (1-(1-edgeParameter θ)^H) := by
      apply Finset.prod_congr rfl
      intro i hi
      rw [hcard i hi]
    _ = _ := by simp

end
end PottsContinuity.RSW
