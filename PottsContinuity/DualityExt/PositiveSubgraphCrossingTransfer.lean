module

public import PottsContinuity.DualityExt.PositiveBoundaryMergeDualTransfer
public import PottsContinuity.DualityExt.PositiveDualSubgraphLaw
public import PottsContinuity.DualityExt.PositivePDLawBridge
public import PottsContinuity.PD.Duality.CrossingDuality
public import PottsContinuity.PD.FK.SubgraphComparison
public import PottsContinuity.PD.FK.IncreasingEvents
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef

/-!
# Probability transfer for a subgraph crossing and its forced-open dual

The deterministic crossing-complement theorem applies to a bond subgraph of
a rectangle after deleted primal bonds are closed. Under the exact induced
dual law, the deleted bonds are represented by forced-open dual bonds. This
module records the corresponding event-probability equality on the edge-
deleted dual carrier.
-/

@[expose] public section

namespace PottsContinuity.DualityExt

open PottsContinuity.PD.FK
open PottsContinuity.PD.Duality

noncomputable section

variable {a : LatticeVertex} {w h : ℕ}
variable {H : SimpleGraph (RectangleVertex a w h)}

local instance crossingTransferEdgeFintype {V : Type*} [Finite V]
    {G : SimpleGraph V} : Fintype G.edgeSet := Fintype.ofFinite _
local instance crossingTransferConfigFintype {V : Type*} [Finite V]
    {G : SimpleGraph V} : Fintype (Configuration G) := Fintype.ofFinite _

private theorem positiveFKProbability_eq_configurationProbability
    {V : Type*} [Finite V] {G : SimpleGraph V}
    (θ : Parameters) (ξ : BoundaryCondition V) (A : Configuration G) :
    positiveFKProbability (q := θ.val) (p := edgeParameter θ) ξ A =
      configurationProbability G θ ξ A := by
  let fPos : Fintype (Configuration G) := positiveDMPConfigurationFintype
  let fPD : Fintype (Configuration G) :=
    @Finset.fintype G.edgeSet (PottsContinuity.PD.FK.edgeFintype G)
  have hweight : positiveFKWeight G θ.val (edgeParameter θ) ξ = weight G θ ξ := by
    funext B
    simp [positiveFKWeight, weight, edgeParameter]
  have hpartition :
      positiveFKPartitionFunction G θ.val (edgeParameter θ) ξ =
        partitionFunction G θ ξ := by
    change @FiniteProbability.partition (Configuration G) fPos
        (positiveFKWeight G θ.val (edgeParameter θ) ξ) =
      @FiniteProbability.partition (Configuration G) fPD (weight G θ ξ)
    calc
      _ = @FiniteProbability.partition (Configuration G) fPos
          (weight G θ ξ) := by rw [hweight]
      _ = @FiniteProbability.partition (Configuration G) fPD
          (weight G θ ξ) :=
            @FiniteProbability.partition_equiv (Configuration G) (Configuration G)
              fPos fPD (Equiv.refl (Configuration G)) (weight G θ ξ)
  unfold positiveFKProbability configurationProbability
  rw [congrFun hweight A, hpartition]

theorem positiveFKEventProbability_eq_measure_toReal
    {V : Type*} [Finite V] {G : SimpleGraph V}
    (θ : Parameters) (ξ : BoundaryCondition V) (S : Set (Configuration G)) :
    positiveFKEventProbability (q := θ.val) (p := edgeParameter θ) ξ S =
      (PottsContinuity.PD.FK.measure G θ ξ S).toReal := by
  classical
  let fPos : Fintype (Configuration G) := positiveReweightConfigFintype
  let fPD : Fintype (Configuration G) :=
    @Finset.fintype G.edgeSet (PottsContinuity.PD.FK.edgeFintype G)
  let g : Configuration G → ℝ := fun A =>
    if A ∈ S then configurationProbability G θ ξ A else 0
  have hleft : positiveFKEventProbability (q := θ.val)
      (p := edgeParameter θ) ξ S =
        @FiniteProbability.partition (Configuration G) fPos g := by
    unfold positiveFKEventProbability
    change @FiniteProbability.partition (Configuration G) fPos
        (fun A => if A ∈ S then positiveFKProbability
          (q := θ.val) (p := edgeParameter θ) ξ A else 0) = _
    apply congrArg (fun f : Configuration G → ℝ =>
      @FiniteProbability.partition (Configuration G) fPos f)
    funext A
    by_cases h : A ∈ S <;> simp [g, h, positiveFKProbability_eq_configurationProbability]
  have hright : (PottsContinuity.PD.FK.measure G θ ξ S).toReal =
      @FiniteProbability.partition (Configuration G) fPD g := by
    rw [PottsContinuity.PD.FK.measure_toReal_eq_indicator_sum]
    change @FiniteProbability.partition (Configuration G) fPD
        (fun A => configurationProbability G θ ξ A *
          S.indicator (fun _ => (1 : ℝ)) A) = _
    apply congrArg (fun f : Configuration G → ℝ =>
      @FiniteProbability.partition (Configuration G) fPD f)
    funext A
    by_cases h : A ∈ S <;> simp [g, h]
  calc
    _ = @FiniteProbability.partition (Configuration G) fPos g := hleft
    _ = @FiniteProbability.partition (Configuration G) fPD g :=
      @FiniteProbability.partition_equiv (Configuration G) (Configuration G)
        fPos fPD (Equiv.refl (Configuration G)) g
    _ = _ := hright.symm

end
end PottsContinuity.DualityExt
