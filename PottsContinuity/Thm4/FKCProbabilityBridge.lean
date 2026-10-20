module

public import PottsContinuity.Thm4.SelfDualParameters
public import PottsContinuity.PD.FK.IncreasingEvents
public import PottsContinuity.FKC.FiniteFK.Model
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef

@[expose] public section

namespace PottsContinuity.Thm4
open PottsContinuity.PD.FK
noncomputable section

/-- Preserve the complete boundary partition, not only its designated set. -/
def fkcBoundaryToPD {V : Type*} (ξ : PottsContinuity.FKC.FiniteFK.BoundaryCondition V) :
    BoundaryCondition V where
  boundary := ξ.boundary
  partition := ξ.partition
  supported := ξ.supported

@[simp] theorem fkcBoundaryToPD_free {V : Type*} (B : Set V) :
    fkcBoundaryToPD (PottsContinuity.FKC.FiniteFK.BoundaryCondition.free B) =
      BoundaryCondition.free B := rfl

@[simp] theorem fkcBoundaryToPD_wired {V : Type*} (B : Set V) :
    fkcBoundaryToPD (PottsContinuity.FKC.FiniteFK.BoundaryCondition.wired B) =
      BoundaryCondition.wired B := rfl

/-- Exact equality of the actual finite measures on the entire power set. -/
theorem fkc_measure_eq {V : Type*} [Finite V] (G : SimpleGraph V)
    (q : PottsContinuity.FKC.ClusterWeight)
    (ξ : PottsContinuity.FKC.FiniteFK.BoundaryCondition V) :
    PottsContinuity.FKC.FiniteFK.measure G q ξ =
      measure G (selfDualParameters ⟨q, q.2.1⟩) (fkcBoundaryToPD ξ) := rfl

end
end PottsContinuity.Thm4
