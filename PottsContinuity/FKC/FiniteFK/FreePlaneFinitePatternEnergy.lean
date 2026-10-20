-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/FreePlaneFinitePatternEnergy.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.FreeBoxTranslation
public import PottsContinuity.FKC.FiniteFK.FreeBoxDihedral
public import PottsContinuity.FKC.Frozen.FreeBoxLimitV1
public import PottsContinuity.FKC.FiniteFK.BoxComparison
public import PottsContinuity.FKC.FiniteFK.BoxExhaustion
public import PottsContinuity.FKC.FiniteFK.CylinderConvergence
public import PottsContinuity.FKC.FiniteFK.FreeBoxPositiveAssociation
public import PottsContinuity.FKC.FiniteFK.FreeBoxFiniteEnergy
public import PottsContinuity.FKC.FiniteFK.CylinderDetermination
public import Mathlib.MeasureTheory.Measure.CompleteLattice
public import Mathlib.MeasureTheory.Measure.MeasuredSets
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
public import Mathlib.Data.Set.SymmDiff
public import Mathlib.MeasureTheory.Measure.Map
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.Topology.Constructions
public import PottsContinuity.FKC.FiniteFK.BoxCylinders
public import Mathlib.Tactic

@[expose] public section

open MeasureTheory Set

namespace PottsContinuity.FKC.FiniteFK
noncomputable section

/-- Configurations realizing a prescribed Boolean pattern on a finite set of
original lattice edges. -/
def finiteOriginalEdgePatternEvent (F : Finset squareLattice.edgeSet)
    (σ : squareLattice.edgeSet → Bool) : Set LatticeConfiguration :=
  {ω | ∀ e ∈ F, ω e = σ e}

private theorem finiteOriginalEdgePatternEvent_insert
    (F : Finset squareLattice.edgeSet) (e : squareLattice.edgeSet)
    (σ : squareLattice.edgeSet → Bool) :
    finiteOriginalEdgePatternEvent (insert e F) σ =
      {ω | ω e = σ e} ∩ finiteOriginalEdgePatternEvent F σ := by
  ext ω
  simp [finiteOriginalEdgePatternEvent]

theorem finiteOriginalEdgePatternEvent_isClopen
    (F : Finset squareLattice.edgeSet) (σ : squareLattice.edgeSet → Bool) :
    IsClopen (finiteOriginalEdgePatternEvent F σ) := by
  classical
  induction F using Finset.induction_on with
  | empty =>
      simpa [finiteOriginalEdgePatternEvent] using
        (isClopen_univ : IsClopen (Set.univ : Set LatticeConfiguration))
  | @insert e F he ih =>
      rw [finiteOriginalEdgePatternEvent_insert]
      exact ((isClopen_discrete ({σ e} : Set Bool)).preimage (continuous_apply e)).inter ih

end
end PottsContinuity.FKC.FiniteFK
