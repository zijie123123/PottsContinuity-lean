-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/ParafermionicCoverRotatedBoxLaw.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.BoxTranslation
public import PottsContinuity.FKC.FiniteFK.Isomorphism
public import PottsContinuity.FKC.Medial.ParafermionicCoverQuarterTurnIterates
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

open PottsContinuity.FKC
open PottsContinuity.FKC.Medial
open MeasureTheory

noncomputable section

/-- The graph isomorphism given by iterating the actual sheet-corrected
quarter-turn on the full cover. -/
def parafermionicCoverQuarterTurnIsoIterate :
    ℕ → parafermionicCoverGraph ≃g parafermionicCoverGraph
  | 0 => (SimpleGraph.Iso.refl :
      parafermionicCoverGraph ≃g parafermionicCoverGraph)
  | k + 1 => parafermionicCoverQuarterTurn_graphIso.trans
      (parafermionicCoverQuarterTurnIsoIterate k)

@[simp] theorem parafermionicCoverQuarterTurnIsoIterate_apply
    (k : ℕ) (v : ParafermionicCoverVertex) :
    parafermionicCoverQuarterTurnIsoIterate k v =
      (parafermionicCoverQuarterTurn^[k]) v := by
  induction k generalizing v with
  | zero => rfl
  | succ k ih =>
      change parafermionicCoverQuarterTurnIsoIterate k
        (parafermionicCoverQuarterTurn v) =
          (parafermionicCoverQuarterTurn^[k]) (parafermionicCoverQuarterTurn v)
      exact ih (parafermionicCoverQuarterTurn v)

/-- The literal image of the finite cover box under one of the four iterated
full-cover quarter-turns. This image carrier is not identified with `U_n`. -/
def parafermionicCoverQuarterTurnImageVertices (n : ℕ) (j : Fin 4) :
    Set ParafermionicCoverVertex :=
  Set.range (fun v : ParafermionicCoverBoxVertex n =>
    parafermionicCoverQuarterTurnIsoIterate j.val v.val)

local instance parafermionicCoverQuarterTurnImageFinite (n : ℕ) (j : Fin 4) :
    Finite {v : ParafermionicCoverVertex //
      v ∈ parafermionicCoverQuarterTurnImageVertices n j} := by
  change Finite (↥(Set.range (fun v : ParafermionicCoverBoxVertex n =>
    parafermionicCoverQuarterTurnIsoIterate j.val v.val)))
  exact Finite.Set.finite_range _

attribute [local instance] configurationMeasurableSpace

end
end PottsContinuity.FKC.FiniteFK
