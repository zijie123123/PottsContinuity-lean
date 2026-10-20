-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `Medial/ParafermionicCoverRefinedSourceClosureTurn.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.Medial.ParafermionicCoverRefinedSourceEndpointTurns
public import PottsContinuity.FKC.Medial.ParafermionicCoverRefinedSourceCycle
public import PottsContinuity.FKC.Medial.ParafermionicCoverCycleCompassTurn
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.Medial

open PottsContinuity.FKC.FiniteFK
open SimpleGraph

private theorem sourceClosure_list_turn_identity (ds : List (Fin 4)) :
    (((ds ++ [1, 1, 0, 0]).zipWith primalCompassQuarterTurn
      ((ds ++ [1, 1, 0, 0]).rotate 1)).sum) =
      parafermionicCoverCompassLinearTurnSum ([0] ++ ds ++ [1]) - 1 := by
  cases ds with
  | nil =>
      norm_num [parafermionicCoverCompassLinearTurnSum,
        primalCompassQuarterTurn]
  | cons a ds =>
    cases ds with
    | nil =>
        fin_cases a <;> norm_num [parafermionicCoverCompassLinearTurnSum,
          primalCompassQuarterTurn]
    | cons b ds =>
      let f : Fin 4 → Fin 4 → ℤ := primalCompassQuarterTurn
      have hleft :
          List.zipWith f (b :: (ds ++ [1, 1, 0, 0]))
            (ds ++ [1, 1, 0, 0, a]) =
          List.zipWith f (b :: ds) (ds ++ [1]) ++
            List.zipWith f [1, 1, 0, 0] [1, 0, 0, a] := by
        have h := List.zipWith_append (f := f) (l₁ := b :: ds)
          (l₁' := [1, 1, 0, 0]) (l₂ := ds ++ [1])
          (l₂' := [1, 0, 0, a]) (by simp)
        simpa [List.cons_append, List.append_assoc] using h
      have hrot :
          (a :: b :: (ds ++ [1, 1, 0, 0])).rotate 1 =
            b :: (ds ++ [1, 1, 0, 0]) ++ [a] := by simp
      change (List.zipWith f (a :: b :: (ds ++ [1, 1, 0, 0]))
        ((a :: b :: (ds ++ [1, 1, 0, 0])).rotate 1)).sum = _
      rw [List.zipWith_rotate_one]
      have hleft' :
          List.zipWith f (b :: (ds ++ [1, 1, 0, 0]))
            (ds ++ ([1, 1, 0, 0] ++ [a])) =
          List.zipWith f (b :: ds) (ds ++ [1]) ++
            List.zipWith f [1, 1, 0, 0] [1, 0, 0, a] := by
        simpa [List.cons_append] using hleft
      rw [List.append_assoc, hleft']
      simp [parafermionicCoverCompassLinearTurnSum, List.map_zip_eq_zipWith,
        List.zipWith_cons_cons, f, primalCompassQuarterTurn]
      have hturn : Function.curry (fun ab : Fin 4 × Fin 4 =>
          if ab.2 = ab.1 + 1 then (1 : ℤ)
          else if ab.2 = ab.1 + 3 then -1 else 0) =
          primalCompassQuarterTurn := by
        funext x y
        rfl
      rw [hturn]
      have hcommon :
          List.zipWith primalCompassQuarterTurn (b :: (ds ++ [1])) (ds ++ [1]) =
          List.zipWith primalCompassQuarterTurn (b :: ds) (ds ++ [1]) := by
        have hprefix : b :: (ds ++ [1]) = (b :: ds) ++ [1] := by
          simp
        rw [hprefix]
        have h := List.zipWith_append (f := primalCompassQuarterTurn)
          (l₁ := b :: ds) (l₁' := [1]) (l₂ := ds ++ [1]) (l₂' := []) (by simp)
        simpa using h
      rw [hcommon]
      ring

theorem parafermionicCoverRefinedSourceCycle_turn_eq_paddedSourcePath
    (n : ℕ) (hn : 1 ≤ n) (A : Configuration (ParafermionicAmbientGraph n)) :
    parafermionicCoverWalkCyclicCompassTurn
      (parafermionicCoverRefinedSourceCycle n hn A) =
      parafermionicCoverCompassLinearTurnSum
        ([0] ++ parafermionicCoverWalkCompassDirections
          (parafermionicCoverRefinedPairingWalk n hn A
            (parafermionicCoverFiniteOriginExplorationPath n hn A)) ++ [1]) - 1 := by
  rw [parafermionicCoverWalkCyclicCompassTurn,
    parafermionicCoverRefinedSourceCycle]
  rw [parafermionicCoverWalkCompassDirections_append]
  simp only [parafermionicCoverWalkCompassDirections, Walk.darts_copy]
  change (List.zipWith primalCompassQuarterTurn
      (parafermionicCoverWalkCompassDirections
          (parafermionicCoverRefinedPairingWalk n hn A
            (parafermionicCoverFiniteOriginExplorationPath n hn A)) ++
        parafermionicCoverWalkCompassDirections
          (parafermionicCoverRefinedCornerWalk parafermionicCoverOriginCornerPortOther))
      ((parafermionicCoverWalkCompassDirections
          (parafermionicCoverRefinedPairingWalk n hn A
            (parafermionicCoverFiniteOriginExplorationPath n hn A)) ++
        parafermionicCoverWalkCompassDirections
          (parafermionicCoverRefinedCornerWalk parafermionicCoverOriginCornerPortOther)).rotate 1)).sum = _
  rw [parafermionicCoverOriginCornerPortOther_cornerWalk_compassDirections]
  exact sourceClosure_list_turn_identity _

end PottsContinuity.FKC.Medial
