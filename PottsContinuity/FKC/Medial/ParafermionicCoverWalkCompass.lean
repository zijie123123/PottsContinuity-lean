-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `Medial/ParafermionicCoverWalkCompass.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.Medial.ParafermionicCoverRefinedRouteDirections
public import PottsContinuity.FKC.Medial.ParafermionicCoverPrimalCycleDirections
public import PottsContinuity.FKC.Medial.ParafermionicCoverRefinedClosedCapPath
public import PottsContinuity.FKC.Medial.ParafermionicCoverRefinedCornerPath
public import Mathlib.Combinatorics.SimpleGraph.Walk.Operations
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.Medial

open SimpleGraph

/-- The ordered compass labels of the actual directed darts of a full-cover walk. -/
noncomputable def parafermionicCoverWalkCompassDirections {u v : ParafermionicCoverVertex}
    (p : parafermionicCoverGraph.Walk u v) : List (Fin 4) :=
  p.darts.map fun d => parafermionicCoverCompassDirection d.fst d.snd d.adj

@[simp] theorem parafermionicCoverWalkCompassDirections_nil (u : ParafermionicCoverVertex) :
    parafermionicCoverWalkCompassDirections (Walk.nil : parafermionicCoverGraph.Walk u u) = [] := by
  simp [parafermionicCoverWalkCompassDirections]

@[simp] theorem parafermionicCoverWalkCompassDirections_cons
    {u v w : ParafermionicCoverVertex}
    (h : parafermionicCoverGraph.Adj u v)
    (p : parafermionicCoverGraph.Walk v w) :
    parafermionicCoverWalkCompassDirections (Walk.cons h p) =
      parafermionicCoverCompassDirection u v h ::
        parafermionicCoverWalkCompassDirections p := by
  simp [parafermionicCoverWalkCompassDirections]

@[simp] theorem parafermionicCoverWalkCompassDirections_append
    {u v w : ParafermionicCoverVertex}
    (p : parafermionicCoverGraph.Walk u v)
    (q : parafermionicCoverGraph.Walk v w) :
    parafermionicCoverWalkCompassDirections (p.append q) =
      parafermionicCoverWalkCompassDirections p ++
        parafermionicCoverWalkCompassDirections q := by
  simp [parafermionicCoverWalkCompassDirections]

theorem parafermionicCoverCompassDirection_eq_of_neighbor
    {u v : ParafermionicCoverVertex}
    (h : parafermionicCoverGraph.Adj u v) (d : Fin 4)
    (hd : parafermionicCoverCompassNeighbor u d = v) :
    parafermionicCoverCompassDirection u v h = d := by
  apply parafermionicCoverCompassNeighbor_injective u
  calc
    parafermionicCoverCompassNeighbor u
        (parafermionicCoverCompassDirection u v h) = v :=
      parafermionicCoverCompassDirection_neighbor u v h
    _ = parafermionicCoverCompassNeighbor u d := hd.symm

theorem parafermionicCoverRefinedClosedCapWalk_compassDirections
    (c : ParafermionicCoverPort) :
    parafermionicCoverWalkCompassDirections
      (parafermionicCoverRefinedClosedCapWalk c) =
        [parafermionicCoverPortCellNormalCompass c + 2,
         parafermionicCoverPortCellNormalCompass c + 2] := by
  simp only [parafermionicCoverWalkCompassDirections_cons,
    parafermionicCoverWalkCompassDirections_nil,
    parafermionicCoverRefinedClosedCapWalk]
  rw [parafermionicCoverCompassDirection_eq_of_neighbor
      (parafermionicCoverRefinedClosedCapMiddle_base_adj c)
      (parafermionicCoverPortCellNormalCompass c + 2)
      (parafermionicCoverRefinedClosedCapStep₁_compass c),
    parafermionicCoverCompassDirection_eq_of_neighbor
      (parafermionicCoverRefinedClosedCapMiddle_closedPair_adj c)
      (parafermionicCoverPortCellNormalCompass c + 2)
      (parafermionicCoverRefinedClosedCapStep₂_compass c)]

theorem parafermionicCoverRefinedCornerWalk_compassDirections
    (c : ParafermionicCoverPort) :
    parafermionicCoverWalkCompassDirections
      (parafermionicCoverRefinedCornerWalk c) =
        [parafermionicCoverPortRadialCompass c + 2,
         parafermionicCoverPortRadialCompass c + 2,
         parafermionicCoverPortCellNormalCompass c,
         parafermionicCoverPortCellNormalCompass c] := by
  simp only [parafermionicCoverWalkCompassDirections_cons,
    parafermionicCoverWalkCompassDirections_nil,
    parafermionicCoverRefinedCornerWalk]
  rw [parafermionicCoverCompassDirection_eq_of_neighbor
      (parafermionicCoverRefinedCornerRoute_adj c).1
      (parafermionicCoverPortRadialCompass c + 2)
      (parafermionicCoverRefinedCornerStep₁_compass c),
    parafermionicCoverCompassDirection_eq_of_neighbor
      (parafermionicCoverRefinedCornerRoute_adj c).2.1
      (parafermionicCoverPortRadialCompass c + 2)
      (parafermionicCoverRefinedCornerStep₂_compass c),
    parafermionicCoverCompassDirection_eq_of_neighbor
      (parafermionicCoverRefinedCornerRoute_adj c).2.2.1
      (parafermionicCoverPortCellNormalCompass c)
      (parafermionicCoverRefinedCornerStep₃_compass c),
    parafermionicCoverCompassDirection_eq_of_neighbor
      (parafermionicCoverRefinedCornerRoute_adj c).2.2.2
      (parafermionicCoverPortCellNormalCompass c)
      (parafermionicCoverRefinedCornerStep₄_compass c)]

end PottsContinuity.FKC.Medial
