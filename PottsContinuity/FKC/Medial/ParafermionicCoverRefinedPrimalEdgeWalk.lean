-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `Medial/ParafermionicCoverRefinedPrimalEdgeWalk.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.Medial.ParafermionicCoverCompass
public import PottsContinuity.FKC.Medial.ParafermionicCoverRefinedOwner
public import PottsContinuity.FKC.Medial.ParafermionicCoverWalkCompass
public import Mathlib.Combinatorics.SimpleGraph.Walk.Operations
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.Medial

def refinedPrimalStep (d : Fin 4) (u : ParafermionicCoverVertex) :
    ParafermionicCoverVertex :=
  match d.val with
  | 0 => ((u.1.1 + 1, u.1.2),
      u.2 + if u.1.1 = 0 ∧ u.1.2 < 0 then 1 else 0)
  | 1 => ((u.1.1, u.1.2 + 1), u.2)
  | 2 => ((u.1.1 - 1, u.1.2),
      u.2 - if u.1.1 = 1 ∧ u.1.2 < 0 then 1 else 0)
  | _ => ((u.1.1, u.1.2 - 1), u.2)

private theorem refinedPrimalStep_eq_compass (u : ParafermionicCoverVertex)
    (d : Fin 4) : refinedPrimalStep d u = parafermionicCoverCompassNeighbor u d := by
  rcases u with ⟨⟨x,y⟩,k⟩
  fin_cases d <;>
    simp [refinedPrimalStep, parafermionicCoverCompassNeighbor,
      parafermionicCoverCompassBaseNeighbor, parafermionicCoverNeighborLift,
      parafermionicCoverSheetShift] <;> omega

def refinedPrimalEndpoint (d : Fin 4) :
    ParafermionicCoverVertex → ℕ → ParafermionicCoverVertex
  | u, 0 => u
  | u, n + 1 => refinedPrimalEndpoint d (refinedPrimalStep d u) n

def refinedPrimalRayWalk (d : Fin 4) :
    (u : ParafermionicCoverVertex) → (n : ℕ) →
      parafermionicCoverGraph.Walk u (refinedPrimalEndpoint d u n)
  | u, 0 => SimpleGraph.Walk.nil
  | u, n + 1 => SimpleGraph.Walk.cons
      (by rw [refinedPrimalStep_eq_compass]; exact parafermionicCoverCompassNeighbor_adj u d)
      (refinedPrimalRayWalk d (refinedPrimalStep d u) n)

 theorem refinedPrimalEndpoint_nine (u : ParafermionicCoverVertex) (d : Fin 4) :
    refinedPrimalEndpoint d (parafermionicCoverRefinedCoarseCenter u) 9 =
      parafermionicCoverRefinedCoarseCenter (parafermionicCoverCompassNeighbor u d) := by
  rcases u with ⟨⟨x,y⟩,k⟩
  rw [← refinedPrimalStep_eq_compass]
  fin_cases d <;>
    norm_num [refinedPrimalEndpoint, refinedPrimalStep,
      parafermionicCoverRefinedCoarseCenter] <;>
    by_cases hx : x = 0 <;>
    (try simp (disch := omega) only [hx, ite_eq_right]) <;>
    (try norm_num) <;>
    omega

def parafermionicCoverRefinedPrimalEdgeWalk (u : ParafermionicCoverVertex) (d : Fin 4) :
    parafermionicCoverGraph.Walk
      (parafermionicCoverRefinedCoarseCenter u)
      (parafermionicCoverRefinedCoarseCenter (parafermionicCoverCompassNeighbor u d)) :=
  (refinedPrimalRayWalk d (parafermionicCoverRefinedCoarseCenter u) 9).copy rfl
    (refinedPrimalEndpoint_nine u d)


/-- The ordered actual compass-neighbor ray used by the refined edge walk. -/
def refinedCompassRayPoints (d : Fin 4) :
    ParafermionicCoverVertex → ℕ → List ParafermionicCoverVertex
  | u, 0 => [u]
  | u, n + 1 => u :: refinedCompassRayPoints d
      (parafermionicCoverCompassNeighbor u d) n

/-- The ten ordered refined vertices along the actual iterated compass-neighbor
ray beginning at a coarse-cell center. -/
def parafermionicCoverRefinedPrimalEdgeWalkPoints
    (u : ParafermionicCoverVertex) (d : Fin 4) : List ParafermionicCoverVertex :=
  refinedCompassRayPoints d (parafermionicCoverRefinedCoarseCenter u) 9

private theorem refinedPrimalRayWalk_support (d : Fin 4)
    (u : ParafermionicCoverVertex) (n : ℕ) :
    (refinedPrimalRayWalk d u n).support = refinedCompassRayPoints d u n := by
  induction n generalizing u with
  | zero => rfl
  | succ n ih =>
      change u :: (refinedPrimalRayWalk d (refinedPrimalStep d u) n).support =
        u :: refinedCompassRayPoints d (parafermionicCoverCompassNeighbor u d) n
      rw [ih, refinedPrimalStep_eq_compass]


private theorem refinedPrimalRayWalk_length (d : Fin 4)
    (u : ParafermionicCoverVertex) (n : ℕ) :
    (refinedPrimalRayWalk d u n).length = n := by
  induction n generalizing u with
  | zero => rfl
  | succ n ih =>
      change (SimpleGraph.Walk.cons _ (refinedPrimalRayWalk d
        (refinedPrimalStep d u) n)).length = n + 1
      rw [SimpleGraph.Walk.length_cons, ih]

private theorem refinedPrimalRayWalk_directions (d : Fin 4)
    (u : ParafermionicCoverVertex) (n : ℕ) :
    parafermionicCoverWalkCompassDirections (refinedPrimalRayWalk d u n) =
      List.replicate n d := by
  induction n generalizing u with
  | zero => rfl
  | succ n ih =>
      let hadj : parafermionicCoverGraph.Adj u (refinedPrimalStep d u) := by
        rw [refinedPrimalStep_eq_compass]
        exact parafermionicCoverCompassNeighbor_adj u d
      have hdir : parafermionicCoverCompassDirection u (refinedPrimalStep d u) hadj = d :=
        parafermionicCoverCompassDirection_eq_of_neighbor hadj d
          (refinedPrimalStep_eq_compass u d).symm
      change parafermionicCoverWalkCompassDirections
        (SimpleGraph.Walk.cons hadj (refinedPrimalRayWalk d
          (refinedPrimalStep d u) n)) = List.replicate (n + 1) d
      rw [parafermionicCoverWalkCompassDirections_cons, hdir, ih]
      simp [List.replicate_succ]

theorem parafermionicCoverRefinedPrimalEdgeWalk_length
    (u : ParafermionicCoverVertex) (d : Fin 4) :
    (parafermionicCoverRefinedPrimalEdgeWalk u d).length = 9 := by
  rw [parafermionicCoverRefinedPrimalEdgeWalk, SimpleGraph.Walk.length_copy]
  exact refinedPrimalRayWalk_length d _ 9

theorem parafermionicCoverRefinedPrimalEdgeWalk_compassDirections
    (u : ParafermionicCoverVertex) (d : Fin 4) :
    parafermionicCoverWalkCompassDirections
      (parafermionicCoverRefinedPrimalEdgeWalk u d) = List.replicate 9 d := by
  rw [parafermionicCoverRefinedPrimalEdgeWalk,
    parafermionicCoverWalkCompassDirections]
  rw [SimpleGraph.Walk.darts_copy]
  exact refinedPrimalRayWalk_directions d _ 9


theorem parafermionicCoverRefinedPrimalEdgeWalk_support
    (u : ParafermionicCoverVertex) (d : Fin 4) :
    (parafermionicCoverRefinedPrimalEdgeWalk u d).support =
      parafermionicCoverRefinedPrimalEdgeWalkPoints u d := by
  rw [parafermionicCoverRefinedPrimalEdgeWalk,
    SimpleGraph.Walk.support_copy]
  simpa [parafermionicCoverRefinedPrimalEdgeWalkPoints] using
    refinedPrimalRayWalk_support d (parafermionicCoverRefinedCoarseCenter u) 9

end PottsContinuity.FKC.Medial
