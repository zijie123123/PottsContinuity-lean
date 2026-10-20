-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `Medial/GraphWalkPathSubstitution.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import Mathlib.Combinatorics.SimpleGraph.Walk.Operations
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.Medial

open SimpleGraph

/-- Replace each source edge of a walk by a specified walk between the images
of its endpoints. -/
def graphWalkSubstitute {V W : Type*} (G : SimpleGraph V) (H : SimpleGraph W)
    (f : V → W)
    (route : ∀ {u v : V}, G.Adj u v → H.Walk (f u) (f v))
    {u v : V} : G.Walk u v → H.Walk (f u) (f v)
  | .nil => .nil
  | .cons h p => (route h).append (graphWalkSubstitute G H f route p)

@[simp]
theorem graphWalkSubstitute_nil {V W : Type*} (G : SimpleGraph V)
    (H : SimpleGraph W) (f : V → W)
    (route : ∀ {u v : V}, G.Adj u v → H.Walk (f u) (f v))
    (u : V) :
    graphWalkSubstitute G H f route (SimpleGraph.Walk.nil : G.Walk u u) =
      SimpleGraph.Walk.nil := rfl

@[simp]
theorem graphWalkSubstitute_cons {V W : Type*} (G : SimpleGraph V)
    (H : SimpleGraph W) (f : V → W)
    (route : ∀ {u v : V}, G.Adj u v → H.Walk (f u) (f v))
    {u v w : V} (h : G.Adj u v) (p : G.Walk v w) :
    graphWalkSubstitute G H f route (SimpleGraph.Walk.cons h p) =
      (route h).append (graphWalkSubstitute G H f route p) := rfl

theorem graphWalkSubstitute_darts_flatMap {V W : Type*} (G : SimpleGraph V)
    (H : SimpleGraph W) (f : V → W)
    (route : ∀ {u v : V}, G.Adj u v → H.Walk (f u) (f v))
    {u v : V} (p : G.Walk u v) :
    (graphWalkSubstitute G H f route p).darts =
      p.darts.flatMap fun d => (route d.adj).darts := by
  induction p with
  | nil => simp [graphWalkSubstitute]
  | @cons u v w h p ih =>
      rw [graphWalkSubstitute_cons, SimpleGraph.Walk.darts_append,
        SimpleGraph.Walk.darts_cons, List.flatMap_cons, ih]

end PottsContinuity.FKC.Medial
