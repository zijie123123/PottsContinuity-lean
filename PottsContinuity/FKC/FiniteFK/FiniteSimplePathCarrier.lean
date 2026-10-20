-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/FiniteSimplePathCarrier.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.ActualConnectionFirstHitPath
public import Mathlib.Combinatorics.SimpleGraph.Walk.Counting

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

variable {V : Type*}

/-- All simple paths with the fixed initial vertex and arbitrary endpoint.
The endpoint and the ordered path are both retained. -/
abbrev FiniteSimplePathCarrier (G : SimpleGraph V) (x : V) :=
  Σ y : V, G.Path x y

/-- The ordered vertex traversal of a path in the fixed-start carrier. -/
def finiteSimplePathSupport {G : SimpleGraph V} {x : V}
    (p : FiniteSimplePathCarrier G x) : List V :=
  (p.2 : G.Walk x p.1).support

section Finite

variable {V : Type*} [DecidableEq V] [Fintype V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (x : V)

/-- Mathlib's finite fixed-endpoint `Path` instance, combined over the finite
endpoint type, makes the full fixed-start path carrier finite. -/
instance finiteSimplePathCarrier_fintype : Fintype (FiniteSimplePathCarrier G x) :=
  inferInstance

omit [DecidableEq V] [Fintype V] [DecidableRel G.Adj] in
/-- The ordered support list exactly encodes a simple path with fixed start,
including its endpoint. -/
theorem finiteSimplePathSupport_injective :
    Function.Injective (finiteSimplePathSupport (G := G) (x := x)) := by
  intro p q hpq
  rcases p with ⟨y, p⟩
  rcases q with ⟨z, q⟩
  change (p : G.Walk x y).support = (q : G.Walk x z).support at hpq
  have hpnil : (p : G.Walk x y).support ≠ [] :=
    SimpleGraph.Walk.support_ne_nil _
  have hqnil : (q : G.Walk x z).support ≠ [] :=
    SimpleGraph.Walk.support_ne_nil _
  have hpLast : (p : G.Walk x y).support.getLast? = some y := by
    rw [List.getLast?_eq_getLast_of_ne_nil hpnil]
    exact congrArg some (SimpleGraph.Walk.getLast_support (p : G.Walk x y))
  have hqLast : (q : G.Walk x z).support.getLast? = some z := by
    rw [List.getLast?_eq_getLast_of_ne_nil hqnil]
    exact congrArg some (SimpleGraph.Walk.getLast_support (q : G.Walk x z))
  have hyz : y = z := by
    have h := congrArg List.getLast? hpq
    rw [hpLast, hqLast] at h
    cases h
    rfl
  subst z
  have hpq' : (p : G.Walk x y).support = (q : G.Walk x y).support := by
    exact hpq
  have hwalk : (p : G.Walk x y) = (q : G.Walk x y) := SimpleGraph.Walk.ext_support hpq'
  exact congrArg (fun r : G.Path x y => (⟨y, r⟩ : FiniteSimplePathCarrier G x))
    (Subtype.ext hwalk)

end Finite

/-- Simple paths from `x` whose endpoint lies in `B` and whose only vertex in
`B` is that endpoint. This finite subtype preserves the complete ordered path,
not merely its vertex set. -/
def FirstHitSimplePathCarrier (G : SimpleGraph V) (x : V) (B : Set V) :=
  {p : FiniteSimplePathCarrier G x // p.1 ∈ B ∧
    ∀ v ∈ finiteSimplePathSupport p, v ∈ B → v = p.1}

section FirstHitFinite

variable {V : Type*} [DecidableEq V] [Fintype V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (x : V) (B : Set V)

/-- The first-hit path carrier is finite as a subtype of the finite path carrier. -/
noncomputable instance firstHitSimplePathCarrier_fintype :
    Fintype (FirstHitSimplePathCarrier G x B) := by
  classical
  letI : Fintype (FiniteSimplePathCarrier G x) :=
    finiteSimplePathCarrier_fintype (G := G) x
  letI : Finite (FiniteSimplePathCarrier G x) := Finite.of_fintype _
  letI : Finite (FirstHitSimplePathCarrier G x B) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  exact Fintype.ofFinite _

end FirstHitFinite

end PottsContinuity.FKC.FiniteFK
