module

public import PottsContinuity.Thm3.RSW.AnnulusPositivity
public import PottsContinuity.Thm3.RSW.SquarePair

/-! Strict subunit square-pair probabilities from the actual all-closed state. -/

@[expose] public section

namespace PottsContinuity.RSW
open MeasureTheory

/-- Any actual finite event with a counterexample has probability below one,
under arbitrary finite boundary wiring. -/
theorem finiteBoundaryEventProbability_lt_one_of_counterexample
    (V : Finset (ℤ × ℤ)) (θ : PD.FK.Parameters)
    (ξ : PD.FK.BoundaryCondition (V : Set (ℤ × ℤ)))
    (E : ((squareLattice.induce (V : Set (ℤ × ℤ))).edgeSet → Bool) → Prop)
    (ω : (squareLattice.induce (V : Set (ℤ × ℤ))).edgeSet → Bool) (hω : ¬ E ω) :
    finiteBoundaryEventProbability V θ ξ E < 1 := by
  classical
  let S := finiteBoolEvent V E
  let ρ := PD.FK.measure (squareLattice.induce (V : Set (ℤ × ℤ))) θ ξ
  have hcomp : 0 < (ρ Sᶜ).toReal :=
    (finiteBoundaryEventProbability_pos_iff V θ ξ (fun η => ¬ E η)).mpr ⟨ω, hω⟩
  have hsum := measureReal_add_measureReal_compl (μ := ρ)
    (s := S) MeasurableSpace.measurableSet_top
  have huniv : ρ.real Set.univ = 1 := probReal_univ
  rw [huniv] at hsum
  change (ρ S).toReal < 1
  change (ρ S).toReal + (ρ Sᶜ).toReal = 1 at hsum
  linarith only [hcomp, hsum]

/-- All-closed edges disconnect every pair of distinct sampled vertices. -/
theorem all_false_not_finiteConnectionEvent (V : Finset (ℤ × ℤ))
    (x y : ℤ × ℤ) (hxy : x ≠ y) : (fun _ => false) ∉ finiteConnectionEvent V x y := by
  rintro ⟨hx, hy, hreach⟩
  rw [rcOpenGraph_all_false, SimpleGraph.reachable_bot] at hreach
  exact hxy (congrArg Subtype.val hreach)

/-- Opposite-side actual connections are strictly subunit at positive width,
including both corner heights. -/
theorem squarePairProbability_lt_one (θ : PD.FK.Parameters) (m : ℕ) (hm : 1 ≤ m)
    (i j : Fin (m+1)) : squarePairProbability θ m i j < 1 := by
  apply finiteBoundaryEventProbability_lt_one_of_counterexample _ θ _ _ (fun _ => false)
  apply all_false_not_finiteConnectionEvent
  intro h
  have hx := congrArg Prod.fst h
  omega

/-- The genuine finite maximum is still strictly below one. -/
theorem maxSquarePairProbability_lt_one (θ : PD.FK.Parameters) (m : ℕ) (hm : 1 ≤ m) :
    maxSquarePairProbability θ m < 1 := by
  apply (Finset.sup'_lt_iff Finset.univ_nonempty).mpr
  intro ij _
  exact squarePairProbability_lt_one θ m hm ij.1 ij.2

end PottsContinuity.RSW
