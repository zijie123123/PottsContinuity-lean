module

public import PottsContinuity.Thm3.Prop4.TubeBoundaryArms
public import PottsContinuity.Thm3.Prop4.TubeExcursion

/-!
# Lemma 7's three-event decomposition for finite box traces

The trace arguments are explicit. The decomposition is valid for any traces
of box vertices; it becomes the source decomposition when they are the actual
lowest and highest open paths. Their construction and stopping properties are
not asserted by this module.
-/

@[expose] public section

open MeasureTheory

namespace PottsContinuity.Thm3.Prop4

noncomputable section

/-- Lower-trace excursion into D_+, restricted to the genuine connection event. -/
def lowerTubeExcursionEvent (n : ℕ) (ε : ℝ) (a b : (box n : Set (ℤ × ℤ)))
    (lower : PD.FK.Configuration (squareLattice.induce (box n : Set (ℤ × ℤ))) →
      Finset (box n : Set (ℤ × ℤ))) :
    Set (PD.FK.Configuration (squareLattice.induce (box n : Set (ℤ × ℤ)))) :=
  PD.FK.connectivityEvent _ a b ∩
    {A | ∃ z ∈ lower A, z.val ∈ inductionTubeAbove n ε a.val b.val}

/-- Upper-trace excursion into D_-. -/
def upperTubeExcursionEvent (n : ℕ) (ε : ℝ) (a b : (box n : Set (ℤ × ℤ)))
    (upper : PD.FK.Configuration (squareLattice.induce (box n : Set (ℤ × ℤ))) →
      Finset (box n : Set (ℤ × ℤ))) :
    Set (PD.FK.Configuration (squareLattice.induce (box n : Set (ℤ × ℤ)))) :=
  PD.FK.connectivityEvent _ a b ∩
    {A | ∃ z ∈ upper A, z.val ∈ inductionTubeBelow n ε a.val b.val}

/-- The remaining event has each trace on its own side of the tube. -/
def betweenTubeTraceEvent (n : ℕ) (ε : ℝ) (a b : (box n : Set (ℤ × ℤ)))
    (lower upper : PD.FK.Configuration (squareLattice.induce (box n : Set (ℤ × ℤ))) →
      Finset (box n : Set (ℤ × ℤ))) :
    Set (PD.FK.Configuration (squareLattice.induce (box n : Set (ℤ × ℤ)))) :=
  PD.FK.connectivityEvent _ a b ∩
    {A | (∀ z ∈ lower A, z.val ∈ inductionTubeBelow n ε a.val b.val ∨
          z.val ∈ inductionTube n ε a.val b.val) ∧
      (∀ z ∈ upper A, z.val ∈ inductionTubeAbove n ε a.val b.val ∨
          z.val ∈ inductionTube n ε a.val b.val)}

/-- The source three-event cover uses only the proved literal region cover. -/
theorem connection_eq_tube_split_of_boxTraces {n : ℕ} (hn : 1 ≤ n) (ε : ℝ)
    (a b : (box n : Set (ℤ × ℤ)))
    (ha : a.val.1 = -(n : ℤ)) (hb : b.val.1 = (n : ℤ))
    (lower upper : PD.FK.Configuration (squareLattice.induce (box n : Set (ℤ × ℤ))) →
      Finset (box n : Set (ℤ × ℤ))) :
    PD.FK.connectivityEvent _ a b = lowerTubeExcursionEvent n ε a b lower ∪
      upperTubeExcursionEvent n ε a b upper ∪ betweenTubeTraceEvent n ε a b lower upper := by
  classical
  ext A
  constructor
  · intro hconn
    by_cases hl : ∃ z ∈ lower A, z.val ∈ inductionTubeAbove n ε a.val b.val
    · exact Or.inl (Or.inl ⟨hconn,hl⟩)
    by_cases hu : ∃ z ∈ upper A, z.val ∈ inductionTubeBelow n ε a.val b.val
    · exact Or.inl (Or.inr ⟨hconn,hu⟩)
    refine Or.inr ⟨hconn,?_,?_⟩
    · intro z hz
      rcases inductionTube_three_region_cover hn ε a.val b.val ha hb z.property with ht | hd | hu'
      · exact Or.inr ht
      · exact Or.inl hd
      · exact False.elim (hl ⟨z,hz,hu'⟩)
    · intro z hz
      rcases inductionTube_three_region_cover hn ε a.val b.val ha hb z.property with ht | hd | hu'
      · exact Or.inr ht
      · exact False.elim (hu ⟨z,hz,hd⟩)
      · exact Or.inl hu'
  · rintro ((h | h) | h)
    all_goals exact h.1

/-- Probability version, before any extremal-path or dual estimate is supplied. -/
theorem connection_probability_le_tube_split_of_boxTraces (θ : PD.FK.Parameters)
    {n : ℕ} (hn : 1 ≤ n) (ε : ℝ) (a b : (box n : Set (ℤ × ℤ)))
    (ha : a.val.1 = -(n : ℤ)) (hb : b.val.1 = (n : ℤ))
    (lower upper : PD.FK.Configuration (squareLattice.induce (box n : Set (ℤ × ℤ))) →
      Finset (box n : Set (ℤ × ℤ)))
    (ξ : PD.FK.BoundaryCondition (box n : Set (ℤ × ℤ))) :
    (PD.FK.measure (squareLattice.induce (box n : Set (ℤ × ℤ))) θ ξ
      (PD.FK.connectivityEvent _ a b)).toReal ≤
      (PD.FK.measure (squareLattice.induce (box n : Set (ℤ × ℤ))) θ ξ
        (lowerTubeExcursionEvent n ε a b lower)).toReal +
      (PD.FK.measure (squareLattice.induce (box n : Set (ℤ × ℤ))) θ ξ
        (upperTubeExcursionEvent n ε a b upper)).toReal +
      (PD.FK.measure (squareLattice.induce (box n : Set (ℤ × ℤ))) θ ξ
        (betweenTubeTraceEvent n ε a b lower upper)).toReal := by
  rw [connection_eq_tube_split_of_boxTraces hn ε a b ha hb lower upper]
  exact (measureReal_union_le _ _).trans (add_le_add (measureReal_union_le _ _) le_rfl)

end

end PottsContinuity.Thm3.Prop4
