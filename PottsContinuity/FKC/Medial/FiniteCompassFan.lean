-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `Medial/FiniteCompassFan.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import Mathlib.Data.Finset.Card
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.Medial

/-- For a set of compass sectors, the signed boundary at direction `d` is its
indicator minus the indicator of the preceding sector. Directions are the
cyclic compass labels `0 = E, 1 = N, 2 = W, 3 = S`. -/
def compassSectorBoundary (Q : Finset (Fin 4)) (d : Fin 4) : ℤ :=
  (if d ∈ Q then 1 else 0) - (if d - 1 ∈ Q then 1 else 0)

/-- The signed quarter-turn for travel directions. The input directions are
those of travel; the reverse-direction cases are totalized to zero, and must
be excluded separately when applying this to a nonbacktracking circuit. -/
def primalCompassQuarterTurn (a b : Fin 4) : ℤ :=
  if b = a + 1 then 1 else if b = a + 3 then -1 else 0

theorem compassSectorBoundary_zero_eq_empty_or_univ (Q : Finset (Fin 4))
    (h : ∀ d, compassSectorBoundary Q d = 0) : Q = ∅ ∨ Q = Finset.univ := by
  have hstep (d : Fin 4) : d ∈ Q ↔ d - 1 ∈ Q := by
    have hd := h d
    simp [compassSectorBoundary] at hd
    by_cases hq : d ∈ Q <;> by_cases hp : d - 1 ∈ Q <;> simp_all
  have h01 : (0 : Fin 4) ∈ Q ↔ 1 ∈ Q := by
    simpa using (hstep (1 : Fin 4)).symm
  have h12 : (1 : Fin 4) ∈ Q ↔ 2 ∈ Q := by
    simpa using (hstep (2 : Fin 4)).symm
  have h23 : (2 : Fin 4) ∈ Q ↔ 3 ∈ Q := by
    simpa using (hstep (3 : Fin 4)).symm
  have hall (x : Fin 4) : x ∈ Q ↔ (0 : Fin 4) ∈ Q := by
    fin_cases x
    · exact Iff.rfl
    · exact h01.symm
    · exact h12.symm.trans h01.symm
    · exact Iff.trans h23.symm (Iff.trans h12.symm h01.symm)
  by_cases hQ : Q.Nonempty
  · right
    apply Finset.eq_univ_iff_forall.mpr
    intro x
    rcases hQ with ⟨y, hy⟩
    exact (hall x).mpr ((hall y).mp hy)
  · left
    exact Finset.not_nonempty_iff_eq_empty.mp hQ

theorem primalCompassQuarterTurn_eq_sector_boundary_formula
    (Q : Finset (Fin 4)) (a b : Fin 4) (k : ℤ) (hab : a ≠ b)
    (hk : k = -1 ∨ k = 1)
    (h : ∀ d, compassSectorBoundary Q d =
      if d = b then k else if d = a then -k else 0) :
    primalCompassQuarterTurn (a + 2) b = k * (2 - (Q.card : ℤ)) := by
  rcases hk with hk | hk <;> subst k
  fin_cases a <;> fin_cases b
  all_goals
    try norm_num at hab
  all_goals
    by_cases hq0 : (0 : Fin 4) ∈ Q <;>
      by_cases hq1 : (1 : Fin 4) ∈ Q <;>
      by_cases hq2 : (2 : Fin 4) ∈ Q <;>
      by_cases hq3 : (3 : Fin 4) ∈ Q
  all_goals
      have hneg : (-1 : Fin 4) = 3 := by decide
      have h0 := h (0 : Fin 4)
      have h1 := h (1 : Fin 4)
      have h2 := h (2 : Fin 4)
      have h3 := h (3 : Fin 4)
      simp [compassSectorBoundary, hneg, hq0, hq1, hq2, hq3] at h0 h1 h2 h3
      all_goals
        have hQ : Q =
          (if (0 : Fin 4) ∈ Q then ({(0 : Fin 4)} : Finset (Fin 4)) else ∅) ∪
          (if (1 : Fin 4) ∈ Q then ({(1 : Fin 4)} : Finset (Fin 4)) else ∅) ∪
          (if (2 : Fin 4) ∈ Q then ({(2 : Fin 4)} : Finset (Fin 4)) else ∅) ∪
          (if (3 : Fin 4) ∈ Q then ({(3 : Fin 4)} : Finset (Fin 4)) else ∅) := by
          ext x
          fin_cases x <;> simp [hq0, hq1, hq2, hq3]
        have hcard : (Q.card : ℤ) =
          (if (0 : Fin 4) ∈ Q then 1 else 0) + (if (1 : Fin 4) ∈ Q then 1 else 0) +
          (if (2 : Fin 4) ∈ Q then 1 else 0) + (if (3 : Fin 4) ∈ Q then 1 else 0) := by
          rw [hQ]
          simp [hq0, hq1, hq2, hq3]
        simp [hq0, hq1, hq2, hq3] at hcard
        norm_num [primalCompassQuarterTurn]
        all_goals omega

end PottsContinuity.FKC.Medial
