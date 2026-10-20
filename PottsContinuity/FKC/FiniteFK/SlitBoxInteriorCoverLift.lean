-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/SlitBoxInteriorCoverLift.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.SlitBoxDomain
public import PottsContinuity.FKC.Medial.ParafermionicCoverGraph
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

open PottsContinuity.FKC

/-- Retained box vertices away from the wired arc. -/
abbrev SlitBoxInteriorVertex (n : ℕ) :=
  {v : SlitBoxVertex n // v ∉ slitBoxWiredArc n}

/-- The sheet assigned to an interior slit vertex. The lower seam has sheet one
on its right side; the upper seam lies on the removed wired arc. -/
def slitBoxInteriorCoverLift (n : ℕ) (v : SlitBoxInteriorVertex n) :
    ParafermionicCoverVertex :=
  ((v.1.val.1, v.1.val.2), if 0 < v.1.val.1 then 1 else 0)

theorem slitBoxInteriorCoverLift_injective (n : ℕ) :
    Function.Injective (slitBoxInteriorCoverLift n) := by
  intro u v h
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg Prod.fst h

private theorem slitBoxInterior_sheetShift_eq (n : ℕ)
    {u v : SlitBoxInteriorVertex n}
    (hbase : squareLattice.Adj u.1.val v.1.val) :
    parafermionicCoverSheetShift u.1.val v.1.val =
      (if 0 < v.1.val.1 then (1 : ℤ) else 0) -
        (if 0 < u.1.val.1 then (1 : ℤ) else 0) := by
  rcases (squareLattice_adj_iff u.1.val v.1.val).mp hbase with hhor | hver
  · rcases hhor with ⟨hstep, hy⟩
    rcases hstep with hstep | hstep
    · by_cases hu0 : u.1.val.1 = 0
      · have hv1 : v.1.val.1 = 1 := by omega
        have hylt : u.1.val.2 < 0 := by
          by_contra hn
          have huArc : u.1 ∈ slitBoxWiredArc n := by
            apply (mem_slitBoxWiredArc_iff n u.1).2
            have huBox : u.1.val ∈ latticeRectangle (-(n : ℤ), -(n : ℤ)) (2*n) (2*n) := u.1.property
            rw [mem_latticeRectangle] at huBox
            exact ⟨hu0, by omega, by omega⟩
          exact u.2 huArc
        have hy' : u.1.val.2 = v.1.val.2 := by omega
        have hylt' : v.1.val.2 < 0 := by omega
        simp [parafermionicCoverSheetShift, hu0, hv1, hy', hylt']
      · by_cases hv0 : v.1.val.1 = 0
        · have huNeg : u.1.val.1 = -1 := by omega
          simp [parafermionicCoverSheetShift, huNeg, hv0]
        · have hsign : (if 0 < v.1.val.1 then (1 : ℤ) else 0) =
              (if 0 < u.1.val.1 then (1 : ℤ) else 0) := by
            by_cases hpos : 0 < u.1.val.1
            · have : 0 < v.1.val.1 := by omega
              simp [hpos, this]
            · have : ¬ 0 < v.1.val.1 := by omega
              simp [hpos, this]
          have hshift : parafermionicCoverSheetShift u.1.val v.1.val = 0 := by
            unfold parafermionicCoverSheetShift
            split_ifs <;> omega
          rw [hshift, hsign]
          simp
    · by_cases hv0 : v.1.val.1 = 0
      · have hu1 : u.1.val.1 = 1 := by omega
        have hylt : v.1.val.2 < 0 := by
          by_contra hn
          have hvArc : v.1 ∈ slitBoxWiredArc n := by
            apply (mem_slitBoxWiredArc_iff n v.1).2
            have hvBox : v.1.val ∈ latticeRectangle (-(n : ℤ), -(n : ℤ)) (2*n) (2*n) := v.1.property
            rw [mem_latticeRectangle] at hvBox
            exact ⟨hv0, by omega, by omega⟩
          exact v.2 hvArc
        have hy' : u.1.val.2 = v.1.val.2 := by omega
        simp [parafermionicCoverSheetShift, hu1, hv0, hy', hylt]
      · by_cases hu0 : u.1.val.1 = 0
        · have hvNeg : v.1.val.1 = -1 := by omega
          simp [parafermionicCoverSheetShift, hu0, hvNeg]
        · have hsign : (if 0 < v.1.val.1 then (1 : ℤ) else 0) =
              (if 0 < u.1.val.1 then (1 : ℤ) else 0) := by
            by_cases hpos : 0 < u.1.val.1
            · have : 0 < v.1.val.1 := by omega
              simp [hpos, this]
            · have : ¬ 0 < v.1.val.1 := by omega
              simp [hpos, this]
          have hshift : parafermionicCoverSheetShift u.1.val v.1.val = 0 := by
            unfold parafermionicCoverSheetShift
            split_ifs <;> omega
          rw [hshift, hsign]
          simp
  · rcases hver with ⟨hx, hstep⟩
    have hsign : (if 0 < v.1.val.1 then (1 : ℤ) else 0) =
        (if 0 < u.1.val.1 then (1 : ℤ) else 0) := by rw [← hx]
    have hshift : parafermionicCoverSheetShift u.1.val v.1.val = 0 := by
      unfold parafermionicCoverSheetShift
      split_ifs <;> omega
    rw [hshift, hsign]
    simp

theorem slitBoxInteriorCoverLift_adj_iff (n : ℕ)
    (u v : SlitBoxInteriorVertex n) :
    (slitBoxGraph n).Adj u.1 v.1 ↔
      parafermionicCoverGraph.Adj (slitBoxInteriorCoverLift n u)
        (slitBoxInteriorCoverLift n v) := by
  constructor
  · intro hs
    have hs' := (slitBoxGraph_adj_iff n u.1 v.1).mp hs
    rcases hs' with ⟨hbase, _⟩
    change squareLattice.Adj u.1.val v.1.val ∧
      (if 0 < v.1.val.1 then (1 : ℤ) else 0) =
        (if 0 < u.1.val.1 then (1 : ℤ) else 0) +
          parafermionicCoverSheetShift u.1.val v.1.val
    refine ⟨hbase, ?_⟩
    rw [slitBoxInterior_sheetShift_eq n hbase]
    omega
  · intro hc
    change squareLattice.Adj u.1.val v.1.val ∧
      (if 0 < v.1.val.1 then (1 : ℤ) else 0) =
        (if 0 < u.1.val.1 then (1 : ℤ) else 0) +
          parafermionicCoverSheetShift u.1.val v.1.val at hc
    apply (slitBoxGraph_adj_iff n u.1 v.1).mpr
    refine ⟨hc.1, ?_⟩
    intro hboth
    exact u.2 ((mem_slitBoxWiredArc_iff n u.1).mpr hboth.1)

theorem slitBoxInteriorCoverLift_neighbor_closed (n : ℕ)
    (u : SlitBoxInteriorVertex n) (v : ParafermionicCoverVertex)
    (hvbox : v.1 ∈ latticeRectangle (-(n : ℤ), -(n : ℤ)) (2 * n) (2 * n))
    (hvout : ¬ (v.1.1 = 0 ∧ 0 ≤ v.1.2 ∧ v.1.2 ≤ n))
    (hadj : parafermionicCoverGraph.Adj (slitBoxInteriorCoverLift n u) v) :
    v = slitBoxInteriorCoverLift n
      ⟨⟨v.1, hvbox⟩, fun hmem => hvout ((mem_slitBoxWiredArc_iff n ⟨v.1, hvbox⟩).mp hmem)⟩ := by
  let w : SlitBoxInteriorVertex n :=
    ⟨⟨v.1, hvbox⟩, fun hmem => hvout ((mem_slitBoxWiredArc_iff n ⟨v.1, hvbox⟩).mp hmem)⟩
  have hadjBase : (slitBoxGraph n).Adj u.1 w.1 := by
    apply (slitBoxGraph_adj_iff n u.1 w.1).2
    refine ⟨hadj.1, ?_⟩
    intro hboth
    exact u.2 ((mem_slitBoxWiredArc_iff n u.1).mpr hboth.1)
  have hcover : parafermionicCoverGraph.Adj (slitBoxInteriorCoverLift n u)
      (slitBoxInteriorCoverLift n w) := (slitBoxInteriorCoverLift_adj_iff n u w).mp hadjBase
  calc
    v = parafermionicCoverNeighborLift (slitBoxInteriorCoverLift n u) v.1 :=
      parafermionicCoverNeighborLift_unique (slitBoxInteriorCoverLift n u) v.1 v rfl hadj
    _ = slitBoxInteriorCoverLift n w :=
      (parafermionicCoverNeighborLift_unique (slitBoxInteriorCoverLift n u) v.1
        (slitBoxInteriorCoverLift n w) rfl hcover).symm

end PottsContinuity.FKC.FiniteFK
