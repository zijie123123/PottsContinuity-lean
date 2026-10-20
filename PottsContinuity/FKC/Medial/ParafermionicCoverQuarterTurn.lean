-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `Medial/ParafermionicCoverQuarterTurn.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.Medial.ParafermionicCoverGraph
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.Medial

open PottsContinuity.FKC

/-- Base quarter-turn about the branch face centered at `(1/2,-1/2)`. -/
def parafermionicCoverQuarterTurnBase (p : LatticeVertex) : LatticeVertex :=
  (-p.2, p.1 - 1)

/-- Sheet correction that moves the lower seam to the rotated seam. -/
def parafermionicCoverQuarterTurnGauge (p : LatticeVertex) : ℤ :=
  if p.1 ≤ 0 ∧ p.2 < 0 then 1 else 0

/-- The explicit lifted quarter-turn, with its actual sheet correction. -/
def parafermionicCoverQuarterTurn (u : ParafermionicCoverVertex) :
    ParafermionicCoverVertex :=
  (parafermionicCoverQuarterTurnBase u.1,
    u.2 + parafermionicCoverQuarterTurnGauge u.1)

/-- The inverse lifted quarter-turn. -/
def parafermionicCoverQuarterTurnInv (u : ParafermionicCoverVertex) :
    ParafermionicCoverVertex :=
  ((u.1.2 + 1, -u.1.1),
    u.2 - if u.1.1 > 0 ∧ u.1.2 < 0 then 1 else 0)

 theorem parafermionicCoverQuarterTurn_left_inv (u : ParafermionicCoverVertex) :
    parafermionicCoverQuarterTurnInv (parafermionicCoverQuarterTurn u) = u := by
  rcases u with ⟨⟨x, y⟩, k⟩
  simp [parafermionicCoverQuarterTurnInv, parafermionicCoverQuarterTurn,
    parafermionicCoverQuarterTurnBase, parafermionicCoverQuarterTurnGauge]
  split_ifs <;> omega

 theorem parafermionicCoverQuarterTurn_right_inv (u : ParafermionicCoverVertex) :
    parafermionicCoverQuarterTurn (parafermionicCoverQuarterTurnInv u) = u := by
  rcases u with ⟨⟨x, y⟩, k⟩
  simp [parafermionicCoverQuarterTurnInv, parafermionicCoverQuarterTurn,
    parafermionicCoverQuarterTurnBase, parafermionicCoverQuarterTurnGauge]
  split_ifs <;> omega

private theorem parafermionicCoverQuarterTurn_base_adj_iff
    (p q : LatticeVertex) :
    squareLattice.Adj (parafermionicCoverQuarterTurnBase p)
      (parafermionicCoverQuarterTurnBase q) ↔ squareLattice.Adj p q := by
  rcases p with ⟨x, y⟩
  rcases q with ⟨x', y'⟩
  rw [squareLattice_adj_iff]
  simp only [parafermionicCoverQuarterTurnBase]
  constructor <;> intro h <;> rcases h with ⟨hxx | hxx, hyy⟩ | ⟨hxx, hyy | hyy⟩ <;>
    simp [squareLattice_adj_iff] <;> omega

private theorem parafermionicCoverQuarterTurn_shift
    (p q : LatticeVertex) (h : squareLattice.Adj p q) :
    parafermionicCoverSheetShift (parafermionicCoverQuarterTurnBase p)
        (parafermionicCoverQuarterTurnBase q) =
      parafermionicCoverSheetShift p q +
        parafermionicCoverQuarterTurnGauge q - parafermionicCoverQuarterTurnGauge p := by
  rcases p with ⟨x, y⟩
  rcases q with ⟨x', y'⟩
  rw [squareLattice_adj_iff] at h
  rcases h with ⟨hx | hx, hy⟩ | ⟨hx, hy | hy⟩
  all_goals
    simp only [parafermionicCoverQuarterTurnBase, parafermionicCoverQuarterTurnGauge,
      parafermionicCoverSheetShift]
    split_ifs <;> omega

def parafermionicCoverQuarterTurn_graphIso :
    parafermionicCoverGraph ≃g parafermionicCoverGraph where
  toEquiv :=
    { toFun := parafermionicCoverQuarterTurn
      invFun := parafermionicCoverQuarterTurnInv
      left_inv := parafermionicCoverQuarterTurn_left_inv
      right_inv := parafermionicCoverQuarterTurn_right_inv }
  map_rel_iff' := by
    intro u v
    change (squareLattice.Adj (parafermionicCoverQuarterTurnBase u.1)
        (parafermionicCoverQuarterTurnBase v.1) ∧
      v.2 + parafermionicCoverQuarterTurnGauge v.1 =
        (u.2 + parafermionicCoverQuarterTurnGauge u.1) +
          parafermionicCoverSheetShift
            (parafermionicCoverQuarterTurnBase u.1)
            (parafermionicCoverQuarterTurnBase v.1)) ↔
      (squareLattice.Adj u.1 v.1 ∧
        v.2 = u.2 + parafermionicCoverSheetShift u.1 v.1)
    constructor
    · rintro ⟨hbase, hsheet⟩
      have hsource := (parafermionicCoverQuarterTurn_base_adj_iff u.1 v.1).mp hbase
      refine ⟨hsource, ?_⟩
      rw [parafermionicCoverQuarterTurn_shift u.1 v.1 hsource] at hsheet
      omega
    · rintro ⟨hbase, hsheet⟩
      refine ⟨(parafermionicCoverQuarterTurn_base_adj_iff u.1 v.1).mpr hbase, ?_⟩
      rw [parafermionicCoverQuarterTurn_shift u.1 v.1 hbase]
      omega


/-- The lifted turn sends the exact finite `U_n` vertex set into the genuinely
larger sheet-capped box `U_(n+1)`. -/
theorem parafermionicCoverQuarterTurn_mem_box_succ (n : ℕ)
    (u : ParafermionicCoverVertex) (hu : u ∈ parafermionicCoverBoxVertices n) :
    parafermionicCoverQuarterTurn u ∈ parafermionicCoverBoxVertices (n + 1) := by
  rw [parafermionicCoverBoxVertices_mem] at hu ⊢
  rcases hu with ⟨hxlo, hxhi, hylo, hyhi, hklo, hkhi⟩
  rcases u with ⟨⟨x, y⟩, k⟩
  simp only at hxlo hxhi hylo hyhi hklo hkhi
  dsimp [parafermionicCoverQuarterTurn, parafermionicCoverQuarterTurnBase,
    parafermionicCoverQuarterTurnGauge]
  have hn : 0 ≤ (n : ℤ) := Int.natCast_nonneg n
  have hn2 : 0 ≤ (n : ℤ) ^ 2 := sq_nonneg (n : ℤ)
  have hn3 : 0 ≤ (n : ℤ) ^ 3 := by positivity
  have hn4 : 0 ≤ (n : ℤ) ^ 4 := by positivity
  have hpowZ : (n : ℤ) ^ 5 + 1 ≤ ((n : ℤ) + 1) ^ 5 := by nlinarith
  simp only [Nat.cast_pow] at hklo hkhi ⊢
  split_ifs <;> constructor <;> omega


end PottsContinuity.FKC.Medial
