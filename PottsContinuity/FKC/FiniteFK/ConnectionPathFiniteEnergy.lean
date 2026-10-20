-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/ConnectionPathFiniteEnergy.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.AdjacentBoundaryConnectionLowerBound
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

open MeasureTheory
noncomputable section

/-- Along any actual graph walk, connection mass can decrease by at most the
single-edge finite-energy factor at each step. The walk itself need not be
open; the cost accounts for opening its edges. -/
theorem actualConnection_probability_along_walk_finite_energy
    {V : Type*} [Finite V] [DecidableEq V] {G : SimpleGraph V}
    (q : ClusterWeight) (ξ : BoundaryCondition V) {x y z : V}
    (p : G.Walk x y) :
    (1 / (1 + loopWeight q) : ℝ) ^ p.length *
        (measure G q ξ {A | ActualConnected G A x z}).toReal ≤
      (measure G q ξ {A | ActualConnected G A y z}).toReal := by
  classical
  let ε : ℝ := 1 / (1 + loopWeight q)
  have hε : 0 ≤ ε := by
    dsimp [ε]
    exact div_nonneg (by norm_num) (le_of_lt (PottsContinuity.FKC.one_add_loopWeight_pos q))
  induction p with
  | nil =>
      simp [ActualConnected]
  | @cons u v w huv tail ih =>
      have hstep : ε *
          (measure G q ξ {A | ActualConnected G A u z}).toReal ≤
        (measure G q ξ {A | ActualConnected G A v z}).toReal := by
        have h := adjacent_boundary_connection_probability_lower_bound q ξ
          huv.symm ({z} : Set V)
        simpa [ε, Set.mem_singleton_iff] using h
      rw [SimpleGraph.Walk.length_cons]
      calc
        ε ^ (tail.length + 1) *
            (measure G q ξ {A | ActualConnected G A u z}).toReal =
          ε ^ tail.length *
            (ε * (measure G q ξ {A | ActualConnected G A u z}).toReal) := by
              rw [pow_succ]
              ring
        _ ≤ ε ^ tail.length *
            (measure G q ξ {A | ActualConnected G A v z}).toReal :=
          mul_le_mul_of_nonneg_left hstep (pow_nonneg hε _)
        _ ≤ (measure G q ξ {A | ActualConnected G A w z}).toReal := ih

/-- If the deterministic walk has length at most `L`, one may pay the uniform
cost for `L` steps. The FK factor is derived to lie in `[0,1]` from `q`. -/
theorem actualConnection_probability_along_walk_length_le
    {V : Type*} [Finite V] [DecidableEq V] {G : SimpleGraph V}
    (q : ClusterWeight) (ξ : BoundaryCondition V) {x y z : V}
    (p : G.Walk x y) (L : ℕ) (hL : p.length ≤ L) :
    (1 / (1 + loopWeight q) : ℝ) ^ L *
        (measure G q ξ {A | ActualConnected G A x z}).toReal ≤
      (measure G q ξ {A | ActualConnected G A y z}).toReal := by
  let ε : ℝ := 1 / (1 + loopWeight q)
  have hε : 0 ≤ ε := by
    dsimp [ε]
    exact div_nonneg (by norm_num) (le_of_lt (PottsContinuity.FKC.one_add_loopWeight_pos q))
  have hε1 : ε ≤ 1 := by
    dsimp [ε]
    apply (div_le_iff₀ (PottsContinuity.FKC.one_add_loopWeight_pos q)).2
    have hq := PottsContinuity.FKC.one_le_loopWeight q
    linarith
  let d := L - p.length
  have hLd : L = p.length + d := by dsimp [d]; omega
  have hd : ε ^ d ≤ 1 := pow_le_one₀ hε hε1
  have hpow : ε ^ L ≤ ε ^ p.length := by
    rw [hLd, pow_add]
    calc
      ε ^ p.length * ε ^ d ≤ ε ^ p.length * 1 :=
        mul_le_mul_of_nonneg_left hd (pow_nonneg hε _)
      _ = ε ^ p.length := by ring
  have hprob : 0 ≤ (measure G q ξ
      {A | ActualConnected G A x z}).toReal := ENNReal.toReal_nonneg
  have hpath := actualConnection_probability_along_walk_finite_energy (z := z) q ξ p
  dsimp [ε] at hpow ⊢
  calc
    (1 / (1 + loopWeight q) : ℝ) ^ L *
        (measure G q ξ {A | ActualConnected G A x z}).toReal ≤
      (1 / (1 + loopWeight q) : ℝ) ^ p.length *
        (measure G q ξ {A | ActualConnected G A x z}).toReal :=
          mul_le_mul_of_nonneg_right hpow hprob
    _ ≤ (measure G q ξ {A | ActualConnected G A y z}).toReal := hpath

/-- Moving both endpoints along finite deterministic walks costs the sum of
their lengths. Connectivity is actual open-path connectivity and is used
symmetrically for the second endpoint. -/
theorem actualConnection_probability_two_walks_length_le
    {V : Type*} [Finite V] [DecidableEq V] {G : SimpleGraph V}
    (q : ClusterWeight) (ξ : BoundaryCondition V)
    {x y z w : V} (p : G.Walk x y) (r : G.Walk z w)
    (L₁ L₂ : ℕ) (hp : p.length ≤ L₁) (hr : r.length ≤ L₂) :
    (1 / (1 + loopWeight q) : ℝ) ^ (L₁ + L₂) *
        (measure G q ξ {A | ActualConnected G A x z}).toReal ≤
      (measure G q ξ {A | ActualConnected G A y w}).toReal := by
  let ε : ℝ := 1 / (1 + loopWeight q)
  have hε : 0 ≤ ε := by
    dsimp [ε]
    exact div_nonneg (by norm_num) (le_of_lt (PottsContinuity.FKC.one_add_loopWeight_pos q))
  have hleft := actualConnection_probability_along_walk_length_le
    (z := z) q ξ p L₁ hp
  have hright := actualConnection_probability_along_walk_length_le
    (x := z) (y := w) (z := y) q ξ r L₂ hr
  have hright' : ε ^ L₂ *
      (measure G q ξ {A | ActualConnected G A y z}).toReal ≤
        (measure G q ξ {A | ActualConnected G A y w}).toReal := by
    have hset₁ : {A | ActualConnected G A z y} =
        {A | ActualConnected G A y z} := by
      ext A
      exact ⟨fun h => h.symm, fun h => h.symm⟩
    have hsym₁ : measure G q ξ {A | ActualConnected G A z y} =
        measure G q ξ {A | ActualConnected G A y z} := congrArg (measure G q ξ) hset₁
    have hset₂ : {A | ActualConnected G A w y} =
        {A | ActualConnected G A y w} := by
      ext A
      exact ⟨fun h => h.symm, fun h => h.symm⟩
    have hsym₂ : measure G q ξ {A | ActualConnected G A w y} =
        measure G q ξ {A | ActualConnected G A y w} := congrArg (measure G q ξ) hset₂
    have hright0 := actualConnection_probability_along_walk_length_le
      (x := z) (y := w) (z := y) q ξ r L₂ hr
    rw [hsym₁, hsym₂] at hright0
    change ε ^ L₂ * (measure G q ξ
      {A | ActualConnected G A y z}).toReal ≤
        (measure G q ξ {A | ActualConnected G A y w}).toReal at hright0
    exact hright0
  have hprob : 0 ≤ (measure G q ξ
      {A | ActualConnected G A x z}).toReal := ENNReal.toReal_nonneg
  have hmul : ε ^ L₂ * (ε ^ L₁ *
      (measure G q ξ {A | ActualConnected G A x z}).toReal) ≤
      ε ^ L₂ * (measure G q ξ {A | ActualConnected G A y z}).toReal :=
    mul_le_mul_of_nonneg_left hleft (pow_nonneg hε _)
  calc
    (1 / (1 + loopWeight q) : ℝ) ^ (L₁ + L₂) *
        (measure G q ξ {A | ActualConnected G A x z}).toReal =
      ε ^ L₂ * (ε ^ L₁ *
        (measure G q ξ {A | ActualConnected G A x z}).toReal) := by
          dsimp [ε]
          rw [pow_add]
          ring
    _ ≤ ε ^ L₂ *
        (measure G q ξ {A | ActualConnected G A y z}).toReal := hmul
    _ ≤ (measure G q ξ {A | ActualConnected G A y w}).toReal := hright'

end
end PottsContinuity.FKC.FiniteFK
