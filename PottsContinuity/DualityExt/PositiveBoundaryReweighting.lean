module

public import PottsContinuity.DualityExt.PositiveBoundaryMerge
public import Mathlib.Tactic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
# Exact event reweighting under a two-class boundary merge

Merging separately wired boundary classes multiplies the unnormalized mass of
the configurations that still separate them by `q⁻¹`. This file derives the
resulting normalized event probability, including its partition-function
correction, for every positive cluster weight.
-/

@[expose] public section

namespace PottsContinuity.DualityExt

open PottsContinuity.PD.FK
open PottsContinuity.PD.FK.FiniteProbability
open scoped BigOperators

noncomputable section

variable {V : Type*} [Finite V] {G : SimpleGraph V}

local instance positiveReweightEdgeFintype : Fintype G.edgeSet := Fintype.ofFinite _
local instance positiveReweightEdgeDecidableEq : DecidableEq G.edgeSet :=
  positiveDMPEdgeDecidableEq
local instance positiveReweightConfigFintype : Fintype (Configuration G) := Fintype.ofFinite _
local instance positiveReweightConfigDecidableEq : DecidableEq (Configuration G) :=
  Classical.decEq _

/-- Configurations whose old open components do not join the selected boundary
vertices. -/
noncomputable def positiveBoundaryDisconnectedEvent
    (ξ : BoundaryCondition V) (u v : V) : Set (Configuration G) := by
  classical
  exact {A | ¬ (componentSetoid G ξ A).r u v}

/-- Real probability of an event under the positive-`q` finite FK law. -/
noncomputable def positiveFKEventProbability {q p : ℝ}
    (ξ : BoundaryCondition V) (S : Set (Configuration G)) : ℝ := by
  classical
  exact ∑ A : Configuration G,
    if A ∈ S then positiveFKProbability q p ξ A else 0

noncomputable def positiveEventWeightSum (S : Set (Configuration G))
    (f : Configuration G → ℝ) : ℝ := by
  classical
  exact ∑ A : Configuration G, if A ∈ S then f A else 0

private theorem positiveEventWeightSum_split (S : Set (Configuration G))
    (f : Configuration G → ℝ) :
    positiveEventWeightSum S f + positiveEventWeightSum Sᶜ f = ∑ A, f A := by
  classical
  unfold positiveEventWeightSum
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro A hA
  by_cases h : A ∈ S <;> simp [h]

private theorem positiveEventWeightSum_piecewise (S : Set (Configuration G))
    [DecidablePred (fun A : Configuration G => A ∈ S)]
    (f g : Configuration G → ℝ) :
    (∑ A, if A ∈ S then f A else g A) =
      positiveEventWeightSum S f + positiveEventWeightSum Sᶜ g := by
  classical
  unfold positiveEventWeightSum
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro A hA
  by_cases h : A ∈ S <;> simp [h]

private theorem positiveEventWeightSum_div (S : Set (Configuration G))
    (f : Configuration G → ℝ) (c : ℝ) :
    positiveEventWeightSum S (fun A => f A / c) =
      positiveEventWeightSum S f / c := by
  classical
  unfold positiveEventWeightSum
  calc
    (∑ A : Configuration G, if A ∈ S then f A / c else 0) =
        ∑ A, (if A ∈ S then f A else 0) / c := by
          apply Finset.sum_congr rfl
          intro A hA
          by_cases h : A ∈ S <;> simp [h]
    _ = (∑ A : Configuration G, if A ∈ S then f A else 0) / c := by
          rw [Finset.sum_div]

private theorem positiveFKProbability_sum {q p : ℝ}
    (hq : 0 < q) (hp : 0 < p) (hp1 : p < 1) (ξ : BoundaryCondition V) :
    ∑ A : Configuration G, positiveFKProbability q p ξ A = 1 := by
  unfold positiveFKProbability positiveFKPartitionFunction
  exact FiniteProbability.sum_probability _
    (positiveFKWeight_pos' hq hp hp1 ξ)

private theorem positiveFKEventProbability_eq_weightSum_div {q p : ℝ}
    (_hq : 0 < q) (_hp : 0 < p) (_hp1 : p < 1) (ξ : BoundaryCondition V)
    (S : Set (Configuration G)) :
    positiveFKEventProbability (q := q) (p := p) ξ S =
      positiveEventWeightSum S (positiveFKWeight G q p ξ) /
        positiveFKPartitionFunction G q p ξ := by
  classical
  unfold positiveFKEventProbability positiveFKProbability
  change positiveEventWeightSum S
    (fun A => positiveFKWeight G q p ξ A /
      positiveFKPartitionFunction G q p ξ) = _
  exact positiveEventWeightSum_div S (positiveFKWeight G q p ξ)
    (positiveFKPartitionFunction G q p ξ)

private theorem positiveFKPartitionFunction_pos' {q p : ℝ}
    (hq : 0 < q) (hp : 0 < p) (hp1 : p < 1) (ξ : BoundaryCondition V) :
    0 < positiveFKPartitionFunction G q p ξ := by
  unfold positiveFKPartitionFunction
  exact FiniteProbability.partition_pos _ (positiveFKWeight_pos' hq hp hp1 ξ)

private theorem positiveFKProbability_pos' {q p : ℝ}
    (hq : 0 < q) (hp : 0 < p) (hp1 : p < 1)
    (ξ : BoundaryCondition V) (A : Configuration G) :
    0 < positiveFKProbability q p ξ A := by
  unfold positiveFKProbability
  exact div_pos (positiveFKWeight_pos' hq hp hp1 ξ A)
    (positiveFKPartitionFunction_pos' hq hp hp1 ξ)

private theorem positiveFKEventProbability_nonneg {q p : ℝ}
    (hq : 0 < q) (hp : 0 < p) (hp1 : p < 1)
    (ξ : BoundaryCondition V) (S : Set (Configuration G)) :
    0 ≤ positiveFKEventProbability (q := q) (p := p) ξ S := by
  classical
  unfold positiveFKEventProbability
  apply Finset.sum_nonneg
  intro A hA
  split_ifs
  · exact (positiveFKProbability_pos' hq hp hp1 ξ A).le
  · exact le_rfl

private theorem positiveFKEventProbability_le_one {q p : ℝ}
    (hq : 0 < q) (hp : 0 < p) (hp1 : p < 1)
    (ξ : BoundaryCondition V) (S : Set (Configuration G)) :
    positiveFKEventProbability (q := q) (p := p) ξ S ≤ 1 := by
  classical
  unfold positiveFKEventProbability
  calc
    _ ≤ ∑ A : Configuration G, positiveFKProbability q p ξ A := by
      apply Finset.sum_le_sum
      intro A hA
      by_cases h : A ∈ S
      · simp [h]
      · simpa [h] using (positiveFKProbability_pos' hq hp hp1 ξ A).le
    _ = 1 := positiveFKProbability_sum hq hp hp1 ξ

/-- Event probabilities are unchanged when a boundary condition is replaced by
another name for the same partition. -/
theorem positiveFKEventProbability_eq_of_partition_eq {q p : ℝ}
    (_hq : 0 < q) (_hp : 0 < p) (_hp1 : p < 1)
    (ξ η : BoundaryCondition V) (hξη : ξ.partition = η.partition)
    (S : Set (Configuration G)) :
    positiveFKEventProbability (q := q) (p := p) ξ S =
      positiveFKEventProbability (q := q) (p := p) η S := by
  have hw (A : Configuration G) :
      positiveFKWeight G q p ξ A = positiveFKWeight G q p η A := by
    simp [positiveFKWeight, componentCount, componentSetoid, hξη]
  have hZ : positiveFKPartitionFunction G q p ξ =
      positiveFKPartitionFunction G q p η := by
    unfold positiveFKPartitionFunction
    congr 1
    funext A
    exact hw A
  unfold positiveFKEventProbability positiveFKProbability
  rw [hZ]
  apply Finset.sum_congr rfl
  intro A hA
  simp only [hw A]

/-- Any event contained in the old disconnection event receives at least its
old probability divided by `q` after the two vertices are wired together. -/
theorem positiveFKEventProbability_boundaryMerge_subset_disconnected_ge_div
    {q p : ℝ} (hq : 1 ≤ q) (hp : 0 < p) (hp1 : p < 1)
    (ξ : BoundaryCondition V) (u v : V) (S : Set (Configuration G))
    (hS : S ⊆ positiveBoundaryDisconnectedEvent (G := G) ξ u v) :
    positiveFKEventProbability (q := q) (p := p) ξ S / q ≤
      positiveFKEventProbability (q := q) (p := p)
        (positiveBoundaryMerge ξ u v) S := by
  classical
  have hqpos : 0 < q := lt_of_lt_of_le (by norm_num) hq
  let E := positiveBoundaryDisconnectedEvent (G := G) ξ u v
  let w₀ := positiveFKWeight G q p ξ
  let w₁ := positiveFKWeight G q p (positiveBoundaryMerge ξ u v)
  let Z₀ := positiveFKPartitionFunction G q p ξ
  let Z₁ := positiveFKPartitionFunction G q p (positiveBoundaryMerge ξ u v)
  let a := positiveFKEventProbability (q := q) (p := p) ξ S
  let b := positiveFKEventProbability (q := q) (p := p) ξ E
  let D := (1 - b) + b / q
  have hZ₀ : 0 < Z₀ := by
    dsimp [Z₀]
    exact positiveFKPartitionFunction_pos' hqpos (by linarith) hp1 ξ
  have hweight (A : Configuration G) :
      w₁ A = if A ∈ E then w₀ A / q else w₀ A := by
    by_cases hA : A ∈ E
    · have hsep : ¬ (componentSetoid G ξ A).r u v := by
        simpa [E, positiveBoundaryDisconnectedEvent] using hA
      have hw := (positiveFKWeight_boundaryMerge (q := q) (p := p)
        hqpos ξ A u v).2 hsep
      simpa [E, w₀, w₁, hA] using hw
    · have hconn : (componentSetoid G ξ A).r u v := by
        simpa [E, positiveBoundaryDisconnectedEvent] using hA
      have hw := (positiveFKWeight_boundaryMerge (q := q) (p := p)
        hqpos ξ A u v).1 hconn
      simpa [E, w₀, w₁, hA] using hw
  let S₀ := positiveEventWeightSum S w₀
  let E₀ := positiveEventWeightSum E w₀
  have ha : S₀ = Z₀ * a := by
    have ha' : a = S₀ / Z₀ := by
      change positiveFKEventProbability (q := q) (p := p) ξ S =
        positiveEventWeightSum S w₀ / Z₀
      exact positiveFKEventProbability_eq_weightSum_div hqpos (by linarith) hp1 ξ S
    rw [ha']
    field_simp [hZ₀.ne']
  have hb : E₀ = Z₀ * b := by
    have hb' : b = E₀ / Z₀ := by
      change positiveFKEventProbability (q := q) (p := p) ξ E =
        positiveEventWeightSum E w₀ / Z₀
      exact positiveFKEventProbability_eq_weightSum_div hqpos (by linarith) hp1 ξ E
    rw [hb']
    field_simp [hZ₀.ne']
  have hZ₁ : Z₁ = E₀ / q + (Z₀ - E₀) := by
    change (∑ A : Configuration G, w₁ A) =
      E₀ / q + ((∑ A : Configuration G, w₀ A) - E₀)
    calc
      _ = ∑ A : Configuration G, if A ∈ E then w₀ A / q else w₀ A := by
        apply Finset.sum_congr rfl
        intro A hA
        exact hweight A
      _ = positiveEventWeightSum E (fun A => w₀ A / q) +
          positiveEventWeightSum Eᶜ w₀ := positiveEventWeightSum_piecewise E _ _
      _ = E₀ / q + ((∑ A : Configuration G, w₀ A) - E₀) := by
        rw [positiveEventWeightSum_div]
        have hsplit := positiveEventWeightSum_split E w₀
        dsimp [E₀] at hsplit ⊢
        linarith
  have hZ₁' : Z₁ = Z₀ * D := by
    rw [hZ₁, hb]
    dsimp [D]
    ring
  have hDpos : 0 < D := by
    have hZ₁pos : 0 < Z₁ := by
      dsimp [Z₁]
      exact positiveFKPartitionFunction_pos' hqpos (by linarith) hp1
        (positiveBoundaryMerge ξ u v)
    have hmul : 0 < Z₀ * D := by rw [← hZ₁']; exact hZ₁pos
    by_contra hD'
    have hD'le : D ≤ 0 := le_of_not_gt hD'
    have hmul' : Z₀ * D ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hZ₀.le hD'le
    linarith
  have hnum : positiveEventWeightSum S w₁ = S₀ / q := by
    calc
      positiveEventWeightSum S w₁ =
          positiveEventWeightSum S (fun A => w₀ A / q) := by
        unfold positiveEventWeightSum
        apply Finset.sum_congr rfl
        intro A hA
        by_cases hmem : A ∈ S
        · have hE : A ∈ E := hS hmem
          simp [hmem, hE, hweight]
        · simp [hmem]
      _ = positiveEventWeightSum S w₀ / q := positiveEventWeightSum_div S w₀ q
      _ = S₀ / q := by rfl
  have hprob : positiveFKEventProbability (q := q) (p := p)
      (positiveBoundaryMerge ξ u v) S =
        positiveEventWeightSum S w₁ / Z₁ := by
    simpa [w₁, Z₁] using positiveFKEventProbability_eq_weightSum_div
      hqpos (by linarith) hp1 (positiveBoundaryMerge ξ u v) S
  have ha0 : 0 ≤ a := by
    dsimp [a]
    exact positiveFKEventProbability_nonneg hqpos (by linarith) hp1 ξ S
  have hdiv0 : 0 ≤ a / q := div_nonneg ha0 hqpos.le
  have hle : (a / q) * D ≤ a / q := by
    have hDle : D ≤ 1 := by
      dsimp [D]
      have hb0 : 0 ≤ b := by
        dsimp [b]
        exact positiveFKEventProbability_nonneg hqpos (by linarith) hp1 ξ E
      have hb1 : b ≤ 1 := by
        dsimp [b]
        exact positiveFKEventProbability_le_one hqpos (by linarith) hp1 ξ E
      have hdiv : b / q ≤ b := by
        rw [div_le_iff₀ hqpos]
        nlinarith [hq, hb0]
      linarith
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hDle hdiv0
  change a / q ≤ positiveFKEventProbability (q := q) (p := p)
    (positiveBoundaryMerge ξ u v) S
  rw [hprob, hnum, hZ₁', ha]
  calc
    a / q ≤ (a / q) / D := (le_div_iff₀ hDpos).2 hle
    _ = (Z₀ * a / q) / (Z₀ * D) := by
      field_simp [hZ₀.ne', hDpos.ne']

end
end PottsContinuity.DualityExt

