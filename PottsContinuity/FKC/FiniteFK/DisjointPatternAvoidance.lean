-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/DisjointPatternAvoidance.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.FiniteGraphPatternEnergy
public import Mathlib.Tactic

@[expose] public section

open MeasureTheory
open scoped BigOperators

namespace PottsContinuity.FKC.FiniteFK
noncomputable section

variable {V : Type*} [Finite V] {G : SimpleGraph V}

local instance disjointPatternEdgeFintype : Fintype G.edgeSet := Fintype.ofFinite _
local instance disjointPatternEdgeDecidableEq : DecidableEq G.edgeSet := Classical.decEq _
attribute [local instance] configurationMeasurableSpace
local instance : DiscreteMeasurableSpace (Configuration G) :=
  ⟨fun _ => MeasurableSpace.measurableSet_top⟩

/-- Configurations avoiding every prescribed finite edge pattern in a finite
family. -/
def finitePatternAvoidanceEvent {ι : Type*} [DecidableEq ι] (J : Finset ι)
    (F : ι → Finset G.edgeSet) (σ : ι → G.edgeSet → Bool) :
    Set (Configuration G) :=
  {A | ∀ i ∈ J, A ∉ finiteConfigurationPatternEvent (F i) (σ i)}

omit [Finite V] in
private theorem finiteConfigurationPatternEvent_stable_erase_of_not_mem
    (E : Finset G.edgeSet) (σ : G.edgeSet → Bool)
    (e : G.edgeSet) (he : e ∉ E) (A : Configuration G) :
    (A ∈ finiteConfigurationPatternEvent E σ) ↔
      (A.erase e ∈ finiteConfigurationPatternEvent E σ) := by
  simp only [finiteConfigurationPatternEvent, Set.mem_ofPred_eq]
  constructor
  · intro h f hf
    have hne : f ≠ e := by
      intro hEq
      subst f
      exact he hf
    have hmem : f ∈ A.erase e ↔ f ∈ A := by simp [hne]
    rw [hmem]
    exact h f hf
  · intro h f hf
    have hne : f ≠ e := by
      intro hEq
      subst f
      exact he hf
    have hmem : f ∈ A.erase e ↔ f ∈ A := by simp [hne]
    rw [← hmem]
    exact h f hf

omit [Finite V] in
private theorem finitePatternAvoidanceEvent_insert
    {ι : Type*} [DecidableEq ι] (i : ι) (J : Finset ι) (_hi : i ∉ J)
    (F : ι → Finset G.edgeSet) (σ : ι → G.edgeSet → Bool) :
    finitePatternAvoidanceEvent (insert i J) F σ =
      finitePatternAvoidanceEvent J F σ ∩
        (finiteConfigurationPatternEvent (F i) (σ i))ᶜ := by
  ext A
  simp [finitePatternAvoidanceEvent, Finset.mem_insert, and_comm]

/-- For pairwise edge-disjoint prescribed patterns, the probability of avoiding
all of them is at most the product of their one-pattern avoidance bounds. An
empty edge block prescribes the always-true pattern, so it forces avoidance
probability to zero and contributes the zero factor in this formula. -/
theorem configurationProbability_disjoint_pattern_avoidance
    {ι : Type*} [DecidableEq ι] (q : ClusterWeight) (ξ : BoundaryCondition V)
    (J : Finset ι) (F : ι → Finset G.edgeSet) (σ : ι → G.edgeSet → Bool)
    (hdisj : ∀ i ∈ J, ∀ j ∈ J, i ≠ j → Disjoint (F i) (F j)) :
    (measure G q ξ (finitePatternAvoidanceEvent J F σ)).toReal ≤
      ∏ i ∈ J, (1 - (1 / (1 + loopWeight q)) ^ (F i).card) := by
  classical
  let κ : ℝ := 1 / (1 + loopWeight q)
  have hκ0 : 0 ≤ κ := by
    dsimp [κ]
    exact div_nonneg (by norm_num) (one_add_loopWeight_pos q).le
  have hκ1 : κ ≤ 1 := by
    dsimp [κ]
    rw [div_le_one (one_add_loopWeight_pos q)]
    linarith [one_le_loopWeight q]
  have hfactor_nonneg : ∀ n : ℕ, 0 ≤ 1 - κ ^ n := by
    intro n
    have hpow : κ ^ n ≤ 1 := pow_le_one₀ hκ0 hκ1
    linarith
  induction J using Finset.induction_on with
  | empty =>
      simp [finitePatternAvoidanceEvent]
  | @insert i J hi ih =>
      have hdisjRest : ∀ j ∈ J, ∀ k ∈ J, j ≠ k → Disjoint (F j) (F k) := by
        intro j hj k hk hjk
        exact hdisj j (Finset.mem_insert_of_mem hj) k (Finset.mem_insert_of_mem hk) hjk
      have hmain := ih hdisjRest
      let S := finitePatternAvoidanceEvent J F σ
      let P := finiteConfigurationPatternEvent (F i) (σ i)
      have hstable : ∀ e ∈ F i, ∀ A, A ∈ S ↔ A.erase e ∈ S := by
        intro e he A
        change (∀ j ∈ J, A ∉ finiteConfigurationPatternEvent (F j) (σ j)) ↔
          (∀ j ∈ J, A.erase e ∉ finiteConfigurationPatternEvent (F j) (σ j))
        constructor
        · intro h j hj
          have hnotmem : e ∉ F j := by
            intro hej
            have hdis := hdisj i (Finset.mem_insert_self i J) j
              (Finset.mem_insert_of_mem hj)
              (by intro hij; subst j; exact hi hj)
            exact Finset.disjoint_left.mp hdis he hej
          have heq := finiteConfigurationPatternEvent_stable_erase_of_not_mem
            (F j) (σ j) e hnotmem A
          exact (not_congr heq).mp (h j hj)
        · intro h j hj
          have hnotmem : e ∉ F j := by
            intro hej
            have hdis := hdisj i (Finset.mem_insert_self i J) j
              (Finset.mem_insert_of_mem hj)
              (by intro hij; subst j; exact hi hj)
            exact Finset.disjoint_left.mp hdis he hej
          have heq := finiteConfigurationPatternEvent_stable_erase_of_not_mem
            (F j) (σ j) e hnotmem A
          exact (not_congr heq).mpr (h j hj)
      have henergy := configurationProbability_finite_pattern_finite_energy
        q ξ S (F i) (σ i) hstable
      have hpartition :
          (measure G q ξ (S ∩ P)).toReal +
            (measure G q ξ (S ∩ Pᶜ)).toReal =
              (measure G q ξ S).toReal := by
        have hPmeas : MeasurableSet P := MeasurableSpace.measurableSet_top
        have h := MeasureTheory.measureReal_inter_add_sdiff
          (μ := measure G q ξ) (s := S) (t := P)
          hPmeas
        have hset : S \ P = S ∩ Pᶜ := by
          ext A
          simp
        rw [← hset]
        exact h
      have hrec := finitePatternAvoidanceEvent_insert i J hi F σ
      rw [hrec]
      change (measure G q ξ (S ∩ Pᶜ)).toReal ≤
        ∏ j ∈ insert i J, (1 - κ ^ (F j).card)
      have hlower : κ ^ (F i).card * (measure G q ξ S).toReal ≤
          (measure G q ξ (S ∩ P)).toReal := by
        simpa [κ] using henergy.1
      have hstep : (measure G q ξ (S ∩ Pᶜ)).toReal ≤
          (1 - κ ^ (F i).card) * (measure G q ξ S).toReal := by
        nlinarith [hpartition, hlower]
      calc
        (measure G q ξ (S ∩ Pᶜ)).toReal ≤
            (1 - κ ^ (F i).card) * (measure G q ξ S).toReal := hstep
        _ ≤ (1 - κ ^ (F i).card) *
            (∏ j ∈ J, (1 - κ ^ (F j).card)) :=
              mul_le_mul_of_nonneg_left hmain (hfactor_nonneg _)
        _ = ∏ j ∈ insert i J, (1 - κ ^ (F j).card) := by
              simp [Finset.prod_insert, hi, κ]

end
end PottsContinuity.FKC.FiniteFK
