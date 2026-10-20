module

public import PottsContinuity.Thm3.Prop4.ClosedCutEnergy
public import PottsContinuity.PD.RCInfinite.FiniteEnergy
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.MeasureTheory.Measure.Real

@[expose] public section

namespace PottsContinuity.PlanarMixed.TiltedHalfHeight
open MeasureTheory PD.FK PD.RCInfinite Thm3.Prop4
noncomputable section
variable {V : Type*} [Finite V] {G : SimpleGraph V}
local instance routeTwelveEnergyEdgeFintype : Fintype G.edgeSet := Fintype.ofFinite _
local instance routeTwelveEnergyEdgeDecidableEq : DecidableEq G.edgeSet := Classical.decEq _
attribute [local instance] configurationMeasurableSpace

/-- The uniform opening cost lies strictly between zero and one. -/
theorem openEnergy_lt_one (θ : Parameters) : openEnergy θ < 1 := by
  unfold openEnergy
  apply (div_lt_one (edge_conditional_denominator_pos θ)).mpr
  have h := mul_pos (one_sub_edgeParameter_pos θ) (clusterWeight_pos θ)
  linarith

/-- The conditional opening estimate holds after every event determined by
other original edges. -/
theorem finite_open_edge_energy (θ : Parameters) (ξ : BoundaryCondition V)
    (e : G.edgeSet) (B : Set (Configuration G))
    (hstable : ∀ A, A ∈ B ↔ A.erase e ∈ B) :
    openEnergy θ*(measure G θ ξ B).toReal ≤
      (measure G θ ξ (B ∩ {A | e ∈ A})).toReal := by
  classical
  let p := e.val.out
  have hrepr : s(p.1,p.2)=e.val := Quot.out_eq _
  have hadj : G.Adj p.1 p.2 := G.mem_edgeSet.mp (hrepr ▸ e.property)
  have heq : (⟨s(p.1,p.2),G.mem_edgeSet.mpr hadj⟩ : G.edgeSet)=e := Subtype.ext hrepr
  have h := (configurationProbability_edge_finite_energy θ ξ B hadj
    (by simpa only [heq] using hstable)).1
  simpa only [heq,openEnergy] using h

/-- Open every edge of a finite block, retaining any event that does not
read that block. The bound is uniform over the boundary partition. -/
theorem finite_open_block_energy (θ : Parameters) (ξ : BoundaryCondition V)
    (F : Finset G.edgeSet) (B : Set (Configuration G))
    (hstable : ∀ e∈F, ∀ A, A∈B ↔ A.erase e∈B) :
    (openEnergy θ)^F.card*(measure G θ ξ B).toReal ≤
      (measure G θ ξ (B ∩ {A | F⊆A})).toReal := by
  classical
  induction F using Finset.induction_on with
  | empty => simp
  | @insert e F he ih =>
    have hprev := ih (fun f hf => hstable f (Finset.mem_insert_of_mem hf))
    have hsubset (A : Configuration G) : F⊆A ↔ F⊆A.erase e := by
      constructor
      · intro h f hf
        exact Finset.mem_erase.mpr ⟨by intro hfe; subst f; exact he hf,h hf⟩
      · exact fun h => h.trans (Finset.erase_subset e A)
    have hnext := finite_open_edge_energy θ ξ e (B ∩ {A | F⊆A}) (by
      intro A
      exact and_congr (hstable e (Finset.mem_insert_self e F) A) (hsubset A))
    have hsets : (B ∩ {A | F⊆A}) ∩ {A | e∈A} = B ∩ {A | insert e F⊆A} := by
      ext A
      simp only [Set.mem_inter_iff,Set.mem_ofPred_eq,Finset.insert_subset_iff]
      tauto
    rw [hsets] at hnext
    calc
      _ = openEnergy θ*((openEnergy θ)^F.card*(measure G θ ξ B).toReal) := by
        rw [Finset.card_insert_of_notMem he,pow_succ]
        ring
      _ ≤ openEnergy θ*(measure G θ ξ (B ∩ {A | F⊆A})).toReal :=
        mul_le_mul_of_nonneg_left hprev (openEnergy_pos θ).le
      _ ≤ _ := hnext

/-- Failure to open a fresh finite block has the complementary cost. -/
theorem finite_notOpenBlock_probability_le (θ : Parameters) (ξ : BoundaryCondition V)
    (F : Finset G.edgeSet) (B : Set (Configuration G))
    (hstable : ∀ e∈F, ∀ A, A∈B ↔ A.erase e∈B) :
    (measure G θ ξ (B ∩ {A | ¬ F⊆A})).toReal ≤
      (1-(openEnergy θ)^F.card)*(measure G θ ξ B).toReal := by
  have hparts := measureReal_inter_add_sdiff (μ := measure G θ ξ)
    (s := B) (t := {A | F⊆A}) (MeasurableSpace.measurableSet_top)
  have hset : B \ {A | F⊆A} = B ∩ {A | ¬ F⊆A} := by ext A; simp
  rw [hset] at hparts
  have hlower := finite_open_block_energy θ ξ F B hstable
  change (measure G θ ξ (B ∩ {A | F⊆A})).toReal +
    (measure G θ ξ (B ∩ {A | ¬ F⊆A})).toReal = (measure G θ ξ B).toReal at hparts
  nlinarith

/-- Every one of the first k blocks fails to be fully open. -/
def noOpenBlocks (blocks : ℕ → Finset G.edgeSet) (k : ℕ) : Set (Configuration G) :=
  {A | ∀ j<k, ¬ blocks j⊆A}

/-- Disjoint blocks of at most M edges have a uniform exponential failure tail. -/
theorem finite_noOpenBlocks_probability_le (θ : Parameters) (ξ : BoundaryCondition V)
    (blocks : ℕ → Finset G.edgeSet) (k M : ℕ)
    (hdisjoint : ∀ i j, i<j → Disjoint (blocks i) (blocks j))
    (hcard : ∀ j<k, (blocks j).card≤M) :
    (measure G θ ξ (noOpenBlocks blocks k)).toReal ≤
      (1-(openEnergy θ)^M)^k := by
  have hbase := (openEnergy_pos θ).le
  have hbase1 := (openEnergy_lt_one θ).le
  have hr : 0≤1-(openEnergy θ)^M := sub_nonneg.mpr (pow_le_one₀ hbase hbase1)
  induction k with
  | zero => simp [noOpenBlocks]
  | succ k ih =>
    have hprev := ih (fun j hj => hcard j (by omega))
    let B := noOpenBlocks blocks k
    let F := blocks k
    have hstable : ∀ e∈F, ∀ A, A∈B ↔ A.erase e∈B := by
      intro e he A
      have hs (j : ℕ) (hj : j<k) : blocks j⊆A ↔ blocks j⊆A.erase e := by
        constructor
        · intro h f hf
          have hfe : f≠e := by
            intro hfe
            subst f
            exact (Finset.disjoint_left.mp (hdisjoint j k hj) hf) he
          exact Finset.mem_erase.mpr ⟨hfe,h hf⟩
        · exact fun h => h.trans (Finset.erase_subset e A)
      exact forall_congr' fun j => forall_congr' fun hj => not_congr (hs j hj)
    have hstep := finite_notOpenBlock_probability_le θ ξ F B hstable
    have hevent : noOpenBlocks blocks (k+1) = B ∩ {A | ¬F⊆A} := by
      ext A
      change (∀ j<k+1,¬blocks j⊆A) ↔ (∀ j<k,¬blocks j⊆A) ∧ ¬blocks k⊆A
      constructor
      · intro h
        exact ⟨fun j hj => h j (by omega),h k (by omega)⟩
      · rintro ⟨h,hk⟩ j hj
        by_cases hlt : j<k
        · exact h j hlt
        · have heq : j=k := by omega
          exact heq ▸ hk
    have hpow : (openEnergy θ)^M ≤ (openEnergy θ)^F.card := by
      have hle := hcard k (by omega)
      have hsplit : M-F.card+F.card=M := Nat.sub_add_cancel hle
      rw [← hsplit,pow_add]
      simpa only [one_mul] using mul_le_mul_of_nonneg_right
        (pow_le_one₀ hbase hbase1 : (openEnergy θ)^(M-F.card)≤1) (pow_nonneg hbase F.card)
    rw [hevent]
    calc
      _ ≤ (1-(openEnergy θ)^F.card)*(measure G θ ξ B).toReal := hstep
      _ ≤ (1-(openEnergy θ)^M)*(measure G θ ξ B).toReal :=
        mul_le_mul_of_nonneg_right (by linarith) ENNReal.toReal_nonneg
      _ ≤ (1-(openEnergy θ)^M)*(1-(openEnergy θ)^M)^k :=
        mul_le_mul_of_nonneg_left hprev hr
      _ = _ := by rw [pow_succ]; ring

end
end PottsContinuity.PlanarMixed.TiltedHalfHeight
