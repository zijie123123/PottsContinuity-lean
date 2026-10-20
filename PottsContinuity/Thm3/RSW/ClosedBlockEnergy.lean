module

public import PottsContinuity.PD.FK.FiniteEnergy
public import PottsContinuity.FKC.FiniteFK.FirstClosedBlockScan
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.MeasureTheory.Measure.Real

@[expose] public section

namespace PottsContinuity.RSW
open PD.FK MeasureTheory
open scoped BigOperators
noncomputable section
variable {V : Type*} [Finite V] {G : SimpleGraph V}
local instance closedBlockEnergyEdgeEq : DecidableEq G.edgeSet := Classical.decEq _
local instance closedBlockEnergyEdgeFintype : Fintype G.edgeSet := Fintype.ofFinite _
attribute [local instance] configurationMeasurableSpace

/-- Uniform closed-edge finite energy written for an arbitrary original edge. -/
theorem measure_closed_edge_inter_lower (θ : Parameters) (ξ : BoundaryCondition V)
    (e : G.edgeSet) (S : Set (Configuration G))
    (hstable : ∀ A, A ∈ S ↔ A.erase e ∈ S) :
    (1-edgeParameter θ)*(measure G θ ξ S).toReal ≤
      (measure G θ ξ (S ∩ {A | e ∉ A})).toReal := by
  obtain ⟨⟨u,v⟩,heval⟩ := Sym2.mk_surjective e.val
  have hadj : G.Adj u v := by
    apply G.mem_edgeSet.mpr
    exact Eq.mp (congrArg (fun z : Sym2 V => z ∈ G.edgeSet) heval.symm) e.property
  have heq : (⟨s(u,v),G.mem_edgeSet.mpr hadj⟩ : G.edgeSet)=e := Subtype.ext heval
  have h := configurationProbability_edge_finite_energy_closed θ ξ S hadj
    (by simpa only [heq] using hstable)
  simpa only [heq] using h.1

/-- Closing an entire finite original-edge block costs at most its uniform
finite-energy factor, even inside an event independent of those edges. -/
theorem measure_closed_block_inter_lower (θ : Parameters) (ξ : BoundaryCondition V)
    (F : Finset G.edgeSet) (S : Set (Configuration G))
    (hstable : ∀ e ∈ F, ∀ A, A ∈ S ↔ A.erase e ∈ S) :
    (1-edgeParameter θ)^F.card*(measure G θ ξ S).toReal ≤
      (measure G θ ξ (S ∩ {A | Disjoint A F})).toReal := by
  induction F using Finset.induction_on with
  | empty => simp
  | @insert e F he ih =>
    have hsF : ∀ f ∈ F, ∀ A, A ∈ S ↔ A.erase f ∈ S :=
      fun f hf => hstable f (Finset.mem_insert_of_mem hf)
    have hIH := ih hsF
    let T := S ∩ {A : Configuration G | Disjoint A F}
    have hsT : ∀ A, A ∈ T ↔ A.erase e ∈ T := by
      intro A
      change (A ∈ S ∧ Disjoint A F) ↔ (A.erase e ∈ S ∧ Disjoint (A.erase e) F)
      have hd : Disjoint A F ↔ Disjoint (A.erase e) F := by
        simp only [Finset.disjoint_left]
        constructor
        · intro h f hf hfF
          exact h (Finset.mem_erase.mp hf).2 hfF
        · intro h f hf hfF
          exact h (Finset.mem_erase.mpr ⟨by intro hfe; subst f; exact he hfF,hf⟩) hfF
      exact and_congr (hstable e (Finset.mem_insert_self _ _) A) hd
    have henergy := measure_closed_edge_inter_lower θ ξ e T hsT
    have hset : T ∩ {A : Configuration G | e ∉ A} = S ∩ {A | Disjoint A (insert e F)} := by
      ext A
      simp only [T,Set.mem_inter_iff,Set.mem_ofPred_eq,Finset.disjoint_insert_right]
      tauto
    rw [hset] at henergy
    calc
      _ = (1-edgeParameter θ)*((1-edgeParameter θ)^F.card*(measure G θ ξ S).toReal) := by
        rw [Finset.card_insert_of_notMem he,pow_succ]
        ring
      _ ≤ (1-edgeParameter θ)*(measure G θ ξ T).toReal :=
        mul_le_mul_of_nonneg_left hIH (by have := edgeParameter_lt_one θ; linarith)
      _ ≤ _ := henergy

/-- Pairwise disjoint closed blocks need no independence assumption: the
probability that every block is hit by an open edge has a product bound. -/
theorem measure_disjoint_closed_blocks_failure_le
    {ι : Type*} [DecidableEq ι] (θ : Parameters) (ξ : BoundaryCondition V)
    (J : Finset ι) (F : ι → Finset G.edgeSet)
    (hdisj : ∀ i ∈ J, ∀ j ∈ J, i ≠ j → Disjoint (F i) (F j)) :
    (measure G θ ξ {A | ∀ i ∈ J, ¬Disjoint A (F i)}).toReal ≤
      ∏ i ∈ J, (1-(1-edgeParameter θ)^(F i).card) := by
  have hp0 : 0 ≤ 1-edgeParameter θ := by have := edgeParameter_lt_one θ; linarith
  have hp1 : 1-edgeParameter θ ≤ 1 := by have := edgeParameter_pos θ; linarith
  induction J using Finset.induction_on with
  | empty => simp
  | @insert i J hi ih =>
    have hrest : ∀ j ∈ J, ∀ k ∈ J, j ≠ k → Disjoint (F j) (F k) := by
      intro j hj k hk hjk
      exact hdisj j (Finset.mem_insert_of_mem hj) k (Finset.mem_insert_of_mem hk) hjk
    have hIH := ih hrest
    let S : Set (Configuration G) := {A | ∀ j ∈ J, ¬Disjoint A (F j)}
    let E : Set (Configuration G) := {A | Disjoint A (F i)}
    have hs : ∀ e ∈ F i, ∀ A, A ∈ S ↔ A.erase e ∈ S := by
      intro e he A
      have heJ : ∀ j ∈ J, e ∉ F j := by
        intro j hj hej
        exact (Finset.disjoint_left.mp
          (hdisj i (Finset.mem_insert_self _ _) j (Finset.mem_insert_of_mem hj)
            (by intro hij; subst j; exact hi hj))) he hej
      have hd : ∀ j ∈ J, Disjoint A (F j) ↔ Disjoint (A.erase e) (F j) := by
        intro j hj
        simp only [Finset.disjoint_left]
        constructor
        · intro h f hf hfF
          exact h (Finset.mem_erase.mp hf).2 hfF
        · intro h f hf hfF
          exact h (Finset.mem_erase.mpr ⟨by intro hfe; subst f; exact heJ j hj hfF,hf⟩) hfF
      change (∀ j ∈ J, ¬Disjoint A (F j)) ↔ ∀ j ∈ J, ¬Disjoint (A.erase e) (F j)
      exact forall_congr' (fun j => forall_congr' (fun hj => not_congr (hd j hj)))
    have henergy := measure_closed_block_inter_lower θ ξ (F i) S hs
    have hpartition := measureReal_inter_add_sdiff (μ := measure G θ ξ) (s := S) (t := E)
      MeasurableSpace.measurableSet_top
    have htarget : {A : Configuration G | ∀ j ∈ insert i J, ¬Disjoint A (F j)} = S \ E := by
      ext A
      simp only [S,E,Set.mem_ofPred_eq,Set.mem_sdiff,Finset.mem_insert,forall_eq_or_imp]
      tauto
    rw [htarget]
    have hlocal : (measure G θ ξ (S \ E)).toReal ≤
        (1-(1-edgeParameter θ)^(F i).card)*(measure G θ ξ S).toReal := by
      change _ ≤ _ at henergy
      change (measure G θ ξ (S ∩ E)).toReal+(measure G θ ξ (S \ E)).toReal =
        (measure G θ ξ S).toReal at hpartition
      linarith only [henergy,hpartition]
    apply hlocal.trans
    rw [Finset.prod_insert hi]
    exact mul_le_mul_of_nonneg_left hIH (by
      have hh : (1-edgeParameter θ)^(F i).card ≤ 1 := pow_le_one₀ hp0 hp1
      linarith)

end
end PottsContinuity.RSW
