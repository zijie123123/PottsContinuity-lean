/- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
accessible (see `related_formalizations` in formalization.yaml): file
`FiniteFK/BoundaryMergeComparison.lean`.
Adaptation: namespace BD12, reuse PD.FK, independent interior p and all real q >= 1.
This proves only the finite boundary-merge comparison used in BD12 Lemma
self-duality; symmetric-domain geometry and dual-law identification are separate.
-/
module

public import PottsContinuity.PD.FK.ComponentMerge
public import PottsContinuity.PD.FK.IncreasingEvents
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.Order.CompletePartialOrder

@[expose] public section

namespace PottsContinuity.BD12

open PD.FK

open MeasureTheory
open scoped BigOperators

noncomputable section

variable {V : Type*} [Finite V] {G : SimpleGraph V}

local instance boundaryMergeEdgeFintype : Fintype G.edgeSet := Fintype.ofFinite _
local instance boundaryMergeEdgeDecidableEq : DecidableEq G.edgeSet := Classical.decEq _

/-- Add the identification of `u` and `v` to an existing boundary. -/
def boundaryMerge (ξ : BoundaryCondition V) (u v : V) : BoundaryCondition V where
  boundary := ξ.boundary ∪ {u, v}
  partition := ξ.partition ⊔ (BoundaryCondition.wired ({u, v} : Set V)).partition
  supported := by
    intro x y h
    let t : Setoid V := {
      r := fun x y => x = y ∨ x ∈ ξ.boundary ∪ {u, v} ∧ y ∈ ξ.boundary ∪ {u, v}
      iseqv := {
        refl := fun x => Or.inl rfl
        symm := by
          intro x y h
          rcases h with h | h
          · exact Or.inl h.symm
          · exact Or.inr ⟨h.2, h.1⟩
        trans := by
          intro x y z hxy hyz
          rcases hxy with hxy | hxy
          · subst y
            exact hyz
          · rcases hyz with hyz | hyz
            · subst z
              exact Or.inr hxy
            · exact Or.inr ⟨hxy.1, hyz.2⟩
      }
    }
    have hle : ξ.partition ⊔ (BoundaryCondition.wired ({u, v} : Set V)).partition ≤ t := by
      apply sup_le
      · intro x y h
        rcases ξ.supported h with heq | ⟨hx, hy⟩
        · exact Or.inl heq
        · exact Or.inr ⟨Or.inl hx, Or.inl hy⟩
      · intro x y h
        rcases (BoundaryCondition.wired_rel ({u, v} : Set V) x y).mp h with h | ⟨hx, hy⟩
        · exact Or.inl h
        · exact Or.inr ⟨Or.inr hx, Or.inr hy⟩
    exact hle h

omit [Finite V] in
@[simp] theorem componentSetoid_merge (ξ : BoundaryCondition V) (A : Configuration G)
    (u v : V) :
    componentSetoid G (boundaryMerge ξ u v) A =
      componentSetoid G ξ A ⊔ (BoundaryCondition.wired ({u, v} : Set V)).partition := by
  simp [componentSetoid, boundaryMerge, sup_assoc]

omit [Finite V] in
private theorem openGraph_singleEdge_reachableSetoid_eq_wired {u v : V} (hne : u ≠ v) :
    (openGraph (⊤ : SimpleGraph V) ({⟨s(u,v), by simp [hne]⟩} : Configuration (⊤ : SimpleGraph V))).reachableSetoid =
      (BoundaryCondition.wired ({u,v} : Set V)).partition := by
  classical
  let G : SimpleGraph V := ⊤
  have huv : G.Adj u v := by simp [G, hne]
  let e : G.edgeSet := ⟨s(u,v), G.mem_edgeSet.mpr huv⟩
  have hadj : (openGraph G {e}).Adj u v := by
    rw [openGraph_adj, openEdges]
    exact ⟨e, by simp, rfl⟩
  have hreachUV : (openGraph G {e}).Reachable u v := actualConnected_of_adj G {e} hadj
  have hreachVU : (openGraph G {e}).Reachable v u := hreachUV.symm
  change (openGraph G ({e} : Configuration G)).reachableSetoid = _
  apply Setoid.ext
  intro x y
  constructor
  · intro h
    apply reachableSetoid_le_of_adj (openGraph G {e})
      (BoundaryCondition.wired ({u,v} : Set V)).partition
    · intro a b hab
      rw [openGraph_adj] at hab
      rcases hab with ⟨e', he', hab⟩
      have he'e : e' = e := by simpa using he'
      subst e'
      rcases Sym2.eq_iff.mp hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact (BoundaryCondition.wired_rel ({u,v} : Set V) u v).2
          (Or.inr ⟨by simp, by simp⟩)
      · exact (BoundaryCondition.wired_rel ({u,v} : Set V) v u).2
          (Or.inr ⟨by simp, by simp⟩)
    · exact h
  · intro h
    rcases (BoundaryCondition.wired_rel ({u,v} : Set V) x y).mp h with hxy | ⟨hx,hy⟩
    · subst y
      change (openGraph G {e}).Reachable x x
      exact .refl _
    · have hx' : x = u ∨ x = v := by simpa using hx
      have hy' : y = u ∨ y = v := by simpa using hy
      rcases hx' with hxU | hxV <;> rcases hy' with hyU | hyV
      · subst x
        subst y
        change (openGraph G {e}).Reachable u u
        exact .refl _
      · subst x
        subst y
        exact hreachUV
      · subst x
        subst y
        exact hreachVU
      · subst x
        subst y
        change (openGraph G {e}).Reachable v v
        exact .refl _

def boundaryConditionOfSetoid (s : Setoid V) : BoundaryCondition V where
  boundary := Set.univ
  partition := s
  supported := by
    intro x y h
    exact Or.inr ⟨Set.mem_univ _, Set.mem_univ _⟩

private theorem componentCount_mergeSetoid_eq_or_succ
    (s : Setoid V) (u v : V) :
    Nat.card (Quotient (s ⊔ (BoundaryCondition.wired ({u,v} : Set V)).partition)) =
      Nat.card (Quotient s) ∨
    Nat.card (Quotient (s ⊔ (BoundaryCondition.wired ({u,v} : Set V)).partition)) + 1 =
      Nat.card (Quotient s) := by
  classical
  by_cases huv_eq : u = v
  · subst v
    left
    have hw : (BoundaryCondition.wired ({u,u} : Set V)).partition = (⊥ : Setoid V) := by
      apply Setoid.ext
      intro x y
      constructor
      · intro h
        rcases (BoundaryCondition.wired_rel ({u,u} : Set V) x y).mp h with h | ⟨hx,hy⟩
        · exact h
        · have hx' : x = u := by simpa using hx
          have hy' : y = u := by simpa using hy
          exact hx'.trans hy'.symm
      · intro h
        subst y
        exact (BoundaryCondition.wired_rel ({u,u} : Set V) x x).2 (Or.inl rfl)
    rw [hw]
    simp
  · let G : SimpleGraph V := ⊤
    have huv : G.Adj u v := by simp [G, huv_eq]
    let ξ := boundaryConditionOfSetoid s
    let e : G.edgeSet := ⟨s(u,v), G.mem_edgeSet.mpr huv⟩
    have hzero : componentSetoid G ξ (∅ : Configuration G) = s := by
      simp [componentSetoid_empty, ξ, boundaryConditionOfSetoid]
    have hone : componentSetoid G ξ ({e} : Configuration G) =
        s ⊔ (BoundaryCondition.wired ({u,v} : Set V)).partition := by
      rw [componentSetoid, openGraph_singleEdge_reachableSetoid_eq_wired huv_eq]
      simp [ξ, boundaryConditionOfSetoid, sup_comm]
    by_cases hrel : s.r u v
    · left
      have hrel' : (componentSetoid G ξ (∅ : Configuration G)).r u v := by
        rw [hzero]
        exact hrel
      have hins := componentSetoid_insert_eq_of_related ξ (∅ : Configuration G) huv hrel'
      have hwire : (BoundaryCondition.wired ({u,v} : Set V)).partition ≤ s := by
        intro x y hxy
        rcases (BoundaryCondition.wired_rel ({u,v} : Set V) x y).mp hxy with hxy | ⟨hx,hy⟩
        · subst y
          exact s.refl _
        · have hx' : x = u ∨ x = v := by simpa using hx
          have hy' : y = u ∨ y = v := by simpa using hy
          rcases hx' with rfl | rfl <;> rcases hy' with rfl | rfl
          · exact s.refl _
          · exact hrel
          · exact s.symm hrel
          · exact s.refl _
      have hset : s ⊔ (BoundaryCondition.wired ({u,v} : Set V)).partition = s :=
        le_antisymm (sup_le le_rfl hwire) le_sup_left
      have hins' : componentSetoid G ξ ({e} : Configuration G) = componentSetoid G ξ ∅ := by
        simpa [e] using hins
      have hcnt : componentCount G ξ ({e} : Configuration G) = componentCount G ξ ∅ := by
        rw [componentCount, componentCount, hins']
      simp [hset]
    · right
      have hrel' : ¬ (componentSetoid G ξ (∅ : Configuration G)).r u v := by
        rw [hzero]
        exact hrel
      have hcnt := componentCount_insert_of_not_related ξ (∅ : Configuration G) huv hrel'
      simpa [componentCount, e, hzero, hone] using hcnt

theorem componentCount_merge_eq_or_succ (ξ : BoundaryCondition V)
    (A : Configuration G) (u v : V) :
    componentCount G (boundaryMerge ξ u v) A = componentCount G ξ A ∨
      componentCount G (boundaryMerge ξ u v) A + 1 = componentCount G ξ A := by
  rw [componentCount, componentCount, componentSetoid_merge]
  exact componentCount_mergeSetoid_eq_or_succ (componentSetoid G ξ A) u v

private theorem weight_boundaryMerge_le (q : Parameters) (ξ : BoundaryCondition V)
    (A : Configuration G) (u v : V) :
    weight G q (boundaryMerge ξ u v) A ≤ weight G q ξ A := by
  have hk := componentCount_merge_eq_or_succ ξ A u v
  have hcount : componentCount G (boundaryMerge ξ u v) A ≤ componentCount G ξ A := by
    rcases hk with h | h
    · omega
    · omega
  unfold weight
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_right₀ q.property hcount)
    (mul_nonneg (pow_nonneg (edgeParameter_pos q).le _)
      (pow_nonneg (one_sub_edgeParameter_pos q).le _))

private theorem weight_boundaryMerge_le_mul (q : Parameters) (ξ : BoundaryCondition V)
    (A : Configuration G) (u v : V) :
    weight G q ξ A ≤ q.val * weight G q (boundaryMerge ξ u v) A := by
  have hk := componentCount_merge_eq_or_succ ξ A u v
  have hpow : q.val ^ componentCount G ξ A ≤
      q.val * q.val ^ componentCount G (boundaryMerge ξ u v) A := by
    rcases hk with h | h
    · calc
        q.val ^ componentCount G ξ A =
            q.val ^ componentCount G (boundaryMerge ξ u v) A := by rw [h]
        _ = 1 * q.val ^ componentCount G (boundaryMerge ξ u v) A := by ring
        _ ≤ q.val * q.val ^ componentCount G (boundaryMerge ξ u v) A :=
          mul_le_mul_of_nonneg_right q.property
            (pow_nonneg (clusterWeight_nonneg q) _)
    · have hn : componentCount G ξ A = componentCount G (boundaryMerge ξ u v) A + 1 := by omega
      calc
        q.val ^ componentCount G ξ A =
            q.val ^ (componentCount G (boundaryMerge ξ u v) A + 1) := by rw [hn]
        _ = q.val ^ componentCount G (boundaryMerge ξ u v) A * q.val := by rw [pow_succ]
        _ = q.val * q.val ^ componentCount G (boundaryMerge ξ u v) A := by ring
        _ ≤ q.val * q.val ^ componentCount G (boundaryMerge ξ u v) A := le_rfl
  unfold weight
  have hfac : 0 ≤ edgeParameter q ^ A.card *
      (1 - edgeParameter q) ^ (Nat.card G.edgeSet - A.card) :=
    mul_nonneg (pow_nonneg (edgeParameter_pos q).le _)
      (pow_nonneg (one_sub_edgeParameter_pos q).le _)
  calc
    (edgeParameter q ^ A.card * (1 - edgeParameter q) ^ (Nat.card G.edgeSet - A.card)) *
        q.val ^ componentCount G ξ A ≤
      (edgeParameter q ^ A.card * (1 - edgeParameter q) ^ (Nat.card G.edgeSet - A.card)) *
        (q.val * q.val ^ componentCount G (boundaryMerge ξ u v) A) := mul_le_mul_of_nonneg_left hpow hfac
    _ = q.val * ((edgeParameter q ^ A.card *
        (1 - edgeParameter q) ^ (Nat.card G.edgeSet - A.card)) *
          q.val ^ componentCount G (boundaryMerge ξ u v) A) := by ring

private theorem partitionFunction_boundaryMerge_bounds (q : Parameters)
    (ξ : BoundaryCondition V) (u v : V) :
    partitionFunction G q (boundaryMerge ξ u v) ≤ partitionFunction G q ξ ∧
      partitionFunction G q ξ ≤ q.val * partitionFunction G q (boundaryMerge ξ u v) := by
  constructor
  · unfold partitionFunction FiniteProbability.partition
    exact Finset.sum_le_sum (fun A _ => weight_boundaryMerge_le q ξ A u v)
  · unfold partitionFunction FiniteProbability.partition
    calc
      ∑ A, weight G q ξ A ≤ ∑ A, q.val * weight G q (boundaryMerge ξ u v) A :=
        Finset.sum_le_sum (fun A _ => weight_boundaryMerge_le_mul q ξ A u v)
      _ = q.val * ∑ A, weight G q (boundaryMerge ξ u v) A := by rw [Finset.mul_sum]

private theorem configurationProbability_boundaryMerge_le (q : Parameters)
    (ξ : BoundaryCondition V) (A : Configuration G) (u v : V) :
    configurationProbability G q (boundaryMerge ξ u v) A ≤
      q.val * configurationProbability G q ξ A := by
  have hW := weight_boundaryMerge_le q ξ A u v
  have hZ := partitionFunction_boundaryMerge_bounds (G := G) q ξ u v
  have hcross : weight G q (boundaryMerge ξ u v) A * partitionFunction G q ξ ≤
      (q.val * weight G q ξ A) * partitionFunction G q (boundaryMerge ξ u v) := by
    calc
      weight G q (boundaryMerge ξ u v) A * partitionFunction G q ξ ≤
          weight G q ξ A * partitionFunction G q ξ :=
        mul_le_mul_of_nonneg_right hW (partitionFunction_pos G q ξ).le
      _ ≤ weight G q ξ A * (q.val * partitionFunction G q (boundaryMerge ξ u v)) :=
        mul_le_mul_of_nonneg_left hZ.2 (weight_pos G q ξ A).le
      _ = (q.val * weight G q ξ A) * partitionFunction G q (boundaryMerge ξ u v) := by ring
  rw [configurationProbability, configurationProbability, ← mul_div_assoc]
  exact (div_le_div_iff₀ (partitionFunction_pos G q (boundaryMerge ξ u v))
      (partitionFunction_pos G q ξ)).2 hcross

omit [Finite V] in
private theorem eventIndicator_nonneg (S : Set (Configuration G)) (A : Configuration G) :
    0 ≤ S.indicator (fun _ => (1 : ℝ)) A := by
  by_cases h : A ∈ S <;> simp [Set.indicator, h]

theorem measure_boundaryMerge_le_mul (q : Parameters) (ξ : BoundaryCondition V)
    (u v : V) (S : Set (Configuration G)) :
    (measure G q (boundaryMerge ξ u v) S).toReal ≤ q.val * (measure G q ξ S).toReal := by
  rw [measure_toReal_eq_indicator_sum, measure_toReal_eq_indicator_sum]
  calc
    ∑ A, configurationProbability G q (boundaryMerge ξ u v) A *
        S.indicator (fun _ => (1 : ℝ)) A ≤
      ∑ A, (q.val * configurationProbability G q ξ A) *
        S.indicator (fun _ => (1 : ℝ)) A :=
      Finset.sum_le_sum (fun A _ => mul_le_mul_of_nonneg_right
        (configurationProbability_boundaryMerge_le q ξ A u v) (eventIndicator_nonneg S A))
    _ = q.val * ∑ A, configurationProbability G q ξ A *
        S.indicator (fun _ => (1 : ℝ)) A := by
      simp_rw [mul_assoc]
      rw [← Finset.mul_sum]

end

end PottsContinuity.BD12
