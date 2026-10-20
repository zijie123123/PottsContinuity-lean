module

public import PottsContinuity.BD12.DRTRusso
public import PottsContinuity.PD.FK.ComponentSupermodular
public import Mathlib.Combinatorics.SetFamily.FourFunctions
public import Mathlib.Tactic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Combinatorics.SimpleGraph.Basic

/-! FKG and the corrected Russo lower bound for the finite weighted DRT law. -/

@[expose] public section

namespace PottsContinuity.BD12

open PD.FK
open scoped BigOperators
noncomputable section

variable {V : Type*} [Finite V] (G : SimpleGraph V)
local instance drtAssociationEdgeFintype : Fintype G.edgeSet := Fintype.ofFinite _
local instance drtAssociationEdgeDecidableEq : DecidableEq G.edgeSet := Classical.decEq _

theorem drtWeight_lattice_condition (q : Set.Ioi (0 : ℝ)) (hq : 1 ≤ (q : ℝ))
    (ξ : BoundaryCondition V) (J : G.edgeSet → Set.Ioi (0 : ℝ))
    (β : Set.Ioi (0 : ℝ)) (A B : Configuration G) :
    drtWeight G q ξ J β A * drtWeight G q ξ J β B ≤
      drtWeight G q ξ J β (A ∩ B) * drtWeight G q ξ J β (A ∪ B) := by
  classical
  let a := fun e : G.edgeSet => Real.exp ((β : ℝ) * (J e : ℝ)) - 1
  have ha (e : G.edgeSet) : 0 ≤ a e :=
    (sub_pos.mpr (Real.one_lt_exp_iff.mpr (mul_pos β.property (J e).property))).le
  have hfactor (C D : Configuration G) :
      drtWeight G q ξ J β C * drtWeight G q ξ J β D =
        (q : ℝ) ^ (componentCount G ξ C + componentCount G ξ D) *
          ((∏ e ∈ C, a e) * ∏ e ∈ D, a e) := by
    simp only [drtWeight, pow_add, a]
    ring
  have hedge : (∏ e ∈ A, a e) * ∏ e ∈ B, a e =
      (∏ e ∈ A ∩ B, a e) * ∏ e ∈ A ∪ B, a e := by
    rw [← Finset.prod_union_inter]
    exact mul_comm _ _
  rw [hfactor A B, hfactor (A ∩ B) (A ∪ B), hedge]
  exact mul_le_mul_of_nonneg_right
    (pow_le_pow_right₀ hq (componentCount_supermodular ξ A B))
    (mul_nonneg (Finset.prod_nonneg (fun e _ => ha e))
      (Finset.prod_nonneg (fun e _ => ha e)))

/-- Increasing nonnegative observables are positively associated under the
actual weighted FK law, for every q>=1 and every boundary partition. -/
theorem drtCovariance_nonneg (q : Set.Ioi (0 : ℝ)) (hq : 1 ≤ (q : ℝ))
    (ξ : BoundaryCondition V) (J : G.edgeSet → Set.Ioi (0 : ℝ))
    (β : Set.Ioi (0 : ℝ)) (f g : Configuration G → ℝ)
    (hf0 : ∀ A, 0 ≤ f A) (hg0 : ∀ A, 0 ≤ g A)
    (hf : Monotone f) (hg : Monotone g) :
    0 ≤ drtCovariance G q ξ J β f g := by
  have h := _root_.fkg (μ := drtWeight G q ξ J β) (f := f) (g := g)
    (fun A => (drtWeight_pos G q ξ J β A).le) hf0 hg0 hf hg
    (drtWeight_lattice_condition G q hq ξ J β)
  have hz := drtPartition_pos G q ξ J β
  apply sub_nonneg.mpr
  unfold drtMean
  calc
    _ = ((∑ A, drtWeight G q ξ J β A * f A) *
      (∑ A, drtWeight G q ξ J β A * g A)) /
        ((∑ A, drtWeight G q ξ J β A) * ∑ A, drtWeight G q ξ J β A) :=
      div_mul_div_comm _ _ _ _
    _ ≤ ((∑ A, drtWeight G q ξ J β A) *
        ∑ A, drtWeight G q ξ J β A * (f A * g A)) /
        ((∑ A, drtWeight G q ξ J β A) * ∑ A, drtWeight G q ξ J β A) :=
      div_le_div_of_nonneg_right h (mul_pos hz hz).le
    _ = _ := by field_simp

omit [Finite V] in
theorem drtEdgeIndicator_nonneg (e : G.edgeSet) (A : Configuration G) :
    0 ≤ drtEdgeIndicator G e A := by
  classical
  unfold drtEdgeIndicator
  split_ifs <;> norm_num

omit [Finite V] in
theorem drtEdgeIndicator_monotone (e : G.edgeSet) :
    Monotone (drtEdgeIndicator G e) := by
  classical
  intro A B hAB
  by_cases he : e ∈ A
  · have heB := hAB he
    simp only [drtEdgeIndicator, ite_eq_left he, ite_eq_left heB, le_refl]
  · simp only [drtEdgeIndicator, ite_eq_right he]
    exact drtEdgeIndicator_nonneg G e B

/-- The lower bound needed in DRT's sharpness proof, with no assumed
covariance estimate: FKG supplies it for every increasing nonnegative f. -/
theorem drt_russo_lower_bound (q : Set.Ioi (0 : ℝ)) (hq : 1 ≤ (q : ℝ))
    (ξ : BoundaryCondition V) (J : G.edgeSet → Set.Ioi (0 : ℝ))
    (β : Set.Ioi (0 : ℝ)) (f : Configuration G → ℝ)
    (hf0 : ∀ A, 0 ≤ f A) (hf : Monotone f) :
    (∑ e : G.edgeSet, ((J e : ℝ) / (Real.exp ((β : ℝ) * (J e : ℝ)) - 1)) *
      drtCovariance G q ξ J β f (drtEdgeIndicator G e)) ≤
    deriv (fun t : ℝ => (∑ A, drtWeight G q ξ J t A * f A) /
      ∑ A, drtWeight G q ξ J t A) β := by
  apply drt_russo_lower_bound_of_covariance_nonneg G q ξ J β f
  intro e
  exact drtCovariance_nonneg G q hq ξ J β f (drtEdgeIndicator G e)
    hf0 (drtEdgeIndicator_nonneg G e) hf (drtEdgeIndicator_monotone G e)

end
end PottsContinuity.BD12
