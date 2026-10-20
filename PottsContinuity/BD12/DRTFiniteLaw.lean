module

public import PottsContinuity.BD12.FiniteWeightDerivative
public import PottsContinuity.PD.FK.Model
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Finite weighted FK law in the DRT inverse-temperature parameter

The unnormalized expression is analytic for every real argument. Normalized
laws and observables take a strictly positive temperature parameter, where
all weights and the partition function are positive. This is exactly the
finite-volume random-cluster measure of Section 1.2 of arXiv:1705.03104v2, with
its actual component count.
-/

@[expose] public section

namespace PottsContinuity.BD12

open PD.FK
open scoped BigOperators
noncomputable section

variable {V : Type*} [Finite V] (G : SimpleGraph V)

local instance drtFiniteLawEdgeFintype : Fintype G.edgeSet := Fintype.ofFinite _

/-- The analytic DRT unnormalized weight, with positive cluster weight and
positive bond couplings. Positivity requires the physical argument beta>0. -/
def drtWeight (q : Set.Ioi (0 : ℝ)) (ξ : BoundaryCondition V)
    (J : G.edgeSet → Set.Ioi (0 : ℝ)) (β : ℝ) (A : Configuration G) : ℝ :=
  (q : ℝ) ^ componentCount G ξ A * ∏ e ∈ A, (Real.exp (β * (J e : ℝ)) - 1)

theorem drtWeight_pos (q : Set.Ioi (0 : ℝ)) (ξ : BoundaryCondition V)
    (J : G.edgeSet → Set.Ioi (0 : ℝ)) (β : Set.Ioi (0 : ℝ)) (A : Configuration G) :
    0 < drtWeight G q ξ J β A := by
  apply mul_pos (pow_pos q.property _)
  apply Finset.prod_pos
  intro e _
  exact sub_pos.mpr (Real.one_lt_exp_iff.mpr (mul_pos β.property (J e).property))

theorem drtPartition_pos (q : Set.Ioi (0 : ℝ)) (ξ : BoundaryCondition V)
    (J : G.edgeSet → Set.Ioi (0 : ℝ)) (β : Set.Ioi (0 : ℝ)) :
    0 < ∑ A : Configuration G, drtWeight G q ξ J β A :=
  Finset.sum_pos (fun A _ => drtWeight_pos G q ξ J β A) Finset.univ_nonempty

/-- The genuine normalized finite DRT law, on every positive beta. -/
def drtLaw (q : Set.Ioi (0 : ℝ)) (ξ : BoundaryCondition V)
    (J : G.edgeSet → Set.Ioi (0 : ℝ)) (β : Set.Ioi (0 : ℝ)) :
    PMF (Configuration G) :=
  FiniteProbability.pmf (drtWeight G q ξ J β) (drtWeight_pos G q ξ J β)

/-- Mean under the finite DRT law; its denominator is strictly positive on
the entire declared parameter carrier. -/
def drtMean (q : Set.Ioi (0 : ℝ)) (ξ : BoundaryCondition V)
    (J : G.edgeSet → Set.Ioi (0 : ℝ)) (β : Set.Ioi (0 : ℝ))
    (f : Configuration G → ℝ) : ℝ :=
  (∑ A, drtWeight G q ξ J β A * f A) / ∑ A, drtWeight G q ξ J β A

theorem drtLaw_apply (q : Set.Ioi (0 : ℝ)) (ξ : BoundaryCondition V)
    (J : G.edgeSet → Set.Ioi (0 : ℝ)) (β : Set.Ioi (0 : ℝ)) (A : Configuration G) :
    drtLaw G q ξ J β A =
      ENNReal.ofReal (drtWeight G q ξ J β A / ∑ B, drtWeight G q ξ J β B) := rfl

/-- The normalized weighted mean is exactly the expectation of the genuine PMF. -/
theorem drtMean_eq_sum_law (q : Set.Ioi (0 : ℝ)) (ξ : BoundaryCondition V)
    (J : G.edgeSet → Set.Ioi (0 : ℝ)) (β : Set.Ioi (0 : ℝ))
    (f : Configuration G → ℝ) :
    drtMean G q ξ J β f = ∑ A, (drtLaw G q ξ J β A).toReal * f A := by
  simp only [drtLaw_apply, ENNReal.toReal_ofReal
    (div_pos (drtWeight_pos G q ξ J β _) (drtPartition_pos G q ξ J β)).le]
  simp only [drtMean, div_mul_eq_mul_div, Finset.sum_div]

/-- Covariance of two finite observables under the same actual law. -/
def drtCovariance (q : Set.Ioi (0 : ℝ)) (ξ : BoundaryCondition V)
    (J : G.edgeSet → Set.Ioi (0 : ℝ)) (β : Set.Ioi (0 : ℝ))
    (f g : Configuration G → ℝ) : ℝ :=
  drtMean G q ξ J β (fun A => f A * g A) -
    drtMean G q ξ J β f * drtMean G q ξ J β g

/-- Correct logarithmic derivative of a single DRT open-bond factor. -/
def drtEdgeScore (J : G.edgeSet → Set.Ioi (0 : ℝ)) (β : Set.Ioi (0 : ℝ))
    (e : G.edgeSet) : ℝ :=
  (J e : ℝ) * Real.exp ((β : ℝ) * (J e : ℝ)) /
    (Real.exp ((β : ℝ) * (J e : ℝ)) - 1)

omit [Finite V] in
theorem drtEdgeScore_pos (J : G.edgeSet → Set.Ioi (0 : ℝ))
    (β : Set.Ioi (0 : ℝ)) (e : G.edgeSet) : 0 < drtEdgeScore G J β e :=
  div_pos (mul_pos (J e).property (Real.exp_pos _))
    (sub_pos.mpr (Real.one_lt_exp_iff.mpr (mul_pos β.property (J e).property)))

theorem drtWeight_hasDerivAt (q : Set.Ioi (0 : ℝ)) (ξ : BoundaryCondition V)
    (J : G.edgeSet → Set.Ioi (0 : ℝ)) (β : Set.Ioi (0 : ℝ)) (A : Configuration G) :
    HasDerivAt (fun t : ℝ => drtWeight G q ξ J t A)
      (drtWeight G q ξ J β A * ∑ e ∈ A, drtEdgeScore G J β e) β := by
  have he (e : G.edgeSet) :
      HasDerivAt (fun t : ℝ => Real.exp (t * (J e : ℝ)) - 1)
        ((Real.exp ((β : ℝ) * (J e : ℝ)) - 1) * drtEdgeScore G J β e) β := by
    have hbase := (((hasDerivAt_id (β : ℝ)).mul_const (J e : ℝ)).exp).sub_const 1
    have hne : Real.exp ((β : ℝ) * (J e : ℝ)) - 1 ≠ 0 :=
      (sub_pos.mpr (Real.one_lt_exp_iff.mpr (mul_pos β.property (J e).property))).ne'
    convert hbase using 1 <;> simp only [drtEdgeScore, id_eq, one_mul];
      field_simp [hne]
  have hprod := hasDerivAt_finset_product_score A
    (fun e t => Real.exp (t * (J e : ℝ)) - 1) (drtEdgeScore G J β) β
    (fun e _ => he e)
  convert hprod.const_mul ((q : ℝ) ^ componentCount G ξ A) using 1 <;>
    simp only [drtWeight, mul_assoc]

/-- Correct finite-volume derivative in score-covariance form. The temperature
function is the explicit normalized analytic expression near the positive beta. -/
theorem drtMean_hasDerivAt_score_corrected (q : Set.Ioi (0 : ℝ))
    (ξ : BoundaryCondition V) (J : G.edgeSet → Set.Ioi (0 : ℝ))
    (β : Set.Ioi (0 : ℝ)) (f : Configuration G → ℝ) :
    HasDerivAt
      (fun t : ℝ => (∑ A, drtWeight G q ξ J t A * f A) /
        ∑ A, drtWeight G q ξ J t A)
      (drtCovariance G q ξ J β f (fun A => ∑ e ∈ A, drtEdgeScore G J β e)) β := by
  exact hasDerivAt_normalized_weighted_sum (drtWeight G q ξ J)
    (fun A => ∑ e ∈ A, drtEdgeScore G J β e) f β
    (drtWeight_hasDerivAt G q ξ J β) (drtPartition_pos G q ξ J β).ne'

end
end PottsContinuity.BD12
