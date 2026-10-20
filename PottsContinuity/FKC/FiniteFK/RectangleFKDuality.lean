-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/RectangleFKDuality.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.RectangleEuler
public import PottsContinuity.FKC.FiniteFK.RectangleEdgeCardinality
public import PottsContinuity.FKC.FiniteFK.CriticalWeightNormalization

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

open PottsContinuity.FKC PottsContinuity.FKC.Medial

noncomputable section

local instance rectanglePrimalConfigurationEdgeFintype (a : LatticeVertex) (w h : ℕ) :
    Fintype (rectangleGraph a w h).edgeSet := Fintype.ofFinite _

local instance rectangleDualConfigurationEdgeFintype (a : LatticeVertex) (w h : ℕ) :
    Fintype (rectangleDualGraph a w h).edgeSet := Fintype.ofFinite _

 def rectangleCarrierConfigurationEquiv (a : LatticeVertex) (w h : ℕ) :
    Configuration (rectangleGraph a w h) ≃
      Finset (rectanglePrimalEdgeCarrier a w h) where
  toFun A := by
    change Finset (rectangleGraph a w h).edgeSet
    exact A
  invFun A := by
    change Finset (rectangleGraph a w h).edgeSet
    exact A
  left_inv A := rfl
  right_inv A := rfl

/-- The actual finite configuration bijection: primal open edges map to the
complementary open dual edges, with wired dual boundary condition. -/
noncomputable def rectanglePrimalDualConfigurationEquiv (a : LatticeVertex)
    (w h : ℕ) : Configuration (rectangleGraph a w h) ≃
      Configuration (rectangleDualGraph a w h) :=
  (rectangleCarrierConfigurationEquiv a w h).trans
    (rectangleDualConfigurationEquiv a w h)

@[simp] theorem rectanglePrimalDualConfigurationEquiv_apply (a : LatticeVertex)
    (w h : ℕ) (A : Configuration (rectangleGraph a w h)) :
    rectanglePrimalDualConfigurationEquiv a w h A =
      rectangleDualConfiguration a w h
        (rectangleCarrierConfigurationEquiv a w h A) := by
  simp [rectanglePrimalDualConfigurationEquiv]

private theorem rectangleFK_exponent_identity (a : LatticeVertex) (w h : ℕ)
    (A : Configuration (rectangleGraph a w h)) :
    A.card + 2 * componentCount (rectangleGraph a w h)
        (BoundaryCondition.free (∅ : Set (RectangleVertex a w h))) A =
      (w + h) + (rectanglePrimalDualConfigurationEquiv a w h A).card +
        2 * componentCount (rectangleDualGraph a w h)
          (rectangleDualBoundaryCondition a w h)
          (rectanglePrimalDualConfigurationEquiv a w h A) := by
  classical
  let B := rectanglePrimalDualConfigurationEquiv a w h A
  have hEuler := rectangleEuler_additive_card_config a w h A
  have hcard : A.card + B.card = Nat.card (rectangleGraph a w h).edgeSet := by
    have hc := rectangleDualConfiguration_card_add_eq_primal_edgeSet a w h
      (rectangleCarrierConfigurationEquiv a w h A)
    have hcarrier : (rectangleCarrierConfigurationEquiv a w h A).card = A.card := rfl
    rw [← hcarrier]
    simpa [B, rectanglePrimalDualConfigurationEquiv] using hc
  have hN := rectangleGraph_edgeSet_card_expanded a w h
  have hshape : 2 * ((w + 1) * (h + 1)) =
      (2 * w * h + w + h) + w + h + 2 := by ring
  change componentCount (rectangleDualGraph a w h)
      (rectangleDualBoundaryCondition a w h)
        (rectangleDualConfiguration a w h (rectangleCarrierConfigurationEquiv a w h A)) +
        (w + 1) * (h + 1) =
    A.card + componentCount (rectangleGraph a w h)
      (BoundaryCondition.free (∅ : Set (RectangleVertex a w h))) A + 1 at hEuler
  rw [← rectanglePrimalDualConfigurationEquiv_apply] at hEuler
  have hEulerZ :
      (componentCount (rectangleDualGraph a w h)
          (rectangleDualBoundaryCondition a w h) B : ℤ) +
        (((w + 1) * (h + 1) : ℕ) : ℤ) =
      (A.card : ℤ) +
        (componentCount (rectangleGraph a w h)
          (BoundaryCondition.free (∅ : Set (RectangleVertex a w h))) A : ℤ) + 1 := by
    exact_mod_cast hEuler
  have hcardN : A.card + B.card = 2 * w * h + w + h := by
    rw [← hN]
    exact hcard
  have hcardZ : (A.card : ℤ) + (B.card : ℤ) =
      ((2 * w * h + w + h : ℕ) : ℤ) := by exact_mod_cast hcardN
  have hshapeZ : (2 : ℤ) * (((w + 1) * (h + 1) : ℕ) : ℤ) =
      (((2 * w * h + w + h) + w + h + 2 : ℕ) : ℤ) := by
    exact_mod_cast hshape
  apply Nat.cast_injective (R := ℤ)
  push_cast
  nlinarith [hEulerZ, hcardZ, hshapeZ]

/-- At fixed cluster weight, the primal free-boundary FK weight differs from
the complementary wired-dual weight by the exact factor `(sqrt q)^(w+h)`. -/
theorem rectangleFK_weight_eq_loopWeight_factor_mul_dualWeight
    (q : ClusterWeight) (a : LatticeVertex) (w h : ℕ)
    (A : Configuration (rectangleGraph a w h)) :
    weight (rectangleGraph a w h) q
        (BoundaryCondition.free (∅ : Set (RectangleVertex a w h))) A =
      loopWeight q ^ (w + h) *
        weight (rectangleDualGraph a w h) q
          (rectangleDualBoundaryCondition a w h)
          (rectanglePrimalDualConfigurationEquiv a w h A) := by
  rw [weight_eq_loopWeight_formula (rectangleGraph a w h) q
      (BoundaryCondition.free (∅ : Set (RectangleVertex a w h))) A,
    weight_eq_loopWeight_formula (rectangleDualGraph a w h) q
      (rectangleDualBoundaryCondition a w h)
      (rectanglePrimalDualConfigurationEquiv a w h A)]
  have h_edges : Nat.card (rectangleDualGraph a w h).edgeSet =
      Nat.card (rectangleGraph a w h).edgeSet :=
    rectangleDualGraph_edgeSet_card_eq_primal_edgeSet a w h
  have h_exp := rectangleFK_exponent_identity a w h A
  rw [h_edges, h_exp]
  rw [pow_add]
  ring

/-- Exact finite-volume FK duality: the genuine free-primal law pushes forward
under complementary edge transport to the genuine wired-dual law. -/
theorem rectangleFKLaw_map_primalDualConfigurationEquiv
    (q : ClusterWeight) (a : LatticeVertex) (w h : ℕ) :
    (law (rectangleGraph a w h) q
      (BoundaryCondition.free (∅ : Set (RectangleVertex a w h)))).map
        (rectanglePrimalDualConfigurationEquiv a w h) =
      law (rectangleDualGraph a w h) q (rectangleDualBoundaryCondition a w h) := by
  classical
  exact FiniteProbability.pmf_map_equiv_of_common_factor
    (rectanglePrimalDualConfigurationEquiv a w h) (loopWeight q ^ (w + h))
    (weight (rectangleGraph a w h) q
      (BoundaryCondition.free (∅ : Set (RectangleVertex a w h))))
    (weight (rectangleDualGraph a w h) q (rectangleDualBoundaryCondition a w h))
    (pow_pos (loopWeight_pos q) _)
    (weight_pos (rectangleGraph a w h) q
      (BoundaryCondition.free (∅ : Set (RectangleVertex a w h))))
    (weight_pos (rectangleDualGraph a w h) q (rectangleDualBoundaryCondition a w h))
    (rectangleFK_weight_eq_loopWeight_factor_mul_dualWeight q a w h)

end

end PottsContinuity.FKC.FiniteFK
