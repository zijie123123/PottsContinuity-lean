module

public import PottsContinuity.DualityExt.RectangleResults
public import PottsContinuity.PD.FK.ProbabilityProduct
public import PottsContinuity.PD.Duality.RectangleEuler
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Probability.ProbabilityMassFunction.Basic

/-!
# Rectangular FK duality for all positive cluster weights

The reusable PD random-cluster parameter carrier assumes `q ≥ 1`. The source
duality identity itself only needs `q > 0`; this module develops that parameter
range for finite lattice rectangles, using the proved rectangle Euler identity.
-/

@[expose] public section

namespace PottsContinuity.DualityExt

open PottsContinuity.PD.FK
open PottsContinuity.PD.FK.FiniteProbability
open PottsContinuity.PD.Duality
open PottsContinuity.PD.FK.Medial

noncomputable section

local instance rectanglePrimalEdgeFintype (a : LatticeVertex) (w h : ℕ) :
    Fintype (rectangleGraph a w h).edgeSet := Fintype.ofFinite _

local instance rectangleDualEdgeFintype (a : LatticeVertex) (w h : ℕ) :
    Fintype (rectangleDualGraph a w h).edgeSet := Fintype.ofFinite _

local instance rectanglePrimalConfigFintype (a : LatticeVertex) (w h : ℕ) :
    Fintype (Configuration (rectangleGraph a w h)) := Fintype.ofFinite _

local instance rectangleDualConfigFintype (a : LatticeVertex) (w h : ℕ) :
    Fintype (Configuration (rectangleDualGraph a w h)) := Fintype.ofFinite _

 def rectangleCarrierConfigurationEquiv (a : LatticeVertex) (w h : ℕ) :
    Configuration (rectangleGraph a w h) ≃
      Finset (rectanglePrimalEdgeCarrier a w h) where
  toFun A := by
    change Finset (rectangleGraph a w h).edgeSet
    exact A
  invFun A := by
    change Finset (rectangleGraph a w h).edgeSet
    exact A
  left_inv _ := rfl
  right_inv _ := rfl

/-- The actual complementary dual configuration bijection, with the primal
edge carrier coercion made explicit for the source-facing FK law. -/
noncomputable def positiveRectangleDualConfigurationEquiv
    (a : LatticeVertex) (w h : ℕ) :
    Configuration (rectangleGraph a w h) ≃
      Configuration (rectangleDualGraph a w h) :=
  (rectangleCarrierConfigurationEquiv a w h).trans
    (rectangleDualConfigurationEquiv a w h)

/-- The finite FK weight for any positive `q` and interior edge parameter. -/
def positiveFKWeight {V : Type*} [Finite V] (G : SimpleGraph V)
    (q p : ℝ) (ξ : BoundaryCondition V) (A : Configuration G) : ℝ :=
  p ^ A.card * (1 - p) ^ (Nat.card G.edgeSet - A.card) *
    q ^ componentCount G ξ A

 theorem positiveFKWeight_pos {V : Type*} [Finite V] (G : SimpleGraph V)
    {q p : ℝ} (hq : 0 < q) (hp : 0 < p) (hp1 : p < 1)
    (ξ : BoundaryCondition V) (A : Configuration G) :
    0 < positiveFKWeight G q p ξ A := by
  unfold positiveFKWeight
  exact mul_pos
    (mul_pos (pow_pos hp _) (pow_pos (sub_pos.mpr hp1) _))
    (pow_pos hq _)

/-- The finite FK law for any positive `q` and interior edge parameter. -/
def positiveFKLaw {V : Type*} [Finite V] (G : SimpleGraph V)
    (q p : ℝ) (hq : 0 < q) (hp : 0 < p) (hp1 : p < 1)
    (ξ : BoundaryCondition V) : PMF (Configuration G) := by
  letI : Fintype G.edgeSet := Fintype.ofFinite _
  letI : Fintype (Configuration G) := Fintype.ofFinite _
  exact FiniteProbability.pmf (positiveFKWeight G q p ξ)
    (positiveFKWeight_pos G hq hp hp1 ξ)

def positiveRectangleDualityFactor (q p : ℝ) (a : LatticeVertex)
    (w h : ℕ) : ℝ :=
  (p + q * (1 - p)) ^ Nat.card (rectangleGraph a w h).edgeSet *
    q ^ ((w + 1) * (h + 1)) /
      q ^ (Nat.card (rectangleGraph a w h).edgeSet + 1)

theorem positiveRectangleDualityFactor_pos
    {q p : ℝ} (hq : 0 < q) (hp : 0 < p) (hp1 : p < 1)
    (a : LatticeVertex) (w h : ℕ) :
    0 < positiveRectangleDualityFactor q p a w h := by
  unfold positiveRectangleDualityFactor
  exact div_pos
    (mul_pos
      (pow_pos (dualParameter_den_pos hq hp hp1) _)
      (pow_pos hq _))
    (pow_pos hq _)

private theorem positive_dual_weight_algebra {q p : ℝ}
    (hq : 0 < q) (hp : 0 < p) (hp1 : p < 1)
    (a b k l V N : ℕ) (hcard : a + b = N)
    (heuler : l + V = a + k + 1) :
    p ^ a * (1 - p) ^ b * q ^ k =
      ((p + q * (1 - p)) ^ N * q ^ V / q ^ (N + 1)) *
        (dualParameter q p ^ b * (1 - dualParameter q p) ^ a * q ^ l) := by
  let D := p + q * (1 - p)
  have hD : D ≠ 0 := (dualParameter_den_pos hq hp hp1).ne'
  have hqne : q ≠ 0 := hq.ne'
  have hqexp : V + b + l = N + 1 + k := by omega
  rw [one_sub_dualParameter hq hp hp1, dualParameter]
  change _ = (D ^ N * q ^ V / q ^ (N + 1)) *
    ((q * (1 - p) / D) ^ b * (p / D) ^ a * q ^ l)
  calc
    _ = (p ^ a * (1 - p) ^ b) *
        (q ^ (V + b + l) / q ^ (N + 1)) * (D ^ N / D ^ (a + b)) := by
      rw [hqexp, hcard, pow_add]
      field_simp
    _ = (D ^ N * q ^ V / q ^ (N + 1)) *
        ((q * (1 - p) / D) ^ b * (p / D) ^ a * q ^ l) := by
      simp only [div_pow, mul_pow, pow_add]
      field_simp

/-- The square-root self-dual edge parameter, defined for every `q > 0`. -/
noncomputable def squareRootDualityParameter (q : ℝ) : ℝ :=
  Real.sqrt q / (1 + Real.sqrt q)

theorem squareRootDualityParameter_mem_Ioo {q : ℝ} (hq : 0 < q) :
    squareRootDualityParameter q ∈ Set.Ioo (0 : ℝ) 1 := by
  have hs : 0 < Real.sqrt q := Real.sqrt_pos.2 hq
  change 0 < Real.sqrt q / (1 + Real.sqrt q) ∧
    Real.sqrt q / (1 + Real.sqrt q) < 1
  constructor
  · exact div_pos hs (by positivity)
  · exact (div_lt_one (by positivity)).2 (by linarith)

/-- The edge parameter `√q / (1 + √q)` is fixed by planar FK duality for
every positive cluster weight. -/
theorem dualParameter_squareRoot_fixed {q : ℝ} (hq : 0 < q) :
    dualParameter q (squareRootDualityParameter q) =
      squareRootDualityParameter q := by
  have hs : 0 < Real.sqrt q := Real.sqrt_pos.2 hq
  have hs2 : Real.sqrt q ^ 2 = q := Real.sq_sqrt hq.le
  have hden : 1 + Real.sqrt q ≠ 0 := by positivity
  have hsub : 1 - Real.sqrt q / (1 + Real.sqrt q) =
      1 / (1 + Real.sqrt q) := by
    field_simp
    ring
  have hD : Real.sqrt q / (1 + Real.sqrt q) +
      q * (1 / (1 + Real.sqrt q)) ≠ 0 := by positivity
  change dualParameter q (Real.sqrt q / (1 + Real.sqrt q)) =
    Real.sqrt q / (1 + Real.sqrt q)
  rw [dualParameter, hsub]
  field_simp [hden, hD]
  nlinarith [hs2]

theorem positive_rectangle_weight_eq_factor_mul_dual_weight
    {q p : ℝ} (hq : 0 < q) (hp : 0 < p) (hp1 : p < 1)
    (a : LatticeVertex) (w h : ℕ)
    (A : Configuration (rectangleGraph a w h)) :
    positiveFKWeight (rectangleGraph a w h) q p
        (BoundaryCondition.free ∅) A =
      positiveRectangleDualityFactor q p a w h *
        positiveFKWeight (rectangleDualGraph a w h) q (dualParameter q p)
          (rectangleDualBoundaryCondition a w h)
          (positiveRectangleDualConfigurationEquiv a w h A) := by
  let B := positiveRectangleDualConfigurationEquiv a w h A
  have hcard : A.card + B.card = Nat.card (rectangleGraph a w h).edgeSet := by
    convert rectangleDualConfiguration_card_add_eq_primal_edgeSet a w h
      (rectangleCarrierConfigurationEquiv a w h A) using 1; rfl
  have hEulerRaw := rectangleEuler_additive_card_config a w h A
  have hEuler : componentCount (rectangleDualGraph a w h)
      (rectangleDualBoundaryCondition a w h) B + (w + 1) * (h + 1) =
        A.card + componentCount (rectangleGraph a w h)
          (BoundaryCondition.free ∅) A + 1 := by
    convert hEulerRaw using 1; rfl
  have hsub : Nat.card (rectangleGraph a w h).edgeSet - A.card = B.card := by
    omega
  have hsubD : Nat.card (rectangleDualGraph a w h).edgeSet - B.card = A.card := by
    rw [rectangleDualGraph_edgeSet_card_eq_primal_edgeSet]
    omega
  change p ^ A.card * (1 - p) ^
      (Nat.card (rectangleGraph a w h).edgeSet - A.card) *
      q ^ componentCount (rectangleGraph a w h) (BoundaryCondition.free ∅) A =
    positiveRectangleDualityFactor q p a w h *
      (dualParameter q p ^ B.card * (1 - dualParameter q p) ^
        (Nat.card (rectangleDualGraph a w h).edgeSet - B.card) *
        q ^ componentCount (rectangleDualGraph a w h)
          (rectangleDualBoundaryCondition a w h) B)
  rw [hsub, hsubD]
  unfold positiveRectangleDualityFactor
  exact positive_dual_weight_algebra hq hp hp1 A.card B.card
    (componentCount (rectangleGraph a w h) (BoundaryCondition.free ∅) A)
    (componentCount (rectangleDualGraph a w h)
      (rectangleDualBoundaryCondition a w h) B)
    ((w + 1) * (h + 1)) (Nat.card (rectangleGraph a w h).edgeSet)
    hcard hEuler

/-- Membership characterization for the positive-`q` rectangle dual map, in
the labelled dual-edge carrier. -/
@[simp] theorem mem_positiveRectangleDualConfigurationEquiv
    (a : LatticeVertex) (w h : ℕ)
    (A : Configuration (rectangleGraph a w h))
    (e : RectangleDualEdgeCarrier a w h) :
    rectangleDualGraphEdgeEquiv a w h e ∈
        positiveRectangleDualConfigurationEquiv a w h A ↔ e.primalEdge ∉ A := by
  have hmap : positiveRectangleDualConfigurationEquiv a w h A =
      rectangleDualConfiguration a w h A := by
    rfl
  rw [hmap]
  exact mem_rectangleDualConfiguration a w h A e

end
end PottsContinuity.DualityExt
