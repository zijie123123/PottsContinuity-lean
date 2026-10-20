-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `Parameters.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
public import Mathlib.Tactic

/-! Cluster-weight parameters of the critical FK model on the square lattice.
The public carrier is exactly `1 ≤ q < 4`.
-/

@[expose] public section

namespace PottsContinuity.FKC

noncomputable section

/-- Cluster weights `1 ≤ q < 4`. -/
abbrev ClusterWeight := {q : ℝ // 1 ≤ q ∧ q < 4}

/-- The loop weight associated with the FK cluster weight. -/
def loopWeight (q : ClusterWeight) : ℝ := Real.sqrt q.val

/-- The critical square-lattice FK edge parameter `√q/(1+√q)`. -/
def edgeParameter (q : ClusterWeight) : ℝ :=
  Real.sqrt q.val / (1 + Real.sqrt q.val)

lemma clusterWeight_pos (q : ClusterWeight) : 0 < q.val :=
  lt_of_lt_of_le zero_lt_one q.property.1

lemma clusterWeight_nonneg (q : ClusterWeight) : 0 ≤ q.val :=
  (clusterWeight_pos q).le

lemma loopWeight_pos (q : ClusterWeight) : 0 < loopWeight q :=
  Real.sqrt_pos.mpr (clusterWeight_pos q)

lemma loopWeight_sq (q : ClusterWeight) : loopWeight q ^ 2 = q.val :=
  Real.sq_sqrt (clusterWeight_nonneg q)

lemma one_le_loopWeight (q : ClusterWeight) : 1 ≤ loopWeight q := by
  nlinarith only [loopWeight_sq q, loopWeight_pos q, q.property.1]

lemma loopWeight_lt_two (q : ClusterWeight) : loopWeight q < 2 := by
  nlinarith only [loopWeight_sq q, loopWeight_pos q, q.property.2]

lemma one_add_loopWeight_pos (q : ClusterWeight) : 0 < 1 + loopWeight q :=
  add_pos zero_lt_one (loopWeight_pos q)

lemma edgeParameter_pos (q : ClusterWeight) : 0 < edgeParameter q :=
  div_pos (loopWeight_pos q) (one_add_loopWeight_pos q)

lemma edgeParameter_lt_one (q : ClusterWeight) : edgeParameter q < 1 := by
  change loopWeight q / (1 + loopWeight q) < 1
  apply (div_lt_one (one_add_loopWeight_pos q)).mpr
  linarith only [loopWeight_pos q]

lemma one_sub_edgeParameter_pos (q : ClusterWeight) : 0 < 1 - edgeParameter q :=
  sub_pos.mpr (edgeParameter_lt_one q)

lemma one_sub_edgeParameter (q : ClusterWeight) :
    1 - edgeParameter q = 1 / (1 + loopWeight q) := by
  change 1 - loopWeight q / (1 + loopWeight q) = _
  field_simp [(one_add_loopWeight_pos q).ne']
  ring

lemma edgeParameter_odds (q : ClusterWeight) :
    edgeParameter q / (1 - edgeParameter q) = loopWeight q := by
  rw [one_sub_edgeParameter]
  change (loopWeight q / (1 + loopWeight q)) / (1 / (1 + loopWeight q)) = _
  field_simp [(one_add_loopWeight_pos q).ne']

end

end PottsContinuity.FKC
