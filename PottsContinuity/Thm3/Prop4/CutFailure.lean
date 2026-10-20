module

public import PottsContinuity.Thm3.Prop4.ClosedCutEnergy
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.MeasureTheory.Measure.Real

/-!
# Geometric decay for failure of disjoint closed cuts

All probabilities are those of the actual finite FK law. No product measure,
independence of cuts, or limiting specification is assumed.
-/

@[expose] public section

open MeasureTheory

namespace PottsContinuity.Thm3.Prop4

open PD.FK

noncomputable section

variable {V : Type*} [Finite V] (G : SimpleGraph V)

local instance cutFailureEdgeFintype : Fintype G.edgeSet := Fintype.ofFinite _
local instance cutFailureEdgeDecidableEq : DecidableEq G.edgeSet := Classical.decEq _
attribute [local instance] configurationMeasurableSpace

/-- Every one of the first K cuts has at least one actually open edge. -/
def closedCutFailure (F : ℕ → Finset G.edgeSet) (K : ℕ) : Set (Configuration G) :=
  {A | ∀ i < K, ¬Disjoint A (F i)}

omit [Finite V] in
/-- The next scan fails exactly if the preceding scan and the next cut fail. -/
theorem closedCutFailure_succ (F : ℕ → Finset G.edgeSet) (K : ℕ) :
    closedCutFailure G F (K+1) = closedCutFailure G F K ∩ {A | ¬Disjoint A (F K)} := by
  ext A
  simp only [closedCutFailure,Set.mem_ofPred_eq,Set.mem_inter_iff]
  constructor
  · intro h
    exact ⟨fun i hi => h i (by omega),h K (by omega)⟩
  · rintro ⟨h,hK⟩ i hi
    by_cases hiK : i = K
    · simpa only [hiK] using hK
    · exact h i (by omega)

/-- A common lower bound on each cut's closing cost gives a geometric bound
for the probability that all disjoint cuts fail. -/
theorem closedCutFailure_probability_le (θ : Parameters) (ξ : BoundaryCondition V)
    (F : ℕ → Finset G.edgeSet) (η : ℝ) (_hη : 0 ≤ η) (hη1 : η ≤ 1)
    (K : ℕ)
    (hdisj : ∀ i < K, ∀ j < K, i ≠ j → Disjoint (F i) (F j))
    (hcost : ∀ i < K, η ≤ (1-edgeParameter θ)^(F i).card) :
    (measure G θ ξ (closedCutFailure G F K)).toReal ≤ (1-η)^K := by
  classical
  induction K with
  | zero => simp [closedCutFailure]
  | succ K ih =>
    have hprev := ih (fun i hi j hj hij => hdisj i (by omega) j (by omega) hij)
      (fun i hi => hcost i (by omega))
    have hstable : ∀ e ∈ F K, ∀ A,
        A ∈ closedCutFailure G F K ↔ A.erase e ∈ closedCutFailure G F K := by
      intro e he A
      have hiff (i : ℕ) (hi : i < K) : Disjoint A (F i) ↔ Disjoint (A.erase e) (F i) := by
        have heNot : e ∉ F i := by
          intro hei
          exact (Finset.disjoint_left.mp (hdisj K (by omega) i (by omega) (by omega))) he hei
        rw [Finset.disjoint_erase_comm,Finset.erase_eq_of_notMem heNot]
      exact forall_congr' fun i => forall_congr' fun hi => not_congr (hiff i hi)
    have hclosed := finite_closed_cut_energy G θ ξ (F K) (closedCutFailure G F K) hstable
    have hscaled := mul_le_mul_of_nonneg_right (hcost K (by omega))
      (show 0 ≤ (measure G θ ξ (closedCutFailure G F K)).toReal from ENNReal.toReal_nonneg)
    have hpart := measureReal_inter_add_sdiff (μ := measure G θ ξ)
      (s := closedCutFailure G F K) (t := {A | Disjoint A (F K)}) (by simp)
    have hdiff : closedCutFailure G F K \ {A | Disjoint A (F K)} = closedCutFailure G F (K+1) := by
      rw [closedCutFailure_succ]
      rfl
    rw [hdiff] at hpart
    simp only [Measure.real] at hpart
    calc
      _ ≤ (1-η)*(measure G θ ξ (closedCutFailure G F K)).toReal := by
        nlinarith only [hscaled,hclosed,hpart]
      _ ≤ (1-η)*(1-η)^K := mul_le_mul_of_nonneg_left hprev (sub_nonneg.mpr hη1)
      _ = _ := by ring

/-- Uniformly bounded cut sizes yield the explicit geometric failure rate. -/
theorem closedCutFailure_probability_le_of_card (θ : Parameters) (ξ : BoundaryCondition V)
    (F : ℕ → Finset G.edgeSet) (R K : ℕ)
    (hdisj : ∀ i < K, ∀ j < K, i ≠ j → Disjoint (F i) (F j))
    (hcard : ∀ i < K, (F i).card ≤ R) :
    (measure G θ ξ (closedCutFailure G F K)).toReal ≤
      (1-(1-edgeParameter θ)^R)^K := by
  have hρ0 := (one_sub_edgeParameter_pos θ).le
  have hρ1 : 1-edgeParameter θ ≤ 1 := by linarith only [edgeParameter_pos θ]
  apply closedCutFailure_probability_le G θ ξ F _ (pow_nonneg hρ0 _) (pow_le_one₀ hρ0 hρ1) K hdisj
  intro i hi
  exact pow_le_pow_of_le_one hρ0 hρ1 (hcard i hi)

end

end PottsContinuity.Thm3.Prop4
