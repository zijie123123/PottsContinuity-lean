module

public import PottsContinuity.BD12.JointHybridSwitch

/-! The actual switched coordinate does not depend on the continuation of the
original exploration. These are pointwise dependence statements, prior to any
conditional expectation calculation. -/

@[expose] public section

namespace PottsContinuity.BD12
open scoped Classical
noncomputable section
variable {E : Type*} [Fintype E] [DecidableEq E]

omit [Fintype E] in
/-- The literal updated fresh coordinate equals the revealed Boolean answer. -/
theorem finiteRevealPattern_mem_self (H : Finset E) (e : E) (b : Bool) :
    e ∈ finiteRevealPattern H e b ↔ b = true := by
  cases b <;> simp [finiteRevealPattern]

/-- At a query, the final hybrid value at its fresh edge is exactly its current
threshold bit, independently of all original and replacement future inputs. -/
theorem finiteJointHybridEval_query_mem
    (w : Finset E → Set.Ioi (0 : ℝ)) (f : Finset E → ℝ) (cutoff : ℕ)
    (U V : ℕ → ℝ) (R HX HY : Finset E) (e : E) (he : e ∉ R)
    (next : Bool → FiniteRevealTree E (insert e R)) (stopped : Bool) :
    e ∈ finiteJointHybridEval w f cutoff U V (.query e he next) HX HY stopped ↔
      finiteUniformBit (finitePinnedMean w R HY (fun A => if e ∈ A then 1 else 0))
        (if cutoff ≤ R.card ∧ (stopped || decide (finiteDetermines f R HX)) = false
          then U R.card else V R.card) = true := by
  rw [finiteJointHybridEval]
  generalize finiteUniformBit _ (U R.card) = bx
  generalize finiteUniformBit _ _ = byy
  have h := finiteJointHybridEval_inter w f cutoff U V (next bx)
    (finiteRevealPattern HX e bx) (finiteRevealPattern HY e byy)
    (stopped || decide (finiteDetermines f R HX))
  have hm := Finset.ext_iff.mp h e
  simpa only [Finset.mem_inter, Finset.mem_insert_self, and_true,
    finiteRevealPattern_mem_self] using hm

end
end PottsContinuity.BD12
