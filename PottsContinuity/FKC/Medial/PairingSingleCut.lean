-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `Medial/PairingSingleCut.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.Medial.PairingGraph
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.Medial

universe u

variable {P : Type u} [DecidableEq P]

/-- Cut the pairing edge incident to `s` by making both ends fixed. -/
def pairingSingleCut (B : Equiv.Perm P) (s p : P) : P :=
  if p = s ∨ p = B s then p else B p

theorem pairingSingleCut_involutive (B : Equiv.Perm P) (s : P)
    (hB : Function.Involutive B) : Function.Involutive (pairingSingleCut B s) := by
  intro p
  by_cases hp : p = s ∨ p = B s
  · simp [pairingSingleCut, hp]
  · have hBp : ¬ (B p = s ∨ B p = B s) := by
      intro h
      rcases h with h | h
      · exact hp (Or.inr ((hB p).symm.trans (congrArg B h)))
      · exact hp (Or.inl (B.injective h))
    simp only [pairingSingleCut, ite_eq_right hp, ite_eq_right hBp]
    exact hB p

def pairingSingleCutPerm (B : Equiv.Perm P) (s : P)
    (hB : Function.Involutive B) : Equiv.Perm P :=
  (pairingSingleCut_involutive B s hB).toPerm (pairingSingleCut B s)

@[simp] theorem pairingSingleCutPerm_apply (B : Equiv.Perm P) (s p : P)
    (hB : Function.Involutive B) : pairingSingleCutPerm B s hB p = pairingSingleCut B s p := by
  rfl

theorem pairingSingleCutPerm_fixed_iff (B : Equiv.Perm P) (s p : P)
    (hB : Function.Involutive B) (hfree : ∀ p, B p ≠ p) :
    pairingSingleCutPerm B s hB p = p ↔ p = s ∨ p = B s := by
  rw [pairingSingleCutPerm_apply]
  change (if p = s ∨ p = B s then p else B p) = p ↔ _
  by_cases hp : p = s ∨ p = B s
  · simp [hp]
  · simp [hp, hfree p]

omit [DecidableEq P] in
theorem pairingSingleCut_endpoints_ne (B : Equiv.Perm P) (s : P)
    (hfree : ∀ p, B p ≠ p) : s ≠ B s := by
  intro h
  exact hfree s h.symm

variable [Fintype P]

theorem pairingGraph_singleCut_existsUnique_isPath
    (A B : Equiv.Perm P) (hA : Function.Involutive A)
    (hB : Function.Involutive B) (hAfree : ∀ p, A p ≠ p)
    (hBfree : ∀ p, B p ≠ p) (s : P) :
    ∃! p : (pairingGraph A (pairingSingleCutPerm B s hB)
        hA (pairingSingleCut_involutive B s hB)).Walk
        (s, true) (B s, true), p.IsPath := by
  apply pairingGraph_existsUnique_isPath A (pairingSingleCutPerm B s hB)
      hA (pairingSingleCut_involutive B s hB) hAfree
  · exact pairingSingleCut_endpoints_ne B s hBfree
  · intro p
    exact pairingSingleCutPerm_fixed_iff B s p hB hBfree

end PottsContinuity.FKC.Medial
