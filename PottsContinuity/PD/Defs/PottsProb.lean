-- Adapted from the author's PottsDiscontinuity formalization
-- (https://github.com/zijie123123/PottsDiscontinuity-lean), file `PottsDiscontinuity/Frozen/Defs/PottsProb.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.PD.Defs.PottsHamiltonian
public import Mathlib.Tactic

/-!
# `pottsProb` from the PottsDiscontinuity formalization

A definition of the formalization of arXiv:1611.09877v2 that is reused here by the adapted
modules of `PottsContinuity/PD/`. It is not part of the statement surface of this repository.
-/

@[expose] public section

open MeasureTheory Filter Topology Real
open scoped ENNReal

namespace PottsContinuity.PD

open Classical in
/-- The finite-volume Potts measure `μⁱ_{G,β}[σ] = exp(-β Hⁱ_G(σ)) / ∑_{σ'} exp(-β Hⁱ_G(σ'))`. -/
noncomputable def pottsProb (q : ℕ) (V : Finset (ℤ × ℤ)) (β : ℝ) (i : Fin (q + 1))
    (σ : ↥(V : Set (ℤ × ℤ)) → Set.Icc 1 q) : ℝ :=
  Real.exp (-β * pottsHamiltonian q V i σ) /
    ∑ σ' : ↥(V : Set (ℤ × ℤ)) → Set.Icc 1 q, Real.exp (-β * pottsHamiltonian q V i σ')

end PottsContinuity.PD
