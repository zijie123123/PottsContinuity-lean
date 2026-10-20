module

public import PottsContinuity.Thm3.RSW.TranslatedAnnulus
public import PottsContinuity.Thm3.RSW.AnnulusChainWindows

/-! The actual sampled local annulus events in the exact buffered domain. -/

@[expose] public section

namespace PottsContinuity.RSW
open PD.FK
noncomputable section

/-- One member of the integer-spaced circuit chain, read by literal edge
restriction from the common frozen buffered rectangle. -/
def bufferedAnnulusChainLocalEvent (α : ℝ) (n m K : ℕ)
    (hscale : 16*m ≤ n) (hspan : (K*m:ℕ) ≤ ⌊α*(n:ℝ)⌋+(m:ℤ))
    (l : Fin (K+1)) :
    Set ((squareLattice.induce
      (latticeRectangle (-(n:ℤ)) ⌊(α+1)*(n:ℝ)⌋ (-(n:ℤ)) (2*(n:ℤ)) :
        Set (ℤ × ℤ))).edgeSet → Bool) :=
  translatedAnnulusEvent
    (latticeRectangle (-(n:ℤ)) ⌊(α+1)*(n:ℝ)⌋ (-(n:ℤ)) (2*(n:ℤ))) m
    (annulusChainCenter n m l.val)
    (fun z hz => annulus_chain_window_in_buffer α n m K hscale hspan l.val
      (Nat.le_of_lt_succ l.isLt) z hz)

/-- Every local chain event is increasing in the actual ambient edge states. -/
theorem bufferedAnnulusChainLocalEvent_isUpperSet (α : ℝ) (n m K : ℕ)
    (hscale : 16*m ≤ n) (hspan : (K*m:ℕ) ≤ ⌊α*(n:ℝ)⌋+(m:ℤ)) (l : Fin (K+1)) :
    IsUpperSet (bufferedAnnulusChainLocalEvent α n m K hscale hspan l) :=
  translatedAnnulusEvent_isUpperSet _ m (annulusChainCenter n m l.val) _

/-- The free local annulus lower bound holds for every member of the chain
under the common free law; all window containment has already been proved. -/
theorem annulusProbability_le_bufferedAnnulusChainLocalProbability
    (θ : Parameters) (α : ℝ) (n m K : ℕ)
    (hscale : 16*m ≤ n) (hspan : (K*m:ℕ) ≤ ⌊α*(n:ℝ)⌋+(m:ℤ)) (l : Fin (K+1)) :
    annulusProbability θ 8 m ≤
      finiteBoundaryEventProbability
        (latticeRectangle (-(n:ℤ)) ⌊(α+1)*(n:ℝ)⌋ (-(n:ℤ)) (2*(n:ℤ))) θ
        (frozenBoundaryCondition
          (latticeRectangle (-(n:ℤ)) ⌊(α+1)*(n:ℝ)⌋ (-(n:ℤ)) (2*(n:ℤ))) 0)
        (fun ω => ω ∈ bufferedAnnulusChainLocalEvent α n m K hscale hspan l) :=
  annulusProbability_le_translatedAnnulusProbability θ _ m (annulusChainCenter n m l.val) _

end
end PottsContinuity.RSW
