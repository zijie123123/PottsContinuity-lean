module

public import PottsContinuity.Thm3.RSW.AnnulusChainLocal
public import PottsContinuity.Thm3.RSW.FiniteFkg
public import PottsContinuity.Thm3.RSW.FiniteLower

/-!
# P5b(R=8) to exact buffered P5, conditional only on circuit-chain gluing

Local free comparison, finite FKG, integer window containment, real-aspect
floor endpoints, the uniform chain count and finite-scale positivity are all
proved. The remaining premise is a deterministic inclusion of actual sampled
annulus events into the actual target crossing.
-/

@[expose] public section

namespace PottsContinuity.RSW
open MeasureTheory PD.FK
noncomputable section

/-- Finite FKG gives the quantitative buffered lower bound from the actual
local annulus events and their deterministic gluing inclusion. -/
theorem bufferedCrossing_lower_of_annulusChain
    (θ : Parameters) (α : ℝ) (n m K M : ℕ)
    (hscale : 16*m ≤ n) (hspan : (K*m:ℕ) ≤ ⌊α*(n:ℝ)⌋+(m:ℤ)) (hKM : K ≤ M)
    (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hlocal : a ≤ annulusProbability θ 8 m)
    (hannulusChain : ∀ ω,
      (∀ l : Fin (K+1), ω ∈ bufferedAnnulusChainLocalEvent α n m K hscale hspan l) →
      horizontalCrossing
        (latticeRectangle (-(n:ℤ)) ⌊(α+1)*(n:ℝ)⌋ (-(n:ℤ)) (2*(n:ℤ)))
        0 ⌊α*(n:ℝ)⌋ 0 n ω) :
    a^(M+1) ≤ bufferedCrossingProbability θ.toP θ.toQ α n := by
  let V := latticeRectangle (-(n:ℤ)) ⌊(α+1)*(n:ℝ)⌋ (-(n:ℤ)) (2*(n:ℤ))
  let E (l : Fin (K+1)) := fun ω => ω ∈ bufferedAnnulusChainLocalEvent α n m K hscale hspan l
  have hbound := finiteBoundaryEventProbability_lower_of_finite_gluing V θ
    (frozenBoundaryCondition V 0) (Finset.univ : Finset (Fin (K+1))) E
    (horizontalCrossing V 0 ⌊α*(n:ℝ)⌋ 0 n) a ha0
    (fun l _ => bufferedAnnulusChainLocalEvent_isUpperSet α n m K hscale hspan l)
    (fun l _ => hlocal.trans
      (annulusProbability_le_bufferedAnnulusChainLocalProbability θ α n m K hscale hspan l))
    (fun ω hω => hannulusChain ω (fun l => hω l (Finset.mem_univ l)))
  simp only [Finset.card_univ,Fintype.card_fin] at hbound
  rw [finiteBoundaryEventProbability_frozen] at hbound
  exact (pow_le_pow_of_le_one ha0 ha1 (Nat.add_le_add_right hKM 1)).trans hbound

/-- The full R=8 to P5 implication, with all floor and finite-scale steps
proved. Its only additional premise is explicit deterministic circuit-chain
gluing; it does not assume any crossing probability or RSW consequence. -/
theorem annulus8_to_buffered_crossings_of_annulusChain
    (θ : Parameters)
    (huniform : ∃ a : ℝ, 0 < a ∧ ∀ m : ℕ, 1 ≤ m → a ≤ annulusProbability θ 8 m)
    (hannulusChain : ∀ α : ℝ, 0 < α → ∀ n m K : ℕ, 32 ≤ n → 1 ≤ m →
      ∀ (hscale : 16*m ≤ n) (hspan : (K*m:ℕ) ≤ ⌊α*(n:ℝ)⌋+(m:ℤ)),
      ⌊α*(n:ℝ)⌋ ≤ (K*m:ℕ) → ∀ ω,
      (∀ l : Fin (K+1), ω ∈ bufferedAnnulusChainLocalEvent α n m K hscale hspan l) →
      horizontalCrossing
        (latticeRectangle (-(n:ℤ)) ⌊(α+1)*(n:ℝ)⌋ (-(n:ℤ)) (2*(n:ℤ)))
        0 ⌊α*(n:ℝ)⌋ 0 n ω) :
    ∀ α : ℝ, 0 < α → ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 1 ≤ n →
      c ≤ bufferedCrossingProbability θ.toP θ.toQ α n := by
  obtain ⟨a,ha,huniform⟩ := huniform
  have ha1 : a ≤ 1 := (huniform 1 le_rfl).trans (annulusProbability_lt_one θ 8 1).le
  intro α hα
  apply bufferedCrossingProbability_uniform_of_tail θ α hα 32
  refine ⟨a^(⌈32*α+1⌉₊+1),pow_pos ha _,fun n hn => ?_⟩
  let m := n/16
  obtain ⟨hm,hscale,hnm⟩ := annulus_chain_radius_bounds n hn
  obtain ⟨K,hcover,hspan,hKM⟩ := exists_annulus_chain_length α hα n m hm hnm
  exact bufferedCrossing_lower_of_annulusChain θ α n m K ⌈32*α+1⌉₊
    hscale hspan.le hKM a ha.le ha1 (huniform m hm)
    (hannulusChain α hα n m K hn hm hscale hspan.le hcover)

end
end PottsContinuity.RSW
