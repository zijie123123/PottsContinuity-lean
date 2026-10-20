module

public import PottsContinuity.Thm3.RSW.ReflectedBlock
public import PottsContinuity.Thm3.RSW.FinitePathChain
public import PottsContinuity.Thm3.RSW.FiniteFkg

/-!
# Reflected chains in a common finite free law

The doubled-square blocks meet at exactly the same prescribed vertex. Each
local free estimate is compared with the common ambient free law, retaining
its band support. Finite FKG and walk clipping give the actual crossing.
-/

@[expose] public section

namespace PottsContinuity.RSW
open MeasureTheory PD.FK
noncomputable section

/-- K adjacent doubled-square blocks give a crossing, with exponent 2K from
reflection. The common sampled domain need only contain the full band; its
finite-volume law is never translated. -/
theorem squarePair_pow_le_horizontalCrossing_of_reflected_chain
    (θ : Parameters) (V : Finset (ℤ × ℤ)) (m : ℕ) (i j : Fin (m+1))
    (K : ℕ) (hK : 1 ≤ K) (a b A B : ℤ)
    (hA : a ≤ A) (hAB : A ≤ B) (hB : B ≤ a+2*(m:ℤ)*(K:ℤ))
    (hband : latticeRectangle a (a+2*(m:ℤ)*(K:ℤ)) b (b+(m:ℤ)) ⊆ V) :
    (squarePairProbability θ m i j)^(2*K) ≤
      finiteBoundaryEventProbability V θ (frozenBoundaryCondition V 0)
        (horizontalCrossing V A B b (b+(m:ℤ))) := by
  classical
  let S := latticeRectangle a (a+2*(m:ℤ)*(K:ℤ)) b (b+(m:ℤ))
  let u (l : ℕ) : ℤ × ℤ := (a+2*(m:ℤ)*(l:ℤ), b+(j.val:ℤ))
  let E (l : ℕ) := fun ω => ω ∈ finitePathEvent V S (u l) (u (l+1))
  have hlocal (l : ℕ) (hl : l ∈ Finset.range K) :
      (squarePairProbability θ m i j)^2 ≤ finiteBoundaryEventProbability V θ
        (frozenBoundaryCondition V 0) (E l) := by
    have hlK : (l:ℤ)+1 ≤ (K:ℤ) := by exact_mod_cast (Nat.succ_le_of_lt (Finset.mem_range.mp hl))
    let c := a+(2*(l:ℤ)+1)*(m:ℤ)
    have hblockS : reflectedBlock m c b ⊆ S := by
      intro z hz
      have h0 : 0 ≤ (l:ℤ)*(m:ℤ) := mul_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _)
      have h1 := mul_le_mul_of_nonneg_right hlK (Int.natCast_nonneg m)
      simp only [reflectedBlock,S,latticeRectangle,Finset.mem_product,Finset.mem_Icc,c] at hz ⊢
      constructor
      · constructor <;> nlinarith only [hz.1.1,hz.1.2,h0,h1]
      · exact hz.2
    have hp := squarePair_sq_le_translated_block_path θ V m i j c b
      (fun z hz => hband (hblockS hz))
    have hleft : (c-(m:ℤ), b+(j.val:ℤ)) = u l := by
      apply Prod.ext
      · dsimp [c,u]; ring
      · rfl
    have hright : (c+(m:ℤ), b+(j.val:ℤ)) = u (l+1) := by
      apply Prod.ext
      · dsimp [c,u]; ring
      · rfl
    rw [hleft,hright] at hp
    exact hp.trans (measureReal_mono (fun _ h =>
      finitePathEvent_mono_region V _ S hblockS _ _ h))
  have hglue : ∀ ω, (∀ l ∈ Finset.range K, E l ω) → horizontalCrossing V A B b (b+(m:ℤ)) ω := by
    intro ω hω
    have hp := finitePathEvent_chain V S u ω K hK
      (fun l hl => hω l (Finset.mem_range.mpr hl))
    apply finitePathEvent_implies_horizontalCrossing V S (u 0) (u K)
      A B b (b+(m:ℤ)) hAB (by simpa only [u,Nat.cast_zero,mul_zero,add_zero] using hA) hB
      (fun z hz => ?_) ω hp
    simp only [S,latticeRectangle,Finset.mem_product,Finset.mem_Icc] at hz
    exact hz.2
  have hbound := finiteBoundaryEventProbability_lower_of_finite_gluing V θ
    (frozenBoundaryCondition V 0) (Finset.range K) E _
    ((squarePairProbability θ m i j)^2) (sq_nonneg _)
    (fun l _ => finitePathEvent_isUpperSet V S (u l) (u (l+1))) hlocal hglue
  simpa only [Finset.card_range,← pow_mul] using hbound

end
end PottsContinuity.RSW
