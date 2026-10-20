-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/ParafermionicCoverIntermediateLayers.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.ParafermionicCoverLayerDecay
public import Mathlib.Data.Int.Interval
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

/-- The integer sheets available in the finite parafermionic cover box. -/
abbrev ParafermionicCoverLayerIndex (n : ℕ) :=
  {k : ℤ // -((n ^ 5 : ℕ) : ℤ) ≤ k ∧ k ≤ ((n ^ 5 : ℕ) : ℤ)}

def positiveLayerEmbedding (n : ℕ) :
    (↥(Finset.Ioo (0 : ℤ) ((n ^ 5 : ℕ) : ℤ))) ↪ ParafermionicCoverLayerIndex n where
  toFun k := ⟨k.1, by
    have hk := k.2
    simp only [Finset.mem_Ioo] at hk
    constructor <;> omega⟩
  inj' := by
    intro a b h
    apply Subtype.ext
    exact congrArg (fun x : ParafermionicCoverLayerIndex n => x.1) h

def negativeLayerEmbedding (n : ℕ) :
    (↥(Finset.Ioo (-((n ^ 5 : ℕ) : ℤ)) (0 : ℤ))) ↪ ParafermionicCoverLayerIndex n where
  toFun k := ⟨k.1, by
    have hk := k.2
    simp only [Finset.mem_Ioo] at hk
    constructor <;> omega⟩
  inj' := by
    intro a b h
    apply Subtype.ext
    exact congrArg (fun x : ParafermionicCoverLayerIndex n => x.1) h

/-- All strictly positive intermediate sheets, excluding both interval endpoints. -/
def parafermionicCoverPositiveIntermediateLayers (n : ℕ) :
    Finset (ParafermionicCoverLayerIndex n) :=
  (Finset.Ioo (0 : ℤ) ((n ^ 5 : ℕ) : ℤ)).attach.map (positiveLayerEmbedding n)

/-- All strictly negative intermediate sheets, excluding both interval endpoints. -/
def parafermionicCoverNegativeIntermediateLayers (n : ℕ) :
    Finset (ParafermionicCoverLayerIndex n) :=
  (Finset.Ioo (-((n ^ 5 : ℕ) : ℤ)) (0 : ℤ)).attach.map (negativeLayerEmbedding n)

theorem mem_parafermionicCoverPositiveIntermediateLayers (n : ℕ)
    (k : ParafermionicCoverLayerIndex n) :
    k ∈ parafermionicCoverPositiveIntermediateLayers n ↔
      0 < k.1 ∧ k.1 < ((n ^ 5 : ℕ) : ℤ) := by
  classical
  constructor
  · intro hk
    rcases Finset.mem_map.mp hk with ⟨a, ha, hEq⟩
    have hmem : a.1 ∈ Finset.Ioo (0 : ℤ) ((n ^ 5 : ℕ) : ℤ) := a.2
    have hval : a.1 = k.1 := congrArg Subtype.val hEq
    simpa [Finset.mem_Ioo, hval] using hmem
  · intro hk
    have hmem : k.1 ∈ Finset.Ioo (0 : ℤ) ((n ^ 5 : ℕ) : ℤ) := by
      simpa [Finset.mem_Ioo] using hk
    refine Finset.mem_map.mpr ⟨⟨k.1, hmem⟩, by simp, ?_⟩
    apply Subtype.ext
    rfl

theorem mem_parafermionicCoverNegativeIntermediateLayers (n : ℕ)
    (k : ParafermionicCoverLayerIndex n) :
    k ∈ parafermionicCoverNegativeIntermediateLayers n ↔
      -((n ^ 5 : ℕ) : ℤ) < k.1 ∧ k.1 < 0 := by
  classical
  constructor
  · intro hk
    rcases Finset.mem_map.mp hk with ⟨a, ha, hEq⟩
    have hmem : a.1 ∈ Finset.Ioo (-((n ^ 5 : ℕ) : ℤ)) (0 : ℤ) := a.2
    have hval : a.1 = k.1 := congrArg Subtype.val hEq
    simpa [Finset.mem_Ioo, hval] using hmem
  · intro hk
    have hmem : k.1 ∈ Finset.Ioo (-((n ^ 5 : ℕ) : ℤ)) (0 : ℤ) := by
      simpa [Finset.mem_Ioo] using hk
    refine Finset.mem_map.mpr ⟨⟨k.1, hmem⟩, by simp, ?_⟩
    apply Subtype.ext
    rfl

theorem card_parafermionicCoverPositiveIntermediateLayers (n : ℕ) (hn : 1 ≤ n) :
    (parafermionicCoverPositiveIntermediateLayers n).card = n ^ 5 - 1 := by
  classical
  rw [parafermionicCoverPositiveIntermediateLayers, Finset.card_map, Finset.card_attach]
  have hN : (0 : ℤ) < ((n ^ 5 : ℕ) : ℤ) := by
    exact_mod_cast Nat.one_le_pow 5 n (by omega)
  have hn5 : 1 ≤ n ^ 5 := Nat.one_le_pow 5 n (by omega)
  have hcast : ((Finset.Ioo (0 : ℤ) ((n ^ 5 : ℕ) : ℤ)).card : ℤ) =
      ((n ^ 5 - 1 : ℕ) : ℤ) := by
    rw [Int.card_Ioo_of_lt (a := (0 : ℤ)) (b := ((n ^ 5 : ℕ) : ℤ)) hN]
    rw [Nat.cast_sub hn5]
    norm_num
  exact_mod_cast hcast

theorem card_parafermionicCoverNegativeIntermediateLayers (n : ℕ) (hn : 1 ≤ n) :
    (parafermionicCoverNegativeIntermediateLayers n).card = n ^ 5 - 1 := by
  classical
  rw [parafermionicCoverNegativeIntermediateLayers, Finset.card_map, Finset.card_attach]
  have hN : (-((n ^ 5 : ℕ) : ℤ)) < (0 : ℤ) := by
    have hn5 : 1 ≤ n ^ 5 := Nat.one_le_pow 5 n (by omega)
    omega
  have hn5 : 1 ≤ n ^ 5 := Nat.one_le_pow 5 n (by omega)
  have hcast : ((Finset.Ioo (-((n ^ 5 : ℕ) : ℤ)) (0 : ℤ)).card : ℤ) =
      ((n ^ 5 - 1 : ℕ) : ℤ) := by
    rw [Int.card_Ioo_of_lt (a := (-((n ^ 5 : ℕ) : ℤ))) (b := (0 : ℤ)) hN]
    simp only [zero_sub]
    rw [Nat.cast_sub hn5]
    ring
  exact_mod_cast hcast

end PottsContinuity.FKC.FiniteFK
