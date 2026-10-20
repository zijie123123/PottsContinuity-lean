-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `Medial/ParafermionicCoverFiniteFaceEnclosure.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.Medial.ParafermionicCoverFiniteFaces
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.Medial

open PottsContinuity.FKC

def coverFiniteFaceEnclosureHeight (v : ParafermionicCoverVertex) : ℕ :=
  max v.1.1.natAbs (max v.1.2.natAbs v.2.natAbs)

private theorem exists_coverFiniteFaceEnclosureHeight_bound
    (L : List ParafermionicCoverVertex) :
    ∃ M : ℕ, ∀ v ∈ L, coverFiniteFaceEnclosureHeight v ≤ M := by
  induction L with
  | nil => exact ⟨0, by simp⟩
  | cons a L ih =>
      obtain ⟨M, hM⟩ := ih
      refine ⟨max M (coverFiniteFaceEnclosureHeight a), ?_⟩
      intro v hv
      simp only [List.mem_cons] at hv
      rcases hv with rfl | hv
      · exact Nat.le_max_right _ _
      · exact le_trans (hM v hv) (Nat.le_max_left _ _)

/-- Any two finite lists of actual lifted vertices and nonbranch ordinary-face
bases fit simultaneously in one prescribed finite box. Each listed face is a
genuine retained ordinary face of that same box. -/
theorem parafermionicCoverFiniteFaceLists_enclosed_in_box
    (L F : List ParafermionicCoverVertex)
    (hordinary : ∀ f ∈ F, f.1 ≠ (0,-1)) :
    ∃ N : ℕ, 1 ≤ N ∧
      (∀ v ∈ L, v ∈ parafermionicCoverBoxVertices N) ∧
      (∀ f ∈ F, f ∈ parafermionicCoverFiniteOrdinaryFaces N) := by
  obtain ⟨M, hM⟩ := exists_coverFiniteFaceEnclosureHeight_bound (L ++ F)
  let N := M + 1
  have hN : 1 ≤ N := by simp [N]
  have hMlt : M < N := by simp [N]
  have hNpow : N ≤ N ^ 5 := Nat.le_self_pow (n := 5) (by decide) N
  have hMpow : M < N ^ 5 := lt_of_lt_of_le hMlt hNpow
  have hLbound : ∀ v ∈ L, coverFiniteFaceEnclosureHeight v ≤ M := by
    intro v hv
    exact hM v (List.mem_append.mpr (Or.inl hv))
  have hFbound : ∀ f ∈ F, coverFiniteFaceEnclosureHeight f ≤ M := by
    intro f hf
    exact hM f (List.mem_append.mpr (Or.inr hf))
  refine ⟨N,hN,?_,?_⟩
  · intro v hv
    have hh := hLbound v hv
    have hxN : v.1.1.natAbs ≤ M :=
      (Nat.le_max_left _ _).trans hh
    have hyN : v.1.2.natAbs ≤ M :=
      (Nat.le_max_left _ _).trans ((Nat.le_max_right _ _).trans hh)
    have hkN : v.2.natAbs ≤ M :=
      (Nat.le_max_right _ _).trans ((Nat.le_max_right _ _).trans hh)
    have hxZ : (v.1.1.natAbs : ℤ) ≤ (N : ℤ) := by
      exact_mod_cast (le_trans hxN (Nat.le_succ M))
    have hyZ : (v.1.2.natAbs : ℤ) ≤ (N : ℤ) := by
      exact_mod_cast (le_trans hyN (Nat.le_succ M))
    have hkPow : v.2.natAbs ≤ N ^ 5 := (le_trans hkN (Nat.le_succ M)).trans hNpow
    have hkZ : (v.2.natAbs : ℤ) ≤ ((N ^ 5 : ℕ) : ℤ) := by
      exact_mod_cast hkPow
    have hxabs : |v.1.1| ≤ (N : ℤ) := by
      simpa [Int.natCast_natAbs] using hxZ
    have hyabs : |v.1.2| ≤ (N : ℤ) := by
      simpa [Int.natCast_natAbs] using hyZ
    have hkabs : |v.2| ≤ ((N ^ 5 : ℕ) : ℤ) := by
      simpa [Int.natCast_natAbs] using hkZ
    have hx := abs_le.mp hxabs
    have hy := abs_le.mp hyabs
    have hk := abs_le.mp hkabs
    rw [parafermionicCoverBoxVertices_mem]
    exact ⟨hx.1,hx.2,hy.1,hy.2,hk.1,hk.2⟩
  · intro f hf
    have hh := hFbound f hf
    have hxM : f.1.1.natAbs ≤ M :=
      (Nat.le_max_left _ _).trans hh
    have hyM : f.1.2.natAbs ≤ M :=
      (Nat.le_max_left _ _).trans ((Nat.le_max_right _ _).trans hh)
    have hkM : f.2.natAbs ≤ M :=
      (Nat.le_max_right _ _).trans ((Nat.le_max_right _ _).trans hh)
    have hxZ : (f.1.1.natAbs : ℤ) ≤ (M : ℤ) := by exact_mod_cast hxM
    have hyZ : (f.1.2.natAbs : ℤ) ≤ (M : ℤ) := by exact_mod_cast hyM
    have hkZ : (f.2.natAbs : ℤ) ≤ (M : ℤ) := by exact_mod_cast hkM
    have hxabs : |f.1.1| ≤ (M : ℤ) := by
      simpa [Int.natCast_natAbs] using hxZ
    have hyabs : |f.1.2| ≤ (M : ℤ) := by
      simpa [Int.natCast_natAbs] using hyZ
    have hkabs : |f.2| ≤ (M : ℤ) := by
      simpa [Int.natCast_natAbs] using hkZ
    rcases abs_le.mp hxabs with ⟨hxlo,hxhi⟩
    rcases abs_le.mp hyabs with ⟨hylo,hyhi⟩
    rcases abs_le.mp hkabs with ⟨hklo,hkhi⟩
    have hNcast : (M : ℤ) < (N : ℤ) := by exact_mod_cast hMlt
    have hNpowCast : (M : ℤ) < ((N ^ 5 : ℕ) : ℤ) := by
      exact_mod_cast hMpow
    rw [parafermionicCoverFiniteOrdinaryFaces_mem_iff]
    refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
    · omega
    · omega
    · omega
    · omega
    · have hlow : -((N ^ 5 : ℕ) : ℤ) ≤ f.2 := by omega
      exact hlow
    · omega
    · exact hordinary f hf
    · intro _
      omega

end PottsContinuity.FKC.Medial
