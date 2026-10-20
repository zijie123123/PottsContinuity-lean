module

public import PottsContinuity.Thm1.FiniteESCylinder

@[expose] public section

namespace PottsContinuity.Thm1

open Classical
open PottsContinuity
open PottsContinuity.PD.FK

noncomputable section

local instance pottsESNonnegVertexFintype (V : Finset (ℤ × ℤ)) :
    Fintype (PottsESVertex V) := Fintype.ofFinite _

local instance pottsESNonnegEdgeFintype (V : Finset (ℤ × ℤ)) :
    Fintype (pottsESGraph V).edgeSet := Fintype.ofFinite _

local instance pottsESNonnegConfigDecidableEq (V : Finset (ℤ × ℤ)) :
    DecidableEq (pottsESGraph V).edgeSet := Classical.decEq _

/-- The finite spin-bond PMF, including the closed-bond endpoint at zero
inverse temperature. -/
def pottsESJointLawNonneg (V : Finset (ℤ × ℤ)) (q : ℕ) (_hq : 1 ≤ q)
    (β : ℝ) (hβ : 0 ≤ β) (i : Fin q) :
    PMF ((V → Fin q) × ((pottsESGraph V).edgeSet → Bool)) := by
  classical
  letI : Nonempty (V → Fin q) := ⟨fun _ => i⟩
  exact PMF.ofFintype
    (fun z => ENNReal.ofReal
      (esJointProbability β (pottsESEdgeAgreement V i) z.1 z.2)) (by
        rw [← ENNReal.ofReal_sum_of_nonneg (fun z _ =>
          esJointProbability_nonneg hβ (pottsESEdgeAgreement V i) z.1 z.2),
          Fintype.sum_prod_type, sum_esJointProbability, ENNReal.ofReal_one])

@[simp] theorem pottsESJointLawNonneg_apply (V : Finset (ℤ × ℤ)) (q : ℕ)
    (hq : 1 ≤ q) (β : ℝ) (hβ : 0 ≤ β) (i : Fin q)
    (z : (V → Fin q) × ((pottsESGraph V).edgeSet → Bool)) :
    pottsESJointLawNonneg V q hq β hβ i z =
      ENNReal.ofReal (esJointProbability β (pottsESEdgeAgreement V i) z.1 z.2) := rfl

end

end PottsContinuity.Thm1
