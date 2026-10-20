module

public import PottsContinuity.Thm1.ESExpansion
public import PottsContinuity.Thm1.FiniteESBridge
public import PottsContinuity.Thm1.FiniteESColoring
public import PottsContinuity.Thm1.Parameters
public import PottsContinuity.PD.FK.ConfigurationBridge
public import PottsContinuity.PD.FK.Model
public import PottsContinuity.Frozen.Defs

@[expose] public section

namespace PottsContinuity.Thm1

open Classical
open PottsContinuity
open PottsContinuity.PD.FK

noncomputable section

local instance pottsESMeasureVertexFintype (V : Finset (ℤ × ℤ)) :
    Fintype (PottsESVertex V) := Fintype.ofFinite _

local instance pottsESMeasureEdgeFintype (V : Finset (ℤ × ℤ)) :
    Fintype (pottsESGraph V).edgeSet := Fintype.ofFinite _

local instance pottsESMeasureConfigDecidableEq (V : Finset (ℤ × ℤ)) :
    DecidableEq (pottsESGraph V).edgeSet := Classical.decEq _

/-- The Boolean-bond compatibility condition on the ghost-wired graph. -/
theorem pottsESCompatible_bool_iff (V : Finset (ℤ × ℤ)) {q : ℕ}
    (i : Fin q) (σ : V → Fin q) (ω : (pottsESGraph V).edgeSet → Bool) :
    pottsESCompatible V i (boolConfigurationEquiv (pottsESGraph V) ω) σ ↔
      ∀ e, ω e = true → pottsESEdgeAgreement V i σ e := by
  simp [pottsESCompatible, pottsESEdgeAgreement,
    mem_boolConfigurationEquiv]

/-- The bond expansion's finite spin weight is the frozen Potts weight. -/
theorem esGibbsWeight_eq_pottsWeight (V : Finset (ℤ × ℤ)) {q : ℕ}
    (β : ℝ) (i : Fin q) (σ : V → Fin q) :
    esGibbsWeight β (pottsESEdgeAgreement V i) σ = pottsWeight V β i σ := by
  change Real.exp (β * pottsESGraphAgreeSum V i σ) = pottsWeight V β i σ
  exact pottsESGraphGibbsWeight_eq V β i σ

/-- Summing the joint bond states recovers the frozen finite-volume Potts
probability mass. -/
theorem esJointProbability_spin_marginal_potts (V : Finset (ℤ × ℤ))
    {q : ℕ} (β : ℝ) (i : Fin q) (σ : V → Fin q) :
    ∑ ω : (pottsESGraph V).edgeSet → Bool,
      esJointProbability β (pottsESEdgeAgreement V i) σ ω =
        pottsProb V β i σ := by
  let : Nonempty (V → Fin q) := ⟨fun _ => i⟩
  calc
    _ = esGibbsWeight β (pottsESEdgeAgreement V i) σ /
          ∑ τ : V → Fin q, esGibbsWeight β (pottsESEdgeAgreement V i) τ :=
      esJointProbability_spin_marginal β (pottsESEdgeAgreement V i) σ
    _ = pottsWeight V β i σ / ∑ τ : V → Fin q, pottsWeight V β i τ := by
      simp_rw [esGibbsWeight_eq_pottsWeight]
    _ = pottsProb V β i σ := by
      unfold pottsProb
      congr 1

/-- Boolean open-edge constraints have the same compatible colorings as the
finite configuration they encode. -/
def pottsESBoolCompatibleColoringEquiv (V : Finset (ℤ × ℤ)) {q : ℕ}
    (i : Fin q) (ω : (pottsESGraph V).edgeSet → Bool) :
    {σ : V → Fin q //
      ∀ e, ω e = true → pottsESEdgeAgreement V i σ e} ≃
    {σ : V → Fin q //
      pottsESCompatible V i (boolConfigurationEquiv (pottsESGraph V) ω) σ} where
  toFun σ := ⟨σ.1, (pottsESCompatible_bool_iff V i σ.1 ω).2 σ.2⟩
  invFun σ := ⟨σ.1, (pottsESCompatible_bool_iff V i σ.1 ω).1 σ.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The number of spin assignments compatible with a Boolean bond state is
the component count with its ghost class pinned. -/
theorem pottsESBoolCompatibleColorings_count (V : Finset (ℤ × ℤ))
    {q : ℕ} (i : Fin q) (ω : (pottsESGraph V).edgeSet → Bool) :
    Nat.card {σ : V → Fin q //
      ∀ e, ω e = true → pottsESEdgeAgreement V i σ e} =
      q ^ (componentCount (pottsESGraph V) (pottsESBoundaryCondition V)
        (boolConfigurationEquiv (pottsESGraph V) ω) - 1) := by
  rw [Nat.card_congr (pottsESBoolCompatibleColoringEquiv V i ω),
    card_pottsESCompatibleColorings]

/-- Summing over the spin coordinate of the joint expansion gives the wired
finite random-cluster weight divided by the fixed ghost-class factor. -/
theorem esJointWeight_spin_sum_eq_fk (V : Finset (ℤ × ℤ))
    (q : ℕ) (hq : 1 ≤ q) (β : ℝ) (hβ : 0 < β) (i : Fin q)
    (ω : (pottsESGraph V).edgeSet → Bool) :
    (∑ σ : V → Fin q,
      esJointWeight β (pottsESEdgeAgreement V i) σ ω) =
      weight (pottsESGraph V) (pottsESParameters q β hq hβ)
        (pottsESBoundaryCondition V)
        (boolConfigurationEquiv (pottsESGraph V) ω) / (q : ℝ) := by
  classical
  let θ := pottsESParameters q β hq hβ
  let A := boolConfigurationEquiv (pottsESGraph V) ω
  let k := componentCount (pottsESGraph V) (pottsESBoundaryCondition V) A
  have hk : 0 < k := by
    change 0 < Nat.card (Quotient
      (componentSetoid (pottsESGraph V) (pottsESBoundaryCondition V) A))
    let : Nonempty (Quotient
        (componentSetoid (pottsESGraph V) (pottsESBoundaryCondition V) A)) :=
      ⟨Quotient.mk _ none⟩
    exact Nat.card_pos
  have hq0 : (q : ℝ) ≠ 0 := by
    exact_mod_cast (show q ≠ 0 by omega)
  have hcount := pottsESBoolCompatibleColorings_count V i ω
  have hcountReal :
      (Nat.card {σ : V → Fin q //
        ∀ e, ω e = true → pottsESEdgeAgreement V i σ e} : ℝ) =
        (q : ℝ) ^ (k - 1) := by
    rw [hcount]
    exact_mod_cast rfl
  have hclosed : 1 - edgeParameter θ = Real.exp (-β) := by
    rw [pottsESParameters_edgeParameter]
    ring
  have hpow : (q : ℝ) ^ (k - 1) * (q : ℝ) = (q : ℝ) ^ k := by
    rw [← pow_succ]
    congr 1
    omega
  rw [sum_esJointWeight_spins, esBernoulliWeight_eq, hcountReal]
  rw [weight, ← card_boolConfigurationEquiv, closed_card_boolConfigurationEquiv]
  rw [hclosed]
  rw [show edgeParameter θ = 1 - Real.exp (-β) by
    simpa only [θ] using pottsESParameters_edgeParameter q β hq hβ]
  rw [show θ.val = (q : ℝ) by rfl]
  rw [show componentCount (pottsESGraph V) (pottsESBoundaryCondition V) A = k by rfl]
  change (1 - Real.exp (-β)) ^ A.card *
      Real.exp (-β) ^ (Nat.card (pottsESGraph V).edgeSet - A.card) * (q : ℝ) ^ (k - 1) =
    ((1 - Real.exp (-β)) ^ A.card *
      Real.exp (-β) ^ (Nat.card (pottsESGraph V).edgeSet - A.card) *
      (q : ℝ) ^ k) / (q : ℝ)
  have hpowdiv : (q : ℝ) ^ (k - 1) = (q : ℝ) ^ k / (q : ℝ) :=
    (eq_div_iff hq0).2 hpow
  rw [hpowdiv]
  ring

/-- The total joint partition sum is the wired FK partition sum with the
single fixed-color component removed from its factor. -/
theorem esJointPartition_eq_fk (V : Finset (ℤ × ℤ))
    (q : ℕ) (hq : 1 ≤ q) (β : ℝ) (hβ : 0 < β) (i : Fin q) :
    esJointPartition β (pottsESEdgeAgreement V i) =
      partitionFunction (pottsESGraph V) (pottsESParameters q β hq hβ)
        (pottsESBoundaryCondition V) / (q : ℝ) := by
  classical
  rw [esJointPartition, Finset.sum_comm]
  simp_rw [esJointWeight_spin_sum_eq_fk V q hq β hβ i]
  rw [Equiv.sum_comp (boolConfigurationEquiv (pottsESGraph V))
    (fun A : Configuration (pottsESGraph V) =>
      weight (pottsESGraph V) (pottsESParameters q β hq hβ)
        (pottsESBoundaryCondition V) A / (q : ℝ))]
  rw [← Finset.sum_div, partitionFunction]
  rfl

/-- Summing the joint law over spins gives exactly the ghost-wired FK
configuration probability. -/
theorem esJointProbability_bond_marginal_fk (V : Finset (ℤ × ℤ))
    (q : ℕ) (hq : 1 ≤ q) (β : ℝ) (hβ : 0 < β) (i : Fin q)
    (ω : (pottsESGraph V).edgeSet → Bool) :
    ∑ σ : V → Fin q,
      esJointProbability β (pottsESEdgeAgreement V i) σ ω =
      configurationProbability (pottsESGraph V) (pottsESParameters q β hq hβ)
        (pottsESBoundaryCondition V)
        (boolConfigurationEquiv (pottsESGraph V) ω) := by
  classical
  let : Nonempty (V → Fin q) := ⟨fun _ => i⟩
  let θ := pottsESParameters q β hq hβ
  let A := boolConfigurationEquiv (pottsESGraph V) ω
  have hq0 : (q : ℝ) ≠ 0 := by
    exact_mod_cast (show q ≠ 0 by omega)
  have hZ : partitionFunction (pottsESGraph V)
      (pottsESParameters q β hq hβ) (pottsESBoundaryCondition V) ≠ 0 :=
    (partitionFunction_pos (pottsESGraph V)
      (pottsESParameters q β hq hβ) (pottsESBoundaryCondition V)).ne'
  unfold esJointProbability
  rw [← Finset.sum_div,
    esJointWeight_spin_sum_eq_fk V q hq β hβ i ω,
    esJointPartition_eq_fk V q hq β hβ i,
    configurationProbability]
  field_simp [hq0, hZ]

/-- The finite spin-bond Edwards--Sokal probability mass on the shell graph. -/
def pottsESJointLaw (V : Finset (ℤ × ℤ)) (q : ℕ) (_hq : 1 ≤ q)
    (β : ℝ) (hβ : 0 < β) (i : Fin q) :
    PMF ((V → Fin q) × ((pottsESGraph V).edgeSet → Bool)) := by
  classical
  letI : Nonempty (V → Fin q) := ⟨fun _ => i⟩
  exact PMF.ofFintype
    (fun z => ENNReal.ofReal
      (esJointProbability β (pottsESEdgeAgreement V i) z.1 z.2)) (by
        rw [← ENNReal.ofReal_sum_of_nonneg (fun z _ =>
          esJointProbability_nonneg hβ.le (pottsESEdgeAgreement V i) z.1 z.2),
          Fintype.sum_prod_type, sum_esJointProbability, ENNReal.ofReal_one])

@[simp] theorem pottsESJointLaw_apply (V : Finset (ℤ × ℤ)) (q : ℕ)
    (hq : 1 ≤ q) (β : ℝ) (hβ : 0 < β) (i : Fin q)
    (z : (V → Fin q) × ((pottsESGraph V).edgeSet → Bool)) :
    pottsESJointLaw V q hq β hβ i z =
      ENNReal.ofReal (esJointProbability β (pottsESEdgeAgreement V i) z.1 z.2) := rfl

end

end PottsContinuity.Thm1
