module

public import PottsContinuity.Thm1.FiniteESRootColoring
public import PottsContinuity.Frozen.Defs

@[expose] public section

namespace PottsContinuity.Thm1

open Classical
open PottsContinuity
open PottsContinuity.PD.FK

noncomputable section

local instance pottsESMagVertexFintype (V : Finset (ℤ × ℤ)) :
    Fintype (PottsESVertex V) := Fintype.ofFinite _

local instance pottsESMagEdgeFintype (V : Finset (ℤ × ℤ)) :
    Fintype (pottsESGraph V).edgeSet := Fintype.ofFinite _

local instance pottsESMagConfigDecidableEq (V : Finset (ℤ × ℤ)) :
    DecidableEq (pottsESGraph V).edgeSet := Classical.decEq _

/-- Connection from the origin to the wired exterior in the auxiliary graph. -/
def pottsESOriginExteriorConnected (V : Finset (ℤ × ℤ))
    (h0 : (0, 0) ∈ V) (A : Configuration (pottsESGraph V)) : Prop :=
  (componentSetoid (pottsESGraph V) (pottsESBoundaryCondition V) A).r
    (pottsESOriginVertex V h0) none

/-- The finite wired random-cluster probability of origin-to-exterior
connection on the Edwards--Sokal shell graph. -/
def pottsESOriginExteriorConnectionProbability (V : Finset (ℤ × ℤ))
    (q : ℕ) (hq : 1 ≤ q) (β : ℝ) (hβ : 0 ≤ β) (h0 : (0, 0) ∈ V) : ℝ :=
  if hpos : 0 < β then
    ∑ A : Configuration (pottsESGraph V),
      if pottsESOriginExteriorConnected V h0 A then
        configurationProbability (pottsESGraph V)
          (pottsESParameters q β hq hpos) (pottsESBoundaryCondition V) A
      else 0
  else if hz : β = 0 then 0
    else False.elim (hz (le_antisymm (le_of_not_gt hpos) hβ))

/-- At zero inverse temperature every finite spin configuration has the same
Gibbs weight. -/
theorem pottsProb_zero_uniform (V : Finset (ℤ × ℤ)) (q : ℕ)
    (i : Fin q) (σ : V → Fin q) :
    pottsProb V 0 i σ = 1 / (q : ℝ) ^ Nat.card V := by
  classical
  simp [PottsContinuity.pottsProb,
    PottsContinuity.pottsWeight,
    Nat.card_eq_fintype_card]

/-- The finite-volume origin spin is uniform at zero inverse temperature. -/
theorem pottsES_finite_magnetisation_at_zero (V : Finset (ℤ × ℤ))
    (q : ℕ) (hq : 2 ≤ q) (i : Fin q) (h0 : (0, 0) ∈ V) :
    pottsEventProb V 0 i (fun σ => σ (0, 0) = i) = 1 / (q : ℝ) := by
  classical
  let x₀ : V := ⟨(0, 0), h0⟩
  let : Nonempty V := ⟨x₀⟩
  have hcard : Nat.card {σ : V → Fin q // σ x₀ = i} =
      q ^ (Nat.card V - 1) := by
    simpa [x₀, Nat.card_fin] using card_pinned_functions x₀ i
  have hq0 : (q : ℝ) ≠ 0 := by
    exact_mod_cast (show q ≠ 0 by omega)
  have hn : 1 ≤ Nat.card V := by
    have hn' : 0 < Nat.card V := Nat.card_pos
    omega
  have hpow : (q : ℝ) ^ (Nat.card V - 1) * (q : ℝ) =
      (q : ℝ) ^ Nat.card V := by
    calc
      (q : ℝ) ^ (Nat.card V - 1) * (q : ℝ) =
          (q : ℝ) ^ ((Nat.card V - 1) + 1) := by rw [pow_succ]
      _ = (q : ℝ) ^ Nat.card V := by congr 1; omega
  have hprob (σ : V → Fin q) :
      pottsProb V 0 i σ = 1 / (q : ℝ) ^ Nat.card V :=
    pottsProb_zero_uniform V q i σ
  calc
    pottsEventProb V 0 i (fun σ => σ (0, 0) = i) =
        ∑ σ : V → Fin q, if σ x₀ = i then pottsProb V 0 i σ else 0 := by
      unfold pottsEventProb
      apply Finset.sum_congr rfl
      intro σ _
      simp [x₀, pottsExtend, h0]
    _ = (1 / (q : ℝ) ^ Nat.card V) *
          (Nat.card {σ : V → Fin q // σ x₀ = i} : ℝ) := by
      have hpoint (σ : V → Fin q) :
          (if σ x₀ = i then pottsProb V 0 i σ else 0) =
            (1 / (q : ℝ) ^ Nat.card V) * (if σ x₀ = i then 1 else 0) := by
        by_cases hs : σ x₀ = i <;> simp [hs, hprob]
      calc
        _ = ∑ σ : V → Fin q,
              (1 / (q : ℝ) ^ Nat.card V) *
                (if σ x₀ = i then 1 else 0) := by
          apply Finset.sum_congr rfl
          intro σ _
          exact hpoint σ
        _ = _ := by
          rw [← Finset.mul_sum, Finset.sum_boole]
          simp only [Nat.card_eq_fintype_card, Fintype.card_subtype]
    _ = 1 / (q : ℝ) := by
      rw [hcard]
      field_simp [hq0]
      have hpowcast :
          ((q ^ (Nat.card V - 1) : ℕ) : ℝ) =
            (q : ℝ) ^ (Nat.card V - 1) := by norm_cast
      rw [hpowcast]
      linarith [hpow]

/-- At fixed bonds, the origin color has conditional mass one when its open
component reaches the wired exterior and mass `1/q` otherwise. -/
theorem pottsESJointProbability_origin_pin_bond (V : Finset (ℤ × ℤ))
    (q : ℕ) (hq : 2 ≤ q) (β : ℝ) (hβ : 0 < β) (i : Fin q)
    (h0 : (0, 0) ∈ V) (ω : (pottsESGraph V).edgeSet → Bool) :
    (∑ σ : V → Fin q,
      if σ ⟨(0, 0), h0⟩ = i then
        esJointProbability β (pottsESEdgeAgreement V i) σ ω else 0) =
      configurationProbability (pottsESGraph V) (pottsESParameters q β
        (by omega) hβ) (pottsESBoundaryCondition V)
        (boolConfigurationEquiv (pottsESGraph V) ω) *
        (if pottsESOriginExteriorConnected V h0
          (boolConfigurationEquiv (pottsESGraph V) ω) then
            (1 : ℝ) else 1 / (q : ℝ)) := by
  classical
  let : Nonempty (V → Fin q) := ⟨fun _ => i⟩
  let A := boolConfigurationEquiv (pottsESGraph V) ω
  let R := componentSetoid (pottsESGraph V) (pottsESBoundaryCondition V) A
  let k := componentCount (pottsESGraph V) (pottsESBoundaryCondition V) A
  let qpos : 1 ≤ q := by omega
  let θ := pottsESParameters q β qpos hβ
  let Good := {σ : V → Fin q //
    (∀ e, ω e = true → pottsESEdgeAgreement V i σ e) ∧
      σ ⟨(0, 0), h0⟩ = i}
  let All := {σ : V → Fin q //
    ∀ e, ω e = true → pottsESEdgeAgreement V i σ e}
  have htotal : Nat.card All = q ^ (k - 1) := by
    simpa [All, k, A] using pottsESBoolCompatibleColorings_count V i ω
  have hgood : Nat.card Good =
      (if R.r (pottsESOriginVertex V h0) none then q ^ (k - 1)
        else q ^ (k - 2)) := by
    by_cases hc : R.r (pottsESOriginVertex V h0) none
    · rw [ite_eq_left hc]
      simpa [Good, k, R, A] using
        pottsESRootCompatibleColorings_count_of_connected V i ω h0 hc
    · rw [ite_eq_right hc]
      simpa [Good, k, R, A] using
        pottsESRootCompatibleColorings_count_of_not_connected V i ω h0 hc
  have hFK :
      (∑ σ : V → Fin q, esJointProbability β
        (pottsESEdgeAgreement V i) σ ω) =
        configurationProbability (pottsESGraph V) θ
          (pottsESBoundaryCondition V) A := by
    simpa [A, θ, qpos] using
      esJointProbability_bond_marginal_fk V q qpos β hβ i ω
  have hGoodProbability :
      (∑ σ : V → Fin q,
        if σ ⟨(0, 0), h0⟩ = i then
          esJointProbability β (pottsESEdgeAgreement V i) σ ω else 0) =
        esBernoulliWeight β ω * Nat.card Good /
          esJointPartition β (pottsESEdgeAgreement V i) := by
    have h := sum_esJointProbability_spins_pinned β
      (pottsESEdgeAgreement V i) ω (fun σ => σ ⟨(0, 0), h0⟩ = i)
    have hsum :
        (∑ σ : V → Fin q,
          if σ ⟨(0, 0), h0⟩ = i then
            esJointProbability β (pottsESEdgeAgreement V i) σ ω else 0) =
        (∑ σ : V → Fin q,
          @ite ℝ (σ ⟨(0, 0), h0⟩ = i)
            (Classical.propDecidable (σ ⟨(0, 0), h0⟩ = i))
            (esJointProbability β (pottsESEdgeAgreement V i) σ ω) 0) := by
      apply Finset.sum_congr rfl
      intro σ _
      by_cases hp : σ ⟨(0, 0), h0⟩ = i <;> simp [hp]
    calc
      _ = _ := hsum
      _ = _ := h
  have hAllProbability :
      (∑ σ : V → Fin q,
        esJointProbability β (pottsESEdgeAgreement V i) σ ω) =
        esBernoulliWeight β ω * Nat.card All /
          esJointPartition β (pottsESEdgeAgreement V i) := by
    calc
      _ = (∑ σ : V → Fin q,
            esJointWeight β (pottsESEdgeAgreement V i) σ ω) /
            esJointPartition β (pottsESEdgeAgreement V i) := by
        simp_rw [esJointProbability]
        rw [Finset.sum_div]
      _ = _ := by
        rw [sum_esJointWeight_spins]
  have hq0 : (q : ℝ) ≠ 0 := by
    exact_mod_cast (show q ≠ 0 by omega)
  have hcountFactor :
      (Nat.card Good : ℝ) = (Nat.card All : ℝ) *
        (if R.r (pottsESOriginVertex V h0) none then
          (1 : ℝ) else 1 / (q : ℝ)) := by
    by_cases hc : R.r (pottsESOriginVertex V h0) none
    · have hNat : Nat.card Good = Nat.card All := by
        rw [hgood, htotal]
        simp [hc]
      simp only [ite_eq_left hc, mul_one]
      exact_mod_cast hNat
    · have hclasses : Quotient.mk R (pottsESOriginVertex V h0) ≠
          Quotient.mk R none := by
        intro heq
        exact hc (Quotient.exact heq)
      let : Fintype (Quotient R) := Fintype.ofFinite _
      have hinj : Function.Injective
          (fun j : Fin 2 =>
            if j.val = 0 then Quotient.mk R (pottsESOriginVertex V h0)
              else Quotient.mk R none) := by
        intro j j' hj
        fin_cases j <;> fin_cases j' <;> simp_all
      have hcard : 2 ≤ k := by
        dsimp [k, componentCount]
        have hle := Fintype.card_le_of_injective
          (fun j : Fin 2 =>
            if j.val = 0 then Quotient.mk R (pottsESOriginVertex V h0)
              else Quotient.mk R none) hinj
        simpa [Nat.card_eq_fintype_card] using hle
      have hexp : k - 1 = (k - 2) + 1 := by omega
      have hpow : q ^ (k - 2) * q = q ^ (k - 1) := by
        rw [hexp, pow_succ]
      have hpowReal :
          ((q ^ (k - 2) : ℕ) : ℝ) * (q : ℝ) =
            ((q ^ (k - 1) : ℕ) : ℝ) := by
        exact_mod_cast hpow
      rw [hgood, htotal]
      simp only [ite_eq_right hc]
      calc
        _ = ((q ^ (k - 1) : ℕ) : ℝ) / (q : ℝ) :=
          (eq_div_iff hq0).2 hpowReal
        _ = ((q ^ (k - 1) : ℕ) : ℝ) * (1 / (q : ℝ)) := by ring
  calc
    _ = esBernoulliWeight β ω * Nat.card Good /
          esJointPartition β (pottsESEdgeAgreement V i) := hGoodProbability
    _ = (esBernoulliWeight β ω * Nat.card All /
          esJointPartition β (pottsESEdgeAgreement V i)) *
          (if R.r (pottsESOriginVertex V h0) none then
            (1 : ℝ) else 1 / (q : ℝ)) := by
      rw [hcountFactor]
      ring
    _ = configurationProbability (pottsESGraph V) θ
          (pottsESBoundaryCondition V) A *
          (if R.r (pottsESOriginVertex V h0) none then
            (1 : ℝ) else 1 / (q : ℝ)) := by
      rw [← hAllProbability, hFK]

/-- Corrected finite Edwards--Sokal magnetisation identity on the shell graph.
The random-cluster event uses the complete exterior shell wired together. -/
theorem pottsES_finite_magnetisation_identity_of_pos (V : Finset (ℤ × ℤ))
    (q : ℕ) (hq : 2 ≤ q) (β : ℝ) (hβ : 0 < β) (i : Fin q)
    (h0 : (0, 0) ∈ V) :
    pottsEventProb V β i (fun σ => σ (0, 0) = i) =
      1 / (q : ℝ) + (1 - 1 / (q : ℝ)) *
        pottsESOriginExteriorConnectionProbability V q (by omega) β hβ.le h0 := by
  classical
  let θ := pottsESParameters q β (by omega) hβ
  have hroot (σ : V → Fin q) :
      pottsExtend V i σ (0, 0) = i ↔ σ ⟨(0, 0), h0⟩ = i := by
    simp [pottsExtend, h0]
  calc
    pottsEventProb V β i (fun σ => σ (0, 0) = i) =
        ∑ σ : V → Fin q,
          if σ ⟨(0, 0), h0⟩ = i then pottsProb V β i σ else 0 := by
      unfold pottsEventProb
      apply Finset.sum_congr rfl
      intro σ _
      simp [hroot]
    _ = ∑ σ : V → Fin q,
          if σ ⟨(0, 0), h0⟩ = i then
            ∑ ω : (pottsESGraph V).edgeSet → Bool,
              esJointProbability β (pottsESEdgeAgreement V i) σ ω else 0 := by
      apply Finset.sum_congr rfl
      intro σ _
      by_cases hp : σ ⟨(0, 0), h0⟩ = i <;>
        simp [hp, esJointProbability_spin_marginal_potts]
    _ = ∑ ω : (pottsESGraph V).edgeSet → Bool,
          ∑ σ : V → Fin q,
            if σ ⟨(0, 0), h0⟩ = i then
              esJointProbability β (pottsESEdgeAgreement V i) σ ω else 0 := by
      have hpoint (σ : V → Fin q) :
          (if σ ⟨(0, 0), h0⟩ = i then
            ∑ ω : (pottsESGraph V).edgeSet → Bool,
              esJointProbability β (pottsESEdgeAgreement V i) σ ω else 0) =
            ∑ ω : (pottsESGraph V).edgeSet → Bool,
              if σ ⟨(0, 0), h0⟩ = i then
                esJointProbability β (pottsESEdgeAgreement V i) σ ω else 0 := by
        by_cases hp : σ ⟨(0, 0), h0⟩ = i <;> simp [hp]
      simp_rw [hpoint]
      rw [Finset.sum_comm]
    _ = ∑ ω : (pottsESGraph V).edgeSet → Bool,
          configurationProbability (pottsESGraph V) θ
            (pottsESBoundaryCondition V)
            (boolConfigurationEquiv (pottsESGraph V) ω) *
            (if pottsESOriginExteriorConnected V h0
                (boolConfigurationEquiv (pottsESGraph V) ω) then
              (1 : ℝ) else 1 / (q : ℝ)) := by
      apply Finset.sum_congr rfl
      intro ω _
      simpa [pottsESOriginExteriorConnected, θ] using
        pottsESJointProbability_origin_pin_bond V q hq β hβ i h0 ω
    _ = ∑ A : Configuration (pottsESGraph V),
          configurationProbability (pottsESGraph V) θ
            (pottsESBoundaryCondition V) A *
            (if pottsESOriginExteriorConnected V h0 A then
              (1 : ℝ) else 1 / (q : ℝ)) := by
      rw [Equiv.sum_comp (boolConfigurationEquiv (pottsESGraph V))
        (fun A : Configuration (pottsESGraph V) =>
          configurationProbability (pottsESGraph V) θ
            (pottsESBoundaryCondition V) A *
            (if pottsESOriginExteriorConnected V h0 A then
              (1 : ℝ) else 1 / (q : ℝ)))]
    _ = 1 / (q : ℝ) + (1 - 1 / (q : ℝ)) *
          pottsESOriginExteriorConnectionProbability V q (by omega) β hβ.le h0 := by
      have hterm (A : Configuration (pottsESGraph V)) :
          configurationProbability (pottsESGraph V) θ
              (pottsESBoundaryCondition V) A *
              (if pottsESOriginExteriorConnected V h0 A then
                (1 : ℝ) else 1 / (q : ℝ)) =
            (1 / (q : ℝ)) *
                configurationProbability (pottsESGraph V) θ
                  (pottsESBoundaryCondition V) A +
              (1 - 1 / (q : ℝ)) *
                (if pottsESOriginExteriorConnected V h0 A then
                  configurationProbability (pottsESGraph V) θ
                    (pottsESBoundaryCondition V) A else 0) := by
        by_cases hc : pottsESOriginExteriorConnected V h0 A <;>
          simp [hc] <;> ring
      simp_rw [hterm]
      rw [Finset.sum_add_distrib, ← Finset.mul_sum,
        ← Finset.mul_sum, sum_configurationProbability]
      simp [pottsESOriginExteriorConnectionProbability, θ, hβ]

/-- Corrected finite Edwards--Sokal magnetisation identity for every
nonnegative inverse temperature, with the zero-temperature endpoint defined
by the closed-bond random-cluster law. -/
theorem pottsES_finite_magnetisation_identity (V : Finset (ℤ × ℤ))
    (q : ℕ) (hq : 2 ≤ q) (β : ℝ) (hβ : 0 ≤ β) (i : Fin q)
    (h0 : (0, 0) ∈ V) :
    pottsEventProb V β i (fun σ => σ (0, 0) = i) =
      1 / (q : ℝ) + (1 - 1 / (q : ℝ)) *
        pottsESOriginExteriorConnectionProbability V q (by omega) β hβ h0 := by
  by_cases hpos : 0 < β
  · simpa [pottsESOriginExteriorConnectionProbability, hpos] using
      pottsES_finite_magnetisation_identity_of_pos V q hq β hpos i h0
  · have hzero : β = 0 := le_antisymm (le_of_not_gt hpos) hβ
    subst β
    rw [pottsES_finite_magnetisation_at_zero V q hq i h0]
    simp [pottsESOriginExteriorConnectionProbability]

end

end PottsContinuity.Thm1
