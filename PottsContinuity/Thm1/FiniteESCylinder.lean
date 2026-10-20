module

public import PottsContinuity.Thm1.FiniteESMagnetisation

@[expose] public section

namespace PottsContinuity.Thm1

open Classical
open PottsContinuity
open PottsContinuity.PD.FK

noncomputable section

local instance pottsESCylinderVertexFintype (V : Finset (ℤ × ℤ)) :
    Fintype (PottsESVertex V) := Fintype.ofFinite _

local instance pottsESCylinderEdgeFintype (V : Finset (ℤ × ℤ)) :
    Fintype (pottsESGraph V).edgeSet := Fintype.ofFinite _

local instance pottsESCylinderConfigDecidableEq (V : Finset (ℤ × ℤ)) :
    DecidableEq (pottsESGraph V).edgeSet := Classical.decEq _

/-- Spin assignments compatible with the open edges and a prescribed cylinder
pattern. -/
def pottsESPatternColorings (V : Finset (ℤ × ℤ)) {q : ℕ} (i : Fin q)
    (observed : Finset (ℤ × ℤ)) (ξ : ℤ × ℤ → Fin q)
    (A : Configuration (pottsESGraph V)) :=
  {σ : V → Fin q // pottsESCompatible V i A σ ∧
    ∀ x ∈ observed, pottsExtend V i σ x = ξ x}

/-- Conditional probability of a finite spin pattern given the open-component
partition of the ghost-wired shell graph. -/
def pottsESConnectivityPatternFunctional (V : Finset (ℤ × ℤ))
    {q : ℕ} (i : Fin q) (observed : Finset (ℤ × ℤ))
    (ξ : ℤ × ℤ → Fin q) (A : Configuration (pottsESGraph V)) : ℝ :=
  (Nat.card (pottsESPatternColorings V i observed ξ A) : ℝ) /
    (Nat.card {σ : V → Fin q // pottsESCompatible V i A σ} : ℝ)

/-- The finite Potts cylinder probability is the wired FK expectation of the
component-coloring pattern fraction. -/
theorem pottsES_cylinder_event_joint_law (V : Finset (ℤ × ℤ))
    (q : ℕ) (hq : 1 ≤ q) (β : ℝ) (i : Fin q)
    (observed : Finset (ℤ × ℤ)) (ξ : ℤ × ℤ → Fin q) :
    pottsEventProb V β i (fun σ => ∀ x ∈ observed, σ x = ξ x) =
      ∑ ω : (pottsESGraph V).edgeSet → Bool,
        (∑ σ : V → Fin q,
          esJointProbability β (pottsESEdgeAgreement V i) σ ω) *
          pottsESConnectivityPatternFunctional V i observed ξ
            (boolConfigurationEquiv (pottsESGraph V) ω) := by
  classical
  let : Nonempty (V → Fin q) := ⟨fun _ => i⟩
  let sat := pottsESEdgeAgreement V i
  let pattern : (V → Fin q) → Prop :=
    fun σ => ∀ x ∈ observed, pottsExtend V i σ x = ξ x
  let compatible (ω : (pottsESGraph V).edgeSet → Bool) :=
    {σ : V → Fin q // ∀ e, ω e = true → pottsESEdgeAgreement V i σ e}
  have hcompatible_pos (ω : (pottsESGraph V).edgeSet → Bool) :
      0 < Nat.card (compatible ω) := by
    rw [show compatible ω = {σ : V → Fin q //
      ∀ e, ω e = true → pottsESEdgeAgreement V i σ e} from rfl]
    rw [pottsESBoolCompatibleColorings_count]
    exact Nat.pow_pos (by omega)
  have hpartition : esJointPartition β sat ≠ 0 :=
    (esJointPartition_pos β sat).ne'
  have hpatternSum (ω : (pottsESGraph V).edgeSet → Bool) :
      (∑ σ : V → Fin q,
        if pattern σ then esJointProbability β sat σ ω else 0) =
        (∑ σ : V → Fin q, esJointProbability β sat σ ω) *
          pottsESConnectivityPatternFunctional V i observed ξ
            (boolConfigurationEquiv (pottsESGraph V) ω) := by
    let all := compatible ω
    let good : Type := {σ : V → Fin q //
      (∀ e, ω e = true → pottsESEdgeAgreement V i σ e) ∧ pattern σ}
    let goodPattern : Type := pottsESPatternColorings V i observed ξ
      (boolConfigurationEquiv (pottsESGraph V) ω)
    let C := boolConfigurationEquiv (pottsESGraph V) ω
    have hallcount : Nat.card all =
        Nat.card {σ : V → Fin q // pottsESCompatible V i C σ} := by
      rw [show all = {σ : V → Fin q //
        ∀ e, ω e = true → pottsESEdgeAgreement V i σ e} from rfl]
      rw [Nat.card_congr (pottsESBoolCompatibleColoringEquiv V i ω)]
    have hgoodcount : Nat.card good = Nat.card goodPattern := by
      apply Nat.card_congr
      exact
        { toFun := fun σ => ⟨σ.1,
            (pottsESCompatible_bool_iff V i σ.1 ω).2 σ.2.1, σ.2.2⟩
          invFun := fun σ => ⟨σ.1,
            (pottsESCompatible_bool_iff V i σ.1 ω).1 σ.2.1, σ.2.2⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
    have hgood := sum_esJointProbability_spins_pinned β sat ω pattern
    have hbase :
        (∑ σ : V → Fin q,
          if pattern σ then esJointProbability β sat σ ω else 0) =
        esBernoulliWeight β ω * (Nat.card good : ℝ) /
          esJointPartition β sat := by
      simpa [sat, good, pattern] using hgood
    have hall' :
        (∑ σ : V → Fin q, esJointProbability β sat σ ω) =
          esBernoulliWeight β ω * (Nat.card all : ℝ) /
            esJointPartition β sat := by
      simp only [esJointProbability, ← Finset.sum_div,
        sum_esJointWeight_spins]
      rfl
    have hcardAll : (Nat.card all : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt (hcompatible_pos ω))
    have hcardRatio :
        (Nat.card good : ℝ) / (Nat.card all : ℝ) =
          pottsESConnectivityPatternFunctional V i observed ξ C := by
      unfold pottsESConnectivityPatternFunctional
      rw [← hgoodcount, ← hallcount]
    have hprobRatio :
        (esBernoulliWeight β ω * (Nat.card good : ℝ) /
            esJointPartition β sat) =
          (esBernoulliWeight β ω * (Nat.card all : ℝ) /
            esJointPartition β sat) *
              pottsESConnectivityPatternFunctional V i observed ξ C := by
      rw [← hcardRatio]
      field_simp [hpartition, hcardAll]
    calc
      _ = esBernoulliWeight β ω * (Nat.card good : ℝ) /
            esJointPartition β sat := hbase
      _ = (∑ σ : V → Fin q, esJointProbability β sat σ ω) *
            pottsESConnectivityPatternFunctional V i observed ξ C := by
        rw [← hall'] at hprobRatio
        exact hprobRatio
  calc
    pottsEventProb V β i (fun σ => ∀ x ∈ observed, σ x = ξ x) =
        ∑ σ : V → Fin q,
          if pattern σ then pottsProb V β i σ else 0 := by
      unfold pottsEventProb
      apply Finset.sum_congr rfl
      intro σ _
      simp [pattern, pottsExtend]
    _ = ∑ ω : (pottsESGraph V).edgeSet → Bool,
          ∑ σ : V → Fin q,
            if pattern σ then esJointProbability β sat σ ω else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro σ _
      by_cases hp : pattern σ
      · simp only [ite_eq_left hp]
        exact (esJointProbability_spin_marginal_potts V β i σ).symm
      · simp [hp]
    _ = ∑ ω : (pottsESGraph V).edgeSet → Bool,
          (∑ σ : V → Fin q,
            esJointProbability β sat σ ω) *
            pottsESConnectivityPatternFunctional V i observed ξ
              (boolConfigurationEquiv (pottsESGraph V) ω) := by
      apply Finset.sum_congr rfl
      intro ω _
      exact hpatternSum ω

/-- For positive inverse temperature, the cylinder formula is the expectation
under the finite FK law on the shell graph. -/
theorem pottsES_cylinder_event_connectivity_pattern (V : Finset (ℤ × ℤ))
    (q : ℕ) (hq : 1 ≤ q) (β : ℝ) (hβ : 0 < β) (i : Fin q)
    (observed : Finset (ℤ × ℤ)) (ξ : ℤ × ℤ → Fin q) :
    pottsEventProb V β i (fun σ => ∀ x ∈ observed, σ x = ξ x) =
      ∑ A : Configuration (pottsESGraph V),
        configurationProbability (pottsESGraph V)
          (pottsESParameters q β hq hβ) (pottsESBoundaryCondition V) A *
          pottsESConnectivityPatternFunctional V i observed ξ A := by
  rw [pottsES_cylinder_event_joint_law V q hq β i observed ξ]
  calc
    _ = ∑ ω : (pottsESGraph V).edgeSet → Bool,
          configurationProbability (pottsESGraph V)
              (pottsESParameters q β hq hβ) (pottsESBoundaryCondition V)
              (boolConfigurationEquiv (pottsESGraph V) ω) *
            pottsESConnectivityPatternFunctional V i observed ξ
              (boolConfigurationEquiv (pottsESGraph V) ω) := by
      apply Finset.sum_congr rfl
      intro ω _
      rw [esJointProbability_bond_marginal_fk V q hq β hβ i ω]
    _ = _ := by
      rw [Equiv.sum_comp (boolConfigurationEquiv (pottsESGraph V))
        (fun A : Configuration (pottsESGraph V) =>
          configurationProbability (pottsESGraph V)
            (pottsESParameters q β hq hβ) (pottsESBoundaryCondition V) A *
          pottsESConnectivityPatternFunctional V i observed ξ A)]

end

end PottsContinuity.Thm1
