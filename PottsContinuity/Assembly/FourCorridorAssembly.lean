module

public import PottsContinuity.Assembly.ExactRootRoutes
public import PottsContinuity.Thm3.RSW.BufferedAnnulusGluing
public import PottsContinuity.Thm3.RSW.FourCorridorCircuit
public import PottsContinuity.Thm3.Prop4.EvenSquareDecay

@[expose] public section

namespace PottsContinuity.Assembly

open MeasureTheory
open PottsContinuity
open PottsContinuity.PD.FK
open PottsContinuity.RSW

structure P4toP5RemainingInputs
    (q : Set.Ici (1 : ℝ))
    (μ : Measure (squareLattice.edgeSet → Bool)) where
  C : ℝ
  hC : 1 ≤ C
  hinduction1 : ∀ n : ℕ, 1 ≤ n →
    annulusProbability (selfDualParameters q) 8 (7*n) ≤
      C*(annulusProbability (selfDualParameters q) 8 n)^2
  ε₀ : ℝ
  hε₀ : 0 < ε₀
  hpair : ∀ ε : ℝ, 0 < ε → ε < ε₀ →
    ∃ A c : ℝ, 0 < A ∧ 0 < c ∧
      ∀ m : ℕ, 1 ≤ m →
        maxSquarePairProbability (selfDualParameters q) (2*m) ≤
          A * PottsContinuity.Thm3.Prop4.prop4PairKernel c ε
            (oneArmProbability μ) m

/-- The reduced source inputs needed to construct the P4-to-P5 geometry inputs
`P4toP5GeometryInputs` once their four-corridor, decay, and annulus-chain steps are
supplied. -/

def p4toP5RemainingGeometryProvider : Type :=
  ∀ (q : Set.Ici (1 : ℝ)) (p : Set.Icc (0 : ℝ) 1)
    (μ : Measure (squareLattice.edgeSet → Bool)),
    (p : ℝ) = Real.sqrt (q : ℝ) / (1 + Real.sqrt (q : ℝ)) →
    IsRCInfiniteVolumeLimit p
      ⟨(q : ℝ), Set.mem_Ioi.2 (lt_of_lt_of_le one_pos q.property)⟩ 0 μ →
    P4toP5RemainingInputs q μ

noncomputable def p4toP5GeometryProvider_of_remainingInputs
    (hremaining : p4toP5RemainingGeometryProvider) :
    p4toP5GeometryProvider := by
  intro q p μ hp hμ
  let inputs := hremaining q p μ hp hμ
  let θ := selfDualParameters q
  let qpos : Set.Ioi (0 : ℝ) :=
    ⟨(q : ℝ), Set.mem_Ioi.2 (lt_of_lt_of_le one_pos q.property)⟩
  have hpθ : p = θ.toP := by
    apply Subtype.ext
    simpa [θ, selfDualParameters, PottsContinuity.PD.FK.criticalParameters,
      PottsContinuity.PD.FK.Parameters.toP,
      PottsContinuity.PD.FK.edgeParameter,
      PottsContinuity.PD.rcCriticalParameter] using hp
  have hqθ : qpos = θ.toQ := by
    apply Subtype.ext
    rfl
  have hμθ : IsRCInfiniteVolumeLimit θ.toP θ.toQ 0 μ := by
    rw [← hpθ, ← hqθ]
    exact hμ
  have hdecayUpgrade :
      (∃ c₀ β : ℝ, 0 < c₀ ∧ 0 < β ∧ ∀ n : ℕ, 1 ≤ n →
        oneArmProbability μ n ≤ Real.exp (-c₀*(n:ℝ)^β)) →
      ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 1 ≤ n →
        oneArmProbability μ n ≤ Real.exp (-c*(n:ℝ)) := by
    rintro ⟨c₀, β, hc₀, hβ, hstretched⟩
    exact PottsContinuity.Thm3.Prop4.oneArm_exponential_of_evenSquarePairBound
      q μ hμθ β c₀ inputs.ε₀ hβ hc₀ inputs.hε₀ hstretched inputs.hpair
  exact {
    C := inputs.C
    hC := inputs.hC
    hinduction1 := inputs.hinduction1
    hfourCorridorCircuit := by
      intro n m hn hm hmn ω hTop hBottom hLeft hRight
      exact PottsContinuity.RSW.fourCorridor_annulusCircuitEvent
        n m hn hm hmn ω hTop hBottom hLeft hRight
    hdecayUpgrade := hdecayUpgrade
    hannulusChain := by
      intro α hα n m K hn hm hscale hspan hcover ω hcircuits
      exact PottsContinuity.RSW.buffered_annulus_chain_glues
        α hα n m K hn hm hscale hspan hcover ω hcircuits
  }

theorem hP4toP5_of_remainingGeometryProvider
    (hP4P5geom : p4toP5RemainingGeometryProvider) :
    ∀ (q : Set.Ici (1 : ℝ)) (p : Set.Icc (0 : ℝ) 1)
      (μ₀ : Measure (squareLattice.edgeSet → Bool)),
      (p : ℝ) = Real.sqrt (q : ℝ) / (1 + Real.sqrt (q : ℝ)) →
      IsRCInfiniteVolumeLimit p
        ⟨(q : ℝ), Set.mem_Ioi.mpr (lt_of_lt_of_le one_pos q.property)⟩ 0 μ₀ →
      assertionP4 μ₀ →
      assertionP5 p
        ⟨(q : ℝ), Set.mem_Ioi.mpr (lt_of_lt_of_le one_pos q.property)⟩ :=
  hP4toP5_of_geometryProvider
    (p4toP5GeometryProvider_of_remainingInputs hP4P5geom)

end PottsContinuity.Assembly
