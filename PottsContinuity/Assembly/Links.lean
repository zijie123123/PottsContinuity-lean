module

public import Mathlib
public import PottsContinuity.Frozen.Defs
public import PottsContinuity.Frozen.IsRCInfiniteVolumeLimitUnique
public import PottsContinuity.Frozen.IsRCCriticalPointUnique
public import PottsContinuity.Critical.ThresholdConstruction
public import PottsContinuity.Foundations.EveryExhaustion
public import PottsContinuity.Infinite.Bridge
public import PottsContinuity.Infinite.Symmetry
public import PottsContinuity.BD12.WiredSquare
public import PottsContinuity.BD12.CriticalValue
public import PottsContinuity.DualityExt.AnnulusCounterexample
public import PottsContinuity.PlanarTopology.SubpathExtraction
public import PottsContinuity.Thm3.Easy.P1ToP2DisconnectionBarrier
public import PottsContinuity.Thm3.Easy.P2ToP3Summability
public import PottsContinuity.Thm3.Easy.P2ToP3VerticalRSW
public import PottsContinuity.Thm3.Easy.P3ToP4
public import PottsContinuity.Thm3.Easy.P5ToP5a
public import PottsContinuity.Thm3.Easy.P5OneArmPower
public import PottsContinuity.Thm3.Easy.P5ToP1OfAnnulusTransfer
public import PottsContinuity.Thm3.Easy.P5FrameComparison
public import PottsContinuity.Thm3.RSW.P4GeometryConditional
public import PottsContinuity.Thm4Plane.ScreenPlaneAssembly
public import PottsContinuity.Thm4Plane.ScreenSideFactor
public import PottsContinuity.Thm4Plane.ScreenRecordAssembly
public import PottsContinuity.Thm3.Push.PushOfStripRSW
public import PottsContinuity.Thm4Plane.LogarithmicLimit16

@[expose] public section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace PottsContinuity.Assembly

open PottsContinuity
open PottsContinuity.PD.FK
open PottsContinuity.PD.RCInfinite
open PottsContinuity.RSW

/-! Exact formulations of the five frozen Theorem 3 assertions. -/

def assertionP1 (μ₁ : Measure (squareLattice.edgeSet → Bool)) : Prop :=
  μ₁ {ω | {y | (rcInfiniteOpenGraph ω).Reachable (0, 0) y}.Infinite} = 0

def assertionP2 (μ₀ μ₁ : Measure (squareLattice.edgeSet → Bool)) : Prop :=
  μ₀ = μ₁

def assertionP3 (μ₀ : Measure (squareLattice.edgeSet → Bool)) : Prop :=
  ∑' x : ℤ × ℤ, μ₀ {ω | (rcInfiniteOpenGraph ω).Reachable (0, 0) x} = ∞

def assertionP4 (μ₀ : Measure (squareLattice.edgeSet → Bool)) : Prop :=
  Tendsto
    (fun n : ℕ => 1 / (n : ℝ) * Real.log
      (μ₀.real {ω | ∃ y ∈ vertexBoundary (box n),
        (rcInfiniteOpenGraph ω).Reachable (0, 0) y}))
    atTop (𝓝 0)

def assertionP5 (p : Set.Icc (0 : ℝ) 1) (q : Set.Ioi (0 : ℝ)) : Prop :=
  ∀ α : ℝ, 0 < α → ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 1 ≤ n →
    c ≤ rcEventProb
      (latticeRectangle (-(n : ℤ)) ⌊(α + 1) * n⌋ (-(n : ℤ)) (2 * n))
      p q 0
      (horizontalCrossing
        (latticeRectangle (-(n : ℤ)) ⌊(α + 1) * n⌋ (-(n : ℤ)) (2 * n))
        0 ⌊α * n⌋ 0 n)

/-- The exact P1-to-P2 result `Thm3.Easy.p1_implies_p2`, in the Assembly link vocabulary. -/
theorem hP1toP2_of_disconnectionBarrier :
    ∀ (p : Set.Icc (0 : ℝ) 1)
      (_hp0 : 0 < (p : ℝ)) (_hp1 : (p : ℝ) < 1)
      (q : Set.Ioi (0 : ℝ)) (_hq : 1 ≤ (q : ℝ))
      (μ₀ μ₁ : Measure (squareLattice.edgeSet → Bool)),
      IsRCInfiniteVolumeLimit p q 0 μ₀ →
      IsRCInfiniteVolumeLimit p q 1 μ₁ →
      assertionP1 μ₁ → assertionP2 μ₀ μ₁ := by
  intro p hp0 hp1 q hq μ₀ μ₁ hμ₀ hμ₁ hP1
  exact PottsContinuity.Thm3.Easy.p1_implies_p2
    p q hp0 hp1 hq μ₀ μ₁ hμ₀ hμ₁ hP1

/-- The explicit inputs of the P4⇒P5 helper
`RSW.selfDual_P4_implies_P5_of_induction1_fourCorridorCircuit_decayUpgrade_annulusChain`:
the source annulus recurrence (Lemma 4), actual four-corridor circuit extraction,
corrected decay upgrade (Proposition 4), and actual buffered annulus-chain gluing. These
are premises about local events and estimates, not the P4⇒P5 conclusion itself. -/
structure P4toP5GeometryInputs
    (q : Set.Ici (1 : ℝ))
    (μ : Measure (squareLattice.edgeSet → Bool)) where
  C : ℝ
  hC : 1 ≤ C
  hinduction1 : ∀ n : ℕ, 1 ≤ n →
    annulusProbability (selfDualParameters q) 8 (7*n) ≤
      C*(annulusProbability (selfDualParameters q) 8 n)^2
  hfourCorridorCircuit : ∀ n m : ℕ, 1 ≤ n → 1 ≤ m → m < n → ∀ ω,
    horizontalCrossing (box (8*n)) (-2*(n:ℤ)) (2*(n:ℤ))
      ((n:ℤ)+1) ((n:ℤ)+1+(m:ℤ)) ω →
    horizontalCrossing (box (8*n)) (-2*(n:ℤ)) (2*(n:ℤ))
      (-(n:ℤ)-1-(m:ℤ)) (-(n:ℤ)-1) ω →
    finiteVerticalCrossing (box (8*n)) (-(n:ℤ)-1-(m:ℤ)) (-(n:ℤ)-1)
      (-2*(n:ℤ)) (2*(n:ℤ)) ω →
    finiteVerticalCrossing (box (8*n)) ((n:ℤ)+1) ((n:ℤ)+1+(m:ℤ))
      (-2*(n:ℤ)) (2*(n:ℤ)) ω →
    ω ∈ annulusCircuitEvent (box (8*n)) (0,0) n
  hdecayUpgrade :
    (∃ c₀ β : ℝ, 0 < c₀ ∧ 0 < β ∧ ∀ n : ℕ, 1 ≤ n →
      oneArmProbability μ n ≤ Real.exp (-c₀*(n:ℝ)^β)) →
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 1 ≤ n →
      oneArmProbability μ n ≤ Real.exp (-c*(n:ℝ))
  hannulusChain : ∀ α : ℝ, 0 < α → ∀ n m K : ℕ, 32 ≤ n → 1 ≤ m →
    ∀ (hscale : 16*m ≤ n)
      (hspan : (K*m:ℕ) ≤ ⌊α*(n:ℝ)⌋+(m:ℤ)),
    ⌊α*(n:ℝ)⌋ ≤ (K*m:ℕ) → ∀ ω,
    (∀ l : Fin (K+1),
      ω ∈ bufferedAnnulusChainLocalEvent α n m K hscale hspan l) →
    horizontalCrossing
      (latticeRectangle (-(n:ℤ)) ⌊(α+1)*(n:ℝ)⌋ (-(n:ℤ)) (2*(n:ℤ)))
      0 ⌊α*(n:ℝ)⌋ 0 n ω

/-- A family of the local P4⇒P5 inputs `P4toP5GeometryInputs`, available whenever
the exact explicit-value frozen free limit is. -/
def p4toP5GeometryProvider : Type :=
  ∀ (q : Set.Ici (1 : ℝ)) (p : Set.Icc (0 : ℝ) 1)
    (μ : Measure (squareLattice.edgeSet → Bool)),
    (p : ℝ) = Real.sqrt (q : ℝ) / (1 + Real.sqrt (q : ℝ)) →
    IsRCInfiniteVolumeLimit p
      ⟨(q : ℝ), Set.mem_Ioi.2 (lt_of_lt_of_le one_pos q.property)⟩ 0 μ →
    P4toP5GeometryInputs q μ

/-- Convert the conditional geometric P4⇒P5 assembly of `Thm3/RSW` to the exact frozen
P5 assertion. The source P4 and frozen-limit hypotheses are unchanged; only
its four remaining local inputs are bundled in `P4toP5GeometryInputs`. -/
theorem p4_implies_p5_of_geometryInputs
    (q : Set.Ici (1 : ℝ)) (p : Set.Icc (0 : ℝ) 1)
    (μ : Measure (squareLattice.edgeSet → Bool))
    (hp : (p : ℝ) = Real.sqrt (q : ℝ) / (1 + Real.sqrt (q : ℝ)))
    (hμ : IsRCInfiniteVolumeLimit p
      ⟨(q : ℝ), Set.mem_Ioi.2 (lt_of_lt_of_le one_pos q.property)⟩ 0 μ)
    (hP4 : assertionP4 μ)
    (inputs : P4toP5GeometryInputs q μ) :
    assertionP5 p
      ⟨(q : ℝ), Set.mem_Ioi.2 (lt_of_lt_of_le one_pos q.property)⟩ := by
  let θ : PottsContinuity.PD.FK.Parameters := selfDualParameters q
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
  have hrate : Tendsto
      (fun n : ℕ => 1 / (n : ℝ) * Real.log (oneArmProbability μ n))
      atTop (𝓝 0) := by
    simpa [assertionP4, oneArmProbability] using hP4
  have hbuffered := selfDual_P4_implies_P5_of_induction1_fourCorridorCircuit_decayUpgrade_annulusChain
    q μ hμθ inputs.C inputs.hC inputs.hinduction1 inputs.hfourCorridorCircuit
    inputs.hdecayUpgrade inputs.hannulusChain hrate
  have hP5θ : assertionP5 θ.toP θ.toQ := by
    intro α hα
    obtain ⟨c, hc, hprob⟩ := hbuffered α hα
    refine ⟨c, hc, ?_⟩
    intro n hn
    simpa [assertionP5, bufferedCrossingProbability] using hprob n hn
  simpa only [hpθ.symm, hqθ.symm] using hP5θ

/-- The exact weak-RSW adapter exported in Assembly, delegated to
`Thm3.Easy.wired_weakRSW_from_square`. -/
theorem wired_weakRSW_from_square (q : Set.Ici (1 : ℝ))
    (μ : Measure LatticeConfiguration)
    (hμ : PottsContinuity.PD.IsRCInfiniteVolumeLimit
      (PottsContinuity.PD.FK.criticalParameters q).toP
      (PottsContinuity.PD.FK.criticalParameters q).toQ 1 μ) :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 1 ≤ n →
      c ≤ μ.real (BD12.verticalRectangle (-(n : ℤ), 0) (2 * n) n) :=
  PottsContinuity.Thm3.Easy.wired_weakRSW_from_square q μ hμ

private theorem critical_point_with_self_dual_value
    (q : Set.Ici (1 : ℝ)) :
    ∃ pc : Set.Icc (0 : ℝ) 1,
      IsRCCriticalPoint q pc ∧
        (pc : ℝ) = Real.sqrt (q : ℝ) / (1 + Real.sqrt (q : ℝ)) := by
  have hvalue0 : 0 ≤ Real.sqrt (q : ℝ) / (1 + Real.sqrt (q : ℝ)) := by
    positivity
  have hvalue1 : Real.sqrt (q : ℝ) / (1 + Real.sqrt (q : ℝ)) ≤ 1 := by
    have hs : 0 ≤ Real.sqrt (q : ℝ) := Real.sqrt_nonneg _
    rw [div_le_one (by positivity : 0 < 1 + Real.sqrt (q : ℝ))]
    linarith
  let pc : Set.Icc (0 : ℝ) 1 :=
    ⟨Real.sqrt (q : ℝ) / (1 + Real.sqrt (q : ℝ)), hvalue0, hvalue1⟩
  refine ⟨pc, ?_, rfl⟩
  simpa [pc] using PottsContinuity.BD12.isRCCriticalPoint_sqrt q

/-- Conditional assembly of the frozen P1--P5 cycle at the genuine critical
parameter. P4⇒P5 and P5⇒P1 are hypotheses; the P1⇒P2 link `Thm3.Easy.p1_implies_p2`
is applied internally. P2⇒P3 uses `Thm3.Easy.p2_implies_p3_of_weakRSW` and derives
the weak-RSW estimate from the half-square bound `BD12.wired_square_crossing_ge_half`
and the wired-limit symmetries of `Infinite.Symmetry`; P3⇒P4 is discharged by
`Thm3.Easy.p3_implies_p4`. -/
theorem theorem_3_of_links
    (q : ℝ) (hq : 1 ≤ q)
    (hP4toP5 : ∀ (q : Set.Ici (1 : ℝ))
      (p : Set.Icc (0 : ℝ) 1)
      (μ₀ : Measure (squareLattice.edgeSet → Bool)),
      (p : ℝ) = Real.sqrt (q : ℝ) / (1 + Real.sqrt (q : ℝ)) →
      IsRCInfiniteVolumeLimit p
        ⟨(q : ℝ), Set.mem_Ioi.mpr (lt_of_lt_of_le one_pos q.property)⟩ 0 μ₀ →
      assertionP4 μ₀ →
      assertionP5 p
        ⟨(q : ℝ), Set.mem_Ioi.mpr (lt_of_lt_of_le one_pos q.property)⟩)
    (hP5toP1 : ∀ (q : Set.Ici (1 : ℝ))
      (p : Set.Icc (0 : ℝ) 1)
      (μ₁ : Measure (squareLattice.edgeSet → Bool)),
      (p : ℝ) = Real.sqrt (q : ℝ) / (1 + Real.sqrt (q : ℝ)) →
      IsRCInfiniteVolumeLimit p
        ⟨(q : ℝ), Set.mem_Ioi.mpr (lt_of_lt_of_le one_pos q.property)⟩ 1 μ₁ →
      assertionP5 p
        ⟨(q : ℝ), Set.mem_Ioi.mpr (lt_of_lt_of_le one_pos q.property)⟩ →
      assertionP1 μ₁) :
    ∃ (pc : Set.Icc (0 : ℝ) 1)
      (φ : Fin 2 → Measure (squareLattice.edgeSet → Bool)),
      IsRCCriticalPoint ⟨q, hq⟩ pc ∧
      (∀ i, IsRCInfiniteVolumeLimit pc ⟨q, lt_of_lt_of_le one_pos hq⟩ i (φ i)) ∧
      List.TFAE
        [ assertionP1 (φ 1),
          assertionP2 (φ 0) (φ 1),
          assertionP3 (φ 0),
          assertionP4 (φ 0),
          assertionP5 pc ⟨q, lt_of_lt_of_le one_pos hq⟩ ] := by
  let qI : Set.Ici (1 : ℝ) := ⟨q, hq⟩
  let qpos : Set.Ioi (0 : ℝ) := ⟨q, lt_of_lt_of_le one_pos hq⟩
  obtain ⟨pc, hpc, hpcValue⟩ := critical_point_with_self_dual_value qI
  obtain ⟨μ₀, hμ₀⟩ := Foundations.exists_isRCInfiniteVolumeLimit pc qpos hq 0
  obtain ⟨μ₁, hμ₁⟩ := Foundations.exists_isRCInfiniteVolumeLimit pc qpos hq 1
  have hp0 : 0 < (pc : ℝ) := hpc.1.1
  have hp1 : (pc : ℝ) < 1 := hpc.1.2
  have h12 : assertionP1 μ₁ → assertionP2 μ₀ μ₁ :=
    hP1toP2_of_disconnectionBarrier pc hp0 hp1 qpos hq μ₀ μ₁ hμ₀ hμ₁
  let θ : PottsContinuity.PD.FK.Parameters :=
    PottsContinuity.PD.FK.criticalParameters qI
  have hpcPD : pc = θ.toP := by
    apply Subtype.ext
    rw [hpcValue]
    rfl
  have hqPD : qpos = θ.toQ := by
    apply Subtype.ext
    rfl
  have hμ₀PD : PottsContinuity.PD.IsRCInfiniteVolumeLimit
      θ.toP θ.toQ 0 μ₀ := by
    rw [← hpcPD, ← hqPD]
    exact Infinite.isRCInfiniteVolumeLimit_to_PD_box pc qpos 0 μ₀ hμ₀
  have hμ₁PD : PottsContinuity.PD.IsRCInfiniteVolumeLimit
      θ.toP θ.toQ 1 μ₁ := by
    rw [← hpcPD, ← hqPD]
    exact Infinite.isRCInfiniteVolumeLimit_to_PD_box pc qpos 1 μ₁ hμ₁
  have hμ₀AtCriticalParameters : IsRCInfiniteVolumeLimit
      θ.toP θ.toQ 0 μ₀ := by
    rw [← hpcPD, ← hqPD]
    exact hμ₀
  have hμ₁AtCriticalParameters : IsRCInfiniteVolumeLimit
      θ.toP θ.toQ 1 μ₁ := by
    rw [← hpcPD, ← hqPD]
    exact hμ₁
  have h23 : assertionP2 μ₀ μ₁ → assertionP3 μ₀ := by
    intro hP2
    have hweakRSW := wired_weakRSW_from_square qI μ₁
      (by simpa only [θ] using hμ₁PD)
    exact Thm3.Easy.p2_implies_p3_of_weakRSW qI μ₀ μ₁
      (by simpa only [θ] using hμ₀AtCriticalParameters)
      (by simpa only [θ] using hμ₁AtCriticalParameters) hP2
      hweakRSW
  have h34 : assertionP3 μ₀ → assertionP4 μ₀ := by
    intro hP3
    exact Thm3.Easy.p3_implies_p4 pc hp0 hp1 qpos hq μ₀ hμ₀ hP3
  have h45 : assertionP4 μ₀ → assertionP5 pc qpos :=
    hP4toP5 qI pc μ₀ hpcValue hμ₀
  have h51 : assertionP5 pc qpos → assertionP1 μ₁ := by
    intro hP5
    exact hP5toP1 qI pc μ₁ hpcValue hμ₁ hP5
  have hcycle : List.TFAE
      [assertionP1 μ₁, assertionP2 μ₀ μ₁, assertionP3 μ₀,
        assertionP4 μ₀, assertionP5 pc qpos] := by
    tfae_have 1 → 2 := h12
    tfae_have 2 → 3 := h23
    tfae_have 3 → 4 := h34
    tfae_have 4 → 5 := h45
    tfae_have 5 → 1 := h51
    tfae_finish
  let φ : Fin 2 → Measure (squareLattice.edgeSet → Bool) :=
    fun i => if i = 0 then μ₀ else μ₁
  have hφ₀ : φ 0 = μ₀ := by simp [φ]
  have hφ₁ : φ 1 = μ₁ := by simp [φ]
  refine ⟨pc, φ, hpc, ?_, ?_⟩
  · intro i
    fin_cases i <;> simp [φ] <;> assumption
  · simpa only [hφ₀, hφ₁] using hcycle

/-- Conditional assembly of frozen Theorem 2 from the explicit-value
Theorem 4 free-limit P4, P4⇒P5, and P5⇒P1 link inputs. The free law is
identified with the wired/free witness using uniqueness of the frozen
every-exhaustion limit. -/
theorem theorem_2_of_links
    (q : ℝ) (hq : q ∈ Set.Icc (1 : ℝ) 4)
    (hTheorem4 : ∃ (p₄ : Set.Icc (0 : ℝ) 1)
      (μ₄ : Measure (squareLattice.edgeSet → Bool)),
      (p₄ : ℝ) = Real.sqrt q / (1 + Real.sqrt q) ∧
      IsRCInfiniteVolumeLimit p₄
        ⟨q, lt_of_lt_of_le one_pos hq.1⟩ 0 μ₄ ∧
      assertionP4 μ₄)
    (hP4toP5 : ∀ (q : Set.Ici (1 : ℝ))
      (p : Set.Icc (0 : ℝ) 1)
      (μ₀ : Measure (squareLattice.edgeSet → Bool)),
      (p : ℝ) = Real.sqrt (q : ℝ) / (1 + Real.sqrt (q : ℝ)) →
      IsRCInfiniteVolumeLimit p
        ⟨(q : ℝ), Set.mem_Ioi.mpr (lt_of_lt_of_le one_pos q.property)⟩ 0 μ₀ →
      assertionP4 μ₀ →
      assertionP5 p
        ⟨(q : ℝ), Set.mem_Ioi.mpr (lt_of_lt_of_le one_pos q.property)⟩)
    (hP5toP1 : ∀ (q : Set.Ici (1 : ℝ))
      (p : Set.Icc (0 : ℝ) 1)
      (μ₁ : Measure (squareLattice.edgeSet → Bool)),
      (p : ℝ) = Real.sqrt (q : ℝ) / (1 + Real.sqrt (q : ℝ)) →
      IsRCInfiniteVolumeLimit p
        ⟨(q : ℝ), Set.mem_Ioi.mpr (lt_of_lt_of_le one_pos q.property)⟩ 1 μ₁ →
      assertionP5 p
        ⟨(q : ℝ), Set.mem_Ioi.mpr (lt_of_lt_of_le one_pos q.property)⟩ →
      assertionP1 μ₁) :
    ∃ (pc : Set.Icc (0 : ℝ) 1)
      (φ₁ : Measure (squareLattice.edgeSet → Bool)),
      IsRCCriticalPoint ⟨q, hq.1⟩ pc ∧
      IsRCInfiniteVolumeLimit pc ⟨q, lt_of_lt_of_le one_pos hq.1⟩ 1 φ₁ ∧
      φ₁ {ω | {y | (rcInfiniteOpenGraph ω).Reachable (0, 0) y}.Infinite} = 0 := by
  let qI : Set.Ici (1 : ℝ) := ⟨q, hq.1⟩
  let qpos : Set.Ioi (0 : ℝ) := ⟨q, lt_of_lt_of_le one_pos hq.1⟩
  obtain ⟨pc, hpc, hpcValue⟩ := critical_point_with_self_dual_value qI
  obtain ⟨μ₀, hμ₀⟩ := Foundations.exists_isRCInfiniteVolumeLimit pc qpos hq.1 0
  obtain ⟨μ₁, hμ₁⟩ := Foundations.exists_isRCInfiniteVolumeLimit pc qpos hq.1 1
  obtain ⟨p₄, μ₄, hp₄Value, hμ₄, hP4₄⟩ := hTheorem4
  have hp₄pc : p₄ = pc := by
    apply Subtype.ext
    rw [hp₄Value, hpcValue]
  have hμ₄pc : IsRCInfiniteVolumeLimit pc qpos 0 μ₄ := by
    rw [← hp₄pc]
    exact hμ₄
  have hμ₀eqμ₄ : μ₀ = μ₄ :=
    isRCInfiniteVolumeLimit_unique pc qpos 0 μ₀ μ₄ hμ₀ hμ₄pc
  have hP4₀ : assertionP4 μ₀ := by
    rw [hμ₀eqμ₄]
    exact hP4₄
  have hP5 : assertionP5 pc qpos :=
    hP4toP5 qI pc μ₀ hpcValue hμ₀ hP4₀
  have hP1 : assertionP1 μ₁ :=
    hP5toP1 qI pc μ₁ hpcValue hμ₁ hP5
  refine ⟨pc, μ₁, ?_, hμ₁, hP1⟩
  simpa [qI] using hpc

end PottsContinuity.Assembly
