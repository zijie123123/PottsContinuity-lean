module

public import PottsContinuity.Thm1.FiniteESSignatureSums
public import PottsContinuity.Thm1.ShellBondLimit
public import PottsContinuity.Thm1.ShellFullSignatures

@[expose] public section

namespace PottsContinuity.Thm1

open Classical
open MeasureTheory Filter Topology
open PottsContinuity
open PottsContinuity.PD
open PottsContinuity.PD.FK
open PottsContinuity.PD.RCInfinite
open PottsContinuity.PD.CorrLength

noncomputable section

attribute [local instance] configurationMeasurableSpace

local instance pottsESSignatureConvVertexFintype (V : Finset (ℤ × ℤ)) :
    Fintype (PottsESVertex V) := Fintype.ofFinite _

local instance pottsESSignatureConvEdgeFintype (V : Finset (ℤ × ℤ)) :
    Fintype (pottsESGraph V).edgeSet := Fintype.ofFinite _

local instance pottsESSignatureConvConfigDecidableEq (V : Finset (ℤ × ℤ)) :
    DecidableEq (pottsESGraph V).edgeSet := Classical.decEq _

private theorem pottsESStatusAtomExit_measurable
    (V : Finset (ℤ × ℤ)) (x : ℤ × ℤ) :
    MeasurableSet (pottsESLatticeExitEventFrom V x) := by
  have hEq : pottsESLatticeExitEventFrom V x =
      ⋃ y : {y : ℤ × ℤ // y ∉ V},
        {ω | (PD.rcInfiniteOpenGraph ω).Reachable x y.1} := by
    ext ω
    simp only [pottsESLatticeExitEventFrom, Set.mem_ofPred_eq,
      Set.mem_iUnion, Subtype.exists, exists_prop]
  rw [hEq]
  exact MeasurableSet.iUnion fun y => measurableSet_open_reachable x y.1

private theorem pottsESStatusAtomPair_measurable
    (V : Finset (ℤ × ℤ)) (x y : ℤ × ℤ) :
    MeasurableSet (pottsESLatticePairRelationEvent V x y) := by
  rw [pottsESLatticePairRelationEvent]
  exact (measurableSet_open_reachable x y).union
    ((pottsESStatusAtomExit_measurable V x).inter
      (pottsESStatusAtomExit_measurable V y))

theorem pottsESStatusAtomEvent_measurable
    (V observed : Finset (ℤ × ℤ)) (s : pottsESStatusSignature observed) :
    MeasurableSet (pottsESStatusAtomEvent V observed s) := by
  rw [pottsESStatusAtomEvent, pottsESLatticeFullSignatureEvent]
  have hPairIntersection (Pairs : Finset ((ℤ × ℤ) × (ℤ × ℤ))) :
      MeasurableSet (pottsESLatticePairIntersectionEvent V Pairs) := by
    change MeasurableSet (⋂ p ∈ Pairs,
      pottsESLatticePairRelationEvent V p.1 p.2)
    exact Pairs.measurableSet_biInter fun p hp =>
      pottsESStatusAtomPair_measurable V p.1 p.2
  have hPairPattern (Positive Negative : Finset ((ℤ × ℤ) × (ℤ × ℤ))) :
      MeasurableSet (pottsESLatticePairPatternEvent V Positive Negative) := by
    rw [pottsESLatticePairPatternEvent]
    apply (hPairIntersection Positive).diff
    apply MeasurableSet.iUnion
    intro p
    apply MeasurableSet.iUnion
    intro hp
    exact hPairIntersection (Positive ∪ {p})
  have hPairGhostPattern (Positive Negative : Finset ((ℤ × ℤ) × (ℤ × ℤ)))
      (GhostSites : Finset (ℤ × ℤ)) :
      MeasurableSet
        (pottsESLatticePairGhostPatternEvent V Positive Negative GhostSites) := by
    rw [pottsESLatticePairGhostPatternEvent]
    exact (hPairPattern Positive Negative).inter
      (GhostSites.measurableSet_biInter fun x hx =>
        pottsESStatusAtomExit_measurable V x)
  apply (hPairGhostPattern
    (pottsESStatusPositivePairs observed s)
    (pottsESStatusNegativePairs observed s)
    (pottsESStatusGhostPositive observed s)).diff
  apply MeasurableSet.iUnion
  intro x
  apply MeasurableSet.iUnion
  intro hx
  exact hPairGhostPattern
    (pottsESStatusPositivePairs observed s)
    (pottsESStatusNegativePairs observed s)
    (pottsESStatusGhostPositive observed s ∪ {x})

theorem pottsESFiniteStatusAtom_mass_eq_shell_probability
    (V observed : Finset (ℤ × ℤ)) (θ : Parameters)
    (s : pottsESStatusSignature observed) :
    (∑ A : Configuration (pottsESGraph V),
      if pottsESObservedStatusSignature V observed A = s then
        configurationProbability (pottsESGraph V) θ (pottsESBoundaryCondition V) A
      else 0) =
      (pottsESShellBondProbabilityMeasure θ V :
        Measure LatticeConfiguration).real (pottsESStatusAtomEvent V observed s) := by
  classical
  have hEvent :
      {A : Configuration (pottsESGraph V) |
        pottsESShellBondExtension V A ∈ pottsESStatusAtomEvent V observed s} =
      {A | pottsESObservedStatusSignature V observed A = s} := by
    ext A
    exact pottsESObservedStatusSignature_mem_atom_iff V observed A s
  rw [Measure.real,
    pottsESShellBondProbabilityMeasure_apply θ V
      (pottsESStatusAtomEvent_measurable V observed s), hEvent,
    measure_apply]
  have hToReal : ENNReal.toReal
      (∑ A : Configuration (pottsESGraph V),
        {A | pottsESObservedStatusSignature V observed A = s}.indicator
          (law (pottsESGraph V) θ (pottsESBoundaryCondition V)) A) =
      ∑ A : Configuration (pottsESGraph V),
        if pottsESObservedStatusSignature V observed A = s then
          configurationProbability (pottsESGraph V) θ (pottsESBoundaryCondition V) A
        else 0 := by
    rw [show (∑ A : Configuration (pottsESGraph V),
        {A | pottsESObservedStatusSignature V observed A = s}.indicator
          (law (pottsESGraph V) θ (pottsESBoundaryCondition V)) A) =
      ∑ A ∈ (Finset.univ : Finset (Configuration (pottsESGraph V))),
        {A | pottsESObservedStatusSignature V observed A = s}.indicator
          (law (pottsESGraph V) θ (pottsESBoundaryCondition V)) A by simp]
    rw [ENNReal.toReal_sum (s := Finset.univ)
      (f := fun A : Configuration (pottsESGraph V) =>
        {A | pottsESObservedStatusSignature V observed A = s}.indicator
          (law (pottsESGraph V) θ (pottsESBoundaryCondition V)) A)
      (fun A hA => by
        by_cases hs : pottsESObservedStatusSignature V observed A = s
        · simp [Set.indicator, hs,
            (law (pottsESGraph V) θ (pottsESBoundaryCondition V)).apply_ne_top A]
        · simp [Set.indicator, hs])]
    apply Finset.sum_congr rfl
    intro A hA
    by_cases hs : pottsESObservedStatusSignature V observed A = s
    · simp [Set.indicator, hs, law_apply, ENNReal.toReal_ofReal,
        (configurationProbability_pos (pottsESGraph V) θ
          (pottsESBoundaryCondition V) A).le]
    · simp [Set.indicator, hs]
  exact hToReal.symm

theorem pottsESFiniteStatusAtom_mass_tendsto
    (θ : Parameters) (V : ℕ → Finset (ℤ × ℤ))
    (hNest : ∀ n, V n ⊆ V (n + 1))
    (hExhaust : ∀ x : ℤ × ℤ, ∃ n, x ∈ V n)
    (μ : Measure LatticeConfiguration)
    (hμ : PD.IsRCInfiniteVolumeLimit θ.toP θ.toQ 1 μ)
    (observed : Finset (ℤ × ℤ)) (s : pottsESStatusSignature observed) :
    Tendsto
      (fun n => ∑ A : Configuration (pottsESGraph (V n)),
        if pottsESObservedStatusSignature (V n) observed A = s then
          configurationProbability (pottsESGraph (V n)) θ
            (pottsESBoundaryCondition (V n)) A
        else 0)
      atTop
      (𝓝 (μ.real (pottsESConnectionInfiniteFullSignatureEvent
        (pottsESStatusPositivePairs observed s)
        (pottsESStatusNegativePairs observed s)
        (pottsESStatusGhostPositive observed s)
        (pottsESStatusGhostNegative observed s)))) := by
  have hShell := pottsESShellFullSignature_probability_tendsto θ V
    hNest hExhaust μ hμ
    (pottsESStatusPositivePairs observed s)
    (pottsESStatusNegativePairs observed s)
    (pottsESStatusGhostPositive observed s)
    (pottsESStatusGhostNegative observed s)
  have hEq :
      (fun n => ∑ A : Configuration (pottsESGraph (V n)),
        if pottsESObservedStatusSignature (V n) observed A = s then
          configurationProbability (pottsESGraph (V n)) θ
            (pottsESBoundaryCondition (V n)) A
        else 0) =ᶠ[atTop]
      (fun n =>
        (pottsESShellBondProbabilityMeasure θ (V n) :
          Measure LatticeConfiguration).real
          (pottsESStatusAtomEvent (V n) observed s)) := by
    filter_upwards with n
    exact pottsESFiniteStatusAtom_mass_eq_shell_probability (V n) observed θ s
  have hAtom := hShell.congr' hEq.symm
  simpa only [pottsESStatusAtomEvent] using hAtom

end

end PottsContinuity.Thm1
