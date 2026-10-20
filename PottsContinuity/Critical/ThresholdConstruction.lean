module

public import PottsContinuity.Critical.PathEventLimits
public import PottsContinuity.Foundations.EveryExhaustion
public import PottsContinuity.Frozen.Defs

@[expose] public section

namespace PottsContinuity.Critical

open MeasureTheory Filter Topology
open PottsContinuity.PD.FK
open PottsContinuity.PD.RCInfinite

noncomputable section

/-- The canonical wired box limit, chosen from the proved uniqueness theorem. -/
def wiredBoxCanonicalLimit (θ : Parameters) : ProbabilityMeasure LatticeConfiguration :=
  Classical.choose (wiredBoxLimit_existsUnique θ)

theorem wiredBoxCanonicalLimit_tendsto (θ : Parameters) :
    Tendsto (fun n => wiredBoxProbabilityMeasure θ (0, 0) n) atTop
      (𝓝 (wiredBoxCanonicalLimit θ)) := by
  exact (Classical.choose_spec (wiredBoxLimit_existsUnique θ)).1
    (fun _ => (0, 0)) (fun n => n) origin_latticeBox_nested origin_latticeBox_exhaustive

private theorem wiredBoxCanonicalLimit_PD (θ : Parameters) :
    PottsContinuity.PD.IsRCInfiniteVolumeLimit θ.toP θ.toQ 1
      (wiredBoxCanonicalLimit θ).toMeasure :=
  isRCInfiniteVolumeLimit_of_wiredBox_tendsto θ (wiredBoxCanonicalLimit θ)
    (wiredBoxCanonicalLimit_tendsto θ)

private theorem wiredBoxCanonicalLimit_frozen (θ : Parameters) :
    PottsContinuity.IsRCInfiniteVolumeLimit θ.toP θ.toQ 1
      (wiredBoxCanonicalLimit θ).toMeasure :=
  PottsContinuity.Foundations.pd_interior_limit_all_exhaustions θ 1
    (wiredBoxCanonicalLimit θ).toMeasure (wiredBoxCanonicalLimit_PD θ)

def parametersAt (q : Set.Ici (1 : ℝ)) (p : Set.Ioo (0 : ℝ) 1) : Parameters :=
  { val := (q : ℝ)
    property := q.property
    edgeProbability := p }

def positiveParameterSet (q : Set.Ici (1 : ℝ)) : Set ℝ :=
  {p | ∃ θ : Parameters, θ.val = (q : ℝ) ∧ edgeParameter θ = p ∧
    0 < (wiredBoxCanonicalLimit θ : Measure LatticeConfiguration)
      (infiniteAt (0, 0))}

private theorem positiveParameterSet_lower_bound (q : Set.Ici (1 : ℝ))
    {p : ℝ} (hp : p ∈ positiveParameterSet q) :
    (1 / 8 : ℝ) < p := by
  obtain ⟨θ, hθq, hθp, hpositive⟩ := hp
  by_contra hnot
  have hpSmall : p ≤ 1 / 8 := le_of_not_gt hnot
  have hsmall : 4 * edgeParameter θ < 1 := by
    rw [hθp]
    linarith
  have hzero := limit_infiniteAt_zero_of_four_p_lt_one θ
    (wiredBoxCanonicalLimit θ).toMeasure (wiredBoxCanonicalLimit_PD θ) hsmall
  rw [hzero] at hpositive
  exact (lt_irrefl 0 hpositive)

private theorem allOpenLineReachable (n : ℕ) :
    (PottsContinuity.rcInfiniteOpenGraph (fun _ => true)).Reachable
      (0, 0) ((n : ℤ), 0) := by
  induction n with
  | zero => exact SimpleGraph.Reachable.refl _
  | succ n ih =>
      have hsq : squareLattice.Adj ((n : ℤ), 0) (((n + 1 : ℕ) : ℤ), 0) := by
        change |(n : ℤ) - ((n + 1 : ℕ) : ℤ)| + |(0 : ℤ) - 0| = 1
        simp
      have hadj : (PottsContinuity.rcInfiniteOpenGraph (fun _ => true)).Adj
          ((n : ℤ), 0) (((n + 1 : ℕ) : ℤ), 0) := by
        rw [PottsContinuity.rcInfiniteOpenGraph, SimpleGraph.fromEdgeSet_adj]
        constructor
        · exact ⟨squareLattice.mem_edgeSet.mpr hsq, rfl⟩
        · simp
      exact ih.trans hadj.reachable

private theorem allOpenClusterInfinite :
    {y | (PottsContinuity.rcInfiniteOpenGraph (fun _ => true)).Reachable
      (0, 0) y}.Infinite := by
  let f : ℕ → LatticeVertex := fun n => ((n : ℤ), 0)
  have hinj : Function.Injective f := by
    intro m n hmn
    have hfst := congrArg Prod.fst hmn
    exact Int.ofNat.inj hfst
  have hrange : (Set.range f).Infinite := Set.infinite_range_of_injective hinj
  apply hrange.mono
  intro y hy
  rcases hy with ⟨n, rfl⟩
  exact allOpenLineReachable n

private theorem allClosedCluster_not_infinite :
    ¬ {y | (PottsContinuity.rcInfiniteOpenGraph (fun _ => false)).Reachable
      (0, 0) y}.Infinite := by
  have hgraph : PottsContinuity.rcInfiniteOpenGraph (fun _ => false) = ⊥ := by
    ext x y
    simp [PottsContinuity.rcInfiniteOpenGraph, SimpleGraph.fromEdgeSet]
  have hcluster :
      {y | (PottsContinuity.rcInfiniteOpenGraph (fun _ => false)).Reachable
        (0, 0) y} = {(0, 0)} := by
    ext y
    rw [hgraph]
    simp
  rw [hcluster]
  simp

/-- For each `q ≥ 1`, the wired infinite-volume model has a genuine critical
parameter in `(0,1)`. -/
theorem exists_isRCCriticalPoint (q : Set.Ici (1 : ℝ)) :
    ∃ pc : ℝ, PottsContinuity.IsRCCriticalPoint q pc := by
  classical
  let S := positiveParameterSet q
  have hSlower : ∀ p ∈ S, (1 / 8 : ℝ) ≤ p := by
    intro p hp
    exact (positiveParameterSet_lower_bound q hp).le
  have hSbound : BddBelow S := ⟨1 / 8, hSlower⟩
  let θhi := highParameterForQ q
  have hhiMem : edgeParameter θhi ∈ S := by
    refine ⟨θhi, rfl, rfl, ?_⟩
    exact limit_infiniteAt_measure_pos_high q (wiredBoxCanonicalLimit θhi).toMeasure
      (wiredBoxCanonicalLimit_PD θhi)
  have hSne : S.Nonempty := ⟨edgeParameter θhi, hhiMem⟩
  let pc := sInf S
  have hpcLower : (1 / 8 : ℝ) ≤ pc :=
    le_csInf hSne (by intro p hp; exact hSlower p hp)
  have hpcUpper : pc ≤ edgeParameter θhi := csInf_le hSbound hhiMem
  have hpc : pc ∈ Set.Ioo (0 : ℝ) 1 := by
    constructor
    · linarith
    · exact lt_of_le_of_lt hpcUpper (edgeParameter_lt_one θhi)
  refine ⟨pc, ?_⟩
  unfold PottsContinuity.IsRCCriticalPoint
  refine ⟨hpc, ?_⟩
  intro p
  by_cases hp0 : (p : ℝ) = 0
  · have hp : p = (⟨0, by norm_num⟩ : Set.Icc (0 : ℝ) 1) := Subtype.ext hp0
    subst p
    let qpos : Set.Ioi (0 : ℝ) :=
      ⟨(q : ℝ), Set.mem_Ioi.mpr (lt_of_lt_of_le zero_lt_one q.property)⟩
    refine ⟨Measure.dirac (fun _ => false),
      PottsContinuity.Foundations.endpoint_isRCInfiniteVolumeLimit_all_exhaustions
        qpos 1 false, ?_, ?_⟩
    · intro _
      rw [Measure.dirac_apply]
      simp [allClosedCluster_not_infinite]
    · intro hpc0
      linarith [hpc.1]
  by_cases hp1 : (p : ℝ) = 1
  · have hp : p = (⟨1, by norm_num⟩ : Set.Icc (0 : ℝ) 1) := Subtype.ext hp1
    subst p
    let qpos : Set.Ioi (0 : ℝ) :=
      ⟨(q : ℝ), Set.mem_Ioi.mpr (lt_of_lt_of_le zero_lt_one q.property)⟩
    refine ⟨Measure.dirac (fun _ => true),
      PottsContinuity.Foundations.endpoint_isRCInfiniteVolumeLimit_all_exhaustions
        qpos 1 true, ?_, ?_⟩
    · intro h1pc
      linarith [hpc.2]
    · intro _
      rw [Measure.dirac_apply]
      simp [allOpenClusterInfinite]
  have hp0' : 0 < (p : ℝ) := lt_of_le_of_ne p.property.1 (Ne.symm hp0)
  have hp1' : (p : ℝ) < 1 := lt_of_le_of_ne p.property.2 hp1
  let θ := parametersAt q ⟨(p : ℝ), hp0', hp1'⟩
  let μ := (wiredBoxCanonicalLimit θ).toMeasure
  have hμFrozen := wiredBoxCanonicalLimit_frozen θ
  have hθq : θ.val = (q : ℝ) := rfl
  have hθp : edgeParameter θ = (p : ℝ) := rfl
  refine ⟨μ, hμFrozen, ?_, ?_⟩
  · intro hple
    have hnot : (p : ℝ) ∉ S := by
      intro hpS
      have hpcp : pc ≤ (p : ℝ) := csInf_le hSbound hpS
      linarith
    by_contra hne
    have hpos : 0 < (wiredBoxCanonicalLimit θ : Measure LatticeConfiguration)
        (infiniteAt (0, 0)) := pos_iff_ne_zero.mpr hne
    exact hnot ⟨θ, hθq, hθp, hpos⟩
  · intro hpcp
    obtain ⟨r, hrS, hrp⟩ := exists_lt_of_csInf_lt hSne hpcp
    obtain ⟨θr, hθrq, hθrp, hposr⟩ := hrS
    have hqeq : θr.val = θ.val := hθrq.trans hθq.symm
    have hpeq : edgeParameter θr ≤ edgeParameter θ := by
      rw [hθrp, hθp]
      exact hrp.le
    have hmono := wiredBoxLimit_infiniteAt_parameter_mono θr θ hqeq hpeq
      (wiredBoxCanonicalLimit θr) (wiredBoxCanonicalLimit θ)
      (wiredBoxCanonicalLimit_tendsto θr) (wiredBoxCanonicalLimit_tendsto θ)
    exact lt_of_lt_of_le hposr hmono

end
end PottsContinuity.Critical
