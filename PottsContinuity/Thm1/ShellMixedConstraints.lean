module

public import PottsContinuity.Thm1.ShellLocalComparison
public import PottsContinuity.PD.RCInfinite.BurtonKeane
public import PottsContinuity.PD.CorrLength.ConnectionEvents
public import Mathlib.MeasureTheory.Measure.Continuity

@[expose] public section

namespace PottsContinuity.Thm1

open MeasureTheory Filter Topology
open PottsContinuity
open PottsContinuity.PD
open PottsContinuity.PD.FK
open PottsContinuity.PD.RCInfinite
open PottsContinuity.PD.CorrLength

noncomputable section

attribute [local instance] configurationMeasurableSpace

/-- Simultaneous shell relations and ghost-component memberships. -/
def pottsESLatticeMixedConstraintEvent (V : Finset (ℤ × ℤ))
    (Pairs : Finset ((ℤ × ℤ) × (ℤ × ℤ)))
    (GhostSites : Finset (ℤ × ℤ)) : Set LatticeConfiguration :=
  pottsESLatticePairIntersectionEvent V Pairs ∩
    ⋂ x ∈ GhostSites, pottsESLatticeExitEventFrom V x

/-- The corresponding physical connections and infinite-cluster memberships. -/
def pottsESConnectionInfiniteConstraintEvent
    (Pairs : Finset ((ℤ × ℤ) × (ℤ × ℤ)))
    (GhostSites : Finset (ℤ × ℤ)) : Set LatticeConfiguration :=
  pottsESConnectionIntersectionEvent Pairs ∩
    ⋂ x ∈ GhostSites, infiniteAt x

private theorem pottsESMixed_exit_iInter_eq
    (V : ℕ → Finset (ℤ × ℤ))
    (hNest : ∀ n, V n ⊆ V (n + 1))
    (hExhaust : ∀ x : ℤ × ℤ, ∃ n, x ∈ V n)
    (x : ℤ × ℤ) :
    (⋂ n, pottsESLatticeExitEventFrom (V n) x) = infiniteAt x := by
  have hMono : Monotone V := by
    intro m n hmn
    induction n generalizing m with
    | zero =>
      have hm : m = 0 := by omega
      subst m
      exact Finset.Subset.rfl
    | succ n ih =>
      by_cases hmn' : m ≤ n
      · exact (ih hmn').trans (hNest n)
      · have hm : m = n + 1 := by omega
        subst m
        exact Finset.Subset.rfl
  have hContained (F : Finset (ℤ × ℤ)) : ∃ n, F ⊆ V n := by
    induction F using Finset.induction_on with
    | empty => exact ⟨0, Finset.empty_subset _⟩
    | @insert z F hz ih =>
      obtain ⟨m, hm⟩ := ih
      obtain ⟨n, hn⟩ := hExhaust z
      refine ⟨max m n, ?_⟩
      intro y hy
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact hMono (Nat.le_max_right m n) hn
      · exact hMono (Nat.le_max_left m n) (hm hy)
  ext ω
  simp only [Set.mem_iInter]
  constructor
  · intro hω
    apply (infinite_cluster_iff ω x).2
    intro F
    obtain ⟨n, hn⟩ := hContained F
    obtain ⟨y, hy, hreach⟩ := hω n
    exact ⟨y, fun hyF => hy (hn hyF), hreach⟩
  · intro hω n
    have hinf : (cluster ω x).Infinite := by
      simpa [infiniteAt] using hω
    obtain ⟨y, hy, hreach⟩ := (infinite_cluster_iff ω x).mp hinf (V n)
    exact ⟨y, hy, hreach⟩

/-- A decreasing family of local increasing shell events converges in
probability whenever its intersection agrees almost surely with the target. -/
theorem pottsESShellDecreasingCylinderProbability_tendsto
    (θ : Parameters) (V : ℕ → Finset (ℤ × ℤ))
    (hNest : ∀ n, V n ⊆ V (n + 1))
    (hExhaust : ∀ x : ℤ × ℤ, ∃ n, x ∈ V n)
    (μ : Measure LatticeConfiguration)
    (hμ : PD.IsRCInfiniteVolumeLimit θ.toP θ.toQ 1 μ)
    (E : ℕ → Set LatticeConfiguration)
    (hMeas : ∀ n, MeasurableSet (E n))
    (hAntitone : Antitone E)
    (N : ℕ)
    (hCylinder : ∀ n, N ≤ n → IsCylinder (E n))
    (hDepends : ∀ n, N ≤ n → DependsOn
      (pottsESLatticeEdgeSet (V n) : Set PottsContinuity.PD.FK.squareLattice.edgeSet) (E n))
    (hUpper : ∀ n, N ≤ n → IsUpperSet (E n))
    (EInf : Set LatticeConfiguration)
    (hInterAE : (⋂ n, E n) =ᵐ[μ] EInf) :
    Tendsto
      (fun n => (pottsESShellBondProbabilityMeasure θ (V n) :
        Measure LatticeConfiguration).real (E n))
      atTop (𝓝 (μ.real EInf)) := by
  classical
  let : IsProbabilityMeasure μ := hμ.1
  let ν : ProbabilityMeasure LatticeConfiguration := ⟨μ, hμ.1⟩
  let νn : ℕ → ProbabilityMeasure LatticeConfiguration :=
    fun n => pottsESShellBondProbabilityMeasure θ (V n)
  have hWeak : Tendsto νn atTop (𝓝 ν) := by
    simpa only [νn, ν] using
      pottsESShellBondProbabilityMeasure_tendsto θ V hNest hExhaust μ hμ
  have hFinite : ∃ n, μ (E n) ≠ ⊤ := ⟨0, measure_ne_top μ (E 0)⟩
  have hENN : Tendsto (fun n => μ (E n)) atTop
      (𝓝 (μ (⋂ n, E n))) := by
    exact tendsto_measure_iInter_atTop
      (fun n => (hMeas n).nullMeasurableSet) hAntitone hFinite
  have hReal : Tendsto (fun n => μ.real (E n)) atTop
      (𝓝 (μ.real (⋂ n, E n))) := by
    have h := (ENNReal.continuousAt_toReal
      (measure_ne_top μ (⋂ n, E n))).tendsto.comp hENN
    simpa only [Function.comp_def, Measure.real_def] using h
  have hTarget : μ.real (⋂ n, E n) = μ.real EInf :=
    measureReal_congr hInterAE
  have hRealTarget : Tendsto (fun n => μ.real (E n)) atTop
      (𝓝 (μ.real EInf)) := by
    simpa only [hTarget] using hReal
  have hProbabilityReal (S : Set LatticeConfiguration)
      (hS : IsClopen S) :
      Tendsto (fun n => (νn n : Measure LatticeConfiguration).real S)
        atTop (𝓝 (μ.real S)) := by
    have hMeasure := ProbabilityMeasure.tendsto_measure_of_isClopen_of_tendsto
      hWeak hS
    have hCoe := (NNReal.continuous_coe.continuousAt.tendsto).comp hMeasure
    have hCoe' : Tendsto (fun n => ((νn n S : NNReal) : ℝ)) atTop
        (𝓝 (((ν S : NNReal) : ℝ))) := by
      simpa only [Function.comp_def] using hCoe
    have hMeasureRealEq (T : Set LatticeConfiguration) :
        μ.real T = ((ν T : NNReal) : ℝ) := by
      change (ν : Measure LatticeConfiguration).real T = _
      exact ProbabilityMeasure.measureReal_eq_coe_coeFn ν T
    have hSeq : (fun n => (νn n : Measure LatticeConfiguration).real S) =
        fun n => ((νn n S : NNReal) : ℝ) := by
      funext n
      exact ProbabilityMeasure.measureReal_eq_coe_coeFn (νn n) S
    rw [hSeq]
    simpa only [hMeasureRealEq] using hCoe'
  have hLower : ∀ᶠ n : ℕ in atTop,
      μ.real (E n) ≤
        (pottsESShellBondProbabilityMeasure θ (V n) :
          Measure LatticeConfiguration).real (E n) := by
    filter_upwards [Filter.eventually_atTop.2 ⟨N, fun n hn => hn⟩]
      with n hn
    exact pottsESShellUpperCylinder_lower_bound θ μ hμ (V n) (E n)
      (hCylinder n hn) (hDepends n hn) (hUpper n hn)
  apply tendsto_order.2
  constructor
  · intro a ha
    let c := (a + μ.real EInf) / 2
    have hac : a < c := by dsimp [c]; linarith
    have hcTarget : c < μ.real EInf := by dsimp [c]; linarith
    have hMuTail := (tendsto_order.1 hRealTarget).1 c hcTarget
    filter_upwards [hMuTail, hLower] with n hn hle
    exact lt_of_lt_of_le (lt_trans hac hn) hle
  · intro b hb
    let c := (μ.real EInf + b) / 2
    have hTargetC : μ.real EInf < c := by dsimp [c]; linarith
    have hcB : c < b := by dsimp [c]; linarith
    have hMuTail := (tendsto_order.1 hRealTarget).2 c hTargetC
    obtain ⟨K, hK⟩ := Filter.eventually_atTop.1 hMuTail
    let k := max N K
    have hkN : N ≤ k := Nat.le_max_left N K
    have hkK : K ≤ k := Nat.le_max_right N K
    have hMuK : μ.real (E k) < c := hK k hkK
    have hFixed := hProbabilityReal (E k) ((hCylinder k hkN).isClopen)
    have hProbTail := (tendsto_order.1 hFixed).2 b (lt_trans hMuK hcB)
    have hIndex : ∀ᶠ n : ℕ in atTop, k ≤ n :=
      Filter.eventually_atTop.2 ⟨k, fun n hn => hn⟩
    filter_upwards [hProbTail, hIndex] with n hn hkn
    have hSubset : E n ⊆ E k := hAntitone (by exact hkn)
    have hMonoMeasure :
        (pottsESShellBondProbabilityMeasure θ (V n) :
          Measure LatticeConfiguration).real (E n) ≤
        (pottsESShellBondProbabilityMeasure θ (V n) :
          Measure LatticeConfiguration).real (E k) :=
      measureReal_mono hSubset
    exact lt_of_le_of_lt hMonoMeasure hn

/-- The exact decreasing intersection of the shell mixed constraints before
using uniqueness of the infinite cluster. -/
private theorem pottsESLatticeMixedConstraintEvent_iInter_eq
    (V : ℕ → Finset (ℤ × ℤ))
    (hNest : ∀ n, V n ⊆ V (n + 1))
    (hExhaust : ∀ x : ℤ × ℤ, ∃ n, x ∈ V n)
    (Pairs : Finset ((ℤ × ℤ) × (ℤ × ℤ)))
    (GhostSites : Finset (ℤ × ℤ)) :
    (⋂ n, pottsESLatticeMixedConstraintEvent (V n) Pairs GhostSites) =
      (⋂ p ∈ Pairs,
        {ω | (PD.rcInfiniteOpenGraph ω).Reachable p.1 p.2 ∨
          (ω ∈ infiniteAt p.1 ∧ ω ∈ infiniteAt p.2)}) ∩
        ⋂ x ∈ GhostSites, infiniteAt x := by
  ext ω
  simp only [Set.mem_iInter, pottsESLatticeMixedConstraintEvent,
    pottsESLatticePairIntersectionEvent, Set.mem_inter_iff,
    Set.mem_iInter]
  constructor
  · intro h
    constructor
    · intro p hp
      have hPair : ∀ n, ω ∈ pottsESLatticePairRelationEvent (V n) p.1 p.2 :=
        fun n => (h n).1 p hp
      have hPairSet : ω ∈ ⋂ n,
          pottsESLatticePairRelationEvent (V n) p.1 p.2 := by
        simpa only [Set.mem_iInter] using hPair
      rw [pottsESLatticePairRelationEvent_iInter_eq
        V hNest hExhaust p.1 p.2] at hPairSet
      simpa only [Set.mem_ofPred_eq] using hPairSet
    · intro x hx
      have hExit : ∀ n, ω ∈ pottsESLatticeExitEventFrom (V n) x :=
        fun n => (h n).2 x hx
      have hExitSet : ω ∈ ⋂ n, pottsESLatticeExitEventFrom (V n) x := by
        simpa only [Set.mem_iInter] using hExit
      rw [pottsESMixed_exit_iInter_eq V hNest hExhaust x] at hExitSet
      exact hExitSet
  · intro h n
    constructor
    · intro p hp
      have hPairSet : ω ∈ ⋂ n,
          pottsESLatticePairRelationEvent (V n) p.1 p.2 := by
        rw [pottsESLatticePairRelationEvent_iInter_eq
          V hNest hExhaust p.1 p.2]
        exact h.1 p hp
      exact (Set.mem_iInter.mp hPairSet) n
    · intro x hx
      have hExitSet : ω ∈ ⋂ n, pottsESLatticeExitEventFrom (V n) x := by
        rw [pottsESMixed_exit_iInter_eq V hNest hExhaust x]
        exact h.2 x hx
      exact (Set.mem_iInter.mp hExitSet) n


private theorem pottsESMixed_exit_measurable
    (V : Finset (ℤ × ℤ)) (x : ℤ × ℤ) :
    MeasurableSet (pottsESLatticeExitEventFrom V x) := by
  have hEq : pottsESLatticeExitEventFrom V x =
      ⋃ y : {y : ℤ × ℤ // y ∉ V},
        {ω | (PD.rcInfiniteOpenGraph ω).Reachable x y.val} := by
    ext ω
    simp only [pottsESLatticeExitEventFrom, Set.mem_ofPred_eq,
      Set.mem_iUnion, Subtype.exists, exists_prop]
  rw [hEq]
  exact MeasurableSet.iUnion fun y => measurableSet_open_reachable x y.val

private theorem pottsESMixed_pair_measurable
    (V : Finset (ℤ × ℤ)) (x y : ℤ × ℤ) :
    MeasurableSet (pottsESLatticePairRelationEvent V x y) := by
  rw [pottsESLatticePairRelationEvent]
  exact (measurableSet_open_reachable x y).union
    ((pottsESMixed_exit_measurable V x).inter
      (pottsESMixed_exit_measurable V y))

private theorem pottsESMixed_event_measurable
    (V : Finset (ℤ × ℤ))
    (Pairs : Finset ((ℤ × ℤ) × (ℤ × ℤ)))
    (GhostSites : Finset (ℤ × ℤ)) :
    MeasurableSet (pottsESLatticeMixedConstraintEvent V Pairs GhostSites) := by
  have hPairs : MeasurableSet (pottsESLatticePairIntersectionEvent V Pairs) := by
    change MeasurableSet (⋂ p ∈ Pairs,
      pottsESLatticePairRelationEvent V p.1 p.2)
    exact Pairs.measurableSet_biInter fun p hp =>
      pottsESMixed_pair_measurable V p.1 p.2
  have hGhost : MeasurableSet (⋂ x ∈ GhostSites,
      pottsESLatticeExitEventFrom V x) :=
    GhostSites.measurableSet_biInter fun x hx =>
      pottsESMixed_exit_measurable V x
  exact hPairs.inter hGhost

private theorem pottsESMixed_graph_mono
    {ω η : LatticeConfiguration} (hωη : ω ≤ η) :
    PD.rcInfiniteOpenGraph ω ≤ PD.rcInfiniteOpenGraph η := by
  intro x y hxy
  obtain ⟨hedge, hopen⟩ := (rcInfiniteOpenGraph_adj ω x y).mp hxy
  have hstate : η ⟨s(x, y), hedge⟩ = true := by
    exact (Bool.le_iff_imp.mp (hωη ⟨s(x, y), hedge⟩) hopen)
  exact (rcInfiniteOpenGraph_adj η x y).mpr ⟨hedge, hstate⟩

private theorem pottsESMixed_exit_upper
    (V : Finset (ℤ × ℤ)) (x : ℤ × ℤ) :
    IsUpperSet (pottsESLatticeExitEventFrom V x) := by
  intro ω η hωη hω
  obtain ⟨y, hy, hreach⟩ := hω
  exact ⟨y, hy, hreach.mono (pottsESMixed_graph_mono hωη)⟩

private theorem pottsESMixed_pair_upper
    (V : Finset (ℤ × ℤ)) (x y : ℤ × ℤ) :
    IsUpperSet (pottsESLatticePairRelationEvent V x y) := by
  intro ω η hωη hω
  change (PD.rcInfiniteOpenGraph ω).Reachable x y ∨
    (ω ∈ pottsESLatticeExitEventFrom V x ∧
      ω ∈ pottsESLatticeExitEventFrom V y) at hω
  change (PD.rcInfiniteOpenGraph η).Reachable x y ∨
    (η ∈ pottsESLatticeExitEventFrom V x ∧
      η ∈ pottsESLatticeExitEventFrom V y)
  rcases hω with hpath | ⟨hExitX, hExitY⟩
  · exact Or.inl (hpath.mono (pottsESMixed_graph_mono hωη))
  · exact Or.inr ⟨pottsESMixed_exit_upper V x hωη hExitX,
      pottsESMixed_exit_upper V y hωη hExitY⟩

private theorem pottsESMixed_event_upper
    (V : Finset (ℤ × ℤ))
    (Pairs : Finset ((ℤ × ℤ) × (ℤ × ℤ)))
    (GhostSites : Finset (ℤ × ℤ)) :
    IsUpperSet (pottsESLatticeMixedConstraintEvent V Pairs GhostSites) := by
  intro ω η hωη hω
  simp only [pottsESLatticeMixedConstraintEvent, Set.mem_inter_iff,
    pottsESLatticePairIntersectionEvent, Set.mem_iInter] at hω ⊢
  constructor
  · intro p hp
    exact pottsESMixed_pair_upper V p.1 p.2 hωη (hω.1 p hp)
  · intro x hx
    exact pottsESMixed_exit_upper V x hωη (hω.2 x hx)

private theorem pottsESMixed_exit_dependsOn
    (V : Finset (ℤ × ℤ)) (x : ℤ × ℤ) :
    PottsContinuity.PD.RCInfinite.DependsOn
      (pottsESLatticeEdgeSet V : Set
        PottsContinuity.PD.FK.squareLattice.edgeSet)
      (pottsESLatticeExitEventFrom V x) := by
  by_cases hx : x ∈ V
  · intro ω η hstates
    constructor
    · rintro ⟨y, hy, hreach⟩
      exact hreach.elim fun p =>
        pottsESOpenWalk_exitTransfer V (fun e he => hstates e he) p hx hy
    · rintro ⟨y, hy, hreach⟩
      exact hreach.elim fun p =>
        pottsESOpenWalk_exitTransfer V (fun e he => (hstates e he).symm) p hx hy
  · have hEq : pottsESLatticeExitEventFrom V x = Set.univ := by
      ext ω
      constructor
      · intro _
        trivial
      · intro _
        exact ⟨x, hx, SimpleGraph.Reachable.refl _⟩
    rw [hEq]
    intro ω η _
    simp

private theorem pottsESMixed_event_dependsOn
    (V : Finset (ℤ × ℤ))
    (Pairs : Finset ((ℤ × ℤ) × (ℤ × ℤ)))
    (GhostSites : Finset (ℤ × ℤ))
    (hPairs : ∀ p ∈ Pairs, p.1 ∈ V ∧ p.2 ∈ V)
    (_hGhost : ∀ x ∈ GhostSites, x ∈ V) :
    PottsContinuity.PD.RCInfinite.DependsOn
      (pottsESLatticeEdgeSet V : Set
        PottsContinuity.PD.FK.squareLattice.edgeSet)
      (pottsESLatticeMixedConstraintEvent V Pairs GhostSites) := by
  intro ω η hstates
  simp only [pottsESLatticeMixedConstraintEvent, Set.mem_inter_iff,
    pottsESLatticePairIntersectionEvent, Set.mem_iInter]
  constructor
  · intro hω
    constructor
    · intro p hp
      exact (pottsESLatticePairRelationEvent_dependsOn V p.1 p.2
        (hPairs p hp).1 (hPairs p hp).2 ω η hstates).mp (hω.1 p hp)
    · intro x hx
      exact (pottsESMixed_exit_dependsOn V x ω η hstates).mp (hω.2 x hx)
  · intro hη
    constructor
    · intro p hp
      exact (pottsESLatticePairRelationEvent_dependsOn V p.1 p.2
        (hPairs p hp).1 (hPairs p hp).2 ω η hstates).mpr (hη.1 p hp)
    · intro x hx
      exact (pottsESMixed_exit_dependsOn V x ω η hstates).mpr (hη.2 x hx)

private theorem pottsESMixed_event_cylinder
    (V : Finset (ℤ × ℤ))
    (Pairs : Finset ((ℤ × ℤ) × (ℤ × ℤ)))
    (GhostSites : Finset (ℤ × ℤ))
    (hPairs : ∀ p ∈ Pairs, p.1 ∈ V ∧ p.2 ∈ V)
    (hGhost : ∀ x ∈ GhostSites, x ∈ V) :
    IsCylinder (pottsESLatticeMixedConstraintEvent V Pairs GhostSites) :=
  ⟨pottsESLatticeEdgeSet V,
    pottsESMixed_event_dependsOn V Pairs GhostSites hPairs hGhost⟩

private theorem pottsESMixed_exit_antitone
    {V W : Finset (ℤ × ℤ)} (hVW : V ⊆ W) (x : ℤ × ℤ) :
    pottsESLatticeExitEventFrom W x ⊆ pottsESLatticeExitEventFrom V x := by
  intro ω hω
  obtain ⟨y, hy, hreach⟩ := hω
  exact ⟨y, fun hyV => hy (hVW hyV), hreach⟩

private theorem pottsESMixed_event_antitone
    {V W : Finset (ℤ × ℤ)} (hVW : V ⊆ W)
    (Pairs : Finset ((ℤ × ℤ) × (ℤ × ℤ)))
    (GhostSites : Finset (ℤ × ℤ)) :
    pottsESLatticeMixedConstraintEvent W Pairs GhostSites ⊆
      pottsESLatticeMixedConstraintEvent V Pairs GhostSites := by
  intro ω hω
  simp only [pottsESLatticeMixedConstraintEvent, Set.mem_inter_iff,
    pottsESLatticePairIntersectionEvent, Set.mem_iInter] at hω ⊢
  constructor
  · intro p hp
    exact pottsESLatticePairRelationEvent_antitone hVW p.1 p.2 (hω.1 p hp)
  · intro x hx
    exact pottsESMixed_exit_antitone hVW x (hω.2 x hx)

private theorem pottsESMixed_volume_mono
    (V : ℕ → Finset (ℤ × ℤ))
    (hNest : ∀ n, V n ⊆ V (n + 1)) : Monotone V := by
  intro m n hmn
  induction n generalizing m with
  | zero =>
    have hm : m = 0 := by omega
    subst m
    exact Finset.Subset.rfl
  | succ n ih =>
    by_cases hmn' : m ≤ n
    · exact (ih hmn').trans (hNest n)
    · have hm : m = n + 1 := by omega
      subst m
      exact Finset.Subset.rfl

private theorem pottsESMixed_eventually_contains
    (V : ℕ → Finset (ℤ × ℤ)) (hMono : Monotone V)
    (hExhaust : ∀ x : ℤ × ℤ, ∃ n, x ∈ V n)
    (F : Finset (ℤ × ℤ)) : ∃ N, ∀ n, N ≤ n → F ⊆ V n := by
  induction F using Finset.induction_on with
  | empty => exact ⟨0, fun _ _ => Finset.empty_subset _⟩
  | @insert x F hx ih =>
    obtain ⟨m, hm⟩ := ih
    obtain ⟨n, hn⟩ := hExhaust x
    refine ⟨max m n, ?_⟩
    intro k hk y hy
    rcases Finset.mem_insert.mp hy with rfl | hy
    · exact hMono (le_trans (Nat.le_max_right m n) hk) hn
    · exact hMono (le_trans (Nat.le_max_left m n) hk) (hm m (le_refl m) hy)

/-- Joint finite shell constraints on wired components and the ghost component
converge along every nested exhaustion to the corresponding RC events. -/
theorem pottsESShellMixedConstraint_probability_tendsto
    (θ : Parameters) (V : ℕ → Finset (ℤ × ℤ))
    (hNest : ∀ n, V n ⊆ V (n + 1))
    (hExhaust : ∀ x : ℤ × ℤ, ∃ n, x ∈ V n)
    (μ : Measure LatticeConfiguration)
    (hμ : PD.IsRCInfiniteVolumeLimit θ.toP θ.toQ 1 μ)
    (Pairs : Finset ((ℤ × ℤ) × (ℤ × ℤ)))
    (GhostSites : Finset (ℤ × ℤ)) :
    Tendsto
      (fun n => (pottsESShellBondProbabilityMeasure θ (V n) :
        Measure LatticeConfiguration).real
          (pottsESLatticeMixedConstraintEvent (V n) Pairs GhostSites))
      atTop (𝓝 (μ.real
        (pottsESConnectionInfiniteConstraintEvent Pairs GhostSites))) := by
  classical
  let E : ℕ → Set LatticeConfiguration :=
    fun n => pottsESLatticeMixedConstraintEvent (V n) Pairs GhostSites
  have hSites := pottsESMixed_eventually_contains V
    (pottsESMixed_volume_mono V hNest) hExhaust
    (Pairs.image Prod.fst ∪ (Pairs.image Prod.snd ∪ GhostSites))
  obtain ⟨N, hSites⟩ := hSites
  have hPairs (n : ℕ) (hn : N ≤ n) (p : (ℤ × ℤ) × (ℤ × ℤ))
      (hp : p ∈ Pairs) : p.1 ∈ V n ∧ p.2 ∈ V n := by
    have hF := hSites n hn
    constructor
    · apply hF
      apply Finset.mem_union.mpr
      left
      exact Finset.mem_image.mpr ⟨p, hp, rfl⟩
    · apply hF
      apply Finset.mem_union.mpr
      right
      apply Finset.mem_union.mpr
      left
      exact Finset.mem_image.mpr ⟨p, hp, rfl⟩
  have hGhost (n : ℕ) (hn : N ≤ n) (x : ℤ × ℤ) (hx : x ∈ GhostSites) :
      x ∈ V n := by
    have hF := hSites n hn
    apply hF
    apply Finset.mem_union.mpr
    right
    apply Finset.mem_union.mpr
    right
    exact hx
  have hMeas (n : ℕ) : MeasurableSet (E n) := by
    exact pottsESMixed_event_measurable (V n) Pairs GhostSites
  have hAntitone : Antitone E := by
    intro m n hmn
    exact pottsESMixed_event_antitone
      (pottsESMixed_volume_mono V hNest hmn) Pairs GhostSites
  have hCylinder : ∀ n, N ≤ n → IsCylinder (E n) := by
    intro n hn
    simpa [E] using pottsESMixed_event_cylinder (V n) Pairs GhostSites
      (hPairs n hn) (hGhost n hn)
  have hDepends : ∀ n, N ≤ n →
      PottsContinuity.PD.RCInfinite.DependsOn
        (pottsESLatticeEdgeSet (V n) : Set
          PottsContinuity.PD.FK.squareLattice.edgeSet) (E n) := by
    intro n hn
    simpa [E] using pottsESMixed_event_dependsOn (V n) Pairs GhostSites
      (hPairs n hn) (hGhost n hn)
  have hUpper : ∀ n, N ≤ n → IsUpperSet (E n) := by
    intro n hn
    exact pottsESMixed_event_upper (V n) Pairs GhostSites
  have hUnique := isRCInfiniteVolumeLimit_atMostOneInfiniteCluster
    θ 1 μ hμ
  have hInterAE : (⋂ n, E n) =ᵐ[μ]
      pottsESConnectionInfiniteConstraintEvent Pairs GhostSites := by
    filter_upwards [hUnique] with ω hAtMostOne
    apply propext
    rw [pottsESLatticeMixedConstraintEvent_iInter_eq
      V hNest hExhaust Pairs GhostSites]
    simp only [pottsESConnectionInfiniteConstraintEvent,
      pottsESConnectionIntersectionEvent, Set.mem_inter_iff,
      Set.mem_iInter]
    constructor
    · intro h
      constructor
      · intro p hp
        rcases h.1 p hp with hconn | ⟨hxInf, hyInf⟩
        · exact (connectionEvent_iff_rcInfiniteReachable p.1 p.2 ω).mpr hconn
        · exact (connectionEvent_iff_rcInfiniteReachable p.1 p.2 ω).mpr
            (hAtMostOne p.1 p.2 hxInf hyInf)
      · exact h.2
    · intro h
      constructor
      · intro p hp
        exact Or.inl ((connectionEvent_iff_rcInfiniteReachable
          p.1 p.2 ω).mp (h.1 p hp))
      · exact h.2
  have hLimit := pottsESShellDecreasingCylinderProbability_tendsto
    θ V hNest hExhaust μ hμ E hMeas hAntitone N hCylinder hDepends hUpper
    (pottsESConnectionInfiniteConstraintEvent Pairs GhostSites) hInterAE
  simpa only [E] using hLimit

end

end PottsContinuity.Thm1
