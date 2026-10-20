module

public import Mathlib
public import PottsContinuity.Foundations.Bridges
public import PottsContinuity.Frozen.Defs
public import PottsContinuity.PD.FK.BoxLimits
public import PottsContinuity.PD.FK.EndpointLimits
public import PottsContinuity.PD.FK.FrozenLimitBridge
public import PottsContinuity.PD.RCInfinite.SubgraphExhaustion

@[expose] public section

open MeasureTheory Filter Topology

namespace PottsContinuity.Foundations

open PottsContinuity
open Classical

private theorem eventually_edge_lift_exhaustion (G : ℕ → Finset (ℤ × ℤ))
    (hG : Monotone G) (hExhaust : ∀ x, ∃ n, x ∈ G n)
    (A : Finset squareLattice.edgeSet) :
    ∀ᶠ n : ℕ in atTop, ∀ e ∈ A,
      ∃ f : (squareLattice.induce (G n : Set (ℤ × ℤ))).edgeSet,
        Sym2.map Subtype.val f.1 = e.1 := by
  obtain ⟨r, hr⟩ := PottsContinuity.PD.RCInfinite.exists_box_supporting_edge_finset A
  have hbox : ∀ e ∈ A,
      e ∈ Set.range (PottsContinuity.PD.FK.frozenEdgeEmbedding
        (PottsContinuity.PD.FK.latticeBox (0, 0) r)) := by
    intro e he
    exact PottsContinuity.PD.RCInfinite.boxEdges_subset_frozenEdgeEmbedding_range r
      (hr e he)
  have hcontain := PottsContinuity.PD.RCInfinite.eventually_latticeBox_subset_of_exhaustion
    G (fun n => hG (Nat.le_succ n)) hExhaust r
  filter_upwards [hcontain] with n hcontain
  intro e he
  have he' := PottsContinuity.PD.RCInfinite.frozenEdgeEmbedding_range_mono
    hcontain (hbox e he)
  obtain ⟨f, hf⟩ := Set.mem_range.mp he'
  exact ⟨f, congrArg Subtype.val hf⟩

private theorem endpoint_weight_eq_zero (V : Finset (ℤ × ℤ))
    (q : Set.Ioi (0 : ℝ)) (i : Fin 2) (b : Bool)
    (ω : (squareLattice.induce (V : Set (ℤ × ℤ))).edgeSet → Bool)
    (hω : ω ≠ fun _ => b) :
    rcWeight V (PottsContinuity.PD.FK.endpointParameter b) q i ω = 0 := by
  classical
  have hex : ∃ e, ω e ≠ b := by
    by_contra h
    apply hω
    funext e
    exact not_not.mp fun he => h ⟨e, he⟩
  obtain ⟨e, he⟩ := hex
  cases b with
  | false =>
      have htrue : ω e = true := by cases h : ω e <;> simp_all
      have : Nonempty {f // ω f = true} := ⟨⟨e, htrue⟩⟩
      simp [rcWeight, PottsContinuity.PD.FK.endpointParameter]
  | true =>
      have hfalse : ω e = false := by cases h : ω e <;> simp_all
      have : Nonempty {f // ω f = false} := ⟨⟨e, hfalse⟩⟩
      simp [rcWeight, PottsContinuity.PD.FK.endpointParameter]

private theorem rcProb_endpoint_own (V : Finset (ℤ × ℤ)) (q : Set.Ioi (0 : ℝ))
    (i : Fin 2) (b : Bool)
    (ω : (squareLattice.induce (V : Set (ℤ × ℤ))).edgeSet → Bool) :
    rcProb V (PottsContinuity.PD.FK.endpointParameter b) q i ω =
      if ω = (fun _ => b) then 1 else 0 := by
  classical
  have hsum : (∑ ω', rcWeight V (PottsContinuity.PD.FK.endpointParameter b) q i ω') =
      rcWeight V (PottsContinuity.PD.FK.endpointParameter b) q i (fun _ => b) := by
    apply Finset.sum_eq_single (fun _ => b)
    · intro ω' _ hω'
      exact endpoint_weight_eq_zero V q i b ω' hω'
    · simp
  have hpos : 0 < rcWeight V (PottsContinuity.PD.FK.endpointParameter b) q i
      (fun _ => b) := by
    rw [← hsum]
    simp_rw [rcWeight_eq_PD]
    exact PottsContinuity.PD.rcWeight_denominator_pos V
      (PottsContinuity.PD.FK.endpointParameter b) q i
  by_cases hω : ω = (fun _ => b)
  · rw [ite_eq_left hω, hω]
    unfold rcProb
    rw [hsum, div_self (ne_of_gt hpos)]
  · rw [ite_eq_right hω]
    unfold rcProb
    rw [endpoint_weight_eq_zero V q i b ω hω, zero_div]

theorem endpoint_isRCInfiniteVolumeLimit_all_exhaustions
    (q : Set.Ioi (0 : ℝ)) (i : Fin 2)
    (b : Bool) :
    IsRCInfiniteVolumeLimit (PottsContinuity.PD.FK.endpointParameter b) q i
      (Measure.dirac (fun _ => b)) := by
  classical
  unfold PottsContinuity.IsRCInfiniteVolumeLimit
  constructor
  · infer_instance
  · intro G hG hExhaust A ξ
    have hLift := eventually_edge_lift_exhaustion G hG hExhaust A
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hLift] with n hn
    have hiff :
        (∀ e ∈ A, ∃ f : (squareLattice.induce (G n : Set (ℤ × ℤ))).edgeSet,
          Sym2.map Subtype.val f.1 = e.1 ∧ (fun _ => b) f = ξ e) ↔
          ∀ e ∈ A, b = ξ e := by
      constructor
      · intro h e he
        obtain ⟨f, _, hval⟩ := h e he
        exact hval
      · intro h e he
        obtain ⟨f, hf⟩ := hn e he
        exact ⟨f, hf, h e he⟩
    unfold PottsContinuity.rcEventProb
    symm
    rw [Finset.sum_eq_single (fun _ => b)]
    · rw [rcProb_endpoint_own, Measure.dirac_real_apply]
      simp only [hiff, ite_true, Set.indicator, Set.mem_ofPred_eq, Pi.one_apply]
    · intro ω hω hne
      rw [rcProb_endpoint_own, ite_eq_right hne]
      exact ite_self _
    · simp

theorem pd_interior_limit_all_exhaustions
    (θ : PottsContinuity.PD.FK.Parameters) (i : Fin 2)
    (μ : Measure (PottsContinuity.PD.squareLattice.edgeSet → Bool))
    (hμPD : PottsContinuity.PD.IsRCInfiniteVolumeLimit
      θ.toP θ.toQ i μ) :
    IsRCInfiniteVolumeLimit θ.toP θ.toQ i μ := by
  have hμ : IsRCInfiniteVolumeLimit θ.toP θ.toQ i μ := by
    classical
    cases squareLattice_eq_PD.symm
    unfold PottsContinuity.IsRCInfiniteVolumeLimit
    constructor
    · exact hμPD.1
    intro G hG hExhaust A ξ
    let ext : ∀ n,
        PottsContinuity.PD.FK.Configuration
          (PottsContinuity.PD.squareLattice.induce (G n : Set (ℤ × ℤ))) →
          PottsContinuity.PD.FK.LatticeConfiguration :=
      fun n => PottsContinuity.PD.RCInfinite.finiteSubgraphConfiguration (G n) i
    have hExt : ∀ n C f,
        ext n C (PottsContinuity.PD.FK.frozenEdgeEmbedding (G n) f) =
          decide (f ∈ C) := by
      intro n C f
      by_cases hi : i = 0
      · simp only [ext, PottsContinuity.PD.RCInfinite.finiteSubgraphConfiguration,
          dite_eq_left hi]
        have hiff : PottsContinuity.PD.FK.frozenEdgeEmbedding (G n) f ∈
            C.map (PottsContinuity.PD.FK.frozenEdgeEmbedding (G n)) ↔ f ∈ C := by
          rw [Finset.mem_map]
          constructor
          · rintro ⟨g, hg, hgf⟩
            exact (PottsContinuity.PD.FK.frozenEdgeEmbedding (G n)).injective hgf ▸ hg
          · intro hf
            exact ⟨f, hf, rfl⟩
        exact Bool.decide_congr hiff
      · simp only [ext, PottsContinuity.PD.RCInfinite.finiteSubgraphConfiguration,
          dite_eq_right hi]
        have hiff : (∀ g, PottsContinuity.PD.FK.frozenEdgeEmbedding (G n) g =
            PottsContinuity.PD.FK.frozenEdgeEmbedding (G n) f → g ∈ C) ↔ f ∈ C := by
          constructor
          · intro h
            exact h f rfl
          · intro hf g hgf
            exact (PottsContinuity.PD.FK.frozenEdgeEmbedding (G n)).injective hgf ▸ hf
        exact decide_eq_decide.mpr hiff
    have hweak := PottsContinuity.PD.RCInfinite.finiteInducedSubgraphExhaustion_tendsto
      θ i μ hμPD G (fun n => hG (Nat.le_succ n)) hExhaust
    have hconv := ProbabilityMeasure.tendsto_measure_of_isClopen_of_tendsto hweak
      (PottsContinuity.PD.FK.patternCylinder_isClopen A ξ)
    let ν : ProbabilityMeasure PottsContinuity.PD.FK.LatticeConfiguration :=
      ⟨μ, hμPD.1⟩
    have hreal : Tendsto
        (fun n => (PottsContinuity.PD.RCInfinite.finiteSubgraphProbabilityMeasure
          θ (G n) i : Measure PottsContinuity.PD.FK.LatticeConfiguration).real
            (PottsContinuity.PD.FK.patternCylinder A ξ)) atTop
        (𝓝 (ν.toMeasure.real (PottsContinuity.PD.FK.patternCylinder A ξ))) := by
      simpa only [ProbabilityMeasure.measureReal_eq_coe_coeFn, Function.comp_def] using
        NNReal.continuous_coe.continuousAt.tendsto.comp hconv
    have hrealμ : Tendsto
        (fun n => (PottsContinuity.PD.RCInfinite.finiteSubgraphProbabilityMeasure
          θ (G n) i : Measure PottsContinuity.PD.FK.LatticeConfiguration).real
            (PottsContinuity.PD.FK.patternCylinder A ξ)) atTop
        (𝓝 (μ.real (PottsContinuity.PD.FK.patternCylinder A ξ))) := by
      simpa only [ν, ProbabilityMeasure.toMeasure] using hreal
    have hLift := eventually_edge_lift_exhaustion G hG hExhaust A
    refine hrealμ.congr' ?_
    filter_upwards [hLift] with n hn
    have hA : ∀ e ∈ A, ∃ f,
        PottsContinuity.PD.FK.frozenEdgeEmbedding (G n) f = e := by
      intro e he
      obtain ⟨f, hf⟩ := hn e he
      exact ⟨f, Subtype.ext hf⟩
    let : DecidableRel squareLattice.Adj :=
      PottsContinuity.PD.FK.instDecidableRelLatticeVertexAdjSquareLattice
    let : DecidableRel (squareLattice.induce (G n : Set (ℤ × ℤ))).Adj := by
      exact SimpleGraph.instDecidableComapAdj _ squareLattice
    let : Fintype (squareLattice.induce (G n : Set (ℤ × ℤ))).edgeSet := by
      exact SimpleGraph.fintypeEdgeSet _
    have hpat := PottsContinuity.PD.FK.frozenExtendedProbabilityMeasure_pattern
      θ (G n) i (ext n) (hExt n) A ξ hA
    have hsum : rcEventProb (G n) θ.toP θ.toQ i
        (fun ω => ∀ e ∈ A, ∃ f,
          Sym2.map Subtype.val f.1 = e.1 ∧ ω f = ξ e) =
        ∑ ω : (squareLattice.induce (G n : Set (ℤ × ℤ))).edgeSet → Bool,
          if ∀ e ∈ A, ∃ f : (squareLattice.induce (G n : Set (ℤ × ℤ))).edgeSet,
            Sym2.map Subtype.val f.1 = e.1 ∧ ω f = ξ e
          then PottsContinuity.PD.rcProb (G n) θ.toP θ.toQ i ω else 0 := by
      unfold PottsContinuity.rcEventProb
      refine Finset.sum_congr ?_ ?_
      · ext ω
        simp
      · intro ω hω
        split_ifs with hevent
        · exact rcProb_eq_PD (G n) θ.toP θ.toQ i ω
        · rfl
    have hpat' :
        (PottsContinuity.PD.RCInfinite.finiteSubgraphProbabilityMeasure θ
          (G n) i : Measure PottsContinuity.PD.FK.LatticeConfiguration).real
          (PottsContinuity.PD.FK.patternCylinder A ξ) =
        ∑ ω : (squareLattice.induce (G n : Set (ℤ × ℤ))).edgeSet → Bool,
          if ∀ e ∈ A, ∃ f : (squareLattice.induce (G n : Set (ℤ × ℤ))).edgeSet,
            Sym2.map Subtype.val f.1 = e.1 ∧ ω f = ξ e
          then PottsContinuity.PD.rcProb (G n) θ.toP θ.toQ i ω else 0 := by
      change (PottsContinuity.PD.FK.frozenExtendedProbabilityMeasure θ (G n) i
        (ext n)).toMeasure.real (PottsContinuity.PD.FK.patternCylinder A ξ) = _
      rw [hpat]
      refine Finset.sum_congr ?_ ?_
      · ext ω
        constructor
        · intro _
          exact Finset.mem_univ ω
        · intro _
          trivial
      · intro ω hω
        rfl
    rw [hsum]
    exact hpat'
  exact hμ

/-- The frozen random-cluster infinite-volume measure exists for every admissible
edge probability, cluster weight at least one, and either free or wired condition.
The convergence clause is along every increasing exhaustive sequence of finite
induced vertex sets. -/
theorem exists_isRCInfiniteVolumeLimit (p : Set.Icc (0 : ℝ) 1)
    (q : Set.Ioi (0 : ℝ)) (hq : 1 ≤ (q : ℝ)) (i : Fin 2) :
    ∃ μ : Measure (squareLattice.edgeSet → Bool), IsRCInfiniteVolumeLimit p q i μ := by
  by_cases hp0 : (p : ℝ) = 0
  · have hp : p = PottsContinuity.PD.FK.endpointParameter false := by
      apply Subtype.ext
      exact hp0
    rw [hp]
    exact ⟨Measure.dirac (fun _ => false),
      endpoint_isRCInfiniteVolumeLimit_all_exhaustions q i false⟩
  by_cases hp1 : (p : ℝ) = 1
  · have hp : p = PottsContinuity.PD.FK.endpointParameter true := by
      apply Subtype.ext
      exact hp1
    rw [hp]
    exact ⟨Measure.dirac (fun _ => true),
      endpoint_isRCInfiniteVolumeLimit_all_exhaustions q i true⟩
  have hp0' : 0 < (p : ℝ) := lt_of_le_of_ne p.property.1 (Ne.symm hp0)
  have hp1' : (p : ℝ) < 1 := lt_of_le_of_ne p.property.2 hp1
  let θ : PottsContinuity.PD.FK.Parameters :=
    { val := (q : ℝ)
      property := hq
      edgeProbability := ⟨(p : ℝ), hp0', hp1'⟩ }
  obtain ⟨μ, hμPD⟩ :=
    PottsContinuity.PD.FK.exists_isRCInfiniteVolumeLimit_interior θ i
  exact ⟨μ, pd_interior_limit_all_exhaustions θ i μ hμPD⟩

end PottsContinuity.Foundations
