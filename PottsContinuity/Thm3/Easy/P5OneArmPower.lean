module

public import Mathlib
public import PottsContinuity.Frozen.Defs
public import PottsContinuity.Foundations.Bridges
public import PottsContinuity.Infinite.Bridge
public import PottsContinuity.PD.RCInfinite.FiniteModification
public import PottsContinuity.PD.RCInfinite.ExteriorClusters
public import PottsContinuity.Thm3.Easy.P5AnnuliProduct
public import PottsContinuity.Thm3.Easy.P5OneArmAnnuli
public import PottsContinuity.Thm3.Easy.P5OneArmArithmetic
public import PottsContinuity.Foundations.BoxBoundary
public import PottsContinuity.PD.CorrLength.ConnectionEvents
public import PottsContinuity.PD.RCInfinite.ClusterEvents
public import PottsContinuity.PD.RCInfinite.FiniteBoxCounting

@[expose] public section

namespace PottsContinuity.Thm3.Easy

open MeasureTheory
open Filter Topology
open PottsContinuity
open PottsContinuity.PD.FK
open PottsContinuity.PD.RCInfinite

/-- The PD form of the wired one-arm event. -/
def pdOneArmBoundaryEvent (n : ℕ) : Set LatticeConfiguration :=
  {ω | ∃ y ∈ PottsContinuity.PD.vertexBoundary
      (latticeBox (0, 0) n),
    (PottsContinuity.PD.rcInfiniteOpenGraph ω).Reachable (0, 0) y}

private theorem origin_not_boxBoundary (n : ℕ) (hn : 1 ≤ n) :
    (0, 0) ∉ PottsContinuity.PD.vertexBoundary (latticeBox (0, 0) n) := by
  intro h
  have hside := PottsContinuity.PD.RCInfinite.box_boundary_coordinate_edge n h
  rcases hside with h | h | h | h <;> norm_num at h
  all_goals omega

private theorem origin_adj_edge_mem_boxIncidentEdges {v : LatticeVertex}
    (hv : squareLattice.Adj (0, 0) v) :
    (⟨s((0, 0), v), squareLattice.mem_edgeSet.mpr hv⟩ : squareLattice.edgeSet) ∈
      boxIncidentEdges 0 := by
  apply edge_incident_box_mem_boxIncidentEdges
  refine ⟨(0, 0), center_mem_latticeBox (0, 0) 0, ?_⟩
  simp

private theorem pdOneArm_subset_closedStar_compl (n : ℕ) (hn : 1 ≤ n) :
    pdOneArmBoundaryEvent n ⊆
      (setEdges (boxIncidentEdges 0) (fun _ => false) '' Set.univ)ᶜ := by
  classical
  intro ω hArm hClosed
  rcases hArm with ⟨y, hy, hreach⟩
  rcases hClosed with ⟨η, _, rfl⟩
  rcases hreach with ⟨w⟩
  cases w with
  | nil =>
      exact (origin_not_boxBoundary n hn) hy
  | @cons u v y hadj tail =>
      have hopen := (rcInfiniteOpenGraph_adj
        (setEdges (boxIncidentEdges 0) (fun _ => false) η) (0, 0) v).mp hadj
      rcases hopen with ⟨he, hstate⟩
      have hAdj : squareLattice.Adj (0, 0) v := squareLattice.mem_edgeSet.mp he
      let e : squareLattice.edgeSet := ⟨s((0, 0), v), he⟩
      have heStar : e ∈ boxIncidentEdges 0 := by
        exact origin_adj_edge_mem_boxIncidentEdges hAdj
      have hfalse : setEdges (boxIncidentEdges 0) (fun _ => false) η
          ⟨s((0, 0), v), he⟩ = false := by
        have heStar' :
            (⟨s((0, 0), v), he⟩ : squareLattice.edgeSet) ∈ boxIncidentEdges 0 := by
          simpa [e] using heStar
        unfold setEdges
        exact ite_eq_left heStar'
      rw [hfalse] at hstate
      cases hstate

/-- Finite energy gives a uniform strict upper bound on the wired one-arm
probability: closing every edge incident to the origin isolates it. -/
theorem pd_wired_oneArm_uniform_gap
    (θ : PottsContinuity.PD.FK.Parameters)
    (μ : Measure LatticeConfiguration)
    (hμ : PottsContinuity.PD.IsRCInfiniteVolumeLimit
      θ.toP θ.toQ 1 μ) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ ∀ n : ℕ, 1 ≤ n →
      μ.real (pdOneArmBoundaryEvent n) ≤ 1 - δ := by
  classical
  let F := boxIncidentEdges 0
  let ξ : squareLattice.edgeSet → Bool := fun _ => false
  let B : Set LatticeConfiguration := setEdges F ξ '' Set.univ
  let δ : ℝ := energyBound θ ^ F.card
  let : IsProbabilityMeasure μ := hμ.1
  have hFne : F.Nonempty := by
    let e : squareLattice.edgeSet :=
      ⟨s((0, 0), (1, 0)), squareLattice.mem_edgeSet.mpr
        ((PottsContinuity.PD.FK.squareLattice_adj_iff
          (0, 0) (1, 0)).2
          (Or.inl ⟨Or.inl (by norm_num), by norm_num⟩))⟩
    refine ⟨e, ?_⟩
    apply edge_incident_box_mem_boxIncidentEdges
    exact ⟨(0, 0), center_mem_latticeBox (0, 0) 0, by simp [e]⟩
  have hFcard : F.card ≠ 0 := (Finset.card_pos.mpr hFne).ne'
  have hEnergyLt : energyBound θ < 1 := by
    unfold energyBound
    exact (min_le_right _ _).trans_lt (by
      dsimp [edgeParameter]
      linarith [θ.edgeProbability.property.1])
  have hδpos : 0 < δ := by
    dsimp [δ]
    exact pow_pos (energyBound_pos θ) _
  have hδlt : δ < 1 := by
    dsimp [δ]
    exact pow_lt_one₀ (energyBound_pos θ).le hEnergyLt hFcard
  have hBmeas : MeasurableSet B := by
    exact measurableSet_setEdges_image F ξ MeasurableSet.univ
  have hδle : δ ≤ μ.real B := by
    have henergy := setEdges_image_energy θ 1 μ hμ F ξ
      (A := (Set.univ : Set LatticeConfiguration)) MeasurableSet.univ
    have huniv : μ.real Set.univ = 1 := by
      simp [Measure.real, hμ.1.measure_univ]
    simpa [δ, B, F, ξ, huniv] using henergy
  have hcomplement : μ.real Bᶜ = 1 - μ.real B := by
    rw [measureReal_compl hBmeas]
    simp [Measure.real, hμ.1.measure_univ]
  refine ⟨δ, hδpos, hδlt, ?_⟩
  intro n hn
  have hsubset : pdOneArmBoundaryEvent n ⊆ Bᶜ := by
    change pdOneArmBoundaryEvent n ⊆
      (setEdges (boxIncidentEdges 0) (fun _ => false) '' Set.univ)ᶜ
    exact pdOneArm_subset_closedStar_compl n hn
  calc
    μ.real (pdOneArmBoundaryEvent n) ≤ μ.real Bᶜ := measureReal_mono hsubset
    _ = 1 - μ.real B := hcomplement
    _ ≤ 1 - δ := by linarith

private theorem pdOneArm_subset_dyadicAnnulusTail
    (n start count : ℕ) (hstart : 3 ≤ start)
    (hcount : start + count ≤ Nat.log 2 n) :
    pdOneArmBoundaryEvent n ⊆
      dyadicAnnulusTail dyadicAnnulusOpenCrossingEvent start count := by
  induction count generalizing start with
  | zero =>
      simp [dyadicAnnulusTail]
  | succ count ih =>
      simp only [dyadicAnnulusTail]
      intro ω hArm
      constructor
      ·
        have hpow : 2 ^ start < 2 ^ Nat.log 2 n :=
          Nat.pow_lt_pow_right (by omega) (by omega)
        have hnzero : n ≠ 0 := by
          intro hn
          subst n
          simp at hcount
        have hlog : 2 ^ Nat.log 2 n ≤ n :=
          Nat.pow_log_le_self 2 hnzero
        have hscale : 2 ^ start < n := hpow.trans_le hlog
        change ∃ y ∈ PottsContinuity.PD.vertexBoundary
            (latticeBox (0, 0) n),
          (PottsContinuity.PD.rcInfiniteOpenGraph ω).Reachable (0, 0) y at hArm
        exact oneArmBoundary_forces_dyadicAnnulusOpenCrossing
          n start hstart hscale ω hArm
      · exact (ih (start + 1) (by omega) (by omega)) hArm

private theorem rpow_mono_exponent_of_one_le
    (x a b : ℝ) (hx : 1 ≤ x) (hab : a ≤ b) :
    Real.rpow x a ≤ Real.rpow x b :=
  Real.rpow_le_rpow_of_exponent_le hx hab

/-- The annular-duality estimate `hAnnulusDuality` (a wired-box annulus bound) gives a
polynomial one-arm bound. Scales three and above use the wired DMP product; the finite
energy gap at the origin supplies the finitely many smaller radii. -/
theorem wired_oneArm_power_bound_of_annulusDuality
    (q : Set.Ici (1 : ℝ))
    (μ : Measure (squareLattice.edgeSet → Bool))
    (hμ : IsRCInfiniteVolumeLimit
      (PottsContinuity.PD.FK.criticalParameters q).toP
      (PottsContinuity.PD.FK.criticalParameters q).toQ 1 μ)
    (hAnnulusDuality : ∃ c : ℝ, 0 < c ∧ ∀ j : ℕ, 3 ≤ j →
      (boxMeasure (PottsContinuity.PD.FK.criticalParameters q)
        1 (0, 0) (2 ^ j) : Measure LatticeConfiguration).real
          {ω | PottsContinuity.DualityExt.annulusOpenCrossing
            (2 ^ (j - 1)) ω} ≤ 1 - c) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ n : ℕ, 1 ≤ n →
      μ.real (pdOneArmBoundaryEvent n) ≤ Real.rpow (n : ℝ) (-ε) := by
  classical
  let : IsProbabilityMeasure μ := hμ.1
  let θ := PottsContinuity.PD.FK.criticalParameters q
  have hμFrozen : IsRCInfiniteVolumeLimit θ.toP θ.toQ 1 μ := by
    simpa [θ] using hμ
  have hμPD : PottsContinuity.PD.IsRCInfiniteVolumeLimit
      θ.toP θ.toQ 1 μ :=
    PottsContinuity.Infinite.isRCInfiniteVolumeLimit_to_PD_box
      θ.toP θ.toQ 1 μ hμFrozen
  obtain ⟨δ, hδpos, hδlt, hgap⟩ := pd_wired_oneArm_uniform_gap θ μ hμPD
  obtain ⟨c, hc, hdual⟩ := hAnnulusDuality
  let c' : ℝ := min c (1 / 2)
  have hc'pos : 0 < c' := by
    dsimp [c']
    exact lt_min hc (by norm_num)
  have hc'lt : c' < 1 := by
    dsimp [c']
    exact lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hc'le : c' ≤ c := by
    dsimp [c']
    exact min_le_left _ _
  have hdual' : ∀ j : ℕ, 3 ≤ j →
      (boxMeasure θ 1 (0, 0) (2 ^ j) : Measure LatticeConfiguration).real
          (dyadicAnnulusOpenCrossingEvent j) ≤ 1 - c' := by
    intro j hj
    have hbound := hdual j hj
    have hbound' :
        (boxMeasure θ 1 (0, 0) (2 ^ j) : Measure LatticeConfiguration).real
          (dyadicAnnulusOpenCrossingEvent j) ≤ 1 - c := by
      simpa [dyadicAnnulusOpenCrossingEvent] using hbound
    calc
      (boxMeasure θ 1 (0, 0) (2 ^ j) : Measure LatticeConfiguration).real
          (dyadicAnnulusOpenCrossingEvent j) ≤ 1 - c := hbound'
      _ ≤ 1 - c' := by linarith
  let εsmall : ℝ := -Real.log (1 - δ) / Real.log 31
  have hlogGap : Real.log (1 - δ) < 0 := by
    exact (Real.log_neg_iff (by linarith)).2 (by linarith)
  have hlog31 : 0 < Real.log 31 := Real.log_pos (by norm_num)
  have hεsmall : 0 < εsmall := by
    dsimp [εsmall]
    exact div_pos (neg_pos.mpr hlogGap) hlog31
  let εlarge : ℝ := dyadicOneArmExponent c' / 2
  have hεlarge : 0 < εlarge := by
    dsimp [εlarge]
    exact half_pos (dyadicOneArmExponent_pos c' hc'pos hc'lt)
  let ε : ℝ := min εsmall εlarge
  have hε : 0 < ε := by
    dsimp [ε]
    exact lt_min hεsmall hεlarge
  refine ⟨ε, hε, ?_⟩
  intro n hn
  by_cases hnLarge : 32 ≤ n
  · let k : ℕ := Nat.log 2 n
    have hk : 5 ≤ k := by
      dsimp [k]
      apply Nat.le_log_of_pow_le (by omega)
      norm_num at hnLarge ⊢
      omega
    have hproduct :
        μ.real (dyadicAnnulusTail dyadicAnnulusOpenCrossingEvent 3 (k - 3)) ≤
          (1 - c') ^ (k - 3) := by
      have h := wired_dyadic_annulus_product_of_annulusDuality_fixed
        q μ hμ (k - 3) c' hdual'
      simpa [k] using h
    have honearm : pdOneArmBoundaryEvent n ⊆
        dyadicAnnulusTail dyadicAnnulusOpenCrossingEvent 3 (k - 3) := by
      apply pdOneArm_subset_dyadicAnnulusTail n 3 (k - 3) (by omega)
      dsimp [k]
      omega
    have hlargePower := dyadic_factor_after_scale_three_le_power
      c' hc'pos hc'lt n hnLarge
    have hεlargeLe : ε ≤ εlarge := by
      dsimp [ε]
      exact min_le_right _ _
    have hpowerMono := rpow_mono_exponent_of_one_le (n : ℝ)
      (-εlarge) (-ε) (by exact_mod_cast hn)
      (by dsimp [εlarge]; exact neg_le_neg hεlargeLe)
    calc
      μ.real (pdOneArmBoundaryEvent n) ≤
          μ.real (dyadicAnnulusTail dyadicAnnulusOpenCrossingEvent 3 (k - 3)) :=
        measureReal_mono honearm
      _ ≤ (1 - c') ^ (k - 3) := hproduct
      _ ≤ Real.rpow (n : ℝ) (-εlarge) := by simpa [εlarge] using hlargePower
      _ ≤ Real.rpow (n : ℝ) (-ε) := hpowerMono
  · have hnSmall : n ≤ 31 := by omega
    have hnpos : 0 < n := by omega
    have hnreal : 0 < (n : ℝ) := by exact_mod_cast hnpos
    have hsmallScale :
        1 - δ ≤ Real.rpow (n : ℝ) (-εsmall) := by
      have hsmallBaseEq : Real.rpow (31 : ℝ) (-εsmall) = 1 - δ := by
        change (31 : ℝ) ^ (-εsmall) = 1 - δ
        rw [Real.rpow_def_of_pos (by norm_num : 0 < (31 : ℝ)) (-εsmall)]
        have hscaleEq : Real.log 31 * (-εsmall) = Real.log (1 - δ) := by
          dsimp [εsmall]
          field_simp [ne_of_gt hlog31]
        rw [hscaleEq, Real.exp_log (by linarith : 0 < 1 - δ)]
      calc
        1 - δ = Real.rpow (31 : ℝ) (-εsmall) := hsmallBaseEq.symm
        _ ≤ Real.rpow (n : ℝ) (-εsmall) :=
          Real.rpow_le_rpow_of_nonpos hnreal (by exact_mod_cast hnSmall)
            (neg_nonpos.mpr hεsmall.le)
    have hεsmallLe : ε ≤ εsmall := by
      dsimp [ε]
      exact min_le_left _ _
    have hpowerMono := rpow_mono_exponent_of_one_le (n : ℝ)
      (-εsmall) (-ε) (by exact_mod_cast hn)
      (neg_le_neg hεsmallLe)
    calc
      μ.real (pdOneArmBoundaryEvent n) ≤ 1 - δ := hgap n hn
      _ ≤ Real.rpow (n : ℝ) (-εsmall) := hsmallScale
      _ ≤ Real.rpow (n : ℝ) (-ε) := hpowerMono

private theorem infinite_origin_cluster_subset_pdOneArm (n : ℕ) :
    {ω | {y | (PottsContinuity.rcInfiniteOpenGraph ω).Reachable
        (0, 0) y}.Infinite} ⊆ pdOneArmBoundaryEvent n := by
  classical
  cases Foundations.squareLattice_eq_PD
  intro ω hω
  have hωPD :
      {y | (PottsContinuity.PD.rcInfiniteOpenGraph ω).Reachable
        (0, 0) y}.Infinite := by
    change {y | (PottsContinuity.rcInfiniteOpenGraph ω).Reachable
      (0, 0) y}.Infinite at hω
    rwa [Foundations.rcInfiniteOpenGraph_eq_PD] at hω
  have hboxFinite :
      ((latticeBox (0, 0) n : Finset LatticeVertex) : Set LatticeVertex).Finite :=
    (latticeBox (0, 0) n).finite_toSet
  obtain ⟨v, hvReach, hvOut⟩ :
      ∃ v, (PottsContinuity.PD.rcInfiniteOpenGraph ω).Reachable
        (0, 0) v ∧ v ∉ latticeBox (0, 0) n := by
    by_contra h
    apply hωPD
    apply hboxFinite.subset
    intro v hv
    by_contra hvout
    exact h ⟨v, hv, hvout⟩
  rcases hvReach with ⟨w⟩
  obtain ⟨z, hzBox, p, hpBox, y, hzy, hyOut⟩ :=
    PottsContinuity.PD.RCInfinite.walk_prefix_to_boundary w
      (center_mem_latticeBox (0, 0) n) hvOut
  have hzBoundary :
      z ∈ PottsContinuity.PD.vertexBoundary (latticeBox (0, 0) n) := by
    refine ⟨hzBox, y, ?_, hyOut⟩
    exact PottsContinuity.PD.squareLattice.mem_edgeSet.mp
      ((PottsContinuity.PD.RCInfinite.rcInfiniteOpenGraph_adj ω z y).mp hzy).1
  have hbox : PottsContinuity.PD.box n = latticeBox (0, 0) n := by
    ext x
    simp [PottsContinuity.PD.box, latticeBox, Finset.mem_product,
      Finset.mem_Icc]
  change ∃ z ∈ PottsContinuity.PD.vertexBoundary
      (latticeBox (0, 0) n),
    (PottsContinuity.PD.rcInfiniteOpenGraph ω).Reachable (0, 0) z
  exact ⟨z, hzBoundary, p.reachable⟩

/-- A power bound for the PD one-arm event forces the frozen wired infinite
cluster event to have probability zero. -/
theorem wired_P1_of_pdOneArm_power_bound
    (μ : Measure (squareLattice.edgeSet → Bool))
    (hμ : IsProbabilityMeasure μ)
    (ε : ℝ) (hε : 0 < ε)
    (hbound : ∀ n : ℕ, 1 ≤ n →
      μ.real (pdOneArmBoundaryEvent n) ≤ Real.rpow (n : ℝ) (-ε)) :
    μ {ω | {y | (PottsContinuity.rcInfiniteOpenGraph ω).Reachable
      (0, 0) y}.Infinite} = 0 := by
  classical
  let : IsProbabilityMeasure μ := hμ
  let S : Set (squareLattice.edgeSet → Bool) :=
    {ω | {y | (PottsContinuity.rcInfiniteOpenGraph ω).Reachable
      (0, 0) y}.Infinite}
  have hpow : Tendsto (fun n : ℕ => Real.rpow (n : ℝ) (-ε)) atTop (𝓝 0) := by
    convert (tendsto_rpow_neg_atTop hε).comp tendsto_natCast_atTop_atTop using 1
    rfl
  have htail : ∀ᶠ n : ℕ in atTop, μ.real S ≤ Real.rpow (n : ℝ) (-ε) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact (measureReal_mono (infinite_origin_cluster_subset_pdOneArm n)).trans
      (hbound n hn)
  have hreal : μ.real S ≤ 0 :=
    le_of_tendsto_of_tendsto tendsto_const_nhds hpow htail
  have hzero : μ.real S = 0 := le_antisymm hreal measureReal_nonneg
  exact (MeasureTheory.measureReal_eq_zero_iff (μ := μ) (s := S)).mp hzero

/-- The annulus-duality estimate `hAnnulusDuality` is the only planar input to
this P5 ⇒ P1 closure. -/
theorem p5_implies_p1_of_annulusDuality
    (q : Set.Ici (1 : ℝ))
    (μ : Measure (squareLattice.edgeSet → Bool))
    (hμ : IsRCInfiniteVolumeLimit
      (PottsContinuity.PD.FK.criticalParameters q).toP
      (PottsContinuity.PD.FK.criticalParameters q).toQ 1 μ)
    (hAnnulusDuality : ∃ c : ℝ, 0 < c ∧ ∀ j : ℕ, 3 ≤ j →
      (boxMeasure (PottsContinuity.PD.FK.criticalParameters q)
        1 (0, 0) (2 ^ j) : Measure LatticeConfiguration).real
          {ω | PottsContinuity.DualityExt.annulusOpenCrossing
            (2 ^ (j - 1)) ω} ≤ 1 - c) :
    μ {ω | {y | (PottsContinuity.rcInfiniteOpenGraph ω).Reachable
      (0, 0) y}.Infinite} = 0 := by
  obtain ⟨ε, hε, hpower⟩ :=
    wired_oneArm_power_bound_of_annulusDuality q μ hμ hAnnulusDuality
  exact wired_P1_of_pdOneArm_power_bound μ hμ.1 ε hε hpower

end PottsContinuity.Thm3.Easy
