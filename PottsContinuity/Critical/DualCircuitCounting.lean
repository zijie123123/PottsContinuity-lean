module

public import PottsContinuity.Critical.InfiniteFKCylinder
public import PottsContinuity.PD.Duality.CircuitEnclosure
public import PottsContinuity.PD.Duality.WholePlaneDualConfiguration
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.MeasureTheory.Measure.Real

@[expose] public section

namespace PottsContinuity.Critical

open PottsContinuity.PD.FK
open PottsContinuity.PD.FK.Medial
open PottsContinuity.PD.Duality
open MeasureTheory
open PottsContinuity.PD.RCInfinite

abbrev RCVolumeLimit := PottsContinuity.PD.IsRCInfiniteVolumeLimit

noncomputable section

/-- The primal edges crossed by the dual edges traced by a direction code. -/
def dualCodeCrossingEdgeList (x : LatticeVertex) (ds : List (Fin 4)) :
    List LatticeEdge :=
  (walkCodeEdgeList x ds).map wholePlaneDualCrossingEdgeEquiv

/-- The finite set of primal edges crossed by a dual direction code. -/
def dualCodeCrossingEdgeFinset (x : LatticeVertex) (ds : List (Fin 4)) :
    Finset LatticeEdge :=
  (dualCodeCrossingEdgeList x ds).toFinset

/-- Dual direction codes whose walk uses no dual edge twice. -/
def GoodDualWalkCode (x : LatticeVertex) (n : ℕ) :=
  {c : WalkCode n // (dualCodeCrossingEdgeList x c.toList).Nodup}

instance goodDualWalkCodeFintype (x : LatticeVertex) (n : ℕ) :
    Fintype (GoodDualWalkCode x n) := by
  classical
  unfold GoodDualWalkCode
  infer_instance

theorem dualCodeCrossingEdgeList_length (x : LatticeVertex) (ds : List (Fin 4)) :
    (dualCodeCrossingEdgeList x ds).length = ds.length := by
  simp [dualCodeCrossingEdgeList, walkCodeEdgeList_length]

private theorem dualCodeCrossingEdgeList_nodup_of_cycle {z : LatticeVertex}
    (p : squareLattice.Walk z z) (hp : p.IsCycle) :
    (dualCodeCrossingEdgeList z (walkCodeOfWalk p).toList).Nodup := by
  have hbase : (walkCodeEdgeList z (walkCodeOfWalk p).toList).Nodup := by
    apply List.Nodup.of_map Subtype.val
    rw [walkCodeEdgeList_val_ofWalk]
    exact hp.isTrail.edges_nodup
  unfold dualCodeCrossingEdgeList
  apply (List.nodup_map_iff_inj_on hbase).2
  intro a ha b hb hab
  exact wholePlaneDualCrossingEdgeEquiv.injective hab

theorem cycle_direction_code_isGoodDualWalkCode {z : LatticeVertex}
    (p : squareLattice.Walk z z) (hp : p.IsCycle) :
    ∃ c : GoodDualWalkCode z p.length, c.1 = walkCodeOfWalk p := by
  exact ⟨⟨walkCodeOfWalk p,
    dualCodeCrossingEdgeList_nodup_of_cycle p hp⟩, rfl⟩

theorem dualCodeCrossingEdgeFinset_card_of_good (x : LatticeVertex) (n : ℕ)
    (c : GoodDualWalkCode x n) :
    (dualCodeCrossingEdgeFinset x c.1.toList).card = n := by
  rw [dualCodeCrossingEdgeFinset, List.toFinset_card_of_nodup c.2]
  simp [dualCodeCrossingEdgeList_length]

/-- The union of closed-crossing-edge cylinders over every simple dual walk
of length `n` whose starting vertex lies within distance `n` of the origin. -/
def closedDualWalkCodeUnion (n : ℕ) : Set LatticeConfiguration :=
  ⋃ z : {z : LatticeVertex // z ∈ latticeBox (0, 0) n},
    ⋃ c : GoodDualWalkCode z.1 n,
      LatticeConfiguration.allClosed (dualCodeCrossingEdgeFinset z.1 c.1.toList)

private theorem two_mul_nat_add_one_le_three_pow (n : ℕ) :
    2 * (n : ℝ) + 1 ≤ (3 : ℝ) ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      have hpow : 1 ≤ (3 : ℝ) ^ n := one_le_pow₀ (by norm_num)
      calc
        2 * ((n + 1 : ℕ) : ℝ) + 1 = (2 * (n : ℝ) + 1) + 2 := by push_cast; ring
        _ ≤ (3 : ℝ) ^ n + 2 := by linarith
        _ ≤ (3 : ℝ) ^ n + 2 * (3 : ℝ) ^ n := by nlinarith
        _ = (3 : ℝ) ^ (n + 1) := by rw [pow_succ]; ring

private theorem three_pow_square (n : ℕ) :
    ((3 : ℝ) ^ n) ^ 2 = (9 : ℝ) ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      calc
        ((3 : ℝ) ^ (n + 1)) ^ 2 = ((3 : ℝ) ^ n * 3) ^ 2 := by
          rw [pow_succ (3 : ℝ) n]
        _ = ((3 : ℝ) ^ n) ^ 2 * 9 := by ring
        _ = (9 : ℝ) ^ n * 9 := by rw [ih]
        _ = (9 : ℝ) ^ (n + 1) := by rw [pow_succ (9 : ℝ) n]

private theorem square_box_count_le_nine_pow (n : ℕ) :
    ((2 * (n : ℝ) + 1) ^ 2) ≤ (9 : ℝ) ^ n := by
  have h := two_mul_nat_add_one_le_three_pow n
  have hnonneg : 0 ≤ 2 * (n : ℝ) + 1 := by positivity
  have hpow : 0 ≤ (3 : ℝ) ^ n := by positivity
  have hsq : (2 * (n : ℝ) + 1) ^ 2 ≤ ((3 : ℝ) ^ n) ^ 2 := by
    have hdiff : 0 ≤ (3 : ℝ) ^ n - (2 * (n : ℝ) + 1) := sub_nonneg.mpr h
    have hsum : 0 ≤ (3 : ℝ) ^ n + (2 * (n : ℝ) + 1) := add_nonneg hpow hnonneg
    nlinarith [mul_nonneg hdiff hsum]
  calc
    (2 * (n : ℝ) + 1) ^ 2 ≤ ((3 : ℝ) ^ n) ^ 2 := hsq
    _ = (9 : ℝ) ^ n := three_pow_square n

/-- The closed-circuit code union obeys a finite Peierls bound. The factor
`(2n+1)^2` counts possible starts and `4^n` counts direction codes. -/
theorem limit_closedDualWalkCodeUnion_le (θ : Parameters)
    (μ : Measure LatticeConfiguration)
    (hμ : RCVolumeLimit θ.toP θ.toQ 1 μ) (n : ℕ) :
    μ.real (closedDualWalkCodeUnion n) ≤
      (36 * (1 - openEnergy θ)) ^ n := by
  classical
  have : IsProbabilityMeasure μ := hμ.1
  let Starts := {z : LatticeVertex // z ∈ latticeBox (0, 0) n}
  have hstarts : (Fintype.card Starts : ℝ) = (2 * (n : ℝ) + 1) ^ 2 := by
    have hcard : Fintype.card Starts = (2 * n + 1) ^ 2 := by
      have hinterval : (Finset.Icc (-(n : ℤ)) (n : ℤ)).card = 2 * n + 1 := by
        rw [Int.card_Icc]
        have hcast : (n : ℤ) + 1 - (-(n : ℤ)) = ((2 * n + 1 : ℕ) : ℤ) := by
          push_cast
          omega
        rw [hcast, Int.toNat_natCast]
      change Fintype.card {z : LatticeVertex // z ∈ latticeBox (0, 0) n} = _
      rw [Fintype.card_coe]
      simp [latticeBox, Finset.card_product, hinterval]
      ring
    exact_mod_cast hcard
  have hcodes (z : LatticeVertex) :
      Fintype.card (GoodDualWalkCode z n) ≤ Fintype.card (WalkCode n) :=
    Fintype.card_le_of_injective Subtype.val Subtype.val_injective
  calc
    μ.real (closedDualWalkCodeUnion n) ≤
        ∑ z : Starts, μ.real (⋃ c : GoodDualWalkCode z.1 n,
          LatticeConfiguration.allClosed (dualCodeCrossingEdgeFinset z.1 c.1.toList)) :=
      MeasureTheory.measureReal_iUnion_fintype_le _
    _ ≤ ∑ z : Starts, ∑ c : GoodDualWalkCode z.1 n,
          μ.real (LatticeConfiguration.allClosed
            (dualCodeCrossingEdgeFinset z.1 c.1.toList)) :=
      Finset.sum_le_sum fun z _ => MeasureTheory.measureReal_iUnion_fintype_le _
    _ ≤ ∑ z : Starts, ∑ _c : GoodDualWalkCode z.1 n,
          (1 - openEnergy θ) ^ n := by
      apply Finset.sum_le_sum
      intro z hz
      apply Finset.sum_le_sum
      intro c hc
      have hprob := limit_allClosed_probability_upper θ μ hμ
        (dualCodeCrossingEdgeFinset z.1 c.1.toList)
      rw [dualCodeCrossingEdgeFinset_card_of_good] at hprob
      exact hprob
    _ ≤ ∑ z : Starts, (Fintype.card (WalkCode n) : ℝ) *
          (1 - openEnergy θ) ^ n := by
      apply Finset.sum_le_sum
      intro z hz
      have hcard := hcodes z.1
      have hconst :
          (∑ _c : GoodDualWalkCode z.1 n, (1 - openEnergy θ) ^ n) =
            (Fintype.card (GoodDualWalkCode z.1 n) : ℝ) *
              (1 - openEnergy θ) ^ n := by simp
      rw [hconst]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard)
        (pow_nonneg (sub_nonneg.mpr (openEnergy_le_one θ)) n)
    _ = (Fintype.card Starts : ℝ) *
          ((Fintype.card (WalkCode n) : ℝ) * (1 - openEnergy θ) ^ n) := by
      simp
    _ = (2 * (n : ℝ) + 1) ^ 2 *
          ((4 : ℝ) ^ n * (1 - openEnergy θ) ^ n) := by
      rw [hstarts, card_walkCode]
      push_cast
      rfl
    _ ≤ (9 : ℝ) ^ n *
          ((4 : ℝ) ^ n * (1 - openEnergy θ) ^ n) := by
      exact mul_le_mul_of_nonneg_right (square_box_count_le_nine_pow n)
        (mul_nonneg (pow_nonneg (by norm_num) n)
          (pow_nonneg (sub_nonneg.mpr (openEnergy_le_one θ)) n))
    _ = (36 * (1 - openEnergy θ)) ^ n := by
      rw [← mul_pow, ← mul_pow]
      ring

/-- Every primal edge crossing an edge of a closed-dual circuit is closed. -/
private theorem adjacent_coordinate_bounds {u v : LatticeVertex}
    (h : squareLattice.Adj u v) :
    u.1 - 1 ≤ v.1 ∧ v.1 ≤ u.1 + 1 ∧
      u.2 - 1 ≤ v.2 ∧ v.2 ≤ u.2 + 1 := by
  rcases (squareLattice_adj_iff u v).mp h with ⟨hxy, hy⟩ | ⟨hx, hxy⟩ <;> omega

/-- Every vertex of a lattice walk stays within its length in each coordinate
of its initial vertex. -/
theorem walk_support_coordinate_bounds {z w : LatticeVertex}
    (p : squareLattice.Walk z w) :
    ∀ x ∈ p.support,
      z.1 - (p.length : ℤ) ≤ x.1 ∧ x.1 ≤ z.1 + (p.length : ℤ) ∧
        z.2 - (p.length : ℤ) ≤ x.2 ∧ x.2 ≤ z.2 + (p.length : ℤ) := by
  induction p with
  | nil =>
      intro x hx
      simp only [SimpleGraph.Walk.support_nil, List.mem_singleton] at hx
      subst x
      simp
  | @cons u v w h p ih =>
      intro x hx
      simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hx
      rcases hx with rfl | hx
      · simp only [SimpleGraph.Walk.length_cons, Nat.cast_add, Nat.cast_one]
        constructor <;> omega
      · have htail := ih x hx
        have hadj := adjacent_coordinate_bounds h
        simp only [SimpleGraph.Walk.length_cons, Nat.cast_add, Nat.cast_one] at *
        omega

/-- A closed walk with nonzero ray index at the origin must start within the
coordinate box whose radius is its length. -/
theorem cycle_start_mem_box_of_rayIndex_ne_zero {z : LatticeVertex}
    (p : squareLattice.Walk z z) (hidx : rayIndex (0, 0) p ≠ 0) :
    z ∈ latticeBox (0, 0) p.length := by
  have hsupport := walk_support_coordinate_bounds p
  rw [mem_latticeBox]
  constructor
  · constructor
    · by_contra hleft
      have hleft' : z.1 + (p.length : ℤ) < 0 := by
        simp only [zero_sub] at hleft
        omega
      apply hidx
      apply rayIndex_zero_of_right (0, 0) p
      intro x hx
      have hx' := hsupport x hx
      omega
    · by_contra hright
      have hright' : 0 ≤ z.1 - (p.length : ℤ) := by
        simp only [zero_add] at hright
        omega
      apply hidx
      rw [rayIndex_left_telescope (0, 0) p]
      · simp
      · intro x hx
        have hx' := hsupport x hx
        omega
  · constructor
    · by_contra hbelow
      have hbelow' : z.2 + (p.length : ℤ) < 0 := by
        simp only [zero_sub] at hbelow
        omega
      apply hidx
      apply rayIndex_zero_of_level (0, 0) p 1
      intro x hx
      have hx' := hsupport x hx
      have hxneg : x.2 < 0 := by omega
      simp [hxneg]
    · by_contra habove
      have habove' : 0 ≤ z.2 - (p.length : ℤ) := by
        simp only [zero_add] at habove
        omega
      apply hidx
      apply rayIndex_zero_of_level (0, 0) p 0
      intro x hx
      have hx' := hsupport x hx
      have hxnonneg : ¬ x.2 < 0 := by omega
      simp [hxnonneg]


theorem closedDualCircuit_crossing_primal_edge_closed (ω : LatticeConfiguration)
    {z : LatticeVertex} (p : squareLattice.Walk z z)
    (hclosed : ∀ u w, s(u,w) ∈ p.edges → (wholePlaneClosedDualGraph ω).Adj u w)
    (e : LatticeEdge) (he : e.val ∈ p.edges) :
    ω (wholePlaneDualCrossingEdgeEquiv e) = false := by
  let u : LatticeVertex := e.val.out.1
  let w : LatticeVertex := e.val.out.2
  have hout : s(u,w) = e.val := Quot.out_eq e.val
  have hadj := hclosed u w (hout ▸ he)
  rw [← wholePlaneOpenPrimalGraph_dualConfiguration_eq ω] at hadj
  change ∃ hadj : squareLattice.Adj u w,
      wholePlaneDualConfigurationHomeomorph ω
        ⟨s(u,w), squareLattice.mem_edgeSet.mpr hadj⟩ = true at hadj
  obtain ⟨hgraph, hopen⟩ := hadj
  have heq :
      (⟨s(u,w), squareLattice.mem_edgeSet.mpr hgraph⟩ : LatticeEdge) = e := by
    apply Subtype.ext
    exact hout
  rw [heq, wholePlaneDualConfigurationHomeomorph_apply] at hopen
  simpa using hopen

/-- A finite open cluster produces a nonempty closed-dual circuit code whose
crossing primal edges are all closed. -/
theorem finiteCluster_enclosedCircuit_mem_codeUnion (ω : LatticeConfiguration)
    (hf : (PottsContinuity.PD.RCInfinite.cluster ω (0, 0)).Finite) :
    ∃ n, 0 < n ∧ ω ∈ closedDualWalkCodeUnion n := by
  obtain ⟨z, p, hcycle, hclosed, hidx, _⟩ :=
    finite_cluster_has_surrounding_closedDual_circuit ω (0, 0) hf
  have hpos : 0 < p.length := by
    by_contra h
    have hzero : p.length = 0 := Nat.eq_zero_of_not_pos h
    cases p with
    | nil => simp [rayIndex] at hidx
    | @cons u v w h tail => simp [SimpleGraph.Walk.length_cons] at hzero
  have hbox := cycle_start_mem_box_of_rayIndex_ne_zero p hidx
  obtain ⟨c, hc⟩ := cycle_direction_code_isGoodDualWalkCode p hcycle
  have hclosedEvent :
      ω ∈ LatticeConfiguration.allClosed
        (dualCodeCrossingEdgeFinset z (walkCodeOfWalk p).toList) := by
    intro e he
    have heList : e ∈ dualCodeCrossingEdgeList z (walkCodeOfWalk p).toList :=
      List.mem_toFinset.mp he
    obtain ⟨d, hd, hde⟩ := List.mem_map.mp heList
    have hdval : d.val ∈ p.edges := by
      have hmap : d.val ∈
          (walkCodeEdgeList z (walkCodeOfWalk p).toList).map Subtype.val :=
        List.mem_map.mpr ⟨d, hd, rfl⟩
      rw [walkCodeEdgeList_val_ofWalk] at hmap
      exact hmap
    rw [← hde]
    exact closedDualCircuit_crossing_primal_edge_closed ω p hclosed d hdval
  have hmem : ω ∈ closedDualWalkCodeUnion p.length := by
    apply Set.mem_iUnion.mpr ⟨⟨z, hbox⟩, ?_⟩
    apply Set.mem_iUnion.mpr ⟨c, ?_⟩
    rw [hc]
    exact hclosedEvent
  exact ⟨p.length, hpos, hmem⟩

/-- Every configuration with a finite origin cluster lies in one of the
countable closed-dual circuit code unions. -/
theorem finiteCluster_subset_closedDualCircuitUnion :
    {ω : LatticeConfiguration | (PottsContinuity.PD.RCInfinite.cluster ω (0, 0)).Finite} ⊆
      ⋃ n : ℕ, closedDualWalkCodeUnion (n + 1) := by
  intro ω hω
  obtain ⟨n, hn, hmem⟩ := finiteCluster_enclosedCircuit_mem_codeUnion ω hω
  cases n with
  | zero => omega
  | succ n =>
      exact Set.mem_iUnion.mpr ⟨n, by simpa using hmem⟩

/-- All possible finite origin-cluster circuits, indexed by positive length. -/
def closedDualCircuitCodeUnionAll : Set LatticeConfiguration :=
  ⋃ n : ℕ, closedDualWalkCodeUnion (n + 1)

/-- The countable union of closed-circuit events is bounded by the geometric
series obtained from the per-length Peierls estimate. -/
theorem limit_closedDualCircuitUnion_real_le (θ : Parameters)
    (μ : Measure LatticeConfiguration)
    (hμ : RCVolumeLimit θ.toP θ.toQ 1 μ)
    (hsmall : 36 * (1 - openEnergy θ) < 1) :
    μ.real closedDualCircuitCodeUnionAll ≤
      (36 * (1 - openEnergy θ)) * (1 - 36 * (1 - openEnergy θ))⁻¹ := by
  classical
  have : IsProbabilityMeasure μ := hμ.1
  let a : ℝ := 36 * (1 - openEnergy θ)
  have ha0 : 0 ≤ a := mul_nonneg (by norm_num)
    (sub_nonneg.mpr (openEnergy_le_one θ))
  have ha1 : a < 1 := by simpa [a] using hsmall
  have hgeo : HasSum (fun n : ℕ => a ^ (n + 1)) (a * (1 - a)⁻¹) := by
    convert (hasSum_geometric_of_lt_one ha0 ha1).mul_left a using 1
    ext n
    rw [pow_succ]
    ring
  have hpoint (n : ℕ) :
      μ (closedDualWalkCodeUnion (n + 1)) ≤ ENNReal.ofReal (a ^ (n + 1)) := by
    have hbound := limit_closedDualWalkCodeUnion_le θ μ hμ (n + 1)
    have hbound' : μ.real (closedDualWalkCodeUnion (n + 1)) ≤ a ^ (n + 1) := by
      simpa [a, Nat.add_assoc] using hbound
    exact (ENNReal.toReal_le_toReal (measure_ne_top μ _)
      ENNReal.ofReal_ne_top).mp (by
        simpa [Measure.real, ENNReal.toReal_ofReal (pow_nonneg ha0 _)] using hbound')
  have hsumBound :
      (∑' n : ℕ, μ (closedDualWalkCodeUnion (n + 1))) ≤
        ∑' n : ℕ, ENNReal.ofReal (a ^ (n + 1)) :=
    ENNReal.tsum_le_tsum hpoint
  have hsumFinite :
      (∑' n : ℕ, ENNReal.ofReal (a ^ (n + 1))) ≠ ⊤ :=
    Summable.tsum_ofReal_ne_top hgeo.summable
  have hmeasure := measure_iUnion_le (μ := μ)
    (fun n : ℕ => closedDualWalkCodeUnion (n + 1))
  have hreal : μ.real closedDualCircuitCodeUnionAll ≤
      (∑' n : ℕ, ENNReal.ofReal (a ^ (n + 1))).toReal := by
    exact ENNReal.toReal_mono hsumFinite (hmeasure.trans hsumBound)
  have hsumReal :
      (∑' n : ℕ, ENNReal.ofReal (a ^ (n + 1))).toReal =
        a * (1 - a)⁻¹ := by
    rw [ENNReal.tsum_toReal_eq (fun _ => ENNReal.ofReal_ne_top)]
    simp_rw [ENNReal.toReal_ofReal (pow_nonneg ha0 _)]
    exact hgeo.tsum_eq
  rw [hsumReal] at hreal
  simpa [a] using hreal

/-- A parameter choice, depending on the cluster weight, with a uniformly
small closed-dual edge bound. -/
def highParameterForQ (q : Set.Ici (1 : ℝ)) : Parameters where
  val := q
  property := q.property
  edgeProbability := ⟨72 * (q : ℝ) / (72 * (q : ℝ) + 1), by
    have hqpos : 0 < (q : ℝ) := lt_of_lt_of_le zero_lt_one q.property
    constructor
    · apply div_pos <;> positivity
    · apply (div_lt_iff₀ (by positivity)).2
      nlinarith [q.property]
  ⟩

theorem highParameterForQ_openEnergy (q : Set.Ici (1 : ℝ)) :
    openEnergy (highParameterForQ q) = (72 : ℝ) / 73 := by
  unfold openEnergy highParameterForQ edgeParameter
  have hqpos : 0 < (q : ℝ) := lt_of_lt_of_le zero_lt_one q.property
  have hq : (q : ℝ) ≠ 0 := ne_of_gt hqpos
  have hd : 72 * (q : ℝ) + 1 ≠ 0 := by positivity
  field_simp [hq, hd];
  ring

/-- The total probability of any closed dual circuit surrounding the origin is
strictly less than one at this high parameter. -/
theorem limit_closedDualCircuitUnion_high (q : Set.Ici (1 : ℝ))
    (μ : Measure LatticeConfiguration)
    (hμ : RCVolumeLimit (highParameterForQ q).toP (highParameterForQ q).toQ 1 μ) :
    μ.real closedDualCircuitCodeUnionAll ≤ (36 : ℝ) / 37 := by
  have hsmall :
      36 * (1 - openEnergy (highParameterForQ q)) < 1 := by
    rw [highParameterForQ_openEnergy]
    norm_num
  have h := limit_closedDualCircuitUnion_real_le (highParameterForQ q) μ hμ hsmall
  rw [highParameterForQ_openEnergy] at h
  norm_num at h
  exact h

/-- Every wired infinite-volume limit has positive origin-cluster probability
at the high parameter above. -/
theorem limit_infiniteAt_real_pos_high (q : Set.Ici (1 : ℝ))
    (μ : Measure LatticeConfiguration)
    (hμ : RCVolumeLimit (highParameterForQ q).toP (highParameterForQ q).toQ 1 μ) :
    0 < μ.real (PottsContinuity.PD.RCInfinite.infiniteAt (0, 0)) := by
  have : IsProbabilityMeasure μ := hμ.1
  have hcircuits := limit_closedDualCircuitUnion_high q μ hμ
  have hsubset :
      (PottsContinuity.PD.RCInfinite.infiniteAt (0, 0))ᶜ ⊆
        closedDualCircuitCodeUnionAll := by
    intro ω hω
    change ¬ ω ∈ PottsContinuity.PD.RCInfinite.infiniteAt (0, 0) at hω
    change ¬ ((PottsContinuity.PD.RCInfinite.cluster ω (0, 0)).Infinite) at hω
    have hnotnot :
        ¬¬ (PottsContinuity.PD.RCInfinite.cluster ω (0, 0)).Finite := by
      exact hω
    exact finiteCluster_subset_closedDualCircuitUnion (not_not.mp hnotnot)
  have hcompl :
      μ.real (PottsContinuity.PD.RCInfinite.infiniteAt (0, 0))ᶜ ≤
        (36 : ℝ) / 37 :=
    (measureReal_mono hsubset).trans hcircuits
  rw [probReal_compl_eq_one_sub
    (PottsContinuity.PD.RCInfinite.measurableSet_infiniteAt (0, 0))] at hcompl
  nlinarith

/-- The positive real probability in the preceding estimate implies positive
measure of the infinite-cluster event. -/
theorem limit_infiniteAt_measure_pos_high (q : Set.Ici (1 : ℝ))
    (μ : Measure LatticeConfiguration)
    (hμ : RCVolumeLimit (highParameterForQ q).toP (highParameterForQ q).toQ 1 μ) :
    0 < μ (PottsContinuity.PD.RCInfinite.infiniteAt (0, 0)) := by
  have hpos := limit_infiniteAt_real_pos_high q μ hμ
  have hne : μ (PottsContinuity.PD.RCInfinite.infiniteAt (0, 0)) ≠ 0 := by
    intro hz
    have hz' : μ.real (PottsContinuity.PD.RCInfinite.infiniteAt (0, 0)) = 0 := by
      simp [Measure.real, hz]
    linarith
  exact bot_lt_iff_ne_bot.mpr hne


end
end PottsContinuity.Critical
