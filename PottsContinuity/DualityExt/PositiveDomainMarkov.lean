module

public import PottsContinuity.DualityExt.GeneralFiniteDuality
public import PottsContinuity.PD.FK.ConditionalLaw
public import PottsContinuity.PD.FK.SubgraphComparison
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Finite domain Markov conditioning for every positive cluster weight

The PD conditional-law API is parameterized by `q ≥ 1`. This file proves the
same finite normalization identity for the positive-`q` FK law used by the
rectangle duality extension. A full state on the removed edge set induces its
boundary partition by the actual open bonds in that state.
-/

@[expose] public section

namespace PottsContinuity.DualityExt

open PottsContinuity.PD.FK
open PottsContinuity.PD.FK.FiniteProbability
open scoped BigOperators

noncomputable section

variable {V : Type*} [Finite V] {G : SimpleGraph V}

local instance positiveDMPConfigurationFintype : Fintype (Configuration G) :=
  Fintype.ofFinite _
local instance positiveDMPConfigurationDecidableEq : DecidableEq (Configuration G) :=
  Classical.decEq _
local instance positiveDMPEdgeFintype : Fintype G.edgeSet := Fintype.ofFinite _
local instance positiveDMPEdgeDecidableEq : DecidableEq G.edgeSet := Classical.decEq _
local instance positiveDMPRemainingFintype (R : Configuration G) :
    Fintype (RemainingConfiguration G R) := Fintype.ofFinite _
local instance positiveDMPRemovedFintype (R : Configuration G) :
    Fintype (RemovedConfiguration G R) := Fintype.ofFinite _

/-- The FK weight on the edges not in `R`, with all vertices retained. -/
def positiveRemainingWeight (q p : ℝ) (ξ : BoundaryCondition V)
    (R : Configuration G) (A : RemainingConfiguration G R) : ℝ :=
  p ^ A.val.card * (1 - p) ^ (Nat.card G.edgeSet - R.card - A.val.card) *
    q ^ componentCount G ξ A.val

theorem positiveRemainingWeight_pos {q p : ℝ} (hq : 0 < q)
    (hp : 0 < p) (hp1 : p < 1) (ξ : BoundaryCondition V)
    (R : Configuration G) (A : RemainingConfiguration G R) :
    0 < positiveRemainingWeight q p ξ R A := by
  unfold positiveRemainingWeight
  exact mul_pos
    (mul_pos (pow_pos hp _) (pow_pos (sub_pos.mpr hp1) _))
    (pow_pos hq _)

/-- The FK law on the unremoved edges, normalized with positive weights. -/
def positiveRemainingLaw (q p : ℝ) (hq : 0 < q) (hp : 0 < p) (hp1 : p < 1)
    (ξ : BoundaryCondition V) (R : Configuration G) :
    PMF (RemainingConfiguration G R) :=
  FiniteProbability.pmf (positiveRemainingWeight q p ξ R)
    (positiveRemainingWeight_pos hq hp hp1 ξ R)

/-- The partition function for the positive-`q` FK weight. -/
def positiveFKPartitionFunction (G : SimpleGraph V) (q p : ℝ)
    (ξ : BoundaryCondition V) : ℝ :=
  FiniteProbability.partition (positiveFKWeight G q p ξ)

theorem positiveFKWeight_pos' {q p : ℝ} (hq : 0 < q)
    (hp : 0 < p) (hp1 : p < 1) (ξ : BoundaryCondition V)
    (A : Configuration G) : 0 < positiveFKWeight G q p ξ A := by
  unfold positiveFKWeight
  exact mul_pos
    (mul_pos (pow_pos hp _) (pow_pos (sub_pos.mpr hp1) _))
    (pow_pos hq _)

private theorem positiveFKPartitionFunction_pos {q p : ℝ} (hq : 0 < q)
    (hp : 0 < p) (hp1 : p < 1) (ξ : BoundaryCondition V) :
    0 < positiveFKPartitionFunction G q p ξ :=
  FiniteProbability.partition_pos _ (positiveFKWeight_pos' hq hp hp1 ξ)

/-- The normalized configuration mass for the positive-`q` FK law. -/
def positiveFKProbability (q p : ℝ) (ξ : BoundaryCondition V)
    (A : Configuration G) : ℝ :=
  positiveFKWeight G q p ξ A / positiveFKPartitionFunction G q p ξ

 theorem positiveFKProbability_pos {q p : ℝ} (hq : 0 < q)
    (hp : 0 < p) (hp1 : p < 1) (ξ : BoundaryCondition V)
    (A : Configuration G) : 0 < positiveFKProbability q p ξ A :=
  div_pos (positiveFKWeight_pos' hq hp hp1 ξ A)
    (positiveFKPartitionFunction_pos hq hp hp1 ξ)

theorem positiveFKLaw_apply {q p : ℝ} (hq : 0 < q)
    (hp : 0 < p) (hp1 : p < 1) (ξ : BoundaryCondition V)
    (A : Configuration G) :
    positiveFKLaw G q p hq hp hp1 ξ A =
      ENNReal.ofReal (positiveFKProbability q p ξ A) := by
  unfold positiveFKLaw positiveFKProbability positiveFKPartitionFunction
  rw [FiniteProbability.pmf_apply]

/-- The Bernoulli contribution of an assignment to the removed edge set. -/
def positiveRemovedWeight (p : ℝ) (R : Configuration G)
    (H : RemovedConfiguration G R) : ℝ :=
  p ^ H.val.card * (1 - p) ^ (R.card - H.val.card)

omit [Finite V] in
private theorem positiveRemovedWeight_pos {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (R : Configuration G) (H : RemovedConfiguration G R) :
    0 < positiveRemovedWeight p R H := by
  unfold positiveRemovedWeight
  exact mul_pos (pow_pos hp _) (pow_pos (sub_pos.mpr hp1) _)

/-- The FK weight factors over the remaining and frozen configurations, with
the frozen open paths incorporated into the boundary partition. -/
theorem positiveFKWeight_union_frozen_factorization {q p : ℝ}
    (ξ : BoundaryCondition V)
    (R : Configuration G) (A : RemainingConfiguration G R)
    (H : RemovedConfiguration G R) :
    positiveFKWeight G q p ξ (A.val ∪ H.val) =
      positiveRemainingWeight q p (frozenBoundary ξ H.val) R A *
        positiveRemovedWeight p R H := by
  rw [positiveFKWeight, positiveRemainingWeight, positiveRemovedWeight,
    Finset.card_union_of_disjoint (remaining_disjoint_removed G R A H),
    componentCount_union_frozen,
    closed_edge_count_split G R A H, pow_add, pow_add]
  ring

/-- Every specified state on a finite set of removed edges has positive mass. -/
theorem positiveFrozenStateEvent_support {q p : ℝ} (hq : 0 < q)
    (hp : 0 < p) (hp1 : p < 1) (ξ : BoundaryCondition V)
    (R : Configuration G) (H : RemovedConfiguration G R) :
    ∃ C ∈ frozenStateEvent R H, C ∈
      (positiveFKLaw G q p hq hp hp1 ξ).support := by
  refine ⟨H.val, ?_, ?_⟩
  · exact Finset.inter_eq_left.mpr H.property
  · change positiveFKLaw G q p hq hp hp1 ξ H.val ≠ 0
    rw [positiveFKLaw_apply]
    exact ne_of_gt (ENNReal.ofReal_pos.mpr
      (positiveFKProbability_pos hq hp hp1 ξ H.val))

omit [Finite V] in
private theorem positiveRestored_mem_frozen_iff (R : Configuration G)
    (H B : RemovedConfiguration G R) (A : RemainingConfiguration G R) :
    (A.val ∪ B.val) ∈ frozenStateEvent R H ↔ B = H := by
  change (A.val ∪ B.val) ∩ R = H.val ↔ B = H
  rw [Finset.union_inter_distrib_right,
    Finset.disjoint_iff_inter_eq_empty.mp A.property, Finset.empty_union,
    Finset.inter_eq_left.mpr B.property]
  exact Subtype.val_injective.eq_iff

private theorem positiveFrozenEvent_mass_sum {q p : ℝ}
    (hq : 0 < q) (hp : 0 < p) (hp1 : p < 1) (ξ : BoundaryCondition V)
    (R : Configuration G) (H : RemovedConfiguration G R) :
    (∑' C, (frozenStateEvent R H).indicator
      (positiveFKLaw G q p hq hp hp1 ξ) C) =
      ∑ A : RemainingConfiguration G R,
        positiveFKLaw G q p hq hp hp1 ξ (A.val ∪ H.val) := by
  classical
  rw [tsum_fintype, ← (configurationSplitEquiv G R).symm.sum_comp]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro A hA
  simp only [configurationSplitEquiv_symm_apply, Set.indicator_apply,
    positiveRestored_mem_frozen_iff]
  simp

/-- The probability mass of a configuration in a frozen fiber, normalized over
that fiber, is the remaining-edge FK probability. -/
private theorem positive_frozen_fiber_probability_ratio {q p : ℝ}
    (hq : 0 < q) (hp : 0 < p) (hp1 : p < 1) (ξ : BoundaryCondition V)
    (R : Configuration G) (H : RemovedConfiguration G R)
    (A : RemainingConfiguration G R) :
    positiveFKProbability q p ξ (A.val ∪ H.val) /
      (∑ B : RemainingConfiguration G R,
        positiveFKProbability q p ξ (B.val ∪ H.val)) =
      positiveRemainingWeight q p (frozenBoundary ξ H.val) R A /
        FiniteProbability.partition
          (positiveRemainingWeight q p (frozenBoundary ξ H.val) R) := by
  classical
  let Z := positiveFKPartitionFunction G q p ξ
  let c := positiveRemovedWeight p R H
  let w := positiveRemainingWeight q p (frozenBoundary ξ H.val) R
  have hZ : 0 < Z := by
    dsimp [Z]
    exact positiveFKPartitionFunction_pos hq hp hp1 ξ
  have hc : 0 < c := positiveRemovedWeight_pos hp hp1 R H
  have hw : 0 < FiniteProbability.partition w :=
    FiniteProbability.partition_pos w
      (positiveRemainingWeight_pos hq hp hp1 (frozenBoundary ξ H.val) R)
  have hpoint (B : RemainingConfiguration G R) :
      positiveFKProbability q p ξ (B.val ∪ H.val) = w B * c / Z := by
    rw [positiveFKProbability, positiveFKPartitionFunction,
      positiveFKWeight_union_frozen_factorization ξ R B H]
    rfl
  have hsum :
      (∑ B : RemainingConfiguration G R,
        positiveFKProbability q p ξ (B.val ∪ H.val)) =
        FiniteProbability.partition w * c / Z := by
    calc
      _ = ∑ B : RemainingConfiguration G R, w B * c / Z := by
        apply Finset.sum_congr rfl
        intro B hB
        exact hpoint B
      _ = (∑ B : RemainingConfiguration G R, w B) * c / Z := by
        rw [← Finset.sum_div, Finset.sum_mul]
      _ = FiniteProbability.partition w * c / Z := rfl
  rw [hpoint A, hsum]
  have hzne : Z ≠ 0 := ne_of_gt hZ
  have hcne : c ≠ 0 := ne_of_gt hc
  have hwne : FiniteProbability.partition w ≠ 0 := ne_of_gt hw
  have hpartne : FiniteProbability.partition
      (positiveRemainingWeight q p (frozenBoundary ξ H.val) R) ≠ 0 :=
    ne_of_gt hw
  field_simp [hzne, hcne, hwne, hpartne]; ring

/-- The original law normalized on one complete frozen-edge fiber. -/
def positiveFrozenFiberLaw {q p : ℝ}
    (hq : 0 < q) (hp : 0 < p) (hp1 : p < 1) (ξ : BoundaryCondition V)
    (R : Configuration G) (H : RemovedConfiguration G R) :
    PMF (RemainingConfiguration G R) :=
  FiniteProbability.pmf
    (fun A : RemainingConfiguration G R =>
      positiveFKProbability q p ξ (A.val ∪ H.val))
    (fun A => positiveFKProbability_pos hq hp hp1 ξ (A.val ∪ H.val))

theorem positiveFrozenFiberLaw_eq_positiveRemainingLaw {q p : ℝ}
    (hq : 0 < q) (hp : 0 < p) (hp1 : p < 1) (ξ : BoundaryCondition V)
    (R : Configuration G) (H : RemovedConfiguration G R) :
    positiveFrozenFiberLaw hq hp hp1 ξ R H =
      positiveRemainingLaw q p hq hp hp1 (frozenBoundary ξ H.val) R := by
  ext A
  simp only [positiveFrozenFiberLaw, positiveRemainingLaw,
    FiniteProbability.pmf_apply, FiniteProbability.partition]
  rw [positive_frozen_fiber_probability_ratio hq hp hp1 ξ R H A]
  rfl

/-- Conditioning the positive-`q` FK law on a complete edge state and retaining
all other edges gives exactly the induced frozen-boundary FK law. -/
theorem positive_law_filter_frozen_map_remaining {q p : ℝ}
    (hq : 0 < q) (hp : 0 < p) (hp1 : p < 1) (ξ : BoundaryCondition V)
    (R : Configuration G) (H : RemovedConfiguration G R) :
    ((positiveFKLaw G q p hq hp hp1 ξ).filter (frozenStateEvent R H)
      (positiveFrozenStateEvent_support hq hp hp1 ξ R H)).map
        (fun C => (configurationSplitEquiv G R C).1) =
      positiveRemainingLaw q p hq hp hp1 (frozenBoundary ξ H.val) R := by
  classical
  rw [← positiveFrozenFiberLaw_eq_positiveRemainingLaw hq hp hp1 ξ R H]
  ext A
  rw [PMF.map_apply, tsum_fintype,
    ← (configurationSplitEquiv G R).symm.sum_comp, Fintype.sum_prod_type]
  have hsplit (B : RemainingConfiguration G R) (K : RemovedConfiguration G R) :
      configurationSplitEquiv G R (B.val ∪ K.val) = (B, K) :=
    (configurationSplitEquiv G R).apply_symm_apply (B, K)
  simp_rw [PMF.filter_apply]
  rw [positiveFrozenEvent_mass_sum hq hp hp1 ξ R H]
  simp only [configurationSplitEquiv_symm_apply, hsplit,
    Set.indicator_apply, positiveRestored_mem_frozen_iff, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ,
    ite_true]
  rw [positiveFrozenFiberLaw, FiniteProbability.pmf_apply]
  simp_rw [positiveFKLaw_apply]
  rw [← ENNReal.ofReal_sum_of_nonneg
    (fun B _ => (positiveFKProbability_pos hq hp hp1 ξ (B.val ∪ H.val)).le)]
  have hpos : 0 < ∑ B : RemainingConfiguration G R,
      positiveFKProbability q p ξ (B.val ∪ H.val) :=
    Finset.sum_pos (fun B _ => positiveFKProbability_pos hq hp hp1 ξ (B.val ∪ H.val))
      Finset.univ_nonempty
  rw [FiniteProbability.partition, ENNReal.ofReal_div_of_pos hpos]
  rfl

/-- A condition used to compare positive FK laws depends on the boundary
partition, not on the set chosen to name that boundary. -/
theorem positiveFKLaw_eq_of_partition_eq {q p : ℝ}
    (hq : 0 < q) (hp : 0 < p) (hp1 : p < 1)
    (ξ η : BoundaryCondition V) (hξη : ξ.partition = η.partition) :
    positiveFKLaw G q p hq hp hp1 ξ = positiveFKLaw G q p hq hp hp1 η := by
  have hweight : positiveFKWeight G q p ξ = positiveFKWeight G q p η := by
    funext A
    unfold positiveFKWeight
    simp only [componentCount, componentSetoid, hξη]
  have hZ : positiveFKPartitionFunction G q p ξ =
      positiveFKPartitionFunction G q p η := by
    unfold positiveFKPartitionFunction
    exact congrArg FiniteProbability.partition hweight
  have hpoint (A : Configuration G) :
      positiveFKProbability q p ξ A = positiveFKProbability q p η A := by
    unfold positiveFKProbability
    rw [congrFun hweight A, hZ]
  ext A
  rw [positiveFKLaw_apply hq hp hp1 ξ A,
    positiveFKLaw_apply hq hp hp1 η A, hpoint A]

/-- Remaining-edge laws also depend on a boundary condition only through its
partition. -/
theorem positiveRemainingLaw_eq_of_partition_eq {q p : ℝ}
    (hq : 0 < q) (hp : 0 < p) (hp1 : p < 1)
    (ξ η : BoundaryCondition V) (hξη : ξ.partition = η.partition)
    (R : Configuration G) :
    positiveRemainingLaw q p hq hp hp1 ξ R =
      positiveRemainingLaw q p hq hp hp1 η R := by
  have hw : positiveRemainingWeight q p ξ R = positiveRemainingWeight q p η R := by
    funext A
    simp only [positiveRemainingWeight, componentCount, componentSetoid, hξη]
  have hpart := congrArg FiniteProbability.partition hw
  ext A
  simp only [positiveRemainingLaw, FiniteProbability.pmf_apply]
  rw [congrFun hw A, hpart]

/-- Extending a graph by leaving extra edges closed identifies its law with the
remaining-edge weight, including its actual vertex carrier. -/
theorem positive_law_subgraphRemaining_map {W : SimpleGraph V}
    (hGW : G ≤ W) {q p : ℝ} (hq : 0 < q) (hp : 0 < p) (hp1 : p < 1)
    (ξ : BoundaryCondition V) :
    (positiveFKLaw G q p hq hp hp1 ξ).map
        (subgraphRemainingConfigurationEquiv hGW) =
      positiveRemainingLaw q p hq hp hp1 ξ (subgraphRemovedEdges G W) := by
  let R := subgraphRemovedEdges G W
  let e := subgraphRemainingConfigurationEquiv hGW
  have hweight (A : Configuration G) :
      positiveFKWeight G q p ξ A =
        positiveRemainingWeight q p ξ R (e A) := by
    have hc : componentCount W ξ (subgraphConfigurationEmbedding hGW A) =
        componentCount G ξ A := by
      simp only [componentCount, componentSetoid,
        openGraph_subgraphConfigurationEmbedding]
    have hcard : Nat.card W.edgeSet - R.card = Nat.card G.edgeSet := by
      exact subgraph_edge_card hGW
    have hval : (e A).val = subgraphConfigurationEmbedding hGW A := rfl
    rw [positiveFKWeight, positiveRemainingWeight, hval, hc]
    change p ^ A.card * (1 - p) ^ (Nat.card G.edgeSet - A.card) *
        q ^ componentCount G ξ A =
      p ^ (A.map (subgraphEdgeEmbedding hGW)).card *
        (1 - p) ^ (Nat.card W.edgeSet - R.card -
          (A.map (subgraphEdgeEmbedding hGW)).card) *
        q ^ componentCount G ξ A
    rw [← hcard]
    rw [Finset.card_map]
  unfold positiveFKLaw positiveRemainingLaw
  apply FiniteProbability.pmf_map_equiv_of_weight_eq
  intro A
  exact hweight A

/-- For any boundary condition, the FK law on an edge subgraph with the
partition induced by the forced-open deleted bonds is the host law conditioned
on every deleted bond being open. -/
theorem positive_subgraph_eq_conditioned_open {W : SimpleGraph V}
    (hGW : G ≤ W) {q p : ℝ} (hq : 0 < q) (hp : 0 < p) (hp1 : p < 1)
    (ξ : BoundaryCondition V) :
    (positiveFKLaw G q p hq hp hp1
      (frozenBoundary ξ (subgraphRemovedEdges G W))).map
        (subgraphRemainingConfigurationEquiv hGW) =
      ((positiveFKLaw W q p hq hp hp1 ξ).filter
        (frozenStateEvent (subgraphRemovedEdges G W)
          (⟨subgraphRemovedEdges G W, Finset.Subset.rfl⟩ :
            RemovedConfiguration W (subgraphRemovedEdges G W)))
        (positiveFrozenStateEvent_support hq hp hp1 ξ
          (subgraphRemovedEdges G W)
          ⟨subgraphRemovedEdges G W, Finset.Subset.rfl⟩)).map
        (fun C => (configurationSplitEquiv W
          (subgraphRemovedEdges G W) C).1) := by
  let R := subgraphRemovedEdges G W
  let H : RemovedConfiguration W R := ⟨R, Finset.Subset.rfl⟩
  have hcondition := positive_law_filter_frozen_map_remaining
    (G := W) hq hp hp1 ξ R H
  calc
    _ = positiveRemainingLaw q p hq hp hp1 (frozenBoundary ξ R) R := by
          simpa only [R] using
            (positive_law_subgraphRemaining_map (G := G) hGW hq hp hp1
              (frozenBoundary ξ R))
    _ = _ := by
          simpa only [R, H] using hcondition.symm

omit [Finite V] in
private theorem frozenBoundary_wired_univ_partition (W : SimpleGraph V)
    (R : Configuration W) :
    (frozenBoundary (BoundaryCondition.wired (Set.univ : Set V)) R).partition =
      (BoundaryCondition.wired (Set.univ : Set V)).partition := by
  have htop : (BoundaryCondition.wired (Set.univ : Set V)).partition = ⊤ := by
    apply Setoid.ext
    intro x y
    constructor
    · intro _
      trivial
    · intro _
      exact (BoundaryCondition.wired_rel Set.univ x y).2
        (Or.inr ⟨Set.mem_univ x, Set.mem_univ y⟩)
  simp [frozenBoundary, componentSetoid, htop]

/-- The all-wired law on a same-carrier edge subgraph is the host law
conditioned on every deleted edge being open. The frozen paths do not change
the all-vertex wired partition. -/
theorem positive_wired_subgraph_eq_conditioned_open {W : SimpleGraph V}
    (hGW : G ≤ W) {q p : ℝ} (hq : 0 < q) (hp : 0 < p) (hp1 : p < 1) :
    (positiveFKLaw G q p hq hp hp1
      (BoundaryCondition.wired (Set.univ : Set V))).map
        (subgraphRemainingConfigurationEquiv hGW) =
      ((positiveFKLaw W q p hq hp hp1
          (BoundaryCondition.wired (Set.univ : Set V))).filter
        (frozenStateEvent (subgraphRemovedEdges G W)
          (⟨subgraphRemovedEdges G W, Finset.Subset.rfl⟩ :
            RemovedConfiguration W (subgraphRemovedEdges G W)))
        (positiveFrozenStateEvent_support hq hp hp1
          (BoundaryCondition.wired (Set.univ : Set V))
          (subgraphRemovedEdges G W)
          ⟨subgraphRemovedEdges G W, Finset.Subset.rfl⟩)).map
        (fun C => (configurationSplitEquiv W
          (subgraphRemovedEdges G W) C).1) := by
  let R := subgraphRemovedEdges G W
  let ξ : BoundaryCondition V := BoundaryCondition.wired Set.univ
  let H : RemovedConfiguration W R := ⟨R, Finset.Subset.rfl⟩
  have hdmp := positive_law_filter_frozen_map_remaining
    (G := W) hq hp hp1 ξ R H
  calc
    (positiveFKLaw G q p hq hp hp1 ξ).map
        (subgraphRemainingConfigurationEquiv hGW) =
      positiveRemainingLaw q p hq hp hp1 ξ R := by
        simpa only [R] using
          (positive_law_subgraphRemaining_map (G := G) hGW hq hp hp1 ξ)
    _ = positiveRemainingLaw q p hq hp hp1 (frozenBoundary ξ R) R := by
      have hpart : (frozenBoundary ξ R).partition = ξ.partition := by
        simpa only [ξ] using frozenBoundary_wired_univ_partition W R
      exact (positiveRemainingLaw_eq_of_partition_eq hq hp hp1
        (frozenBoundary ξ R) ξ hpart R).symm
    _ = ((positiveFKLaw W q p hq hp hp1 ξ).filter
        (frozenStateEvent R H)
        (positiveFrozenStateEvent_support hq hp hp1 ξ R H)).map
        (fun C => (configurationSplitEquiv W R C).1) := by
          simpa only [R, H] using hdmp.symm

/-- Adding isolated vertices leaves the normalized positive-`q` free FK law
unchanged. Their factor `q^(# added vertices)` is common to every weight and
cancels in normalization. -/
theorem positiveFKLaw_isolatedExtension_map
    {W : Type*} [Finite W] (f : V ↪ W) {q p : ℝ}
    (hq : 0 < q) (hp : 0 < p) (hp1 : p < 1)
    (B : Set V) (C : Set W) :
    (positiveFKLaw G q p hq hp hp1 (BoundaryCondition.free B)).map
        (isolatedExtensionConfigurationEquiv G f) =
      positiveFKLaw (G.map f) q p hq hp hp1 (BoundaryCondition.free C) := by
  classical
  let : Fintype (G.map f).edgeSet := Fintype.ofFinite _
  let : Fintype (Configuration (G.map f)) := Fintype.ofFinite _
  let d := q ^ Nat.card {w : W // w ∉ Set.range f}
  let c := d⁻¹
  have hd : 0 < d := by dsimp [d]; positivity
  have hc : 0 < c := by dsimp [c]; positivity
  have hweightAux (A : Configuration G) :
      positiveFKWeight (G.map f) q p (BoundaryCondition.free C)
          (isolatedExtensionConfigurationEquiv G f A) =
        d * positiveFKWeight G q p (BoundaryCondition.free B) A := by
    rw [positiveFKWeight, positiveFKWeight, card_isolatedExtensionConfigurationEquiv,
      isolatedExtension_edge_card, componentCount_isolatedExtension G f B C A,
      pow_add]
    dsimp [d]
    ring
  have hweight (A : Configuration G) :
      positiveFKWeight G q p (BoundaryCondition.free B) A =
        c * positiveFKWeight (G.map f) q p (BoundaryCondition.free C)
          (isolatedExtensionConfigurationEquiv G f A) := by
    rw [hweightAux]
    dsimp [c]
    have hdne : d ≠ 0 := hd.ne'
    field_simp [hdne]
  unfold positiveFKLaw
  exact FiniteProbability.pmf_map_equiv_of_common_factor
    (isolatedExtensionConfigurationEquiv G f) c _ _ hc
    (positiveFKWeight_pos' hq hp hp1 (BoundaryCondition.free B))
    (positiveFKWeight_pos' hq hp hp1 (BoundaryCondition.free C))
    hweight

omit [Finite V] in
private theorem frozenFreeBoundary_partition (W : SimpleGraph V) :
    (frozenBoundary (BoundaryCondition.free ∅) (∅ : Configuration W)).partition =
      (BoundaryCondition.free ∅ : BoundaryCondition V).partition := by
  exact componentSetoid_empty W (BoundaryCondition.free ∅)

private theorem positiveRemainingLaw_frozenFree_eq {W : SimpleGraph V}
    {q p : ℝ} (hq : 0 < q) (hp : 0 < p) (hp1 : p < 1)
    (R : Configuration W) :
    positiveRemainingLaw (G := W) q p hq hp hp1
        (frozenBoundary (BoundaryCondition.free ∅) (∅ : Configuration W)) R =
      positiveRemainingLaw (G := W) q p hq hp hp1 (BoundaryCondition.free ∅) R := by
  have hcount (A : RemainingConfiguration W R) :
      componentCount W
          (frozenBoundary (BoundaryCondition.free ∅) (∅ : Configuration W)) A.val =
        componentCount W (BoundaryCondition.free ∅) A.val := by
    have hset : componentSetoid W
        (frozenBoundary (BoundaryCondition.free ∅) (∅ : Configuration W)) A.val =
        componentSetoid W (BoundaryCondition.free ∅) A.val := by
      simp only [componentSetoid, frozenFreeBoundary_partition]
    rw [componentCount, componentCount, hset]
  have hweight :
      positiveRemainingWeight q p
          (frozenBoundary (BoundaryCondition.free ∅) (∅ : Configuration W)) R =
        positiveRemainingWeight q p (BoundaryCondition.free ∅) R := by
    funext A
    unfold positiveRemainingWeight
    rw [hcount A]
  ext A
  simp only [positiveRemainingLaw, FiniteProbability.pmf_apply]
  rw [hweight]

/-- A free FK law on an edge subgraph is exactly the rectangle free law
conditioned on every removed bond being closed, after retaining the subgraph
edges. -/
theorem positive_free_subgraph_eq_conditioned_closed {W : SimpleGraph V}
    (hGW : G ≤ W) {q p : ℝ} (hq : 0 < q) (hp : 0 < p) (hp1 : p < 1) :
    (positiveFKLaw G q p hq hp hp1 (BoundaryCondition.free ∅)).map
        (subgraphRemainingConfigurationEquiv hGW) =
      ((positiveFKLaw W q p hq hp hp1 (BoundaryCondition.free ∅)).filter
        (frozenStateEvent (subgraphRemovedEdges G W)
          (⟨∅, Finset.empty_subset _⟩ :
            RemovedConfiguration W (subgraphRemovedEdges G W)))
        (positiveFrozenStateEvent_support hq hp hp1 (BoundaryCondition.free ∅)
          (subgraphRemovedEdges G W) ⟨∅, Finset.empty_subset _⟩)).map
        (fun C => (configurationSplitEquiv W (subgraphRemovedEdges G W) C).1) := by
  let R := subgraphRemovedEdges G W
  let H0 : RemovedConfiguration W R := ⟨∅, Finset.empty_subset _⟩
  have hdmp := positive_law_filter_frozen_map_remaining
    (G := W) hq hp hp1 (BoundaryCondition.free ∅) R H0
  calc
    (positiveFKLaw G q p hq hp hp1 (BoundaryCondition.free ∅)).map
        (subgraphRemainingConfigurationEquiv hGW) =
      positiveRemainingLaw q p hq hp hp1 (BoundaryCondition.free ∅) R := by
        simpa only [R] using
          (positive_law_subgraphRemaining_map (G := G) hGW hq hp hp1
            (BoundaryCondition.free ∅))
    _ = positiveRemainingLaw q p hq hp hp1
        (frozenBoundary (BoundaryCondition.free ∅) (∅ : Configuration W)) R := by
          exact (positiveRemainingLaw_frozenFree_eq hq hp hp1 R).symm
    _ = ((positiveFKLaw W q p hq hp hp1 (BoundaryCondition.free ∅)).filter
        (frozenStateEvent R H0)
        (positiveFrozenStateEvent_support hq hp hp1 (BoundaryCondition.free ∅) R H0)).map
        (fun C => (configurationSplitEquiv W R C).1) := by
          simpa only [R, H0] using hdmp.symm

end
end PottsContinuity.DualityExt
