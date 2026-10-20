module

public import PottsContinuity.PlanarMixed.FiniteSlit.ActiveCarrier
public import PottsContinuity.PlanarMixed.Square.SubgraphIncreasingEventComparison
public import PottsContinuity.PlanarMixed.BoundaryMergeCost

/-! The finite dual-to-primal comparison, independently of the remaining
finite duality identification. Domain inclusion and boundary merging are proved. -/

@[expose] public section

namespace PottsContinuity.PlanarMixed.FiniteSlit
open PD.FK BD12 MeasureTheory
noncomputable section
local instance finiteSlitComparisonEdgeFintype {V : Type*} [Finite V] (G : SimpleGraph V) :
    Fintype G.edgeSet := Fintype.ofFinite _
local instance finiteSlitComparisonEdgeDecidableEq {V : Type*} (G : SimpleGraph V) :
    DecidableEq G.edgeSet := Classical.decEq _

/-- Added outer arc wiring dominates the joint dual marked-arc wiring. -/
theorem dualBoundary_partition_le_joined (M : ℕ) (x y : ℤ) :
    (dualBoundary M x y).partition ≤
      (BoundaryCondition.wired (alpha M x ∪ beta M x y)).partition := by
  intro u v huv
  rcases (BoundaryCondition.wired_rel _ u v).mp huv with heq | ⟨hu,hv⟩
  · exact (BoundaryCondition.wired_rel _ u v).mpr (Or.inl heq)
  · have hsub : dualBottom M x ∪ dualRay M x y ⊆ alpha M x ∪ beta M x y := by
      rintro z (hz | hz)
      · exact Or.inl (dualBottom_subset_alpha M x hz)
      · exact Or.inr (dualRay_subset_beta M x y hz)
    exact (BoundaryCondition.wired_rel _ u v).mpr (Or.inr ⟨hsub hu,hsub hv⟩)

/-- Adding missing source bonds and the larger marked sets preserves every
actual dual-arc path at its original endpoints. -/
theorem dual_connection_restriction_implies_source (M : ℕ) (x y : ℤ)
    (C : Configuration (graph M x y))
    (hC : subgraphConfigurationRestriction (dualGraph_le_graph M x y) C ∈
      arcsConnectionEvent (dualGraph M x y) (dualBottom M x) (dualRay M x y)) :
    C ∈ connectionEvent M x y := by
  classical
  let hDG := dualGraph_le_graph M x y
  obtain ⟨u,hu,v,hv,hconn⟩ := hC
  have hsub : subgraphConfigurationEmbedding hDG (subgraphConfigurationRestriction hDG C) ⊆ C := by
    intro e he
    obtain ⟨a,ha,rfl⟩ := Finset.mem_map.mp he
    exact (mem_subgraphConfigurationRestriction hDG C a).mp ha
  have hconn' : ActualConnected (graph M x y)
      (subgraphConfigurationEmbedding hDG (subgraphConfigurationRestriction hDG C)) u v := by
    change (openGraph (graph M x y) _).Reachable u v
    rw [openGraph_subgraphConfigurationEmbedding]
    exact hconn
  exact ⟨u,dualBottom_subset_alpha M x hu,v,dualRay_subset_beta M x y hv,
    actualConnected_mono hsub hconn'⟩

/-- The finite comparison costs at most ONE factor q for these enlarged
outer wired arcs; this is stronger than the requested q-squared estimate. -/
theorem dual_connection_probability_le_clusterWeight
    (θ : Parameters) (M : ℕ) (x y : ℤ)
    (hM : 2 ≤ M) (hy : 0 < y) (hyM : y < (M : ℤ)) :
    (measure (dualGraph M x y) θ (dualBoundary M x y)
      (arcsConnectionEvent (dualGraph M x y) (dualBottom M x) (dualRay M x y))).toReal ≤
      θ.val * (measure (graph M x y) θ (boundary M x y hM hy hyM)
        (connectionEvent M x y)).toReal := by
  let ξ := boundary M x y hM hy hyM
  let η : BoundaryCondition (Vertex M x) := BoundaryCondition.wired (alpha M x ∪ beta M x y)
  have hdom := Square.subgraph_increasing_event_measure_toReal_le_of_pullback_subset
    (dualGraph_le_graph M x y) θ (dualBoundary M x y)
    (arcsConnectionEvent (dualGraph M x y) (dualBottom M x) (dualRay M x y))
    (arcsConnectionEvent_isUpperSet _ _) (connectionEvent M x y)
    (fun C hC => dual_connection_restriction_implies_source M x y C hC)
  have hbc := measure_boundary_comparison (G := graph M x y) θ
    (dualBoundary M x y) η (dualBoundary_partition_le_joined M x y)
    (connectionEvent M x y) (arcsConnectionEvent_isUpperSet _ _)
  have hjoined : η.partition = ξ.partition ⊔
      (BoundaryCondition.wired (alpha M x ∪ beta M x y)).partition := by
    symm
    apply sup_eq_right.mpr
    apply sup_le
    · intro u v huv
      rcases (BoundaryCondition.wired_rel _ u v).mp huv with heq | ⟨hu,hv⟩
      · exact (BoundaryCondition.wired_rel _ u v).mpr (Or.inl heq)
      · exact (BoundaryCondition.wired_rel _ u v).mpr (Or.inr ⟨Or.inl hu,Or.inl hv⟩)
    · intro u v huv
      rcases (BoundaryCondition.wired_rel _ u v).mp huv with heq | ⟨hu,hv⟩
      · exact (BoundaryCondition.wired_rel _ u v).mpr (Or.inl heq)
      · exact (BoundaryCondition.wired_rel _ u v).mpr (Or.inr ⟨Or.inr hu,Or.inr hv⟩)
  have hmerge := measure_join_wired_sets_le_mul (G := graph M x y) θ ξ η
    (alpha M x) (beta M x y) le_sup_left le_sup_right hjoined (connectionEvent M x y)
  exact hdom.trans (hbc.trans hmerge)

/-- Requested finite comparison at the explicit self-dual parameter,
for every real cluster weight q>=1 and every valid truncation size. -/
theorem dual_connection_probability_le_q_sq (q : Set.Ici (1 : ℝ))
    (M : ℕ) (x y : ℤ) (hM : 2 ≤ M) (hy : 0 < y) (hyM : y < (M : ℤ)) :
    (measure (dualGraph M x y) (criticalParameters q) (dualBoundary M x y)
      (arcsConnectionEvent (dualGraph M x y) (dualBottom M x) (dualRay M x y))).toReal ≤
      (q : ℝ)^2 * (measure (graph M x y) (criticalParameters q) (boundary M x y hM hy hyM)
        (connectionEvent M x y)).toReal := by
  have h := dual_connection_probability_le_clusterWeight (criticalParameters q) M x y hM hy hyM
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := q.property
  have hq : (q : ℝ) ≤ (q : ℝ)^2 := by nlinarith [sq_nonneg ((q : ℝ)-1)]
  exact h.trans (mul_le_mul_of_nonneg_right hq ENNReal.toReal_nonneg)

end
end PottsContinuity.PlanarMixed.FiniteSlit
