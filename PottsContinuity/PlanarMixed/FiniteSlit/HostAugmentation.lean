module

public import PottsContinuity.PlanarMixed.FiniteSlit.DualProbabilityComparison
public import PottsContinuity.PD.Duality.CrossingDuality

/-! Rectangular augmentation of an actual finite slit sample. Opening all
internal outer-arc bonds preserves the absence of an alpha-beta connection,
so the proved rectangle crossing alternative applies to this exact sample. -/

@[expose] public section

namespace PottsContinuity.PlanarMixed.FiniteSlit
open PD.FK PD.FK.Medial PD.Duality BD12 DualityExt
noncomputable section
local instance finiteSlitHostAugmentationEdgeDecidableEq {V : Type*} (G : SimpleGraph V) :
    DecidableEq G.edgeSet := Classical.decEq _

/-- Both finite marked arcs have explicit original vertices. -/
theorem alpha_nonempty (M : ℕ) (x : ℤ) (hM : 2 ≤ M) : (alpha M x).Nonempty := by
  have hm : (x,0) ∈ PD.FK.latticeRectangle (x-(M : ℤ),0) (2*M-1) M := by
    apply (mem_rectangle_iff M x (by omega) _).mpr
    simp only
    omega
  exact ⟨⟨(x,0),hm⟩,Or.inl ⟨rfl,le_rfl⟩⟩

theorem beta_nonempty (M : ℕ) (x y : ℤ) (hM : 2 ≤ M) (hy : 0 < y) (hyM : y < (M : ℤ)) :
    (beta M x y).Nonempty :=
  ⟨rightTip M x y hM hy hyM,rightTip_mem_beta M x y hM hy hyM⟩

/-- The original sample in the rectangle, with internal arc bonds made OPEN. -/
def hostAugmentation (M : ℕ) (x y : ℤ) (C : Configuration (graph M x y)) :
    Configuration (rectangleGraph (x-(M : ℤ),0) (2*M-1) M) :=
  subgraphConfigurationEmbedding (graph_le_rectangle M x y) C ∪ rectangleArcBonds M x y

/-- Internal rectangular arc bonds identify only vertices of their own wired class. -/
theorem rectangleArcBonds_prewired (M : ℕ) (x y : ℤ)
    (hM : 2 ≤ M) (hy : 0 < y) (hyM : y < (M : ℤ))
    (u v : Vertex M x) (huv : (rectangleGraph (x-(M : ℤ),0) (2*M-1) M).Adj u v)
    (he : (⟨s(u,v),(rectangleGraph _ _ _).mem_edgeSet.mpr huv⟩ :
      (rectangleGraph (x-(M : ℤ),0) (2*M-1) M).edgeSet) ∈ rectangleArcBonds M x y) :
    (boundary M x y hM hy hyM).partition.r u v := by
  rw [rectangleArcBonds,Finset.mem_union,mem_internalBonds_pair _ _ u v huv,
    mem_internalBonds_pair _ _ u v huv] at he
  exact (twoBlockBoundary_partition_rel _ _ _ u v).mpr (Or.inr he)

/-- Augmentation changes no physical connection between the whole marked arcs. -/
theorem hostAugmentation_connection_iff (M : ℕ) (x y : ℤ)
    (hM : 2 ≤ M) (hy : 0 < y) (hyM : y < (M : ℤ)) (C : Configuration (graph M x y)) :
    hostAugmentation M x y C ∈ arcsConnectionEvent (rectangleGraph (x-(M : ℤ),0) (2*M-1) M)
      (alpha M x) (beta M x y) ↔ C ∈ connectionEvent M x y := by
  rw [hostAugmentation,arcsConnectionEvent_union_removed (alpha M x) (beta M x y)
    (alpha_disjoint_beta M x y hM hy hyM) (alpha_nonempty M x hM)
    (beta_nonempty M x y hM hy hyM) (rectangleArcBonds M x y)
    (rectangleArcBonds_prewired M x y hM hy hyM) _ ⟨rectangleArcBonds M x y,le_rfl⟩]
  change (∃ u ∈ alpha M x, ∃ v ∈ beta M x y,
    (openGraph _ (subgraphConfigurationEmbedding _ C)).Reachable u v) ↔ _
  rw [openGraph_subgraphConfigurationEmbedding]
  rfl

/-- A horizontal rectangle crossing is in particular an alpha-beta path. -/
theorem rectangle_horizontal_subset_connection (M : ℕ) (x y : ℤ) (hM : 2 ≤ M)
    (C : Configuration (rectangleGraph (x-(M : ℤ),0) (2*M-1) M))
    (hC : C ∈ rectangleHorizontalCrossingEvent (x-(M : ℤ),0) (2*M-1) M) :
    C ∈ arcsConnectionEvent (rectangleGraph (x-(M : ℤ),0) (2*M-1) M) (alpha M x) (beta M x y) := by
  obtain ⟨u,v,hu,hv,hc⟩ := hC
  have hleft : u.val.1 = x-(M : ℤ) := (Finset.mem_filter.mp hu).2
  have hright : v.val.1 = x+(M : ℤ)-1 := by
    have h := (Finset.mem_filter.mp hv).2
    have hw : ((2*M-1 : ℕ) : ℤ) = 2*(M : ℤ)-1 := by omega
    simp only [hw] at h
    omega
  exact ⟨u,Or.inr (Or.inl hleft),v,Or.inl hright,hc⟩

/-- Every finite alpha-beta nonconnection has a full rectangle dual crossing
in the exact augmented sample. Extraction of the static slit chain is separate. -/
theorem hostAugmentation_dual_crossing_of_nonconnection (M : ℕ) (x y : ℤ)
    (hM : 2 ≤ M) (hy : 0 < y) (hyM : y < (M : ℤ))
    (C : Configuration (graph M x y)) (hC : C ∉ connectionEvent M x y) :
    positiveRectangleDualConfigurationEquiv (x-(M : ℤ),0) (2*M-1) M (hostAugmentation M x y C) ∈
      rectangleDualBottomTopCrossingEvent (x-(M : ℤ),0) (2*M-1) M := by
  apply (rectangle_crossing_duality (x-(M : ℤ),0) (2*M-1) M _).mp
  intro hh
  exact hC ((hostAugmentation_connection_iff M x y hM hy hyM C).mp
    (rectangle_horizontal_subset_connection M x y hM _ hh))

end
end PottsContinuity.PlanarMixed.FiniteSlit
