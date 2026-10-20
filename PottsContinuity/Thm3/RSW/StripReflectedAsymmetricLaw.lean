module

public import PottsContinuity.Thm3.RSW.StripReflectedAsymmetricEmbedding
public import PottsContinuity.Thm3.RSW.PrewiredSubgraphMarginal
public import PottsContinuity.PD.FK.BoundaryPartitionLaw

@[expose] public section

namespace PottsContinuity.RSW
open PD.FK PD.Duality DualityExt
noncomputable section
local instance stripAsymLawEdgeEq {V : Type*} (G : SimpleGraph V) :
    DecidableEq G.edgeSet := Classical.decEq _

/-- The full asymmetric source rectangle has one top-and-ends wired class,
with the original bottom side free except at wired corners. -/
def stripAsymmetricTopSidesBoundary (n M : ℕ) :
    BoundaryCondition (RectangleVertex (-(M:ℤ)-1,-(n:ℤ)) (2*M+1) (4*n)) :=
  BoundaryCondition.wired {v | v.val.2=3*(n:ℤ) ∨ v.val.1= -(M:ℤ)-1 ∨ v.val.1=M}

section
variable (n M : ℕ)
local notation "Asym" => rectangleGraph (-(M:ℤ)-1,-(n:ℤ)) (2*M+1) (4*n)
local notation "Point" => RectangleVertex (-(M:ℤ)-1,-(n:ℤ)) (2*M+1) (4*n)
local notation "Face" => RectangleDualVertex (-(M:ℤ),-(n:ℤ)) (2*M) (4*n)
local notation "f" => stripReflectedAsymmetricEmbedding n M
local notation "ξ" => rectangleDualBoundaryCondition (-(M:ℤ),-(n:ℤ)) (2*M) (4*n)
local notation "pruned" => rectangleSubgraphDualGraph (stripRectangleWithoutTop_map_le n M)

/-- The physical inverse image of the host exterior arc is exactly the
asymmetric rectangle's top and two end arcs. -/
theorem stripReflectedAsymmetric_boundary_iff (u : Point) :
    (f u).val ∈ rectangleDualBoundary (-(M:ℤ),-(n:ℤ)) (2*M) (4*n) ↔
      u.val.2=3*(n:ℤ) ∨ u.val.1= -(M:ℤ)-1 ∨ u.val.1=M := by
  have hu := (mem_latticeRectangle _ _ _ _).mp u.property
  have hexp : (f u).val ∈ rectangleDualExpanded (-(M:ℤ),-(n:ℤ)) (2*M) (4*n) := (f u).property
  simp only [rectangleDualBoundary,Finset.mem_filter,hexp,true_and,rectangleDualInterior]
  change (¬ (-(M:ℤ) ≤ u.val.1 ∧ u.val.1 < -(M:ℤ)+((2*M:ℕ):ℤ) ∧
    -(n:ℤ) ≤ 2*(n:ℤ)-1-u.val.2 ∧ 2*(n:ℤ)-1-u.val.2 < -(n:ℤ)+((4*n:ℕ):ℤ))) ↔ _
  push_cast at hu ⊢
  omega

/-- Pullback of the exact dual exterior partition is the literal asymmetric
source top/ends partition. -/
theorem stripReflectedAsymmetric_boundary_partition :
    (isolatedExtensionPullbackBoundary f ξ).partition =
      (stripAsymmetricTopSidesBoundary n M).partition := by
  apply Setoid.ext
  intro u v
  change (ξ).partition.r (f u) (f v) ↔
    (BoundaryCondition.wired {v : Point | v.val.2=3*(n:ℤ) ∨ v.val.1= -(M:ℤ)-1 ∨ v.val.1=M}).partition.r u v
  rw [rectangleDualBoundaryCondition_rel,BoundaryCondition.wired_rel]
  exact or_congr (f).injective.eq_iff
    (and_congr (stripReflectedAsymmetric_boundary_iff n M u)
      (stripReflectedAsymmetric_boundary_iff n M v))

/-- Read the original reflected asymmetric sample on every retained actual
dual bond; omitted rectangle bonds are already wired arc bonds only. -/
def stripAsymmetricPrunedDualRead (C : Configuration Asym) : Configuration pruned :=
  subgraphConfigurationRestriction (stripPrunedDual_le_reflectedAsymmetric n M)
    (isolatedExtensionConfigurationEquiv Asym f C)

/-- Exact finite reflected-domain law on the retained actual dual carrier.
All physical inclusions and arc partitions are proved, and all q>=1 are allowed. -/
theorem stripAsymmetricPrunedDualRead_law (θ : Parameters) :
    (law Asym θ (stripAsymmetricTopSidesBoundary n M)).map
      (stripAsymmetricPrunedDualRead n M) = law pruned θ ξ := by
  have heq := law_eq_of_boundary_partition_eq (G:=Asym) θ _ _
    (stripReflectedAsymmetric_boundary_partition n M)
  have hi := law_isolatedExtension_map_boundary_pullback Asym f θ ξ
  rw [heq] at hi
  have hr := law_map_subgraphRestriction_of_prewired (stripPrunedDual_le_reflectedAsymmetric n M) θ ξ (by
    intro u v huv he
    have hnot : ¬ (pruned).Adj u v := by
      intro h
      have hh := (mem_subgraphRemovedEdges _).mp he
      exact hh ((pruned).mem_edgeSet.mpr h)
    exact stripReflectedAsymmetric_extra_edge_prewired n M u v huv hnot)
  calc
    _ = ((law Asym θ (stripAsymmetricTopSidesBoundary n M)).map
        (isolatedExtensionConfigurationEquiv Asym f)).map
          (subgraphConfigurationRestriction (stripPrunedDual_le_reflectedAsymmetric n M)) := by
      rw [PMF.map_comp]
      rfl
    _ = _ := by rw [hi,hr]

/-- The actual top-wired source complementary dual read and the reflected
asymmetric top/ends sample have exactly the same retained finite law. -/
theorem selfDual_stripWindowPrunedDual_eq_asymmetric_reflected (q : Set.Ici (1:ℝ)) :
    (law (squareLattice.induce (stripWindow n M : Set (ℤ×ℤ))) (selfDualParameters q)
      (stripWindowBoundary n M 0)).map (stripWindowPrunedDualConfiguration n M) =
    (law Asym (selfDualParameters q) (stripAsymmetricTopSidesBoundary n M)).map
      (stripAsymmetricPrunedDualRead n M) := by
  rw [selfDual_stripWindowPrunedDualConfiguration_law,stripAsymmetricPrunedDualRead_law]

end
end
end PottsContinuity.RSW
