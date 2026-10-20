module

public import PottsContinuity.Thm3.RSW.StripReflectedAsymmetricLaw
public import PottsContinuity.Thm3.RSW.EmbeddedComparison
public import PottsContinuity.PD.FK.EmbeddedBoundaryUpper
public import PottsContinuity.PD.FK.EmbeddedClosedInteriorOuterBoundary

@[expose] public section

namespace PottsContinuity.RSW
open PD.FK MeasureTheory
noncomputable section
attribute [local instance] configurationMeasurableSpace

/-- The complete centered source window sits in the asymmetric window by
identity on physical vertices and original bonds. -/
def stripWindowAsymmetricEmbedding (n M : ℕ) :
    (stripWindow n M : Set (ℤ×ℤ)) ↪
      RectangleVertex (-(M:ℤ)-1,-(n:ℤ)) (2*M+1) (4*n) :=
  (Function.Embedding.refl (ℤ×ℤ)).subtypeMap (by
    intro u hu
    change u ∈ stripWindow n M at hu
    simp only [stripWindow,PottsContinuity.latticeRectangle,Finset.mem_product,Finset.mem_Icc] at hu
    change u ∈ PD.FK.latticeRectangle (-(M:ℤ)-1,-(n:ℤ)) (2*M+1) (4*n)
    rw [mem_latticeRectangle]
    push_cast
    constructor <;> constructor <;> omega)

/-- No source-window bond is altered by this actual domain inclusion. -/
theorem stripWindowAsymmetric_map_le (n M : ℕ) :
    (squareLattice.induce (stripWindow n M : Set (ℤ×ℤ))).map
      (stripWindowAsymmetricEmbedding n M) ≤
      rectangleGraph (-(M:ℤ)-1,-(n:ℤ)) (2*M+1) (4*n) := by
  intro u v h
  rcases (SimpleGraph.map_adj _ _ _ _).mp h with ⟨x,y,hxy,rfl,rfl⟩
  exact hxy

section
variable (n M : ℕ)
local notation "Center" => squareLattice.induce (stripWindow n M : Set (ℤ×ℤ))
local notation "Asym" => rectangleGraph (-(M:ℤ)-1,-(n:ℤ)) (2*M+1) (4*n)
local notation "f" => stripWindowAsymmetricEmbedding n M
local notation "B" => stripWindowWiredVertices n M 1
local notation "ξ" => stripAsymmetricTopSidesBoundary n M

private theorem center_nonBoundary_closed
    {u : (stripWindow n M : Set (ℤ×ℤ))} (hu : u ∉ B)
    {v : RectangleVertex (-(M:ℤ)-1,-(n:ℤ)) (2*M+1) (4*n)}
    (hadj : (Asym).Adj (f u) v) :
    ∃ z : (stripWindow n M : Set (ℤ×ℤ)), f z=v ∧ (Center).Adj u z := by
  have hub : u.val ∈ stripWindow n M := u.property
  simp only [stripWindow,PottsContinuity.latticeRectangle,Finset.mem_product,Finset.mem_Icc] at hub
  have hvb := (mem_latticeRectangle _ _ _ _).mp v.property
  have hleft : u.val.1 ≠ -(M:ℤ) := fun h => hu (Or.inr ⟨rfl,Or.inl h⟩)
  have hright : u.val.1 ≠ (M:ℤ) := fun h => hu (Or.inr ⟨rfl,Or.inr h⟩)
  have hadj' : |u.val.1-v.val.1|+|u.val.2-v.val.2|=1 := hadj
  have hxdiff : |u.val.1-v.val.1| ≤ 1 := by linarith only [hadj',abs_nonneg (u.val.2-v.val.2)]
  have hxbounds := abs_le.mp hxdiff
  have hv : v.val ∈ stripWindow n M := by
    simp only [stripWindow,PottsContinuity.latticeRectangle,Finset.mem_product,Finset.mem_Icc]
    push_cast at hvb
    constructor <;> constructor <;> omega
  refine ⟨⟨v.val,hv⟩,?_,?_⟩
  · exact Subtype.ext rfl
  · exact hadj'

private theorem center_nonBoundary_avoids_outer
    {u : (stripWindow n M : Set (ℤ×ℤ))} (hu : u ∉ B) : f u ∉ (ξ).boundary := by
  have hub : u.val ∈ stripWindow n M := u.property
  simp only [stripWindow,PottsContinuity.latticeRectangle,Finset.mem_product,Finset.mem_Icc] at hub
  intro h
  change u.val.2=3*(n:ℤ) ∨ u.val.1= -(M:ℤ)-1 ∨ u.val.1=(M:ℤ) at h
  rcases h with ht | hl | hr
  · exact hu (Or.inl ht)
  · omega
  · exact hu (Or.inr ⟨rfl,Or.inr hr⟩)

private theorem center_top_partition_le_pullback :
    (stripWindowBoundary n M 0).partition ≤ (isolatedExtensionPullbackBoundary f ξ).partition := by
  intro u v h
  change u=v ∨ u ∈ stripWindowWiredVertices n M 0 ∧ v ∈ stripWindowWiredVertices n M 0 at h
  change f u=f v ∨
    ((u.val.2=3*(n:ℤ) ∨ u.val.1= -(M:ℤ)-1 ∨ u.val.1=M) ∧
     (v.val.2=3*(n:ℤ) ∨ v.val.1= -(M:ℤ)-1 ∨ v.val.1=M))
  rcases h with rfl | ⟨hu,hv⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨Or.inl (by simpa [stripWindowWiredVertices] using hu),
      Or.inl (by simpa [stripWindowWiredVertices] using hv)⟩

/-- Every actual increasing source-window event is stochastically squeezed
between centered top-only and centered top-with-ends laws. This holds for ALL
interior edge parameters and all real cluster weights at least one. -/
theorem stripAsymmetric_boundary_probability_sandwich (θ : Parameters)
    (E : Set (Configuration Center)) (hE : IsUpperSet E) :
    (measure Center θ (stripWindowBoundary n M 0) E).toReal ≤
      (measure Asym θ ξ {C | embeddedConfigurationRestriction Center Asym f
        (stripWindowAsymmetric_map_le n M) C ∈ E}).toReal ∧
    (measure Asym θ ξ {C | embeddedConfigurationRestriction Center Asym f
        (stripWindowAsymmetric_map_le n M) C ∈ E}).toReal ≤
      (measure Center θ (stripWindowBoundary n M 1) E).toReal := by
  constructor
  · exact (measure_boundary_comparison θ (stripWindowBoundary n M 0)
      (isolatedExtensionPullbackBoundary f ξ) (center_top_partition_le_pullback n M) E hE).trans
        (embedded_boundary_probability_le Center Asym f (stripWindowAsymmetric_map_le n M) θ ξ E hE)
  · apply embeddedConfigurationRestriction_preimage_measure_le_of_frozen_partition
      Center Asym f (stripWindowAsymmetric_map_le n M) θ ξ (stripWindowBoundary n M 1) E hE
    intro K
    exact isolatedExtensionPullback_frozenBoundary_partition_le_wired_of_closedInterior
      f (stripWindowAsymmetric_map_le n M) B (fun _ hu _ hadj => center_nonBoundary_closed n M hu hadj)
      ξ (fun _ hu => center_nonBoundary_avoids_outer n M hu) K

end
end
end PottsContinuity.RSW
