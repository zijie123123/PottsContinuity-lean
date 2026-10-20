module

public import PottsContinuity.Thm4Records.NativeCoordinates
public import PottsContinuity.PlanarMixed.Lemma4RecordCarrier.ReferenceCoreAdjacency
public import PottsContinuity.Thm3.RSW.EmbeddedComparison
public import PottsContinuity.PlanarMixed.EmbeddedOpenRestriction

@[expose] public section

namespace PottsContinuity.Thm4Records
open PD.FK RSW Thm4Plane PlanarMixed.Lemma4Connectors PlanarMixed.Square MeasureTheory
noncomputable section
attribute [local instance] configurationMeasurableSpace

abbrev connectorReferenceVertex (m : ℕ) :=
  rectangleDualHorizontalCoreVertex (-(5*(m:ℤ))+1,-(5*(m:ℤ))+1) (10*m-1) (10*m-1)
abbrev connectorReferenceGraph (m : ℕ) :=
  rectangleDualHorizontalCoreGraph (-(5*(m:ℤ))+1,-(5*(m:ℤ))+1) (10*m-1) (10*m-1)

def connectorReferenceVertexMap (m : ℕ) (hm : 1 ≤ m)
    (X : Configuration (FKC.FiniteFK.slitBoxGraph (16*m)))
    (u : connectorNativeVertex m hm X) : connectorReferenceVertex m := by
  have hc := connectorNativeVertex_coordinates m hm X u
  refine ⟨⟨(u.val.val.2+7*(m:ℤ),u.val.val.1),?_⟩,?_⟩
  · change (u.val.val.2+7*(m:ℤ),u.val.val.1) ∈
      PD.FK.latticeRectangle ((-(5*(m:ℤ))+1)-1,(-(5*(m:ℤ))+1)-1)
        ((10*m-1)+1) ((10*m-1)+1)
    rw [PD.FK.mem_latticeRectangle]
    norm_num only [Nat.cast_add,Nat.cast_one,Prod.fst,Prod.snd]
    constructor <;> constructor <;> omega
  · change -(5*(m:ℤ))+1 ≤ u.val.val.1 ∧
      u.val.val.1 ≤ -(5*(m:ℤ))+1+((10*m-1:ℕ):ℤ)-1
    constructor <;> omega

def connectorReferenceEmbedding (m : ℕ) (hm : 1 ≤ m)
    (X : Configuration (FKC.FiniteFK.slitBoxGraph (16*m))) :
    connectorNativeVertex m hm X ↪ connectorReferenceVertex m where
  toFun := connectorReferenceVertexMap m hm X
  inj' := by
    intro u v h
    have hx := congrArg (fun z : connectorReferenceVertex m => z.val.val.1) h
    have hy := congrArg (fun z : connectorReferenceVertex m => z.val.val.2) h
    change u.val.val.2+7*(m:ℤ)=v.val.val.2+7*(m:ℤ) at hx
    change u.val.val.1=v.val.val.1 at hy
    exact Subtype.ext (Subtype.ext (Prod.ext hy (by omega)))

theorem connectorReferenceGraph_map_le (m : ℕ) (hm : 1 ≤ m)
    (X : Configuration (FKC.FiniteFK.slitBoxGraph (16*m))) :
    (connectorIncidentGraph m hm X).map (connectorReferenceEmbedding m hm X) ≤
      connectorReferenceGraph m := by
  intro x y hxy
  obtain ⟨u,v,huv,rfl,rfl⟩ := (SimpleGraph.map_adj _ _ _ _).mp hxy
  obtain ⟨hG,he⟩ := (PlanarMixed.edgeRestriction_adj_exists_not_mem _ _ u.val v.val).mp huv
  have hstep := (FKC.squareLattice_adj_iff _ _).mp
    ((FKC.FiniteFK.slitBoxGraph_adj_iff _ _ _).mp hG).1
  have hex := rStarSourceEdges_not_terminal_row m hm u.val v.val hG
    (remaining_edge_mem_rStarSourceEdges m hm X _ he)
  apply referenceDualCore_adj_of_lattice_adj (-(5*(m:ℤ))+1) (10*m-1) (by omega)
  · apply (PD.FK.squareLattice_adj_iff _ _).mpr
    change (((u.val.val.2+7*(m:ℤ))+1=v.val.val.2+7*(m:ℤ) ∨
      (v.val.val.2+7*(m:ℤ))+1=u.val.val.2+7*(m:ℤ)) ∧ u.val.val.1=v.val.val.1) ∨
      (u.val.val.2+7*(m:ℤ)=v.val.val.2+7*(m:ℤ) ∧
        (u.val.val.1+1=v.val.val.1 ∨ v.val.val.1+1=u.val.val.1))
    omega
  · intro h
    apply hex.1
    change u.val.val.2+7*(m:ℤ)=-(5*(m:ℤ))+1-1 ∧
      v.val.val.2+7*(m:ℤ)=-(5*(m:ℤ))+1-1 at h
    constructor <;> omega
  · intro h
    apply hex.2
    change u.val.val.2+7*(m:ℤ)=-(5*(m:ℤ))+1+((10*m-1:ℕ):ℤ) ∧
      v.val.val.2+7*(m:ℤ)=-(5*(m:ℤ))+1+((10*m-1:ℕ):ℤ) at h
    constructor <;> omega

/-- Literal top-to-bottom connection using only actual residual original bonds. -/
def connectorNativeVertical (m : ℕ) (hm : 1 ≤ m)
    (X : Configuration (FKC.FiniteFK.slitBoxGraph (16*m))) :
    Set (Configuration (connectorIncidentGraph m hm X)) :=
  {C | ∃ u v : connectorNativeVertex m hm X,
    u.val.val.2=-(12*(m:ℤ)) ∧ v.val.val.2=-(2*(m:ℤ)) ∧
      ActualConnected _ C u v}

theorem connectorNativeVertical_isUpperSet (m : ℕ) (hm : 1 ≤ m)
    (X : Configuration (FKC.FiniteFK.slitBoxGraph (16*m))) :
    IsUpperSet (connectorNativeVertical m hm X) := by
  rintro A B hAB ⟨u,v,hu,hv,hconn⟩
  exact ⟨u,v,hu,hv,actualConnected_mono hAB hconn⟩

/-- Pullback of the true square reference wires exactly the two terminal rows. -/
theorem connectorReference_boundary_pullback (m : ℕ) (hm : 1 ≤ m)
    (X : Configuration (FKC.FiniteFK.slitBoxGraph (16*m))) :
    isolatedExtensionPullbackBoundary (connectorReferenceEmbedding m hm X)
      (BoundaryCondition.wired {u : connectorReferenceVertex m |
        rectangleDualHorizontalCoreInclusion (-(5*(m:ℤ))+1,-(5*(m:ℤ))+1)
          (10*m-1) (10*m-1) u ∈
        rectangleDoubleCollarDualInnerVerticalSides (-(5*(m:ℤ))+1,-(5*(m:ℤ))+1)
          (10*m-1) (10*m-1)}) =
      BoundaryCondition.wired (connectorNativeTopBottom m hm X) := by
  have hset : (connectorReferenceEmbedding m hm X) ⁻¹'
      {u : connectorReferenceVertex m |
        rectangleDualHorizontalCoreInclusion (-(5*(m:ℤ))+1,-(5*(m:ℤ))+1)
          (10*m-1) (10*m-1) u ∈
        rectangleDoubleCollarDualInnerVerticalSides (-(5*(m:ℤ))+1,-(5*(m:ℤ))+1)
          (10*m-1) (10*m-1)} = connectorNativeTopBottom m hm X := by
    ext u
    change (u.val.val.2+7*(m:ℤ)=-(5*(m:ℤ))+1-1 ∨
      u.val.val.2+7*(m:ℤ)=-(5*(m:ℤ))+1+((10*m-1:ℕ):ℤ)) ↔ _
    change _ ↔ (u.val.val.2=-(12*(m:ℤ)) ∨ u.val.val.2=-(2*(m:ℤ)))
    omega
  change BoundaryCondition.mk _ _ _ = BoundaryCondition.mk _ _ _
  rw [BoundaryCondition.mk.injEq]
  constructor
  · exact hset
  · ext u v
    change ((connectorReferenceEmbedding m hm X) u=(connectorReferenceEmbedding m hm X) v ∨ _) ↔ _
    rw [Function.Embedding.apply_eq_iff_eq]
    exact or_congr Iff.rfl (and_congr (Set.ext_iff.mp hset u) (Set.ext_iff.mp hset v))


/-- Deleting every queried original bond only increases this noncrossing
probability, under the maximal top/bottom reference wiring. -/
theorem connectorNativeNoncrossing_lower (m : ℕ) (hm : 1 ≤ m)
    (q : Set.Ici (1:ℝ)) (X : Configuration (FKC.FiniteFK.slitBoxGraph (16*m))) :
    1/(1+(q:ℝ)^2) ≤
      (measure (connectorIncidentGraph m hm X) (criticalParameters q)
        (BoundaryCondition.wired (connectorNativeTopBottom m hm X))
        (connectorNativeVertical m hm X)ᶜ).toReal := by
  let J := connectorIncidentGraph m hm X
  let H := connectorReferenceGraph m
  let g := connectorReferenceEmbedding m hm X
  let ξ := BoundaryCondition.wired {u : connectorReferenceVertex m |
    rectangleDualHorizontalCoreInclusion (-(5*(m:ℤ))+1,-(5*(m:ℤ))+1)
      (10*m-1) (10*m-1) u ∈
    rectangleDoubleCollarDualInnerVerticalSides (-(5*(m:ℤ))+1,-(5*(m:ℤ))+1)
      (10*m-1) (10*m-1)}
  let S := connectorNativeVertical m hm X
  let read := embeddedConfigurationRestriction J H g (connectorReferenceGraph_map_le m hm X)
  have hcmp := embedded_boundary_probability_le J H g (connectorReferenceGraph_map_le m hm X)
    (criticalParameters q) ξ S (connectorNativeVertical_isUpperSet m hm X)
  rw [connectorReference_boundary_pullback] at hcmp
  have hcomp : (measure H (criticalParameters q) ξ (read ⁻¹' S)ᶜ).toReal ≤
      (measure J (criticalParameters q) (BoundaryCondition.wired (connectorNativeTopBottom m hm X)) Sᶜ).toReal := by
    change (measure J _ _).real S ≤ (measure H _ _).real (read ⁻¹' S) at hcmp
    change (measure H _ _).real (read ⁻¹' S)ᶜ ≤ (measure J _ _).real Sᶜ
    rw [probReal_compl_eq_one_sub (MeasurableSpace.measurableSet_top : MeasurableSet _),
      probReal_compl_eq_one_sub (MeasurableSpace.measurableSet_top : MeasurableSet _)]
    linarith
  have hsub : (referenceDualCoreHorizontalCrossing (-(5*(m:ℤ))+1) (10*m-1))ᶜ ⊆
      (read ⁻¹' S)ᶜ := by
    intro C hC hS
    obtain ⟨u,v,hu,hv,hconn⟩ := hS
    apply hC
    refine ⟨g u,g v,?_,?_,?_⟩
    · change u.val.val.2+7*(m:ℤ)=-(5*(m:ℤ))+1-1
      omega
    · change v.val.val.2+7*(m:ℤ)=-(5*(m:ℤ))+1+((10*m-1:ℕ):ℤ)
      omega
    · exact hconn.map (PlanarMixed.embeddedOpenRestrictionHom _ _ _ (connectorReferenceGraph_map_le m hm X) C)
  exact (referenceDualCore_noncrossing_lower q (-(5*(m:ℤ))+1) (10*m-1) (by omega)).trans
    ((ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hsub)).trans hcomp)

/-- The true induced law satisfies the square bound once its geometric
attachment order has been established. -/
theorem connectorIncidentNoncrossing_lower_of_partition_order
    (m : ℕ) (hm : 1 ≤ m) (q : Set.Ici (1:ℝ))
    (X : Configuration (FKC.FiniteFK.slitBoxGraph (16*m)))
    (ξ : BoundaryCondition (FKC.FiniteFK.SlitBoxVertex (16*m)))
    (hpart : (connectorIncidentBoundary m hm X ξ).partition ≤
      (BoundaryCondition.wired (connectorNativeTopBottom m hm X)).partition) :
    1/(1+(q:ℝ)^2) ≤
      (measure (connectorIncidentGraph m hm X) (criticalParameters q)
        (connectorIncidentBoundary m hm X ξ) (connectorNativeVertical m hm X)ᶜ).toReal :=
  (connectorNativeNoncrossing_lower m hm q X).trans
    (finite_decreasing_boundary_comparison _ _ _ _ hpart _
      (connectorNativeVertical_isUpperSet m hm X).compl)

end
end PottsContinuity.Thm4Records
