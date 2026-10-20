module

public import PottsContinuity.BD12.KSTFiniteAssociation
public import PottsContinuity.BD12.KSTCascade
public import PottsContinuity.PlanarTopology.KSTQuasiConstruction

/-! The six-event KST probability construction, with the exact geometry
`PlanarTopology.kst_quasi_construction` consumed. All events are literal translated arms
or horizontal crossings. -/

@[expose] public section

namespace PottsContinuity.BD12
open MeasureTheory PD.FK
noncomputable section

/-- The six source events constructing the quasi-crossing at scale (4m,m). -/
def kstConstructionInputs (m : ℕ) : Fin 6 → Set LatticeConfiguration :=
  ![kstTranslateEvent (((m/16 : ℕ) : ℤ),0) (kstArm m),
    kstTranslateEvent (-((m/16 : ℕ) : ℤ),0) (kstArm m),
    kstTranslateEvent (0,((3*m/2 : ℕ) : ℤ)) (kstArm (5*m/2)),
    kstTranslateEvent (0,-((3*m/2 : ℕ) : ℤ)) (kstArm (5*m/2)),
    horizontalRectangle (-5*(m : ℤ),-4*(m : ℤ)) (31*m/4) (8*m),
    horizontalRectangle (-((11*m/4 : ℕ) : ℤ),-4*(m : ℤ)) (31*m/4) (8*m)]

theorem kstConstructionInputs_measurableSet (m : ℕ) (i : Fin 6) :
    MeasurableSet (kstConstructionInputs m i) := by
  fin_cases i
  all_goals first
    | exact kstTranslateEvent_measurable _ (kstArm_isOpen _).measurableSet
    | exact (horizontalRectangle_isCylinder _ _ _).measurableSet

theorem kstConstructionInputs_isUpperSet (m : ℕ) (i : Fin 6) :
    IsUpperSet (kstConstructionInputs m i) := by
  fin_cases i
  all_goals first
    | exact kstTranslateEvent_isUpperSet _ (kstArm_isUpperSet _)
    | exact horizontalRectangle_isUpperSet _ _ _

/-- The product bound for the actual wired law, without a construction premise.
It holds for all FK parameters, not merely the self-dual parameter. -/
theorem wired_kst_construction_product (θ : Parameters) (μ : Measure LatticeConfiguration)
    (hμ : IsRCInfiniteVolumeLimit θ.toP θ.toQ 1 μ) (j : ℕ) :
    let m := 192*4^j
    (∏ i : Fin 6, μ.real (kstConstructionInputs m i)) ≤ μ.real (kstQuasiCrossing (4*m) m) := by
  let : IsProbabilityMeasure μ := hμ.1
  let m := 192*4^j
  apply kst_construction_of_kstCorridor μ
    (fun _ _ => wired_measurable_positive_association θ μ hμ)
    (kstConstructionInputs m) (kstConstructionInputs_measurableSet m) (kstConstructionInputs_isUpperSet m)
  intro ω hω
  apply PlanarTopology.kst_quasi_construction j
  exact ⟨⟨⟨⟨⟨Set.mem_iInter.mp hω 0, Set.mem_iInter.mp hω 1⟩,
    Set.mem_iInter.mp hω 2⟩, Set.mem_iInter.mp hω 3⟩, Set.mem_iInter.mp hω 4⟩,
    Set.mem_iInter.mp hω 5⟩

/-- A common lower bound for the six actual input probabilities yields its
sixth power at the output. No geometric premise remains. -/
theorem wired_kst_construction_lower_bound (θ : Parameters) (μ : Measure LatticeConfiguration)
    (hμ : IsRCInfiniteVolumeLimit θ.toP θ.toQ 1 μ) (j : ℕ)
    (a : ℝ) (ha : 0 ≤ a)
    (hbound : ∀ i : Fin 6, a ≤ μ.real (kstConstructionInputs (192*4^j) i)) :
    a^6 ≤ μ.real (kstQuasiCrossing (4*(192*4^j)) (192*4^j)) := by
  have hprod : (∏ _i : Fin 6, a) ≤ ∏ i : Fin 6, μ.real (kstConstructionInputs (192*4^j) i) :=
    Finset.prod_le_prod₀ (fun _ _ => ha) (fun i _ => hbound i)
  have h := hprod.trans (wired_kst_construction_product θ μ hμ j)
  simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using h

end
end PottsContinuity.BD12
