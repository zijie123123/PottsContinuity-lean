-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/HorizontalStripCoreSeedBoundaryComparison.lean`, with
-- module and namespace relocated (wrappers of the SLE development replaced by `PottsContinuity.FKC.SLEWrap`)
-- and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.HorizontalStripAsymmetricBoundaryProbabilityBound
public import PottsContinuity.FKC.FiniteFK.GeneralRectangleDualBottomCoreConnectivityLaw
public import PottsContinuity.FKC.FiniteFK.Isomorphism
public import PottsContinuity.FKC.FiniteFK.RectangleTranslation
public import PottsContinuity.FKC.FiniteFK.HorizontalStripFiniteHeightProbabilityAlternative
public import Mathlib.MeasureTheory.Measure.Map
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.Medial

open PottsContinuity.FKC.FiniteFK
open FiniteProbability

noncomputable section

attribute [local instance] configurationMeasurableSpace

local instance coreSeedCmpAsymEdgeFintype (N n : ℕ) :
    Fintype (horizontalStripAsymmetricRectangle N n).edgeSet := Fintype.ofFinite _
local instance coreSeedCmpAsymConfigFintype (N n : ℕ) :
    Fintype (Configuration (horizontalStripAsymmetricRectangle N n)) := Fintype.ofFinite _
local instance coreSeedCmpCoreConfigFintype (N n : ℕ) :
    Fintype (Configuration (rectangleGraph ((-(N : ℤ)) - 1, 0) (2 * N + 1) (2 * n))) := Fintype.ofFinite _
local instance coreSeedCmpAsymVertexDecidableEq (N n : ℕ) :
    DecidableEq (RectangleVertex (-((N + 1 : ℕ) : ℤ), 0) (2 * N + 1) (2 * n)) := Classical.decEq _

def coreSeedCmpVertexEquiv (N n : ℕ) :
    RectangleVertex ((-(N : ℤ), 0).1 - 1, (-(N : ℤ), 0).2)
        (2 * N + 1) (2 * n) ≃
      RectangleVertex (-((N + 1 : ℕ) : ℤ), 0) (2 * N + 1) (2 * n) where
  toFun v := ⟨v.val, by
    have hp := v.property
    rw [mem_latticeRectangle] at hp ⊢
    omega⟩
  invFun v := ⟨v.val, by
    have hp := v.property
    rw [mem_latticeRectangle] at hp ⊢
    omega⟩
  left_inv := by intro v; apply Subtype.ext; rfl
  right_inv := by intro v; apply Subtype.ext; rfl

@[simp] private theorem coreSeedCmpVertexEquiv_val (N n : ℕ)
    (v : RectangleVertex ((-(N : ℤ), 0).1 - 1, (-(N : ℤ), 0).2)
      (2 * N + 1) (2 * n)) : (coreSeedCmpVertexEquiv N n v).val = v.val := rfl

def coreSeedCmpGraphIso (N n : ℕ) :
    rectangleGraph ((-(N : ℤ), 0).1 - 1, (-(N : ℤ), 0).2)
      (2 * N + 1) (2 * n) ≃g horizontalStripAsymmetricRectangle N n where
  toEquiv := coreSeedCmpVertexEquiv N n
  map_rel_iff' := by
    intro u v
    change (rectangleGraph (-((N + 1 : ℕ) : ℤ), 0) (2 * N + 1) (2 * n)).Adj
      ((coreSeedCmpVertexEquiv N n) u) ((coreSeedCmpVertexEquiv N n) v) ↔ _
    rw [rectangleGraph_adj_iff, rectangleGraph_adj_iff]
    rw [coreSeedCmpVertexEquiv_val, coreSeedCmpVertexEquiv_val]

@[simp] private theorem coreSeedCmpGraphIso_val (N n : ℕ)
    (v : RectangleVertex ((-(N : ℤ), 0).1 - 1, (-(N : ℤ), 0).2)
      (2 * N + 1) (2 * n)) : (coreSeedCmpGraphIso N n v).val = v.val := rfl

@[simp] private theorem coreSeedCmpGraphIso_symm_val (N n : ℕ)
    (v : RectangleVertex (-((N + 1 : ℕ) : ℤ), 0) (2 * N + 1) (2 * n)) :
    ((coreSeedCmpGraphIso N n).symm v).val = v.val := rfl

private theorem coreSeedCmp_wiredBoundary_image (N n : ℕ) :
    (coreSeedCmpGraphIso N n) ''
      generalRectangleDualBottomCoreAmbientBoundary (-(N : ℤ), 0) (2 * N) (2 * n) =
    horizontalStripAsymmetricFullThreeSides N n := by
  ext v
  constructor
  · rintro ⟨u, hu, rfl⟩
    have hu' := hu
    simp only [generalRectangleDualBottomCoreAmbientBoundary, Set.mem_ofPred_eq] at hu'
    simp only [horizontalStripAsymmetricFullThreeSides, Set.mem_ofPred_eq]
    rw [coreSeedCmpGraphIso_val]

    omega
  · intro hv
    refine ⟨(coreSeedCmpGraphIso N n).symm v, ?_, (coreSeedCmpGraphIso N n).apply_symm_apply v⟩
    have hv' := hv
    simp only [horizontalStripAsymmetricFullThreeSides, Set.mem_ofPred_eq] at hv'
    simp only [generalRectangleDualBottomCoreAmbientBoundary, Set.mem_ofPred_eq]
    rw [coreSeedCmpGraphIso_symm_val]

    omega

private theorem coreSeedCmp_event_image_subset (N n : ℕ)
    (A : Configuration (rectangleGraph ((-(N : ℤ), 0).1 - 1, (-(N : ℤ), 0).2)
      (2 * N + 1) (2 * n))) :
    A ∈ generalRectangleDualBottomCoreAmbientSeedBoundaryEvent
        (-(N : ℤ), 0) (2 * N) (2 * n) (horizontalStripDualLowerCenterSeeds N n) →
    configurationIso (coreSeedCmpGraphIso N n) A ∈
      horizontalStripAsymmetricCenterThreeSidesEvent N n := by
  rintro ⟨u, hu, z, hz, hconn⟩
  have hu0 : (generalRectangleDualBottomCoreVertexEquiv
      (-(N : ℤ), 0) (2 * N) (2 * n) u).val.1 = 0 := hu.1
  have huYlt : (generalRectangleDualBottomCoreVertexEquiv
      (-(N : ℤ), 0) (2 * N) (2 * n) u).val.2 < (n : ℤ) := hu.2
  have huYlo : 0 ≤ (generalRectangleDualBottomCoreVertexEquiv
      (-(N : ℤ), 0) (2 * N) (2 * n) u).val.2 := by
    have hv := (generalRectangleDualBottomCoreVertexEquiv
      (-(N : ℤ), 0) (2 * N) (2 * n) u).property
    rw [mem_latticeRectangle] at hv
    exact hv.2.1
  have hseedval : (coreSeedCmpGraphIso N n
      (generalRectangleDualBottomCoreVertexEquiv (-(N : ℤ), 0) (2 * N) (2 * n) u)).val.1 = 0 ∧
      0 ≤ (coreSeedCmpGraphIso N n
        (generalRectangleDualBottomCoreVertexEquiv (-(N : ℤ), 0) (2 * N) (2 * n) u)).val.2 ∧
      (coreSeedCmpGraphIso N n
        (generalRectangleDualBottomCoreVertexEquiv (-(N : ℤ), 0) (2 * N) (2 * n) u)).val.2 ≤ (n : ℤ) := by
    simp only [coreSeedCmpGraphIso,
      generalRectangleDualBottomCoreVertexEquiv]
    exact ⟨hu0, huYlo, le_of_lt huYlt⟩
  have hside : coreSeedCmpGraphIso N n z ∈ horizontalStripAsymmetricFullThreeSides N n := by
    have hz' : z ∈ generalRectangleDualBottomCoreAmbientBoundary
        (-(N : ℤ), 0) (2 * N) (2 * n) := hz
    have h := Set.mem_image_of_mem (coreSeedCmpGraphIso N n) hz'
    rw [coreSeedCmp_wiredBoundary_image N n] at h
    exact h
  have hconn' : ActualConnected (horizontalStripAsymmetricRectangle N n)
      (configurationIso (coreSeedCmpGraphIso N n) A)
      (coreSeedCmpGraphIso N n (generalRectangleDualBottomCoreVertexEquiv
        (-(N : ℤ), 0) (2 * N) (2 * n) u)) (coreSeedCmpGraphIso N n z) :=
    (actualConnected_configurationIso (coreSeedCmpGraphIso N n) A _ _).mpr hconn
  exact ⟨coreSeedCmpGraphIso N n
      (generalRectangleDualBottomCoreVertexEquiv (-(N : ℤ), 0) (2 * N) (2 * n) u),
    hseedval.1, hseedval.2.1, hseedval.2.2,
    coreSeedCmpGraphIso N n z, hside, hconn'⟩

/-- Under the matching actual top-and-sides wired laws, the core lower-center
seed boundary event is contained in the asymmetric finite center-to-three-sides
event after the literal identity-coordinate graph isomorphism. -/
theorem horizontalStripCoreLowerCenterSeedBoundary_measure_le_asymmetric
    (q : ClusterWeight) (N n : ℕ) :
    measure (rectangleGraph (-(N : ℤ) - 1, 0) (2 * N + 1) (2 * n)) q
      (BoundaryCondition.wired (generalRectangleDualBottomCoreAmbientBoundary
        (-(N : ℤ), 0) (2 * N) (2 * n)))
      (generalRectangleDualBottomCoreAmbientSeedBoundaryEvent
        (-(N : ℤ), 0) (2 * N) (2 * n) (horizontalStripDualLowerCenterSeeds N n)) ≤
    measure (horizontalStripAsymmetricRectangle N n) q
      (horizontalStripAsymmetricTopSidesBoundary N n)
      (horizontalStripAsymmetricCenterThreeSidesEvent N n) := by
  let G := rectangleGraph ((-(N : ℤ), 0).1 - 1, (-(N : ℤ), 0).2)
    (2 * N + 1) (2 * n)
  let H := horizontalStripAsymmetricRectangle N n
  let e := coreSeedCmpGraphIso N n
  let S := horizontalStripDualLowerCenterSeeds N n
  let E₁ := generalRectangleDualBottomCoreAmbientSeedBoundaryEvent
    (-(N : ℤ), 0) (2 * N) (2 * n) S
  let E₂ := horizontalStripAsymmetricCenterThreeSidesEvent N n
  let ξ := BoundaryCondition.wired (generalRectangleDualBottomCoreAmbientBoundary
    (-(N : ℤ), 0) (2 * N) (2 * n))
  let η := horizontalStripAsymmetricTopSidesBoundary N n
  have hboundary : boundaryConditionIso e ξ = η := by
    rw [boundaryConditionIso_wired_image, coreSeedCmp_wiredBoundary_image]
    congr 1
    ext v
    simp [horizontalStripAsymmetricFullThreeSides, horizontalStripAsymmetricTopSidesSet]
    omega
  have hlaw : (law G q ξ).map (configurationIso e) = law H q η := by
    rw [law_configurationIso_map]
    rw [hboundary]
  have hsub : E₁ ⊆ configurationIso e ⁻¹' E₂ := by
    intro A hA
    exact coreSeedCmp_event_image_subset N n A hA
  have hmeasure : (law G q ξ).toMeasure E₁ ≤
      (law G q ξ).toMeasure (configurationIso e ⁻¹' E₂) :=
    MeasureTheory.measure_mono hsub
  calc
    measure G q ξ E₁ ≤ measure G q ξ (configurationIso e ⁻¹' E₂) := hmeasure
    _ = ((law G q ξ).map (configurationIso e)).toMeasure E₂ := by
      change (law G q ξ).toMeasure (configurationIso e ⁻¹' E₂) = _
      symm
      rw [PMF.toMeasure_map_apply _ _ _ measurable_from_top
        (MeasurableSet.of_discrete (s := E₂))]
    _ = measure H q η E₂ := by rw [hlaw]; rfl

end
end PottsContinuity.FKC.Medial
