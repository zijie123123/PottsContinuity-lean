-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/SlitBoxHorizontalReflection.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.SlitBoxDomain
public import PottsContinuity.FKC.FiniteFK.Isomorphism
public import PottsContinuity.FKC.FiniteFK.RectangleTranslation
public import PottsContinuity.FKC.FiniteFK.IncreasingEvents
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

noncomputable section

 theorem slitBoxHorizontalReflection_mem (n : ℕ)
    (v : SlitBoxVertex n) : (-v.val.1, v.val.2) ∈
      latticeRectangle (-(n : ℤ), -(n : ℤ)) (2 * n) (2 * n) := by
  have hv := (mem_latticeRectangle _ v.val (2 * n) (2 * n)).mp v.property
  apply (mem_latticeRectangle _ (-v.val.1, v.val.2) (2 * n) (2 * n)).mpr
  constructor
  · change -(n : ℤ) ≤ -v.val.1 ∧ -v.val.1 ≤ -(n : ℤ) + (2 * n : ℕ)
    constructor <;> push_cast <;> omega
  · change -(n : ℤ) ≤ v.val.2 ∧ v.val.2 ≤ -(n : ℤ) + (2 * n : ℕ)
    exact hv.2

/-- Reflection across the vertical axis of the retained slit box. -/
def slitBoxHorizontalReflectionVertexEquiv (n : ℕ) :
    SlitBoxVertex n ≃ SlitBoxVertex n where
  toFun v := ⟨(-v.val.1, v.val.2), slitBoxHorizontalReflection_mem n v⟩
  invFun v := ⟨(-v.val.1, v.val.2), slitBoxHorizontalReflection_mem n v⟩
  left_inv v := by
    apply Subtype.ext
    ext <;> simp
  right_inv v := by
    apply Subtype.ext
    ext <;> simp

@[simp] theorem slitBoxHorizontalReflectionVertexEquiv_val (n : ℕ)
    (v : SlitBoxVertex n) :
    (slitBoxHorizontalReflectionVertexEquiv n v).val = (-v.val.1, v.val.2) := rfl

def slitBoxGraphHorizontalReflectionIso (n : ℕ) :
    slitBoxGraph n ≃g slitBoxGraph n where
  toEquiv := slitBoxHorizontalReflectionVertexEquiv n
  map_rel_iff' := by
    intro u v
    rw [slitBoxGraph_adj_iff, slitBoxGraph_adj_iff,
      slitBoxHorizontalReflectionVertexEquiv_val,
      slitBoxHorizontalReflectionVertexEquiv_val,
      squareLattice_adj_iff, squareLattice_adj_iff]
    constructor
    · rintro ⟨hAdj, hDel⟩
      refine ⟨?_, ?_⟩
      · omega
      · intro hBoth
        apply hDel
        omega
    · rintro ⟨hAdj, hDel⟩
      refine ⟨?_, ?_⟩
      · omega
      · intro hBoth
        apply hDel
        omega

theorem slitBoxGraphHorizontalReflection_image_wiredArc (n : ℕ) :
    slitBoxGraphHorizontalReflectionIso n '' slitBoxWiredArc n =
      slitBoxWiredArc n := by
  ext v
  constructor
  · rintro ⟨u, hu, rfl⟩
    have hu' : u ∈ slitBoxWiredArc n := by simpa using hu
    have hcoords := (mem_slitBoxWiredArc_iff n u).mp hu'
    apply (mem_slitBoxWiredArc_iff n _).mpr
    change (-u.val.1 = 0 ∧ 0 ≤ u.val.2 ∧ u.val.2 ≤ n)
    rcases hcoords with ⟨hx, hy0, hyn⟩
    exact ⟨by omega, hy0, hyn⟩
  · intro hv
    refine ⟨slitBoxGraphHorizontalReflectionIso n v, ?_, ?_⟩
    · have hv' : v ∈ slitBoxWiredArc n := by simpa using hv
      have hcoords := (mem_slitBoxWiredArc_iff n v).mp hv'
      apply (mem_slitBoxWiredArc_iff n _).mpr
      change (-v.val.1 = 0 ∧ 0 ≤ v.val.2 ∧ v.val.2 ≤ n)
      rcases hcoords with ⟨hx, hy0, hyn⟩
      exact ⟨by omega, hy0, hyn⟩
    · exact (slitBoxGraphHorizontalReflectionIso n).apply_symm_apply v

theorem law_slitBoxGraph_horizontalReflection_map (n : ℕ) (q : ClusterWeight) :
    (law (slitBoxGraph n) q (slitBoxBoundary n)).map
      (configurationIso (slitBoxGraphHorizontalReflectionIso n)) =
        law (slitBoxGraph n) q (slitBoxBoundary n) := by
  rw [law_configurationIso_map, slitBoxBoundary,
    boundaryConditionIso_wired_image,
    slitBoxGraphHorizontalReflection_image_wiredArc]

theorem slitBoxWiredArcConnectionEvent_horizontalReflection_preimage
    (n : ℕ) (u : SlitBoxVertex n) :
    (configurationIso (slitBoxGraphHorizontalReflectionIso n)) ⁻¹'
        slitBoxWiredArcConnectionEvent n
          (slitBoxGraphHorizontalReflectionIso n u) =
      slitBoxWiredArcConnectionEvent n u := by
  ext A
  change (∃ v ∈ slitBoxWiredArc n,
      ActualConnected (slitBoxGraph n)
        (configurationIso (slitBoxGraphHorizontalReflectionIso n) A)
        (slitBoxGraphHorizontalReflectionIso n u) v) ↔
    ∃ v ∈ slitBoxWiredArc n,
      ActualConnected (slitBoxGraph n) A u v
  constructor
  · rintro ⟨v, hv, hconn⟩
    have hvImage : v ∈ slitBoxGraphHorizontalReflectionIso n '' slitBoxWiredArc n := by
      rw [slitBoxGraphHorizontalReflection_image_wiredArc]
      exact hv
    rcases hvImage with ⟨w, hw, hvw⟩
    refine ⟨w, hw, ?_⟩
    have hconn' : ActualConnected (slitBoxGraph n)
        (configurationIso (slitBoxGraphHorizontalReflectionIso n) A)
        (slitBoxGraphHorizontalReflectionIso n u)
        (slitBoxGraphHorizontalReflectionIso n w) := by
      simpa [hvw] using hconn
    exact (actualConnected_configurationIso
      (slitBoxGraphHorizontalReflectionIso n) A u w).mp hconn'
  · rintro ⟨v, hv, hconn⟩
    have hvImage : slitBoxGraphHorizontalReflectionIso n v ∈
        slitBoxWiredArc n := by
      have hmem : slitBoxGraphHorizontalReflectionIso n v ∈
          slitBoxGraphHorizontalReflectionIso n '' slitBoxWiredArc n :=
        ⟨v, hv, rfl⟩
      rw [slitBoxGraphHorizontalReflection_image_wiredArc] at hmem
      exact hmem
    refine ⟨slitBoxGraphHorizontalReflectionIso n v, hvImage, ?_⟩
    exact (actualConnected_configurationIso
      (slitBoxGraphHorizontalReflectionIso n) A u v).mpr hconn

attribute [local instance] configurationMeasurableSpace

theorem measure_slitBoxWiredArcConnectionEvent_horizontalReflection
    (n : ℕ) (q : ClusterWeight) (u : SlitBoxVertex n) :
    measure (slitBoxGraph n) q (slitBoxBoundary n)
        (slitBoxWiredArcConnectionEvent n u) =
      measure (slitBoxGraph n) q (slitBoxBoundary n)
        (slitBoxWiredArcConnectionEvent n
          (slitBoxGraphHorizontalReflectionIso n u)) := by
  let e := configurationIso (slitBoxGraphHorizontalReflectionIso n)
  let σ := slitBoxGraphHorizontalReflectionIso n
  have hlaw := law_slitBoxGraph_horizontalReflection_map n q
  have hmap := congrArg PMF.toMeasure hlaw
  rw [← PMF.toMeasure_map _ _ measurable_from_top] at hmap
  have hpre := slitBoxWiredArcConnectionEvent_horizontalReflection_preimage n u
  calc
    measure (slitBoxGraph n) q (slitBoxBoundary n)
        (slitBoxWiredArcConnectionEvent n u) =
      (law (slitBoxGraph n) q (slitBoxBoundary n)).toMeasure
        (e ⁻¹' slitBoxWiredArcConnectionEvent n (σ u)) := by
          rw [← hpre]
          rfl
    _ = MeasureTheory.Measure.map e
        (law (slitBoxGraph n) q (slitBoxBoundary n)).toMeasure
          (slitBoxWiredArcConnectionEvent n (σ u)) := by
            symm
            rw [MeasureTheory.Measure.map_apply measurable_from_top
              (MeasurableSet.of_discrete
                (s := slitBoxWiredArcConnectionEvent n (σ u)))]
    _ = measure (slitBoxGraph n) q (slitBoxBoundary n)
        (slitBoxWiredArcConnectionEvent n (σ u)) := by
          rw [hmap]
          rfl

theorem slitBoxWiredArcConnectionEvent_fkg_square_lower_bound
    (n : ℕ) (q : ClusterWeight) (u : SlitBoxVertex n) :
    (measure (slitBoxGraph n) q (slitBoxBoundary n)
      (slitBoxWiredArcConnectionEvent n u)).toReal ^ 2 ≤
      (measure (slitBoxGraph n) q (slitBoxBoundary n)
        (slitBoxWiredArcConnectionEvent n u ∩
          slitBoxWiredArcConnectionEvent n
            (slitBoxGraphHorizontalReflectionIso n u))).toReal := by
  let E := slitBoxWiredArcConnectionEvent n u
  let F := slitBoxWiredArcConnectionEvent n
    (slitBoxGraphHorizontalReflectionIso n u)
  have hE : IsUpperSet E := by
    intro A B hAB hA
    exact slitBoxWiredArcConnectionEvent_mono n u hAB hA
  have hF : IsUpperSet F := by
    intro A B hAB hA
    exact slitBoxWiredArcConnectionEvent_mono n
      (slitBoxGraphHorizontalReflectionIso n u) hAB hA
  have hFKG := measure_positive_association q (slitBoxBoundary n) E F hE hF
  have hreflect := measure_slitBoxWiredArcConnectionEvent_horizontalReflection n q u
  have hreal : (measure (slitBoxGraph n) q (slitBoxBoundary n) E).toReal =
      (measure (slitBoxGraph n) q (slitBoxBoundary n) F).toReal :=
    congrArg ENNReal.toReal hreflect
  change (measure (slitBoxGraph n) q (slitBoxBoundary n) E).toReal ^ 2 ≤
      (measure (slitBoxGraph n) q (slitBoxBoundary n) (E ∩ F)).toReal
  calc
    (measure (slitBoxGraph n) q (slitBoxBoundary n) E).toReal ^ 2 =
        (measure (slitBoxGraph n) q (slitBoxBoundary n) E).toReal *
          (measure (slitBoxGraph n) q (slitBoxBoundary n) F).toReal := by
            rw [← hreal]
            ring
    _ ≤ (measure (slitBoxGraph n) q (slitBoxBoundary n) (E ∩ F)).toReal := by
      simpa [E, F] using hFKG

end
end PottsContinuity.FKC.FiniteFK
