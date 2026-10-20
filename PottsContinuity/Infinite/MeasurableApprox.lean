module

public import PottsContinuity.PD.FK.BoxCylinders
public import PottsContinuity.PD.RCInfinite.Cylinders
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Topology.Metrizable.Urysohn
public import Mathlib.Topology.Separation.CompletelyRegular

@[expose] public section

open MeasureTheory Filter Topology
open scoped symmDiff

namespace PottsContinuity.Infinite

open PottsContinuity.PD.FK
open PottsContinuity.PD.RCInfinite

noncomputable section

/-- The finite-coordinate upper hull of a set of configurations. -/
def finiteUpperHull (K : Set LatticeConfiguration)
    (F : Finset squareLattice.edgeSet) : Set LatticeConfiguration :=
  {ω | ∃ x ∈ K, ∀ e ∈ F, x e = true → ω e = true}

theorem finiteUpperHull_isUpperSet (K : Set LatticeConfiguration)
    (F : Finset squareLattice.edgeSet) : IsUpperSet (finiteUpperHull K F) := by
  intro ω η hωη hω
  obtain ⟨x, hxK, hxω⟩ := hω
  refine ⟨x, hxK, ?_⟩
  intro e he hxe
  have hωe : ω e = true := hxω e he hxe
  exact hωη e hωe

theorem finiteUpperHull_isClopen (K : Set LatticeConfiguration)
    (F : Finset squareLattice.edgeSet) : IsClopen (finiteUpperHull K F) := by
  classical
  let patternSet : Finset (Finset squareLattice.edgeSet) :=
    F.powerset.filter fun T => ∃ x ∈ K, ∀ e ∈ F, (x e = true ↔ e ∈ T)
  have hEq : finiteUpperHull K F = ⋃ T ∈ patternSet, LatticeConfiguration.allOpen T := by
    ext ω
    simp only [finiteUpperHull, Set.mem_ofPred_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨x, hxK, hxω⟩
      let T : Finset squareLattice.edgeSet := F.filter fun e => x e = true
      refine ⟨T, ?_, ?_⟩
      · simp only [patternSet, Finset.mem_filter, Finset.mem_powerset]
        refine ⟨Finset.filter_subset _ _, ⟨x, hxK, ?_⟩⟩
        intro e he
        simp [T, he]
      · simpa [LatticeConfiguration.allOpen, T] using hxω
    · rintro ⟨T, hT, hω⟩
      have hpattern : ∃ x ∈ K, ∀ e ∈ F, (x e = true ↔ e ∈ T) := by
        have hT' : T ∈ F.powerset ∧
            ∃ x ∈ K, ∀ e ∈ F, (x e = true ↔ e ∈ T) := by
          simpa [patternSet, Finset.mem_filter] using hT
        exact hT'.2
      obtain ⟨x, hxK, hxT⟩ := hpattern
      refine ⟨x, hxK, ?_⟩
      intro e he hxe
      have heT : e ∈ T := (hxT e he).mp hxe
      change ∀ e ∈ T, ω e = true at hω
      exact hω e heT
  rw [hEq]
  apply isClopen_biUnion_finset
  intro T hT
  exact LatticeConfiguration.allOpen_isClopen T

theorem finiteUpperHull_subset (K : Set LatticeConfiguration)
    (F : Finset squareLattice.edgeSet) : K ⊆ finiteUpperHull K F := by
  intro x hx
  refine ⟨x, hx, ?_⟩
  intro e he hxe
  exact hxe

private theorem finiteUpperHull_anti {K : Set LatticeConfiguration}
    {F G : Finset squareLattice.edgeSet} (hFG : F ⊆ G) :
    finiteUpperHull K G ⊆ finiteUpperHull K F := by
  rintro ω ⟨x, hxK, hxω⟩
  refine ⟨x, hxK, ?_⟩
  intro e he hxe
  exact hxω e (hFG he) hxe

private theorem exists_finiteUpperHull_avoiding
    (K : Set LatticeConfiguration) (hK : IsCompact K)
    (y : LatticeConfiguration) (hno : ∀ x ∈ K, ¬ x ≤ y) :
    ∃ F : Finset squareLattice.edgeSet, y ∉ finiteUpperHull K F := by
  classical
  let I : Set squareLattice.edgeSet := {e | y e = false}
  let U : I → Set LatticeConfiguration := fun e => {x | x e.1 = true}
  have hUopen : ∀ e : I, IsOpen (U e) := by
    intro e
    exact ((isClopen_discrete ({true} : Set Bool)).preimage (continuous_apply e.1)).2
  have hsep : ∀ x ∈ K, ∃ e, x e = true ∧ y e = false := by
    intro x hx
    by_contra h
    push Not at h
    apply hno x hx
    intro e
    cases hx' : x e <;> cases hy' : y e <;> simp_all
  have hcover : K ⊆ ⋃ e : I, U e := by
    intro x hx
    obtain ⟨e, hxe, hye⟩ := hsep x hx
    exact Set.mem_iUnion.2 ⟨⟨e, hye⟩, hxe⟩
  obtain ⟨S, hS⟩ := hK.elim_finite_subcover U hUopen hcover
  let F : Finset squareLattice.edgeSet := S.image Subtype.val
  refine ⟨F, ?_⟩
  intro hy
  obtain ⟨x, hxK, hxω⟩ := hy
  obtain ⟨e, heS, hxe⟩ := Set.mem_iUnion₂.mp (hS hxK)
  have heF : e.1 ∈ F := Finset.mem_image.mpr ⟨e, heS, rfl⟩
  have hxe' : x e.1 = true := by simpa [U] using hxe
  have hytrue : y e.1 = true := hxω e.1 heF hxe'
  exact Bool.noConfusion (hytrue.symm.trans e.2)

theorem exists_finset_upper_separator_of_compact
    (K L : Set LatticeConfiguration) (hK : IsCompact K) (hL : IsCompact L)
    (hKL : ∀ x ∈ K, ∀ y ∈ L, ¬ x ≤ y) :
    ∃ F : Finset squareLattice.edgeSet,
      K ⊆ finiteUpperHull K F ∧ Disjoint (finiteUpperHull K F) L := by
  classical
  let U : Finset squareLattice.edgeSet → Set LatticeConfiguration :=
    fun F => (finiteUpperHull K F)ᶜ
  have hUopen : ∀ F, IsOpen (U F) := by
    intro F
    exact (finiteUpperHull_isClopen K F).1.isOpen_compl
  have hcover : L ⊆ ⋃ F : Finset squareLattice.edgeSet, U F := by
    intro y hy
    obtain ⟨F, hF⟩ := exists_finiteUpperHull_avoiding K hK y (fun x hx => hKL x hx y hy)
    exact Set.mem_iUnion.2 ⟨F, hF⟩
  obtain ⟨S, hS⟩ := hL.elim_finite_subcover U hUopen hcover
  let F : Finset squareLattice.edgeSet := S.biUnion id
  have hdisjoint : Disjoint (finiteUpperHull K F) L := by
    apply Set.disjoint_left.mpr
    intro y hyF hyL
    obtain ⟨F₀, hF₀S, hyU⟩ := Set.mem_iUnion₂.mp (hS hyL)
    have hF₀F : F₀ ⊆ F := by
      exact Finset.subset_biUnion_of_mem id hF₀S
    have hyF₀ : y ∈ finiteUpperHull K F₀ :=
      finiteUpperHull_anti hF₀F hyF
    exact hyU hyF₀
  exact ⟨F, finiteUpperHull_subset K F, hdisjoint⟩

theorem exists_clopen_upper_separator_of_compact
    (K L : Set LatticeConfiguration) (hK : IsCompact K) (hL : IsCompact L)
    (hKL : ∀ x ∈ K, ∀ y ∈ L, ¬ x ≤ y) :
    ∃ U : Set LatticeConfiguration, IsClopen U ∧ IsUpperSet U ∧
      K ⊆ U ∧ Disjoint U L := by
  obtain ⟨F, hKF, hFL⟩ := exists_finset_upper_separator_of_compact K L hK hL hKL
  exact ⟨finiteUpperHull K F, finiteUpperHull_isClopen K F,
    finiteUpperHull_isUpperSet K F, hKF, hFL⟩

/-- A measurable upper event is approximated in measure from both sides by a clopen upper event.
The two error bounds are stated separately so they can be used for different measures. -/
theorem exists_clopen_upper_approx
    (μ : Measure LatticeConfiguration) [IsFiniteMeasure μ]
    {A : Set LatticeConfiguration} (hA : MeasurableSet A)
    (hupper : IsUpperSet A) (ε : ENNReal) (hε : ε ≠ 0) :
    ∃ U : Set LatticeConfiguration, IsClopen U ∧ IsUpperSet U ∧
      μ (A \ U) < ε ∧ μ (U \ A) < ε := by
  have hAfinite : μ A ≠ ⊤ := by finiteness
  have hAcfinite : μ Aᶜ ≠ ⊤ := by finiteness
  obtain ⟨K, hKA, hKclosed, hKerr⟩ :=
    hA.exists_isClosed_sdiff_lt hAfinite hε
  obtain ⟨L, hLA, hLclosed, hLerr⟩ :=
    hA.compl.exists_isClosed_sdiff_lt hAcfinite hε
  have hKL : ∀ x ∈ K, ∀ y ∈ L, ¬ x ≤ y := by
    intro x hx y hy hxy
    exact hLA hy (hupper hxy (hKA hx))
  obtain ⟨U, hUclopen, hUupper, hKU, hUL⟩ :=
    exists_clopen_upper_separator_of_compact K L hKclosed.isCompact hLclosed.isCompact hKL
  refine ⟨U, hUclopen, hUupper, ?_, ?_⟩
  · apply lt_of_le_of_lt (μ.mono ?_) hKerr
    intro x hx
    exact ⟨hx.1, fun hxK => hx.2 (hKU hxK)⟩
  · apply lt_of_le_of_lt (μ.mono ?_) hLerr
    intro x hx
    refine ⟨hx.2, ?_⟩
    intro hxL
    exact (Set.disjoint_left.mp hUL) hx.1 hxL

private theorem measureReal_symmDiff_lt_of_approx
    (μ : Measure LatticeConfiguration) [IsFiniteMeasure μ]
    {A U : Set LatticeConfiguration} (hA : MeasurableSet A)
    (hU : MeasurableSet U) (δ : ℝ) (hδ : 0 < δ)
    (hAU : μ (A \ U) < ENNReal.ofReal δ)
    (hUA : μ (U \ A) < ENNReal.ofReal δ) :
    μ.real (A ∆ U) < 2 * δ := by
  rw [measureReal_symmDiff_eq hA hU]
  have hA' : μ.real (A \ U) < δ := by
    have h := (ENNReal.toReal_lt_toReal (by finiteness) ENNReal.ofReal_ne_top).2 hAU
    simpa [Measure.real_def, ENNReal.toReal_ofReal (le_of_lt hδ)] using h
  have hU' : μ.real (U \ A) < δ := by
    have h := (ENNReal.toReal_lt_toReal (by finiteness) ENNReal.ofReal_ne_top).2 hUA
    simpa [Measure.real_def, ENNReal.toReal_ofReal (le_of_lt hδ)] using h
  calc
    μ.real (A \ U) + μ.real (U \ A) < δ + δ := add_lt_add hA' hU'
    _ = 2 * δ := by ring

private theorem measureReal_inter_symmDiff_le
    (μ : Measure LatticeConfiguration) [IsFiniteMeasure μ]
    (A B U V : Set LatticeConfiguration) :
    μ.real ((A ∩ B) ∆ (U ∩ V)) ≤ μ.real (A ∆ U) + μ.real (B ∆ V) := by
  have hsub : (A ∩ B) ∆ (U ∩ V) ⊆ (A ∆ U) ∪ (B ∆ V) := by
    intro x hx
    simp only [Set.mem_symmDiff, Set.mem_inter_iff, Set.mem_union] at hx ⊢
    tauto
  calc
    μ.real ((A ∩ B) ∆ (U ∩ V)) ≤ μ.real ((A ∆ U) ∪ (B ∆ V)) :=
      measureReal_mono hsub
    _ ≤ μ.real (A ∆ U) + μ.real (B ∆ V) := measureReal_union_le _ _

private theorem mul_le_mul_add_abs {a a' b b' : ℝ}
    (ha'0 : 0 ≤ a') (ha'1 : a' ≤ 1) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    a * b ≤ a' * b' + |a - a'| + |b - b'| := by
  have hfirst : (a - a') * b ≤ |a - a'| := by
    calc
      (a - a') * b ≤ |a - a'| * b := mul_le_mul_of_nonneg_right (le_abs_self _) hb0
      _ ≤ |a - a'| * 1 := mul_le_mul_of_nonneg_left hb1 (abs_nonneg _)
      _ = |a - a'| := by ring
  have hsecond : a' * (b - b') ≤ |b - b'| := by
    calc
      a' * (b - b') ≤ a' * |b - b'| := mul_le_mul_of_nonneg_left (le_abs_self _) ha'0
      _ ≤ 1 * |b - b'| := mul_le_mul_of_nonneg_right ha'1 (abs_nonneg _)
      _ = |b - b'| := by ring
  calc
    a * b = a' * b + (a - a') * b := by ring
    _ ≤ a' * b + |a - a'| := by nlinarith [hfirst]
    _ = a' * b' + a' * (b - b') + |a - a'| := by ring
    _ ≤ a' * b' + |b - b'| + |a - a'| := by linarith
    _ = a' * b' + |a - a'| + |b - b'| := by ring

/-- A finite-coordinate upper hull reads only the coordinates in its defining finset. -/
theorem finiteUpperHull_dependsOn (K : Set LatticeConfiguration)
    (F : Finset squareLattice.edgeSet) :
    DependsOn (F : Set squareLattice.edgeSet) (finiteUpperHull K F) := by
  intro ω η hω
  constructor
  · rintro ⟨x, hxK, hxω⟩
    refine ⟨x, hxK, ?_⟩
    intro e he hxe
    rw [← hω e he]
    exact hxω e he hxe
  · rintro ⟨x, hxK, hxη⟩
    refine ⟨x, hxK, ?_⟩
    intro e he hxe
    rw [hω e he]
    exact hxη e he hxe

/-- Every clopen upper event depends on finitely many edge coordinates. -/
theorem isCylinder_of_clopen_upper {A : Set LatticeConfiguration}
    (hA : IsClopen A) (hupper : IsUpperSet A) : IsCylinder A := by
  classical
  have hAcCompact : IsCompact Aᶜ := hA.2.isClosed_compl.isCompact
  have hKL : ∀ x ∈ A, ∀ y ∈ Aᶜ, ¬ x ≤ y := by
    intro x hx y hy hxy
    exact hy (hupper hxy hx)
  obtain ⟨F, hAF, hUL⟩ := exists_finset_upper_separator_of_compact
    A Aᶜ hA.1.isCompact hAcCompact hKL
  have hUA : finiteUpperHull A F ⊆ A := by
    intro x hx
    by_contra hxA
    exact (Set.disjoint_left.mp hUL) hx hxA
  have hEq : finiteUpperHull A F = A := Set.Subset.antisymm hUA hAF
  refine ⟨F, ?_⟩
  intro ω η hω
  rw [← hEq]
  exact finiteUpperHull_dependsOn A F ω η hω

/-- FKG for measurable upper events follows from FKG for clopen upper events and the
finite-coordinate approximation on the compact configuration space. -/
theorem probabilityMeasure_measurable_upper_fkg_of_clopen
    (μ : ProbabilityMeasure LatticeConfiguration)
    (hclopen : ∀ s t : Set LatticeConfiguration, IsClopen s → IsClopen t →
      IsUpperSet s → IsUpperSet t →
      (((μ s : NNReal) : ℝ) * ((μ t : NNReal) : ℝ) ≤
        ((μ (s ∩ t) : NNReal) : ℝ)))
    {A B : Set LatticeConfiguration} (hA : MeasurableSet A)
    (hB : MeasurableSet B) (hAupper : IsUpperSet A) (hBupper : IsUpperSet B) :
    (((μ A : NNReal) : ℝ) * ((μ B : NNReal) : ℝ) ≤
      ((μ (A ∩ B) : NNReal) : ℝ)) := by
  let a : ℝ := ((μ A : NNReal) : ℝ)
  let b : ℝ := ((μ B : NNReal) : ℝ)
  let c : ℝ := ((μ (A ∩ B) : NNReal) : ℝ)
  change a * b ≤ c
  by_contra hnot
  have hgap : c < a * b := lt_of_not_ge hnot
  let δ : ℝ := (a * b - c) / 9
  have hδ : 0 < δ := div_pos (sub_pos.mpr hgap) (by norm_num)
  have hgapEq : a * b - c = 9 * δ := by dsimp [δ]; ring
  have hε : ENNReal.ofReal δ ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hδ
  obtain ⟨U, hUcl, hUupper, hAminusU, hUminusA⟩ :=
    exists_clopen_upper_approx (μ : Measure LatticeConfiguration) hA hAupper
      (ENNReal.ofReal δ) hε
  obtain ⟨V, hVcl, hVupper, hBminusV, hVminusB⟩ :=
    exists_clopen_upper_approx (μ : Measure LatticeConfiguration) hB hBupper
      (ENNReal.ofReal δ) hε
  let a' : ℝ := ((μ U : NNReal) : ℝ)
  let b' : ℝ := ((μ V : NNReal) : ℝ)
  let c' : ℝ := ((μ (U ∩ V) : NNReal) : ℝ)
  have hAerr : (μ : Measure LatticeConfiguration).real (A ∆ U) < 2 * δ :=
    measureReal_symmDiff_lt_of_approx (μ : Measure LatticeConfiguration)
      hA hUcl.2.measurableSet δ hδ hAminusU hUminusA
  have hBerr : (μ : Measure LatticeConfiguration).real (B ∆ V) < 2 * δ :=
    measureReal_symmDiff_lt_of_approx (μ : Measure LatticeConfiguration)
      hB hVcl.2.measurableSet δ hδ hBminusV hVminusB
  have hAabs : |a - a'| ≤ (μ : Measure LatticeConfiguration).real (A ∆ U) := by
    have h := abs_measureReal_sub_le_measureReal_symmDiff
      (μ := (μ : Measure LatticeConfiguration))
      hA.nullMeasurableSet hUcl.2.measurableSet.nullMeasurableSet
    simpa [a, a', ProbabilityMeasure.measureReal_eq_coe_coeFn] using h
  have hBabs : |b - b'| ≤ (μ : Measure LatticeConfiguration).real (B ∆ V) := by
    have h := abs_measureReal_sub_le_measureReal_symmDiff
      (μ := (μ : Measure LatticeConfiguration))
      hB.nullMeasurableSet hVcl.2.measurableSet.nullMeasurableSet
    simpa [b, b', ProbabilityMeasure.measureReal_eq_coe_coeFn] using h
  have hCabs : |c - c'| < 4 * δ := by
    have h := abs_measureReal_sub_le_measureReal_symmDiff
      (μ := (μ : Measure LatticeConfiguration))
      (hA.inter hB).nullMeasurableSet
      (hUcl.2.measurableSet.inter hVcl.2.measurableSet).nullMeasurableSet
    have h' : |c - c'| ≤ (μ : Measure LatticeConfiguration).real
        ((A ∩ B) ∆ (U ∩ V)) := by
      simpa [c, c', ProbabilityMeasure.measureReal_eq_coe_coeFn] using h
    calc
      |c - c'| ≤ (μ : Measure LatticeConfiguration).real
          ((A ∩ B) ∆ (U ∩ V)) := h'
      _ ≤ (μ : Measure LatticeConfiguration).real (A ∆ U) +
          (μ : Measure LatticeConfiguration).real (B ∆ V) :=
        measureReal_inter_symmDiff_le (μ : Measure LatticeConfiguration) A B U V
      _ < 4 * δ := by linarith [hAerr, hBerr]
  have ha'0 : 0 ≤ a' := by dsimp [a']; positivity
  have ha'1 : a' ≤ 1 := by
    dsimp [a']
    exact_mod_cast ProbabilityMeasure.apply_le_one μ U
  have hb0 : 0 ≤ b := by dsimp [b]; positivity
  have hb1 : b ≤ 1 := by
    dsimp [b]
    exact_mod_cast ProbabilityMeasure.apply_le_one μ B
  have hab : a * b ≤ a' * b' + |a - a'| + |b - b'| :=
    mul_le_mul_add_abs ha'0 ha'1 hb0 hb1
  have hcl := hclopen U V hUcl hVcl hUupper hVupper
  have hcl' : a' * b' ≤ c' := by simpa [a', b', c'] using hcl
  have hcp : c' ≤ c + |c - c'| := by
    have h := le_abs_self (c' - c)
    have habs : |c' - c| = |c - c'| := abs_sub_comm _ _
    linarith
  have habound : a * b ≤ c + 8 * δ := by
    calc
      a * b ≤ a' * b' + |a - a'| + |b - b'| := hab
      _ ≤ c' + |a - a'| + |b - b'| := by linarith
      _ ≤ c + |c - c'| + |a - a'| + |b - b'| := by linarith [hcp]
      _ ≤ c + 8 * δ := by linarith [hAabs.trans_lt hAerr, hBabs.trans_lt hBerr, hCabs]
  nlinarith [hgapEq, hδ]

private theorem measureReal_le_of_measure_le
    {μ ν : Measure LatticeConfiguration} [IsFiniteMeasure ν]
    (hμν : μ ≤ ν) (A : Set LatticeConfiguration) : μ.real A ≤ ν.real A := by
  exact ENNReal.toReal_mono (measure_ne_top ν A) (hμν A)

/-- Stochastic domination for measurable upper events follows from domination on clopen upper
events. A common approximation is taken under the sum of the two probability measures. -/
theorem probabilityMeasure_measurable_upper_domination_of_clopen
    (μ ν : ProbabilityMeasure LatticeConfiguration)
    (hclopen : ∀ U : Set LatticeConfiguration, IsClopen U → IsUpperSet U →
      (((μ U : NNReal) : ℝ) ≤ ((ν U : NNReal) : ℝ)))
    {A : Set LatticeConfiguration} (hA : MeasurableSet A)
    (hupper : IsUpperSet A) :
    (((μ A : NNReal) : ℝ) ≤ ((ν A : NNReal) : ℝ)) := by
  let a : ℝ := ((μ A : NNReal) : ℝ)
  let b : ℝ := ((ν A : NNReal) : ℝ)
  change a ≤ b
  by_contra hnot
  have hgap : b < a := lt_of_not_ge hnot
  let δ : ℝ := (a - b) / 5
  have hδ : 0 < δ := div_pos (sub_pos.mpr hgap) (by norm_num)
  have hgapEq : a - b = 5 * δ := by dsimp [δ]; ring
  let σ : Measure LatticeConfiguration :=
    (μ : Measure LatticeConfiguration) + (ν : Measure LatticeConfiguration)
  have : IsFiniteMeasure σ := inferInstance
  have hε : ENNReal.ofReal δ ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hδ
  obtain ⟨U, hUcl, hUupper, hAminusU, hUminusA⟩ :=
    exists_clopen_upper_approx σ hA hupper (ENNReal.ofReal δ) hε
  let a' : ℝ := ((μ U : NNReal) : ℝ)
  let b' : ℝ := ((ν U : NNReal) : ℝ)
  have hσerr : σ.real (A ∆ U) < 2 * δ :=
    measureReal_symmDiff_lt_of_approx σ hA hUcl.2.measurableSet δ hδ
      hAminusU hUminusA
  have hμσ : (μ : Measure LatticeConfiguration) ≤ σ := Measure.le_add_right le_rfl
  have hνσ : (ν : Measure LatticeConfiguration) ≤ σ := by
    simpa [σ, add_comm] using
      (Measure.le_add_right le_rfl :
        (ν : Measure LatticeConfiguration) ≤
          (ν : Measure LatticeConfiguration) + (μ : Measure LatticeConfiguration))
  have hμerr : (μ : Measure LatticeConfiguration).real (A ∆ U) < 2 * δ := by
    exact (measureReal_le_of_measure_le hμσ (A ∆ U)).trans_lt hσerr
  have hνerr : (ν : Measure LatticeConfiguration).real (A ∆ U) < 2 * δ := by
    exact (measureReal_le_of_measure_le hνσ (A ∆ U)).trans_lt hσerr
  have hμabs : |a - a'| ≤ (μ : Measure LatticeConfiguration).real (A ∆ U) := by
    have h := abs_measureReal_sub_le_measureReal_symmDiff
      (μ := (μ : Measure LatticeConfiguration)) hA.nullMeasurableSet
      hUcl.2.measurableSet.nullMeasurableSet
    simpa [a, a', ProbabilityMeasure.measureReal_eq_coe_coeFn] using h
  have hνabs : |b - b'| ≤ (ν : Measure LatticeConfiguration).real (A ∆ U) := by
    have h := abs_measureReal_sub_le_measureReal_symmDiff
      (μ := (ν : Measure LatticeConfiguration)) hA.nullMeasurableSet
      hUcl.2.measurableSet.nullMeasurableSet
    simpa [b, b', ProbabilityMeasure.measureReal_eq_coe_coeFn] using h
  have hcl := hclopen U hUcl hUupper
  have hcl' : a' ≤ b' := by simpa [a', b'] using hcl
  have hleft : a ≤ a' + |a - a'| := by linarith [le_abs_self (a - a')]
  have hright : b' ≤ b + |b - b'| := by
    have habs : |b' - b| = |b - b'| := abs_sub_comm _ _
    linarith [le_abs_self (b' - b)]
  have hbound : a ≤ b + 4 * δ := by
    calc
      a ≤ a' + |a - a'| := hleft
      _ ≤ b' + |a - a'| := by linarith
      _ ≤ b + |b - b'| + |a - a'| := by linarith [hright]
      _ ≤ b + 4 * δ := by linarith [hμabs.trans_lt hμerr, hνabs.trans_lt hνerr]
  nlinarith [hgapEq, hδ]

end
end PottsContinuity.Infinite
