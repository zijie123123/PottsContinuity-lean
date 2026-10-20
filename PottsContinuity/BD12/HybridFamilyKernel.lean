module

public import PottsContinuity.BD12.JointHybridRegularity

/-! A shared original-coordinate (U,V) kernel for any finite family of DRT
hybrids. Original U is fixed on the conditioned fixedThrough; all other original U
and all replacement V inputs are fresh independent uniforms. Every hybrid uses
the same original branch, stopping flag, and pair of inputs at each node. -/

@[expose] public section

namespace PottsContinuity.BD12
open MeasureTheory
open scoped Classical
noncomputable section

/-- Push a measurable output through a measurable iterated kernel. -/
theorem finiteKernel_map_bind {α β γ : Type*} [MeasurableSpace α]
    [MeasurableSpace β] [MeasurableSpace γ] (μ : Measure α)
    (K : α → Measure β) (hK : Measurable K) (g : β → γ) (hg : Measurable g) :
    (μ.bind K).map g = μ.bind (fun x => (K x).map g) := by
  unfold Measure.bind
  rw [← Measure.join_map_map hg, Measure.map_map (Measure.measurable_map g hg) hK]
  rfl

/-- Integrating a continuation depending only on the first independent input. -/
theorem finiteKernel_prod_bind_fst {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure ℝ) [IsProbabilityMeasure ν]
    (F : ℝ → Measure Ω) (hF : Measurable F) :
    (μ.prod ν).bind (fun uv => F uv.1) = μ.bind F := by
  have hm : (μ.prod ν).map Prod.fst = μ := by
    rw [Measure.map_fst_prod, measure_univ, one_smul]
  calc
    _ = ((μ.prod ν).map Prod.fst).bind F := by
      unfold Measure.bind
      rw [Measure.map_map hF measurable_fst]
      rfl
    _ = _ := by rw [hm]

/-- Integrating a continuation depending only on the second independent input. -/
theorem finiteKernel_prod_bind_snd {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [SFinite ν]
    (F : ℝ → Measure Ω) (hF : Measurable F) :
    (μ.prod ν).bind (fun uv => F uv.2) = ν.bind F := by
  have hm : (μ.prod ν).map Prod.snd = ν := by
    rw [Measure.map_snd_prod, measure_univ, one_smul]
  calc
    _ = ((μ.prod ν).map Prod.snd).bind F := by
      unfold Measure.bind
      rw [Measure.map_map hF measurable_snd]
      rfl
    _ = _ := by rw [hm]

variable {E ι : Type*} [Fintype E] [DecidableEq E] [Fintype ι]
    [MeasurableSpace (Finset E)]

/-- Shared original-coordinate draws for a finite family of cutoffs. At a leaf
we retain both X and every Y, so this is a coupling rather than separate laws. -/
def finiteHybridFamilyKernel (w : Finset E → Set.Ioi (0 : ℝ)) (f : Finset E → ℝ)
    (fixedThrough : ℕ) (fixedU : ℕ → ℝ) (cutoff : ι → ℕ) :
    {R : Finset E} → FiniteRevealTree E R → Finset E → (ι → Finset E) → Bool →
      Measure (Finset E × (ι → Finset E))
  | _, .done, HX, HY, _ => Measure.dirac (HX, HY)
  | R, .query e _ next, HX, HY, stopped =>
      let halted := stopped || decide (finiteDetermines f R HX)
      ((finiteHybridAuxLaw fixedThrough fixedU R.card).prod finiteUnitUniform).bind (fun uv =>
        let bx := finiteUniformBit
          (finitePinnedMean w R HX (fun A => if e ∈ A then 1 else 0)) uv.1
        let byy := fun j => finiteUniformBit
          (finitePinnedMean w R (HY j) (fun A => if e ∈ A then 1 else 0))
          (if cutoff j ≤ R.card ∧ halted = false then uv.1 else uv.2)
        finiteHybridFamilyKernel w f fixedThrough fixedU cutoff (next bx)
          (finiteRevealPattern HX e bx) (fun j => finiteRevealPattern (HY j) e (byy j)) halted)

/-- Each node's continuation is measurable: all branching depends on finitely
many measurable threshold bits, despite sharing full real inputs. -/
theorem finiteHybridFamilyKernel_node_measurable
    (w : Finset E → Set.Ioi (0 : ℝ)) (f : Finset E → ℝ)
    (fixedThrough : ℕ) (fixedU : ℕ → ℝ) (cutoff : ι → ℕ)
    (R : Finset E) (e : E) (_he : e ∉ R)
    (next : Bool → FiniteRevealTree E (insert e R)) (HX : Finset E)
    (HY : ι → Finset E) (stopped : Bool) :
    Measurable (fun uv : ℝ × ℝ =>
      let halted := stopped || decide (finiteDetermines f R HX)
      let bx := finiteUniformBit
        (finitePinnedMean w R HX (fun A => if e ∈ A then 1 else 0)) uv.1
      let byy := fun j => finiteUniformBit
        (finitePinnedMean w R (HY j) (fun A => if e ∈ A then 1 else 0))
        (if cutoff j ≤ R.card ∧ halted = false then uv.1 else uv.2)
      finiteHybridFamilyKernel w f fixedThrough fixedU cutoff (next bx)
        (finiteRevealPattern HX e bx) (fun j => finiteRevealPattern (HY j) e (byy j)) halted) := by
  let halted := stopped || decide (finiteDetermines f R HX)
  let B : ℝ × ℝ → Bool × (ι → Bool) := fun uv =>
    (finiteUniformBit (finitePinnedMean w R HX (fun A => if e ∈ A then 1 else 0)) uv.1,
      fun j => finiteUniformBit (finitePinnedMean w R (HY j) (fun A => if e ∈ A then 1 else 0))
        (if cutoff j ≤ R.card ∧ halted = false then uv.1 else uv.2))
  have hB : Measurable B := by
    apply Measurable.prodMk
    · exact (finiteUniformBit_measurable _).comp measurable_fst
    · apply measurable_pi_iff.mpr
      intro j
      split_ifs
      · exact (finiteUniformBit_measurable _).comp measurable_fst
      · exact (finiteUniformBit_measurable _).comp measurable_snd
  exact (measurable_of_finite (fun b : Bool × (ι → Bool) =>
    finiteHybridFamilyKernel w f fixedThrough fixedU cutoff (next b.1)
      (finiteRevealPattern HX e b.1) (fun j => finiteRevealPattern (HY j) e (b.2 j)) halted)).comp hB

/-- Every hybrid cutoff beyond the fixed original fixedThrough has the actual pinned
law, as a marginal of ONE coupling retaining X and all hybrids. In particular,
conditioning the original fixedThrough through its cutoff leaves that hybrid's law
unchanged. No conditional marginal or independence estimate is assumed. -/
theorem finiteHybridFamilyKernel_marginal
    (w : Finset E → Set.Ioi (0 : ℝ)) (f : Finset E → ℝ)
    (fixedThrough : ℕ) (fixedU : ℕ → ℝ) (cutoff : ι → ℕ)
    {R : Finset E} (T : FiniteRevealTree E R) (HX : Finset E)
    (HY : ι → Finset E) (stopped : Bool) (j : ι) (hj : fixedThrough ≤ cutoff j) :
    (finiteHybridFamilyKernel w f fixedThrough fixedU cutoff T HX HY stopped).map
        (fun XY => XY.2 j) = (finitePinnedLaw w R (HY j)).toMeasure := by
  induction T generalizing HX HY stopped with
  | done =>
    rw [finiteHybridFamilyKernel, Measure.map_dirac' (f := fun XY : Finset E × (ι → Finset E) => XY.2 j) ((measurable_pi_apply j).comp measurable_snd)]
    rw [finitePinnedLaw_univ, PMF.toMeasure_pure]
  | @query R e he next ih =>
    rw [finiteHybridFamilyKernel, finiteKernel_map_bind _ _
      (finiteHybridFamilyKernel_node_measurable w f fixedThrough fixedU cutoff R e he next HX HY stopped)
      (fun XY => XY.2 j) ((measurable_pi_apply j).comp measurable_snd)]
    simp_rw [ih]
    let halted := stopped || decide (finiteDetermines f R HX)
    let F : ℝ → Measure (Finset E) := fun u =>
      (finitePinnedLaw w (insert e R) (finiteRevealPattern (HY j) e
        (finiteUniformBit (finitePinnedMean w R (HY j) (fun A => if e ∈ A then 1 else 0)) u))).toMeasure
    have hF : Measurable F := (measurable_of_finite (fun b : Bool =>
      (finitePinnedLaw w (insert e R) (finiteRevealPattern (HY j) e b)).toMeasure)).comp
        (finiteUniformBit_measurable _)
    change ((finiteHybridAuxLaw fixedThrough fixedU R.card).prod finiteUnitUniform).bind
      (fun uv => F (if cutoff j ≤ R.card ∧ halted = false then uv.1 else uv.2)) = _
    have hreduce : ((finiteHybridAuxLaw fixedThrough fixedU R.card).prod finiteUnitUniform).bind
        (fun uv => F (if cutoff j ≤ R.card ∧ halted = false then uv.1 else uv.2)) =
        finiteUnitUniform.bind F := by
      by_cases h : cutoff j ≤ R.card ∧ halted = false
      · simp only [h]
        have hfixedThrough : ¬R.card < fixedThrough := Nat.not_lt.mpr (hj.trans h.1)
        simp only [finiteHybridAuxLaw, hfixedThrough, ite_false]
        exact finiteKernel_prod_bind_fst _ _ F hF
      · simp only [h, ite_false]
        exact finiteKernel_prod_bind_snd _ _ F hF
    rw [hreduce]
    dsimp only [F]
    rw [finiteUnitUniform_bind_reveal w R (HY j) e he
      (fun b => (finitePinnedLaw w (insert e R) (finiteRevealPattern (HY j) e b)).toMeasure),
      finitePMF_toMeasure_bind, finitePinnedLaw_bind_reveal]

end
end PottsContinuity.BD12
