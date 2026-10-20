module

public import PottsContinuity.BD12.FixedOriginalSeedExtension
public import PottsContinuity.BD12.ProbabilityKernelBind

/-! The fully fixed-original-input seed law is the pushforward of an actual
finite product of independent replacement uniforms. -/

@[expose] public section

namespace PottsContinuity.BD12
open MeasureTheory
noncomputable section

/-- Disintegrate one original/replacement pair when its original value is fixed. -/
theorem fixedOriginal_seed_head (a : ℝ) (start : ℕ)
    (η : Measure (ℕ → ℝ × ℝ)) [IsProbabilityMeasure η] :
    (((Measure.dirac a).prod finiteUnitUniform).prod η).map
        (fun p => Function.update p.2 start p.1) =
      finiteUnitUniform.bind (fun v => η.map (fun S => Function.update S start (a, v))) := by
  let K : ℝ × ℝ → Measure (ℕ → ℝ × ℝ) := fun uv =>
    η.map (fun S => Function.update S start uv)
  have hK : Measurable K := probabilityKernel_param_map_measurable
    (fun _ : ℝ × ℝ => η) measurable_const _ (measurable_stream_update start)
  rw [finiteKernel_prod_map _ _ _ (measurable_stream_update start)]
  change ((Measure.dirac a).prod finiteUnitUniform).bind K = _
  rw [probabilityKernel_prod_bind _ _ K hK,
    Measure.dirac_bind (Measurable.measurable_bind_left
      (f := fun u v => K (u, v)) hK) a]

/-- Product-uniform realization of the actual seed window when all original
inputs in the sampled window are among the prescribed prefix. -/
theorem finiteFixedOriginalExtension_map_product
    (fixedThrough start n : ℕ) (U : ℕ → ℝ) (background : ℕ → ℝ × ℝ)
    (hfixed : start + n ≤ fixedThrough) :
    (Measure.pi (fun _ : Fin n => finiteUnitUniform)).map
        (finiteFixedOriginalExtension start n U background) =
      finiteHybridSeedWindow fixedThrough U background start n := by
  induction n generalizing start with
  | zero =>
    simp only [finiteFixedOriginalExtension, finiteHybridSeedWindow, Measure.map_const,
      measure_univ, one_smul]
  | succ n ih =>
    let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0
    have hp := (measurePreserving_piFinSuccAbove
      (fun _ : Fin (n + 1) => finiteUnitUniform) 0).symm
    have hmap : (finiteUnitUniform.prod (Measure.pi (fun _ : Fin n => finiteUnitUniform))).map e.symm =
        Measure.pi (fun _ : Fin (n + 1) => finiteUnitUniform) := hp.map_eq
    have hcons (z : ℝ × (Fin n → ℝ)) : e.symm z = Fin.cons z.1 z.2 := by
      simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]
    have hF := finiteFixedOriginalExtension_measurable start (n + 1) U background
    calc
      _ = (finiteUnitUniform.prod (Measure.pi (fun _ : Fin n => finiteUnitUniform))).map
          (fun z => Function.update
            (finiteFixedOriginalExtension (start + 1) n U background z.2) start (U start, z.1)) := by
        rw [← hmap, Measure.map_map hF e.symm.measurable]
        apply congrArg (fun F => (finiteUnitUniform.prod
          (Measure.pi (fun _ : Fin n => finiteUnitUniform))).map F)
        funext z
        simp only [Function.comp_apply, hcons, finiteFixedOriginalExtension, Fin.cons_zero, Fin.cons_succ]
      _ = finiteUnitUniform.bind (fun v =>
          (Measure.pi (fun _ : Fin n => finiteUnitUniform)).map (fun z => Function.update
            (finiteFixedOriginalExtension (start + 1) n U background z) start (U start, v))) := by
        apply finiteKernel_prod_map
        have ht : Measurable (fun z : ℝ × (Fin n → ℝ) =>
            finiteFixedOriginalExtension (start + 1) n U background z.2) :=
          (finiteFixedOriginalExtension_measurable (start + 1) n U background).comp measurable_snd
        have hh : Measurable (fun z : ℝ × (Fin n → ℝ) => (U start, z.1)) :=
          measurable_const.prodMk measurable_fst
        exact (measurable_stream_update start).comp (hh.prodMk ht)
      _ = finiteUnitUniform.bind (fun v =>
          (finiteHybridSeedWindow fixedThrough U background (start + 1) n).map
            (fun S => Function.update S start (U start, v))) := by
        apply congrArg (Measure.bind finiteUnitUniform)
        funext v
        have hu : Measurable (fun S : ℕ → ℝ × ℝ => Function.update S start (U start, v)) :=
          (measurable_stream_update start).comp (measurable_const.prodMk measurable_id)
        change (Measure.pi (fun _ : Fin n => finiteUnitUniform)).map
          ((fun S => Function.update S start (U start, v)) ∘
            finiteFixedOriginalExtension (start + 1) n U background) = _
        rw [← Measure.map_map hu (finiteFixedOriginalExtension_measurable (start + 1) n U background),
          ih (start + 1) (by omega)]
      _ = _ := by
        rw [finiteHybridSeedWindow]
        have hi : start < fixedThrough := by omega
        simp only [finiteHybridAuxLaw, hi, ite_true]
        exact (fixedOriginal_seed_head _ _ _).symm

/-- Fully fixed original inputs give exactly U, and the replacement vector is
inserted by the same finiteSeedExtension used in the actual Harris estimates. -/
theorem finiteFixedOriginal_seed_product (n : ℕ) (U V : ℕ → ℝ) :
    (Measure.pi (fun _ : Fin n => finiteUnitUniform)).map
        (fun v => fun i => (U i, finiteSeedExtension n V v i)) =
      finiteHybridSeedWindow n U (fun i => (U i, V i)) 0 n := by
  have h := finiteFixedOriginalExtension_map_product n 0 n U (fun i => (U i, V i)) (by omega)
  have hF : finiteFixedOriginalExtension 0 n U (fun i => (U i, V i)) =
      fun v i => (U i, finiteSeedExtension n V v i) :=
    funext (fun v => finiteFixedOriginalExtension_zero n U V v)
  rw [hF] at h
  exact h

end
end PottsContinuity.BD12
