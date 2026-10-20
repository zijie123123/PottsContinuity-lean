module

public import PottsContinuity.BD12.SeedWindowCongruence
public import PottsContinuity.BD12.ProbabilityKernelBind

/-! Exact finite-prefix tower identity: averaging the newly pinned original
coordinate recovers the preceding fixed-prefix seed law. Replacement inputs
remain independent uniforms throughout. -/

@[expose] public section

namespace PottsContinuity.BD12
open MeasureTheory
noncomputable section

/-- Varying a single prescribed original real input is measurable. -/
theorem measurable_original_stream_update (U : ℕ → ℝ) (c : ℕ) :
    Measurable (fun u : ℝ => Function.update U c u) := by
  apply measurable_pi_iff.mpr
  intro i
  by_cases hi : i = c
  · subst i
    convert (measurable_id : Measurable (fun u : ℝ => u)) using 1
    funext u
    exact Function.update_self c u U
  · simpa only [Function.update_of_ne hi] using
      (measurable_const : Measurable (fun _ : ℝ => U i))

/-- The newly fixed coordinate at the head of the sampled window averages
back to the actual original uniform input. -/
theorem finiteHybridSeedWindow_pin_head_tower (c : ℕ) (U : ℕ → ℝ)
    (background : ℕ → ℝ × ℝ) (n : ℕ) :
    finiteUnitUniform.bind (fun u =>
        finiteHybridSeedWindow (c + 1) (Function.update U c u) background c (n + 1)) =
      finiteHybridSeedWindow c U background c (n + 1) := by
  have hp (u : ℝ) :
      finiteHybridSeedWindow (c + 1) (Function.update U c u) background c (n + 1) =
      (((Measure.dirac u).prod finiteUnitUniform).prod
        (finiteHybridSeedWindow c U background (c + 1) n)).map
          (fun p => Function.update p.2 c p.1) := by
    rw [finiteHybridSeedWindow, finiteHybridSeedWindow_pin_before c U background (c + 1) n
      (by omega) u]
    simp only [finiteHybridAuxLaw, Nat.lt_succ_self, ite_true, Function.update_self]
  simp_rw [hp]
  rw [probabilityKernel_average_dirac_first _ _ _ _ (measurable_stream_update c),
    finiteHybridSeedWindow]
  simp only [finiteHybridAuxLaw, lt_self_iff_false, ite_false]

/-- Exact one-coordinate tower for ANY finite sampled window, including when
the newly pinned coordinate lies before or after the window. -/
theorem finiteHybridSeedWindow_pin_tower (c : ℕ) (U : ℕ → ℝ)
    (background : ℕ → ℝ × ℝ) (start n : ℕ) :
    finiteUnitUniform.bind (fun u =>
        finiteHybridSeedWindow (c + 1) (Function.update U c u) background start n) =
      finiteHybridSeedWindow c U background start n := by
  induction n generalizing start with
  | zero => simp only [finiteHybridSeedWindow, Measure.bind_const, measure_univ, one_smul]
  | succ n ih =>
    rcases lt_trichotomy c start with hbefore | heq | hafter
    · simp_rw [finiteHybridSeedWindow_pin_before c U background start (n + 1) hbefore]
      rw [Measure.bind_const, measure_univ, one_smul]
    · subst start
      exact finiteHybridSeedWindow_pin_head_tower c U background n
    · let Q := (finiteHybridAuxLaw c U start).prod finiteUnitUniform
      let K := fun u : ℝ =>
        finiteHybridSeedWindow (c + 1) (Function.update U c u) background (start + 1) n
      let L := finiteHybridSeedWindow c U background (start + 1) n
      have hK : Measurable K :=
        (finiteHybridSeedWindow_fixedU_measurable (c + 1) background (start + 1) n).comp
          (measurable_original_stream_update U c)
      have hfirst (u : ℝ) :
          finiteHybridAuxLaw (c + 1) (Function.update U c u) start = finiteHybridAuxLaw c U start := by
        simp only [finiteHybridAuxLaw, hafter, show start < c + 1 by omega, ite_true,
          Function.update_of_ne (show start ≠ c by omega)]
      let H : ℝ → (ℝ × ℝ) → Measure (ℕ → ℝ × ℝ) :=
        fun u uv => (K u).map (fun S => Function.update S start uv)
      have hH : Measurable H.uncurry := by
        exact probabilityKernel_param_map_measurable (fun p : ℝ × (ℝ × ℝ) => K p.1)
          (hK.comp measurable_fst)
          (fun p : (ℝ × (ℝ × ℝ)) × (ℕ → ℝ × ℝ) => Function.update p.2 start p.1.2)
          ((measurable_stream_update start).comp
            ((measurable_snd.comp measurable_fst).prodMk measurable_snd))
      have hstep (u : ℝ) :
          finiteHybridSeedWindow (c + 1) (Function.update U c u) background start (n + 1) =
          Q.bind (fun uv => H u uv) := by
        rw [finiteHybridSeedWindow, hfirst u]
        exact finiteKernel_prod_map _ _ _ (measurable_stream_update start)
      simp_rw [hstep]
      rw [Measure.bind_comm hH]
      rw [finiteHybridSeedWindow, finiteKernel_prod_map _ _ _ (measurable_stream_update start)]
      apply congrArg (Measure.bind Q)
      funext uv
      have hupdate : Measurable (fun S : ℕ → ℝ × ℝ => Function.update S start uv) :=
        (measurable_stream_update start).comp (measurable_const.prodMk measurable_id)
      change finiteUnitUniform.bind (fun u => (K u).map (fun S => Function.update S start uv)) = _
      rw [← finiteKernel_map_bind _ K hK _ hupdate]
      have hih : finiteUnitUniform.bind K = L := ih (start + 1)
      rw [hih]

end
end PottsContinuity.BD12
