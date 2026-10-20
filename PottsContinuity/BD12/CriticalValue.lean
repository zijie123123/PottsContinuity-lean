module

public import PottsContinuity.BD12.CriticalValueConditional
public import PottsContinuity.BD12.ThresholdInterfaces

/-! The explicit self-dual value is the genuine frozen threshold for every real q at least one. -/

@[expose] public section

namespace PottsContinuity.BD12

/-- Every genuine critical point equals the explicit self-dual parameter. -/
theorem genuine_criticalPoint_eq_selfDual (q : Set.Ici (1 : ℝ)) (pc : ℝ)
    (hpc : IsRCCriticalPoint q pc) : pc = (PD.rcCriticalParameter q : ℝ) :=
  genuine_criticalPoint_eq_selfDual_of_nonCoexistence_and_coincidence
    q pc hpc planar_noncoexistence_contract (dense_coincidence_contract q)

/-- The literal critical-value formula from BD12, at the genuine threshold. -/
theorem genuine_criticalPoint_eq_sqrt (q : Set.Ici (1 : ℝ)) (pc : ℝ)
    (hpc : IsRCCriticalPoint q pc) : pc = Real.sqrt (q : ℝ)/(1+Real.sqrt (q : ℝ)) :=
  genuine_criticalPoint_eq_selfDual q pc hpc

/-- The explicit value satisfies the actual every-exhaustion frozen threshold
predicate; no threshold or measure is supplied as an extra premise. -/
theorem isRCCriticalPoint_selfDual (q : Set.Ici (1 : ℝ)) :
    IsRCCriticalPoint q (PD.rcCriticalParameter q) :=
  isRCCriticalPoint_selfDual_of_nonCoexistence_and_coincidence
    q planar_noncoexistence_contract (dense_coincidence_contract q)

/-- The literal formula itself is a genuine critical point for every real q at least one. -/
theorem isRCCriticalPoint_sqrt (q : Set.Ici (1 : ℝ)) :
    IsRCCriticalPoint q (Real.sqrt (q : ℝ)/(1+Real.sqrt (q : ℝ))) :=
  isRCCriticalPoint_selfDual q

end PottsContinuity.BD12
