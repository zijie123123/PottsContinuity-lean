module

public import PottsContinuity.BD12.ReverseCriticalLower
public import PottsContinuity.BD12.CriticalUpperBound
public import PottsContinuity.Critical.ThresholdConstruction

/-! Genuine-threshold identification assembled from the two independent interfaces. -/

@[expose] public section

namespace PottsContinuity.BD12

/-- Conditional identification of every genuine threshold, with only planar
non-coexistence and dense free/wired coincidence left as independent inputs. -/
theorem genuine_criticalPoint_eq_selfDual_of_nonCoexistence_and_coincidence
    (q : Set.Ici (1 : ℝ)) (pc : ℝ) (hpc : IsRCCriticalPoint q pc)
    (hplanar : PlanarNonCoexistenceContract) (hcoincidence : DenseCoincidenceContract q) :
    pc = (PD.rcCriticalParameter q : ℝ) :=
  le_antisymm (genuine_criticalPoint_le_selfDual q pc hpc)
    (selfDual_le_genuine_criticalPoint_of_nonCoexistence_and_coincidence
      q pc hpc hplanar hcoincidence)

/-- The explicit value satisfies the genuine frozen threshold predicate under
the same two interfaces; threshold existence is supplied by Critical. -/
theorem isRCCriticalPoint_selfDual_of_nonCoexistence_and_coincidence
    (q : Set.Ici (1 : ℝ)) (hplanar : PlanarNonCoexistenceContract)
    (hcoincidence : DenseCoincidenceContract q) :
    IsRCCriticalPoint q (PD.rcCriticalParameter q) := by
  obtain ⟨pc,hpc⟩ := Critical.exists_isRCCriticalPoint q
  have heq := genuine_criticalPoint_eq_selfDual_of_nonCoexistence_and_coincidence
    q pc hpc hplanar hcoincidence
  exact heq ▸ hpc

end PottsContinuity.BD12
