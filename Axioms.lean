module

public import PottsContinuity

/-!
# Axiom audit

Run `lake env lean Axioms.lean` after `lake build`. Each of the seven main declarations must
depend only on the three standard axioms `[propext, Classical.choice, Quot.sound]`; in particular
no `sorryAx` and no custom axiom.
-/

#print axioms PottsContinuity.theorem_1
#print axioms PottsContinuity.theorem_2
#print axioms PottsContinuity.theorem_3
#print axioms PottsContinuity.isRCInfiniteVolumeLimit_unique
#print axioms PottsContinuity.isRCCriticalPoint_unique
#print axioms PottsContinuity.isPottsInfiniteVolumeLimit_unique
#print axioms PottsContinuity.isPottsCriticalPoint_unique
