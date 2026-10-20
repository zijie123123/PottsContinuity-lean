module

public import PottsContinuity.Thm3.RSW.StripEvents
public import PottsContinuity.Thm3.RSW.StripGluing

/-!
# Translated bottom-arc connections for Lemma 2

The events below are exactly the translated bottom-arc connections of the
source proof, and `stripLocalLower` is the positive lower bound used for them.
Lemma 2 itself is proved as `Push.selfDual_stripRSW_of_localConfinedPrefixSelectors`
(`Thm3.Push.PushOfLocalConfinedSelectors`), whose selector hypothesis is discharged
by `PlanarMixed.StripRSWSelectors.roundedLocalConfinedPrefixSelectorExists`.
-/

@[expose] public section

namespace PottsContinuity.RSW

/-- A translate of the source event connecting I to J inside [0,2n] squared. -/
def stripLocalConnection (n s : ℕ) (x : ℤ) : Set (StripConfiguration n) :=
  stripConfinedConnection n
    (stripRectangleVertices n x (x + 2 * n) 0 (2 * n))
    {v | v.1 ∈ Set.Icc (x + 4 * s) (x + 5 * s) ×ˢ ({0} : Set ℤ)}
    {v | v.1 ∈ Set.Icc (x + 6 * s) (x + 7 * s) ×ˢ ({0} : Set ℤ)}

/-- The source translation index ranges from -9k-5 to 9k-6, inclusively. -/
def stripConnectionShift (k s : ℕ) (j : Fin (18 * k)) : ℤ :=
  ((j.val : ℤ) - (9 * (k : ℤ) + 5)) * s

/-- The smaller of the two local-event lower bounds in source Cases 1 and 2. -/
noncomputable def stripLocalLower (q : Set.Ici (1 : ℝ)) (k : ℕ) : ℝ :=
  (1 / (36 * (k : ℝ))) ^ 2 / (18 * (1 + (q : ℝ) ^ 2))

/-- The local connection bound is strictly positive at every positive aspect. -/
theorem stripLocalLower_pos (q : Set.Ici (1 : ℝ)) (k : ℕ) (hk : 1 ≤ k) :
    0 < stripLocalLower q k := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  exact div_pos (sq_pos_of_pos (div_pos one_pos (mul_pos (by norm_num) hk')))
    (mul_pos (by norm_num) (by positivity))

end PottsContinuity.RSW
