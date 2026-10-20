module

public import PottsContinuity.Thm3.Push.CaseTwoPrecursorFirstHitSelector
public import PottsContinuity.Thm3.Push.CaseTwoTipFirstHitSelector
public import PottsContinuity.Thm3.Push.FirstContactTrace

@[expose] public section

namespace PottsContinuity.Push
open PD.FK PlanarMixed.FiniteSlit
noncomputable section

/-- The stored tip trace in its exact original source-square coordinates. -/
def caseTwoTipOriginalTrace (n s : ℕ) (hfit : 9*s ≤ 2*n)
    (tip : SideCollarFirstHitRecord (5*s) (2*n)) : List (RectangleVertex (0,0) (2*n) (2*n)) :=
  tip.2.map (sourceBandEmbedding (2*n) (4*s) (5*s) (2*n) (by omega) le_rfl)

/-- The stored full precursor trace in its exact original coordinates. -/
def caseTwoPrecursorOriginalTrace (n s : ℕ) (hfit : 9*s ≤ 2*n)
    (precursor : SideCollarFirstHitRecord (9*s) (2*n)) : List (RectangleVertex (0,0) (2*n) (2*n)) :=
  precursor.2.map (reflectedSourceBandEmbedding (2*n) 0 (9*s) (2*n) (by omega) le_rfl)

/-- Crop the precursor at the first visit to the source ray left of the tip.
None means an empty tip trace or a precursor with no such ray contact. -/
def caseTwoTraceCrop (n s : ℕ) (hfit : 9*s ≤ 2*n)
    (tip : SideCollarFirstHitRecord (5*s) (2*n))
    (precursor : SideCollarFirstHitRecord (9*s) (2*n)) :
    Option (List (RectangleVertex (0,0) (2*n) (2*n))) :=
  (caseTwoTipOriginalTrace n s hfit tip).getLast?.bind fun v =>
    firstContactTrace {z | z.val.1 = 4*(s:ℤ)-1 ∧ v.val.2 ≤ z.val.2}
      (caseTwoPrecursorOriginalTrace n s hfit precursor)

/-- On decoded actual walks the computed statistic is exactly the source's
first-contact prefix, including the original first-contact vertex. -/
theorem caseTwoTraceCrop_eq_of_decoded_firstContact
    (n s : ℕ) (hfit : 9*s ≤ 2*n)
    (C : Configuration (rectangleGraph (0,0) (2*n) (2*n)))
    (tip : SideCollarFirstHitRecord (5*s) (2*n))
    (precursor : SideCollarFirstHitRecord (9*s) (2*n))
    {a b u v : RectangleVertex (0,0) (2*n) (2*n)}
    (p : (openGraph (rectangleGraph (0,0) (2*n) (2*n)) C).Walk a u)
    (q : (openGraph (rectangleGraph (0,0) (2*n) (2*n)) C).Walk b v)
    (hp : p.support = caseTwoPrecursorOriginalTrace n s hfit precursor)
    (hq : q.support = caseTwoTipOriginalTrace n s hfit tip)
    (k : ℕ) (hk : IsFirstContact p {z | z.val.1 = 4*(s:ℤ)-1 ∧ v.val.2 ≤ z.val.2} k) :
    caseTwoTraceCrop n s hfit tip precursor = some (p.take k).support := by
  have hend : q.support.getLast? = some v := by
    rw [List.getLast?_eq_some_getLast q.support_ne_nil,SimpleGraph.Walk.getLast_support]
  unfold caseTwoTraceCrop
  rw [← hp,← hq,hend,Option.bind_some]
  exact firstContactTrace_eq_support_take p _ k hk

end
end PottsContinuity.Push
