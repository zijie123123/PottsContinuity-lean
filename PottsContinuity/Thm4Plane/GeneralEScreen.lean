module

public import PottsContinuity.Thm4.SlitCenterLowerBound
public import PottsContinuity.FKC.FiniteFK.SlitBoxFirstHitPathGeometry
public import PottsContinuity.FKC.FiniteFK.SlitBoxBottomCenter
public import PottsContinuity.Thm4Plane.SlitScreenEvent

@[expose] public section

open MeasureTheory

namespace PottsContinuity.Thm4Plane

open PottsContinuity.PD.FK
open PottsContinuity.FKC.FiniteFK

noncomputable section

/-- The radius of the source's inner screen in the slit box `C_n`, using the
integer floor convention for the distance `n/16`. -/
def generalEScreenRadius (n : ℕ) : ℤ := ((n / 16 : ℕ) : ℤ)

/-- The source event `E` on the full slit-box carrier `C_n`: the actual open
cluster of the bottom-center vertex reaches the lattice boundary at distance
`floor(n/16)` in the translated `ℓ∞` metric. -/
def generalEScreenEvent (n : ℕ) :
    Set (PottsContinuity.FKC.FiniteFK.Configuration (slitBoxGraph n)) :=
  {A | ∃ v : SlitBoxVertex n,
    max |v.val.1| |v.val.2 + (n : ℤ)| = generalEScreenRadius n ∧
      PottsContinuity.FKC.FiniteFK.ActualConnected
        (slitBoxGraph n) A (slitBoxBottomCenterVertex n) v}

/-- On the cofinal scales used by the three-crossing construction, this
all-scale event is definitionally the existing screen event. -/
theorem generalEScreenEvent_sixteen_eq (m : ℕ) :
    generalEScreenEvent (16 * m) = slitScreenEvent m := by
  have hr : generalEScreenRadius (16 * m) = (m : ℤ) := by
    dsimp [generalEScreenRadius]
    norm_cast
    omega
  have hscale : ((16 * m : ℕ) : ℤ) = 16 * (m : ℤ) := by norm_cast
  ext A
  constructor
  · rintro ⟨v, hv, hconn⟩
    exact ⟨v, by simpa only [hr, hscale] using hv, hconn⟩
  · rintro ⟨v, hv, hconn⟩
    exact ⟨v, by simpa only [hr, hscale] using hv, hconn⟩

end
end PottsContinuity.Thm4Plane
