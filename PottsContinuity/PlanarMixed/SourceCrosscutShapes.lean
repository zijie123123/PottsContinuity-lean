module

public import PottsContinuity.PlanarMixed.HorizontalCrosscutGeometry
public import PottsContinuity.PlanarMixed.VerticalCrosscutGeometry

@[expose] public section

namespace PottsContinuity.PlanarMixed
open PD.FK BD12
noncomputable section

/-- Bundle the given vertical paths from their disjoint horizontal bands. -/
def verticalCrosscutData_of_separated_traces
    (a : LatticeVertex) (N : ℕ) (C : Configuration (rectangleGraph a N N))
    {u v s t : RectangleVertex a N N}
    (p : (openGraph (rectangleGraph a N N) C).Walk u v)
    (q : (openGraph (rectangleGraph a N N) C).Walk s t)
    (hu : u.val.2 = a.2) (hs : s.val.2 = a.2)
    (hv : v.val.2 = a.2 + (N : ℤ)) (ht : t.val.2 = a.2 + (N : ℤ))
    (b c : ℤ) (hbc : b < c)
    (hp : ∀ z ∈ p.support, z.val.1 ≤ b)
    (hq : ∀ z ∈ q.support, c ≤ z.val.1) : VerticalSquareCrosscutData a N where
  state := C
  firstStart := u
  secondStart := s
  firstEnd := v
  secondEnd := t
  first := p
  second := q
  first_bottom := by dsimp; omega
  second_bottom := by dsimp; omega
  first_top := by dsimp; omega
  second_top := by dsimp; omega
  ordered := by
    have := hp u p.start_mem_support
    have := hq s q.start_mem_support
    dsimp
    omega
  disjoint := by
    intro z hz hz'
    have := hp z hz
    have := hq z hz'
    omega

/-- The three integer-labelled reference squares of source Lemma 4. -/
def lemma4CrosscutSquareBase (n : ℕ) (j : Fin 3) : LatticeVertex :=
  ((10*(j:ℤ)-13)*(n:ℤ), -3*(n:ℤ))

/-- Source Theorem 4's left and right strip paths, clipped to R*, supply an
admissible concrete pair solely from their original coordinate bounds. -/
def generalCCrosscutData
    (m : ℕ)
    (C : Configuration (rectangleGraph (-(5*(m:ℤ)),-(12*(m:ℤ))) (10*m-1) (10*m-1)))
    {u v s t : RectangleVertex (-(5*(m:ℤ)),-(12*(m:ℤ))) (10*m-1) (10*m-1)}
    (p : (openGraph _ C).Walk u v) (q : (openGraph _ C).Walk s t)
    (hu : u.val.2 = -12*(m:ℤ)) (hs : s.val.2 = -12*(m:ℤ))
    (hv : v.val.2 = -12*(m:ℤ) + (10*m-1 : ℕ))
    (ht : t.val.2 = -12*(m:ℤ) + (10*m-1 : ℕ))
    (hp : ∀ z ∈ p.support, z.val.1 ≤ -(m:ℤ)-1)
    (hq : ∀ z ∈ q.support, (m:ℤ) ≤ z.val.1) :
    VerticalSquareCrosscutData (-(5*(m:ℤ)),-(12*(m:ℤ))) (10*m-1) :=
  verticalCrosscutData_of_separated_traces _ _ C p q hu hs hv ht
    (-(m:ℤ)-1) (m:ℤ) (by omega) hp hq

end
end PottsContinuity.PlanarMixed
