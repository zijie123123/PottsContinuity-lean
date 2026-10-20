module

public import PottsContinuity.PlanarMixed.Lemma4Connectors.ConfinementProduct
public import PottsContinuity.PlanarTopology.SubpathExtraction

@[expose] public section

namespace PottsContinuity.PlanarMixed.Lemma4Connectors
open PD.FK RSW PlanarTopology
noncomputable section

/-- A literal horizontal primal crossing inside the full between-trace region. -/
def primalWindowCrossing (V : Finset (ℤ × ℤ))
    (Ω : Set (V : Set (ℤ × ℤ))) (l r b t : ℤ) :
    Set (Configuration (squareLattice.induce (V : Set (ℤ × ℤ)))) :=
  {A | ∃ x y, ∃ p : (openGraph (squareLattice.induce (V : Set (ℤ × ℤ))) A).Walk x y,
    x.val.1 = l ∧ y.val.1 = r ∧
    ∀ z ∈ p.support, z ∈ Ω ∧ l ≤ z.val.1 ∧ z.val.1 ≤ r ∧ b < z.val.2 ∧ z.val.2 < t}

def primalWindowNoncrossing (V : Finset (ℤ × ℤ))
    (Ω : Set (V : Set (ℤ × ℤ))) (l r b t : ℤ) :
    Set (Configuration (squareLattice.induce (V : Set (ℤ × ℤ)))) :=
  (primalWindowCrossing V Ω l r b t)ᶜ

theorem primalWindowCrossing_isUpperSet (V : Finset (ℤ × ℤ))
    (Ω : Set (V : Set (ℤ × ℤ))) (l r b t : ℤ) :
    IsUpperSet (primalWindowCrossing V Ω l r b t) := by
  rintro A B hAB ⟨x,y,p,hx,hy,hp⟩
  refine ⟨x,y,p.mapLe (openGraph_mono hAB),hx,hy,?_⟩
  intro z hz
  rw [SimpleGraph.Walk.support_mapLe_eq_support] at hz
  exact hp z hz

theorem primalWindowNoncrossing_isLowerSet (V : Finset (ℤ × ℤ))
    (Ω : Set (V : Set (ℤ × ℤ))) (l r b t : ℤ) :
    IsLowerSet (primalWindowNoncrossing V Ω l r b t) :=
  (primalWindowCrossing_isUpperSet V Ω l r b t).compl

/-- Every original component vertex of an actual path remains accessible
from its start, so the same region constraint passes to extracted subwalks. -/
theorem primal_window_crossing_of_component_span
    (V : Finset (ℤ × ℤ)) (Ω : Set (V : Set (ℤ × ℤ)))
    (A : Configuration (squareLattice.induce (V : Set (ℤ × ℤ))))
    (l r b t : ℤ) (hlr : l ≤ r) {u w : (V : Set (ℤ × ℤ))}
    (huw : ActualConnected _ A u w)
    (hu : u.val.1 ≤ l) (hw : r ≤ w.val.1)
    (hregion : ∀ z, ActualConnected _ A u z → z ∈ Ω ∧ b < z.val.2 ∧ z.val.2 < t) :
    A ∈ primalWindowCrossing V Ω l r b t := by
  obtain ⟨p⟩ := huw
  have hstep : ∀ x y, (openGraph (squareLattice.induce (V : Set (ℤ × ℤ))) A).Adj x y →
      |x.val.1-y.val.1| ≤ 1 := by
    intro x y hxy
    have h := openGraph_le _ A hxy
    change |x.val.1-y.val.1|+|x.val.2-y.val.2|=1 at h
    have := abs_nonneg (x.val.2-y.val.2)
    omega
  obtain ⟨x,y,q,hsub,hx,hy,hq⟩ := walk_subwalk_between_levels
    (fun z : (V : Set (ℤ × ℤ)) => z.val.1) hstep p hlr hu hw
  refine ⟨x,y,q,hx,hy,?_⟩
  intro z hz
  have hz' := hsub.support_subset hz
  have hconn : ActualConnected _ A u z := ⟨p.takeUntil z hz'⟩
  have h := hregion z hconn
  exact ⟨h.1,(hq z hz).1,(hq z hz).2,h.2⟩

/-- Two corrected noncrossing windows trap a whole core once the closed
original traces keep its component inside the full horizontal strip. -/
theorem fullCoreConfined_of_strip_and_two_noncrossings
    (V : Finset (ℤ × ℤ)) (Ω : Set (V : Set (ℤ × ℤ)))
    (A : Configuration (squareLattice.induce (V : Set (ℤ × ℤ))))
    (z : ℤ × ℤ) (n : ℕ) (l₁ r₁ l₂ r₂ b t : ℤ)
    (h₁ : l₁ ≤ r₁) (h₂ : l₂ ≤ r₂)
    (hcore : ∀ u ∈ vertexBoxRegion V z (2*n), r₁ ≤ u.val.1 ∧ u.val.1 ≤ l₂)
    (hstrip : ∀ u ∈ vertexBoxRegion V z (2*n), ∀ w,
      ActualConnected _ A u w → w ∈ Ω ∧ b < w.val.2 ∧ w.val.2 < t)
    (hleft : A ∈ primalWindowNoncrossing V Ω l₁ r₁ b t)
    (hright : A ∈ primalWindowNoncrossing V Ω l₂ r₂ b t) :
    A ∈ fullCoreConfined V {w | l₁ < w.val.1 ∧ w.val.1 < r₂ ∧ b < w.val.2 ∧ w.val.2 < t} z n := by
  intro u hu w huw
  have hsw := hstrip u hu w huw
  refine ⟨?_,?_,hsw.2⟩
  · by_contra hn
    apply hleft
    apply primal_window_crossing_of_component_span V Ω A l₁ r₁ b t h₁ huw.symm
      (by omega) (hcore u hu).1
    intro v hv
    exact hstrip u hu v (huw.trans hv)
  · by_contra hn
    exact hright (primal_window_crossing_of_component_span V Ω A l₂ r₂ b t h₂ huw
      (hcore u hu).2 (by omega) (hstrip u hu))

end
end PottsContinuity.PlanarMixed.Lemma4Connectors
