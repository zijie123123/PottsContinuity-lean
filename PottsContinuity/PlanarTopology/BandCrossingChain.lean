module

public import PottsContinuity.PlanarTopology.BandCrossingGluing
public import Mathlib.Tactic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Combinatorics.SimpleGraph.Walk.Basic
public import Mathlib.Data.Int.Star

@[expose] public section

namespace PottsContinuity.PlanarTopology
open PD.FK BD12
noncomputable section

/-- General overlap chain: the horizontal span and its translation step need not agree. -/
theorem kst_band_horizontal_chain_width (stages : ℕ) (hstages : 1 ≤ stages)
    (base step width bottom top : ℤ) (hstep : 0 ≤ step) (hwidth : step ≤ width) (hbt : bottom ≤ top)
    (ω : LatticeConfiguration)
    (hH : ∀ i : ℕ, i < stages → ∃ u v, ∃ p : PD.squareLattice.Walk u v,
      kstPathOpen ω p ∧ u.1 = base+(i : ℤ)*step ∧ v.1 = base+(i : ℤ)*step+width ∧
      ∀ z ∈ p.support, bottom ≤ z.2 ∧ z.2 ≤ top)
    (hV : ∀ i : ℕ, i+1 < stages → ∃ u v, ∃ p : PD.squareLattice.Walk u v,
      kstPathOpen ω p ∧ u.2 = bottom ∧ v.2 = top ∧
      kstPathIn p (base+((i : ℤ)+1)*step) (base+(i : ℤ)*step+width) bottom top) :
    ∃ u v, ∃ p : PD.squareLattice.Walk u v,
      kstPathOpen ω p ∧ u.1 = base ∧ v.1 = base+((stages : ℤ)-1)*step+width ∧
      ∀ z ∈ p.support, bottom ≤ z.2 ∧ z.2 ≤ top := by
  induction stages with
  | zero => omega
  | succ k ih =>
    by_cases hk : k = 0
    · subst k
      obtain ⟨u,v,p,hp,hu,hv,hband⟩ := hH 0 (by omega)
      refine ⟨u,v,p,hp,?_,?_,hband⟩
      · simpa using hu
      · simpa using hv
    · obtain ⟨u,v,p,hp,hu,hv,hband⟩ := ih (by omega)
        (fun i hi => hH i (by omega)) (fun i hi => hV i (by omega))
      obtain ⟨x,y,q,hq,hx,hy,hbandq⟩ := hH k (by omega)
      obtain ⟨a,b,V,hVO,ha,hb,hVB⟩ := hV (k-1) (by omega)
      have hkcast : ((k-1 : ℕ) : ℤ) = (k : ℤ)-1 := by omega
      have hVB' : kstPathIn V (base+(k : ℤ)*step) (base+((k : ℤ)-1)*step+width) bottom top := by
        intro z hz
        have hh := hVB z hz
        rw [hkcast] at hh
        exact ⟨by nlinarith [hh.1],by nlinarith [hh.2.1],hh.2.2⟩
      obtain ⟨W,hWO,hWB⟩ := kst_band_walks_glue
        (base+(k : ℤ)*step) (base+((k : ℤ)-1)*step+width) bottom top
        (by nlinarith) hbt ω p q V hp hq hVO
        (by rw [hu]; nlinarith [mul_nonneg (Int.natCast_nonneg k) hstep])
        (by rw [hv]) (by rw [hx]) (by rw [hy]; nlinarith)
        hband hbandq hVB' ha hb
      refine ⟨u,y,W,hWO,hu,?_,hWB⟩
      push_cast
      nlinarith [hy]


end
end PottsContinuity.PlanarTopology
