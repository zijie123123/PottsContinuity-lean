module

public import PottsContinuity.Thm3.Prop4.ActualTubeCrossing
public import PottsContinuity.Thm3.Prop4.CorridorRectangleContainment
public import PottsContinuity.Thm3.Prop4.OpenCorridorChain
public import PottsContinuity.BD12.RectangleConfinedWalk
public import PottsContinuity.BD12.DualStripOpen

/-!
# The concrete finite crossing event of the sloped corridor

There are 2n+1 horizontal stages and 2n vertical connectors. Their actual
crossings yield an original open path across the tube. All complete
rectangle carriers are retained; no extremal-path law is asserted here.
-/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4

open PD.FK
noncomputable section

/-- Simultaneous actual horizontal stages and vertical overlap connectors. -/
def corridorGoodEvent (n s : ℕ) (hs : s ≤ n) (t b : ℝ) : Set LatticeConfiguration :=
  {ω | (∀ i : ℕ, i < 2*n+1 → ω ∈ BD12.horizontalRectangle
      (corridorAbscissa n s i,corridorCenter n s hs t b i-(s : ℤ)) (2*s) (2*s)) ∧
    (∀ i : ℕ, i < 2*n → ω ∈ BD12.verticalRectangle
      (corridorAbscissa n s (i+1),min (corridorCenter n s hs t b i) (corridorCenter n s hs t b (i+1))-(s : ℤ))
      s (2*s+(corridorCenter n s hs t b (i+1)-corridorCenter n s hs t b i).natAbs))}

private theorem vertical_original_witness (ω : LatticeConfiguration) (a : LatticeVertex) (w h : ℕ)
    (hc : ω ∈ BD12.verticalRectangle a w h) :
    ∃ u v, ∃ p : (PD.rcInfiniteOpenGraph ω).Walk u v,
      u.2 = a.2 ∧ v.2 = a.2+(h : ℤ) ∧ ∀ z ∈ p.support, z ∈ PD.FK.latticeRectangle a w h := by
  obtain ⟨u,v,hu,hv,⟨p⟩⟩ := hc
  let f : (PD.rcInfiniteOpenGraph ω).induce (PD.FK.latticeRectangle a w h : Set LatticeVertex) →g
      PD.rcInfiniteOpenGraph ω := {toFun := Subtype.val,map_rel' := fun hh => hh}
  refine ⟨u.val,v.val,p.map f,hu,hv,?_⟩
  intro z hz
  rw [SimpleGraph.Walk.support_map] at hz
  obtain ⟨x,_,rfl⟩ := List.mem_map.mp hz
  exact x.property

/-- The concrete rectangle event forces a true original-state tube crossing at every source slope. -/
theorem corridorGoodEvent_has_tube_crossing {n : ℕ} (hn : 1 ≤ n)
    (s : ℕ) (hs : s ≤ n) (hspos : 1 ≤ s)
    (u v : LatticeVertex) (huB : u ∈ box n) (hvB : v ∈ box n)
    (ha : u.1 = -(n : ℤ)) (hb : v.1 = (n : ℤ))
    (t b : ℝ) (ht : |t| ≤ 1) (hu : (u.2 : ℝ) = t*(u.1 : ℝ)+b)
    (hv : (v.2 : ℝ) = t*(v.1 : ℝ)+b) (R : ℝ) (hR : 4*(s : ℝ)+1 ≤ R)
    (ω : LatticeConfiguration) (hgood : ω ∈ corridorGoodEvent n s hs t b) :
    ω ∈ tubeHorizontalCrossingEvent n R u v := by
  have hH : ∀ i : Fin (2*n+1), ∃ a c, ∃ p : (PD.rcInfiniteOpenGraph ω).Walk a c,
      a.1 = corridorAbscissa n s i.val ∧ c.1 = corridorAbscissa n s i.val+2*(s : ℤ) ∧
      ∀ z ∈ p.support, z ∈ corridorHorizontalVertices n s hs t b i.val := by
    intro i
    simpa only [corridorHorizontalVertices,Prod.fst,Nat.cast_mul,Nat.cast_ofNat] using
      (BD12.horizontalRectangle_iff_confined_open_walk _ _ _ ω).mp (hgood.1 i.val i.isLt)
  choose a c p hleft hright hP using hH
  obtain ⟨W,hW⟩ := original_open_corridor_chain ω (radiusTube n R u v : Set LatticeVertex)
    (2*n+1) (by omega) s (corridorAbscissa n s) (corridorCenter n s hs t b) a c p hleft hright
    (by
      intro i z hz
      have hh := hP i z hz
      rw [corridorHorizontalVertices,PD.FK.mem_latticeRectangle] at hh
      simp only [Nat.cast_mul,Nat.cast_ofNat] at hh
      exact ⟨by omega,by omega⟩)
    (by
      intro i z hz
      exact corridorHorizontalVertices_subset_radiusTube hn s hs u v huB hvB ha hb t b ht hu hv R hR i.val (hP i z hz))
    (fun i _ => corridorAbscissa_step n s i) (by
      intro i hi
      obtain ⟨x,y,V,hx,hy,hV⟩ := vertical_original_witness ω _ _ _ (hgood.2 i (by omega))
      have he : min (corridorCenter n s hs t b i) (corridorCenter n s hs t b (i+1))-(s : ℤ) +
          ((2*s+(corridorCenter n s hs t b (i+1)-corridorCenter n s hs t b i).natAbs : ℕ) : ℤ) =
          max (corridorCenter n s hs t b i) (corridorCenter n s hs t b (i+1))+(s : ℤ) := by
        simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Int.natCast_natAbs,abs_eq_max_neg]
        omega
      refine ⟨x,y,V,hx,hy.trans he,?_,?_⟩
      · intro z hz
        have hh := hV z hz
        rw [PD.FK.mem_latticeRectangle] at hh
        dsimp only at hh
        rw [he] at hh
        exact ⟨hh.1.1,hh.1.2,hh.2.1,hh.2.2⟩
      · intro z hz
        exact corridorConnectorVertices_subset_radiusTube hn s hs u v huB hvB ha hb t b ht hu hv R hR i (hV z hz))
  have hfirst := hleft ⟨0,by omega⟩
  have hlast := hright ⟨(2*n+1)-1,by omega⟩
  change (a ⟨0,by omega⟩).1 = corridorAbscissa n s 0 at hfirst
  rw [corridorAbscissa_zero n s hs] at hfirst
  have hlast' : (c ⟨(2*n+1)-1,by omega⟩).1 = (n : ℤ) := by
    simpa only [Nat.add_sub_cancel,corridorAbscissa_last n s hs hspos,sub_add_cancel] using hlast
  exact tubeHorizontalCrossingEvent_of_walk n R u v ω W hfirst hlast' hW

end
end PottsContinuity.Thm3.Prop4
