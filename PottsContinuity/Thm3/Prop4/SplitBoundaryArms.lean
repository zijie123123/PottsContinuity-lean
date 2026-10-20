module

public import PottsContinuity.Thm3.Prop4.VertexStarArms

/-!
# Corrected square-boundary arms after splitting at z

These are actual connections in one modified configuration, at square radii
whose sum is exactly 2n-2. The wider Euclidean tube supplies both cutoffs.
No dual-screen or separation premise is built into the arm events.
-/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4

noncomputable section

local instance splitBoundaryEdgeDecidableEq (n : ℕ) :
    DecidableEq (squareLattice.induce (box n : Set (ℤ × ℤ))).edgeSet := Classical.decEq _

/-- Any actual connection reaching square radius at least r hits the frozen boundary. -/
theorem finiteEndpointArm_of_square_radius (n r : ℕ)
    (A : PD.FK.Configuration (squareLattice.induce (box n : Set (ℤ × ℤ))))
    (a z : (box n : Set (ℤ × ℤ)))
    (hz : (r : ℤ) ≤ max |z.val.1-a.val.1| |z.val.2-a.val.2|)
    (hconn : PD.FK.ActualConnected _ A a z) : A ∈ finiteEndpointArmEvent n a r := by
  obtain ⟨w⟩ := hconn
  let S : Set (box n : Set (ℤ × ℤ)) :=
    {x | max |x.val.1-a.val.1| |x.val.2-a.val.2| ≤ (r : ℤ)}
  have hstart : a ∈ S := by simp [S]
  by_cases hzin : z ∈ S
  · refine ⟨z,?_,⟨w⟩⟩
    rw [Foundations.vertexBoundary_box_eq]
    exact le_antisymm hzin hz
  · obtain ⟨d,hd,hdin,hdout⟩ := w.exists_boundary_dart S hstart hzin
    have hsq := PD.FK.openGraph_le _ A d.adj
    change |d.fst.val.1-d.snd.val.1|+|d.fst.val.2-d.snd.val.2|=1 at hsq
    have hin : max |d.fst.val.1-a.val.1| |d.fst.val.2-a.val.2| ≤ (r : ℤ) := hdin
    have hout : ¬max |d.snd.val.1-a.val.1| |d.snd.val.2-a.val.2| ≤ (r : ℤ) := hdout
    refine ⟨d.fst,?_,⟨w.takeUntil d.fst (w.dart_fst_mem_support_of_mem_darts hd)⟩⟩
    rw [Foundations.vertexBoundary_box_eq]
    change max |d.fst.val.1-a.val.1| |d.fst.val.2-a.val.2| = (r : ℤ)
    simp only [abs_eq_max_neg] at hin hout hsq ⊢
    omega

/-- Retain the cutoff on each arm while reducing their total to the desired convolution index. -/
theorem exists_arm_radii_with_sum (K L T s : ℕ) (hsK : s ≤ K) (hsL : s ≤ L)
    (hsT : 2*s ≤ T) (hKL : T ≤ K+L) :
    ∃ k l : ℕ, k+l=T ∧ s ≤ k ∧ s ≤ l ∧ k ≤ K ∧ l ≤ L := by
  by_cases hK : K ≤ T-s
  · exact ⟨K,T-K,by omega,hsK,by omega,le_rfl,by omega⟩
  · exact ⟨T-s,s,by omega,by omega,le_rfl,by omega,hsL⟩

/-- Neighbours of one splitting vertex retain a total horizontal displacement of 2n-2. -/
theorem split_neighbour_radius_sum (n : ℕ) (a b z p q : ℤ × ℤ)
    (ha : a.1 = -(n : ℤ)) (hb : b.1 = (n : ℤ))
    (hzp : squareLattice.Adj z p) (hzq : squareLattice.Adj z q) :
    (2*n : ℤ)-2 ≤ max |p.1-a.1| |p.2-a.2| + max |q.1-b.1| |q.2-b.2| := by
  change |z.1-p.1|+|z.2-p.2|=1 at hzp
  change |z.1-q.1|+|z.2-q.2|=1 at hzq
  have hp := le_max_left |p.1-a.1| |p.2-a.2|
  have hq := le_max_left |q.1-b.1| |q.2-b.2|
  have hp₀ := abs_nonneg (z.2-p.2)
  have hq₀ := abs_nonneg (z.2-q.2)
  have hp₁ := le_abs_self (z.1-p.1)
  have hp₂ := le_abs_self (p.1-a.1)
  have hq₁ := neg_le_abs (z.1-q.1)
  have hq₂ := neg_le_abs (q.1-b.1)
  omega

/-- Exact convolution-scale primal arms after star closing, with the corrected tube margin. -/
theorem split_star_surviving_boundary_arms_realCutoff (n s : ℕ) (r : ℝ)
    (hn : 1 ≤ n) (hr : 1 ≤ r) (hsr : (s : ℝ)-1 < r)
    (hsn : 2*s ≤ 2*n-2)
    (A : PD.FK.Configuration (squareLattice.induce (box n : Set (ℤ × ℤ))))
    (a b z : (box n : Set (ℤ × ℤ)))
    (ha : a.val.1 = -(n : ℤ)) (hb : b.val.1 = (n : ℤ))
    (hfar : 4*r ≤ tubeDistance a.val b.val z.val)
    (haz : PD.FK.ActualConnected _ A a z) (hbz : PD.FK.ActualConnected _ A b z) :
    ∃ k l : ℕ, k+l=2*n-2 ∧ s ≤ k ∧ s ≤ l ∧
      (A \ vertexStarEdges (squareLattice.induce (box n : Set (ℤ × ℤ))) z) ∈
        finiteEndpointArmEvent n a k ∧
      (A \ vertexStarEdges (squareLattice.induce (box n : Set (ℤ × ℤ))) z) ∈
        finiteEndpointArmEvent n b l := by
  have ha_ne : a ≠ z := by
    intro heq
    have hdist := tubeDistance_le_twice_endpoint_radius a.val b.val z.val
    rw [heq] at hfar
    rw [heq] at hdist
    simp only [sub_self,abs_zero,max_self,Int.cast_zero,mul_zero] at hdist
    linarith only [hdist,hfar,hr]
  have hb_ne : b ≠ z := by
    intro heq
    have hdist := tubeDistance_le_twice_endpoint_radius b.val a.val z.val
    have hsymm : tubeDistance b.val a.val z.val = tubeDistance a.val b.val z.val := by
      unfold tubeDistance
      rw [segment_symm]
    rw [hsymm,heq] at hdist
    rw [heq] at hfar
    simp only [sub_self,abs_zero,max_self,Int.cast_zero,mul_zero] at hdist
    linarith only [hdist,hfar,hr]
  obtain ⟨p,q,hzp,hzq,hap,hbq⟩ := connected_two_neighbours_after_star_closing
    (squareLattice.induce (box n : Set (ℤ × ℤ))) A z a b ha_ne hb_ne haz hbz
  let K : ℤ := max |p.val.1-a.val.1| |p.val.2-a.val.2|
  let L : ℤ := max |q.val.1-b.val.1| |q.val.2-b.val.2|
  have hK : 0 ≤ K := le_trans (abs_nonneg _) (le_max_left _ _)
  have hL : 0 ≤ L := le_trans (abs_nonneg _) (le_max_left _ _)
  have hKs : (s : ℤ) ≤ K := by
    have h := splitRadius_neighbour_cutoff_of_widenedTube a.val b.val z.val p.val
      r hr hfar hzp
    have hlt : (s : ℤ)-1 < K := by exact_mod_cast (hsr.trans_le h)
    omega
  have hLs : (s : ℤ) ≤ L := by
    have hfar' : 4*r ≤ tubeDistance b.val a.val z.val := by
      simpa only [tubeDistance,segment_symm] using hfar
    have h := splitRadius_neighbour_cutoff_of_widenedTube b.val a.val z.val q.val
      r hr hfar' hzq
    have hlt : (s : ℤ)-1 < L := by exact_mod_cast (hsr.trans_le h)
    omega
  have hsum := split_neighbour_radius_sum n a.val b.val z.val p.val q.val ha hb hzp hzq
  have hKN : (K.toNat : ℤ) = K := Int.toNat_of_nonneg hK
  have hLN : (L.toNat : ℤ) = L := Int.toNat_of_nonneg hL
  have hsKN : s ≤ K.toNat := by omega
  have hsLN : s ≤ L.toNat := by omega
  have hsumN : 2*n-2 ≤ K.toNat+L.toNat := by omega
  obtain ⟨k,l,hkl,hsk,hsl,hk,hl⟩ :=
    exists_arm_radii_with_sum K.toNat L.toNat (2*n-2) s hsKN hsLN hsn hsumN
  refine ⟨k,l,hkl,hsk,hsl,?_,?_⟩
  · exact finiteEndpointArm_of_square_radius n k _ a p (by omega) hap
  · exact finiteEndpointArm_of_square_radius n l _ b q (by omega) hbq

end
end PottsContinuity.Thm3.Prop4
