module

public import PottsContinuity.Thm3.RSW.PolygonOuterBox

/-! # Neighboring source annulus polygons share an actual lattice vertex -/

@[expose] public section

namespace PottsContinuity.RSW
open Set

/-- Two genuine annulus polygons of inner radius r and outer radius 2r, with
centers separated horizontally by r, have a common original lattice vertex.
Enclosure, overlap and nonnesting are proved from the actual polygon bounds. -/
theorem adjacent_annulus_polygons_shared_vertex
    {m k : ℕ} (P : FKC.LatticePolygon m) (Q : FKC.LatticePolygon k)
    (c₁ c₂ : ℤ × ℤ) (r : ℕ) (_hr : 1 ≤ r)
    (hx : c₂.1 = c₁.1+(r:ℤ)) (hy : c₂.2 = c₁.2)
    (hPcenter : FKC.latticeEmbed ⟨1,zero_lt_one⟩ c₁ ∈ P.domain ⟨1,zero_lt_one⟩)
    (hQcenter : FKC.latticeEmbed ⟨1,zero_lt_one⟩ c₂ ∈ Q.domain ⟨1,zero_lt_one⟩)
    (hP : ∀ i, (r:ℤ) < max |(P.vertex i).1-c₁.1| |(P.vertex i).2-c₁.2| ∧
      max |(P.vertex i).1-c₁.1| |(P.vertex i).2-c₁.2| ≤ 2*(r:ℤ))
    (hQ : ∀ i, (r:ℤ) < max |(Q.vertex i).1-c₂.1| |(Q.vertex i).2-c₂.2| ∧
      max |(Q.vertex i).1-c₂.1| |(Q.vertex i).2-c₂.2| ≤ 2*(r:ℤ)) :
    ∃ i : ZMod (m+3), ∃ j : ZMod (k+3), P.vertex i = Q.vertex j := by
  classical
  have hPin := latticePolygon_closed_inner_box_subset_domain P c₁ r hPcenter (fun i => (hP i).1)
  have hQin := latticePolygon_closed_inner_box_subset_domain Q c₂ r hQcenter (fun i => (hQ i).1)
  have hPout := latticePolygon_closure_subset_outer_box P c₁ (2*r)
    (fun i => by simpa only [Nat.cast_mul,Nat.cast_ofNat] using (hP i).2)
  have hQout := latticePolygon_closure_subset_outer_box Q c₂ (2*r)
    (fun i => by simpa only [Nat.cast_mul,Nat.cast_ofNat] using (hQ i).2)
  have hleft : FKC.latticeEmbed ⟨1,zero_lt_one⟩ (c₁.1-(r:ℤ),c₁.2) ∈
      P.domain ⟨1,zero_lt_one⟩ := by
    apply hPin
    apply latticeEmbed_mem_complexClosedBox
    change max |(c₁.1-(r:ℤ))-c₁.1| |c₁.2-c₁.2| ≤ (r:ℤ)
    simp only [max_le_iff,abs_le]
    omega
  have hright : FKC.latticeEmbed ⟨1,zero_lt_one⟩ (c₂.1+(r:ℤ),c₂.2) ∈
      Q.domain ⟨1,zero_lt_one⟩ := by
    apply hQin
    apply latticeEmbed_mem_complexClosedBox
    change max |(c₂.1+(r:ℤ))-c₂.1| |c₂.2-c₂.2| ≤ (r:ℤ)
    simp only [max_le_iff,abs_le]
    omega
  have hxR : (c₂.1:ℝ) = (c₁.1:ℝ)+(r:ℝ) := by exact_mod_cast hx
  have hleftRe : (FKC.latticeEmbed ⟨1,zero_lt_one⟩ (c₁.1-(r:ℤ),c₁.2)).re =
      (c₂.1:ℝ)-((2*r:ℕ):ℝ) := by
    simp only [FKC.latticeEmbed_re,one_mul,Int.cast_sub,Int.cast_natCast,Nat.cast_mul,Nat.cast_ofNat]
    linarith only [hxR]
  have hrightRe : (FKC.latticeEmbed ⟨1,zero_lt_one⟩ (c₂.1+(r:ℤ),c₂.2)).re =
      (c₁.1:ℝ)+((2*r:ℕ):ℝ) := by
    simp only [FKC.latticeEmbed_re,one_mul,Int.cast_add,Int.cast_natCast,Nat.cast_mul,Nat.cast_ofNat]
    linarith only [hxR]
  have houtP : ∃ z ∈ P.carrier ⟨1,zero_lt_one⟩, z ∉ closure (Q.domain ⟨1,zero_lt_one⟩) := by
    by_contra hn
    have hsub : P.carrier ⟨1,zero_lt_one⟩ ⊆ closure (Q.domain ⟨1,zero_lt_one⟩) := by
      intro z hz
      by_contra hnot
      exact hn ⟨z,hz,hnot⟩
    have hbound : ∀ i, (-Complex.reLm) (FKC.latticeEmbed ⟨1,zero_lt_one⟩ (P.vertex i)) ≤
        -((c₂.1:ℝ)-((2*r:ℕ):ℝ)) := by
      intro i
      exact neg_le_neg (hQout (hsub (P.vertex_mem_carrier _ i))).1.1
    have ht := latticePolygon_domain_coordinate_lt P ⟨1,zero_lt_one⟩ (-Complex.reLm)
      Complex.continuous_re.neg ((Homeomorph.neg ℝ).isOpenMap.comp Complex.isOpenMap_re)
      (-((c₂.1:ℝ)-((2*r:ℕ):ℝ))) hbound _ hleft
    change -(FKC.latticeEmbed ⟨1,zero_lt_one⟩ (c₁.1-(r:ℤ),c₁.2)).re < _ at ht
    rw [hleftRe] at ht
    exact (lt_irrefl _) ht
  have houtQ : ∃ z ∈ Q.carrier ⟨1,zero_lt_one⟩, z ∉ closure (P.domain ⟨1,zero_lt_one⟩) := by
    by_contra hn
    have hsub : Q.carrier ⟨1,zero_lt_one⟩ ⊆ closure (P.domain ⟨1,zero_lt_one⟩) := by
      intro z hz
      by_contra hnot
      exact hn ⟨z,hz,hnot⟩
    have hbound : ∀ i, Complex.reLm (FKC.latticeEmbed ⟨1,zero_lt_one⟩ (Q.vertex i)) ≤
        (c₁.1:ℝ)+((2*r:ℕ):ℝ) := by
      intro i
      exact (hPout (hsub (Q.vertex_mem_carrier _ i))).1.2
    have ht := latticePolygon_domain_coordinate_lt Q ⟨1,zero_lt_one⟩ Complex.reLm
      Complex.continuous_re Complex.isOpenMap_re ((c₁.1:ℝ)+((2*r:ℕ):ℝ)) hbound _ hright
    change (FKC.latticeEmbed ⟨1,zero_lt_one⟩ (c₂.1+(r:ℤ),c₂.2)).re < _ at ht
    rw [hrightRe] at ht
    exact (lt_irrefl _) ht
  have hoverlap : (P.domain ⟨1,zero_lt_one⟩ ∩ Q.domain ⟨1,zero_lt_one⟩).Nonempty := by
    refine ⟨FKC.latticeEmbed ⟨1,zero_lt_one⟩ c₁,hPcenter,?_⟩
    apply hQin
    apply latticeEmbed_mem_complexClosedBox
    simp only [max_le_iff,abs_le]
    omega
  exact latticePolygon_shared_vertex_of_overlapNonnesting P Q ⟨1,zero_lt_one⟩ hoverlap houtP houtQ

end PottsContinuity.RSW
