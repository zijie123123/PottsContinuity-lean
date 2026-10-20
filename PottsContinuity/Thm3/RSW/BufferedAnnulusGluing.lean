module

public import PottsContinuity.Thm3.RSW.AnnulusChainPaths
public import PottsContinuity.Thm3.RSW.SampledAnnulus
public import PottsContinuity.Thm3.RSW.AnnulusChainLocal
public import PottsContinuity.Foundations.BoxBoundary

/-! # The actual sampled annulus chain glues in the exact frozen buffer -/

@[expose] public section

namespace PottsContinuity.RSW

/-- The radius-2m circuit support fits both the sampled ambient domain and the
literal target crossing height band. -/
theorem annulus_chain_outer_box_in_buffer_band
    (α : ℝ) (n m K : ℕ) (hscale : 16*m ≤ n)
    (hspan : (K*m:ℕ) ≤ ⌊α*(n:ℝ)⌋+(m:ℤ))
    (l : ℕ) (hl : l ≤ K) (v : ℤ × ℤ)
    (hv : max |v.1-(annulusChainCenter n m l).1|
      |v.2-(annulusChainCenter n m l).2| ≤ 2*(m:ℤ)) :
    v ∈ latticeRectangle (-(n:ℤ)) ⌊(α+1)*(n:ℝ)⌋ (-(n:ℤ)) (2*(n:ℤ)) ∧
      v.2 ∈ Set.Icc (0:ℤ) n := by
  let z : ℤ × ℤ := (v.1-(annulusChainCenter n m l).1,v.2-(annulusChainCenter n m l).2)
  have hx := (le_max_left _ _).trans hv
  have hy := (le_max_right _ _).trans hv
  have hz₂ : z ∈ box (2*m) := by
    rw [Foundations.mem_box_iff_abs_le]
    simpa only [z,Nat.cast_mul,Nat.cast_ofNat] using And.intro hx hy
  have hz₈ : z ∈ box (8*m) := by
    rw [Foundations.mem_box_iff_abs_le]
    change |v.1-(annulusChainCenter n m l).1| ≤ ((8*m:ℕ):ℤ) ∧
      |v.2-(annulusChainCenter n m l).2| ≤ ((8*m:ℕ):ℤ)
    constructor <;> push_cast <;> omega
  have hV := annulus_chain_window_in_buffer α n m K hscale hspan l hl z hz₈
  have heq : (z.1+(annulusChainCenter n m l).1,z.2+(annulusChainCenter n m l).2) = v := by
    ext <;> dsimp [z] <;> omega
  have hheight := annulus_chain_circuit_height_band n m l hscale z hz₂
  have hyEq : z.2+(annulusChainCenter n m l).2 = v.2 := by dsimp [z]; omega
  exact ⟨heq ▸ hV,hyEq ▸ hheight⟩

/-- Gluing along a buffered annulus chain, with exact floor endpoints, integer
centers, sampled original-edge restrictions, K=0 and zero-width targets
retained. -/
theorem buffered_annulus_chain_glues
    (α : ℝ) (hα : 0 < α) (n m K : ℕ) (_hn : 32 ≤ n) (hm : 1 ≤ m)
    (hscale : 16*m ≤ n) (hspan : (K*m:ℕ) ≤ ⌊α*(n:ℝ)⌋+(m:ℤ))
    (hcover : ⌊α*(n:ℝ)⌋ ≤ (K*m:ℕ))
    (ω : (squareLattice.induce
      (latticeRectangle (-(n:ℤ)) ⌊(α+1)*(n:ℝ)⌋ (-(n:ℤ)) (2*(n:ℤ)) :
        Set (ℤ × ℤ))).edgeSet → Bool)
    (hcircuits : ∀ l : Fin (K+1),
      ω ∈ bufferedAnnulusChainLocalEvent α n m K hscale hspan l) :
    horizontalCrossing
      (latticeRectangle (-(n:ℤ)) ⌊(α+1)*(n:ℝ)⌋ (-(n:ℤ)) (2*(n:ℤ)))
      0 ⌊α*(n:ℝ)⌋ 0 n ω := by
  classical
  let V := latticeRectangle (-(n:ℤ)) ⌊(α+1)*(n:ℝ)⌋ (-(n:ℤ)) (2*(n:ℤ))
  let S := V.filter (fun v => v.2 ∈ Set.Icc (0:ℤ) n)
  have hstep : ∀ l < K, (annulusChainCenter n m (l+1)).1 =
      (annulusChainCenter n m l).1+(m:ℤ) ∧
      (annulusChainCenter n m (l+1)).2 = (annulusChainCenter n m l).2 := by
    intro l hl
    constructor
    · simp [annulusChainCenter,Nat.add_mul,Nat.cast_add]
    · rfl
  have hactual : ∀ l ≤ K, ω ∈ annulusCircuitEvent V (annulusChainCenter n m l) m := by
    intro l hl
    exact translatedAnnulusEvent_subset_actualAnnulus V m (annulusChainCenter n m l)
      (fun z hz => annulus_chain_window_in_buffer α n m K hscale hspan l hl z hz)
      (hcircuits ⟨l,by omega⟩)
  have hS : ∀ l ≤ K, ∀ v : ℤ × ℤ,
      max |v.1-(annulusChainCenter n m l).1| |v.2-(annulusChainCenter n m l).2| ≤ 2*(m:ℤ) →
        v ∈ S := by
    intro l hl v hv
    exact Finset.mem_filter.mpr (annulus_chain_outer_box_in_buffer_band α n m K hscale hspan l hl v hv)
  obtain ⟨x,y,hx,hy,hpath⟩ := annulus_chain_spanning_path V S ω m hm
    (annulusChainCenter n m) K hstep hactual hS
  have hA : (0:ℤ) ≤ ⌊α*(n:ℝ)⌋ := Int.floor_nonneg.mpr
    (mul_nonneg hα.le (Nat.cast_nonneg n))
  have hc₀ : (annulusChainCenter n m 0).1 = 0 := by simp [annulusChainCenter]
  have hcK : (annulusChainCenter n m K).1 = (K*m:ℕ) := rfl
  have hx₀ : x.1 ≤ 0 := by rw [hc₀] at hx; omega
  have hyA : ⌊α*(n:ℝ)⌋ ≤ y.1 := by rw [hcK] at hy; omega
  exact finitePathEvent_implies_horizontalCrossing V S x y 0 ⌊α*(n:ℝ)⌋ 0 n hA hx₀ hyA
    (fun z hz => (Finset.mem_filter.mp hz).2) ω hpath

end PottsContinuity.RSW
