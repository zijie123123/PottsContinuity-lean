module

public import PottsContinuity.Thm3.RSW.StripFiniteSupportPositive
public import PottsContinuity.PlanarTopology.HorizontalWalks

/-! # Strict positivity of actual finite strip rectangle crossings -/

@[expose] public section

namespace PottsContinuity.RSW
open MeasureTheory PD.FK

/-- The all-open strip state has exactly the original induced lattice graph. -/
theorem stripOpenGraph_allOpen (n : ℕ) :
    stripOpenGraph n (fun _ => true) = stripGraph n := by
  unfold stripOpenGraph
  have h : {e | ∃ h : e ∈ (stripGraph n).edgeSet,
      (fun _ : (stripGraph n).edgeSet => true) ⟨e,h⟩ = true} =
      (stripGraph n).edgeSet := by ext; simp only [Set.mem_ofPred_eq,exists_prop,and_true]
  rw [h,SimpleGraph.fromEdgeSet_edgeSet]

/-- A literal horizontal row is a confined actual crossing in the all-open
state. This includes width zero and scale zero. -/
theorem stripHorizontalCrossing_nonempty (n : ℕ) (a b : ℤ) (hab : a ≤ b) :
    (stripHorizontalCrossing n a b 0 ((2*n:ℕ):ℤ)).Nonempty := by
  obtain ⟨p,hp⟩ := PlanarTopology.horizontal_walk_between a b 0
  have hstrip : ∀ z ∈ p.support, z ∈ stripVertices n := by
    intro z hz
    have h := hp z hz
    change -(n:ℤ) ≤ z.2 ∧ z.2 ≤ 3*(n:ℤ)
    omega
  let q := p.induce (stripVertices n) hstrip
  have hsupport : ∀ v ∈ q.support, v.val ∈ p.support := by
    intro v hv
    have hmap := congrArg SimpleGraph.Walk.support (p.map_induce hstrip)
    rw [SimpleGraph.Walk.support_map] at hmap
    have hvmap : v.val ∈ (p.induce (stripVertices n) hstrip).support.map
        (SimpleGraph.Embedding.induce (G := PD.FK.squareLattice) (stripVertices n)).toHom :=
      List.mem_map.mpr ⟨v,hv,rfl⟩
    exact hmap ▸ hvmap
  refine ⟨(fun _ => true),?_⟩
  change ∃ x y : stripVertices n, ∃ w : (stripOpenGraph n (fun _ => true)).Walk x y,
    x.val ∈ ({a} : Set ℤ) ×ˢ Set.Icc 0 ((2*n:ℕ):ℤ) ∧
    y.val ∈ ({b} : Set ℤ) ×ˢ Set.Icc 0 ((2*n:ℕ):ℤ) ∧
    ∀ v ∈ w.support, v.val ∈ Set.Icc a b ×ˢ Set.Icc 0 ((2*n:ℕ):ℤ)
  rw [stripOpenGraph_allOpen]
  refine ⟨_,_,q,?_,?_,?_⟩
  · simp only [Set.mem_prod,Set.mem_singleton_iff,Set.mem_Icc]
    exact ⟨trivial,by omega,by omega⟩
  · simp only [Set.mem_prod,Set.mem_singleton_iff,Set.mem_Icc]
    exact ⟨trivial,by omega,by omega⟩
  · intro v hv
    have h := hp v.val (hsupport v hv)
    simp only [min_eq_left hab,max_eq_right hab] at h
    exact ⟨⟨h.1,h.2.1⟩,by omega,by omega⟩

/-- Every ordered horizontal rectangle crossing has strictly positive
probability in every genuine top-wired strip limit at interior parameters. -/
theorem stripHorizontalCrossing_probability_pos
    (θ : Parameters) (n : ℕ)
    (μ : Measure (StripConfiguration n)) (hμ : IsTopWiredStripLimit θ n 0 μ)
    (a b : ℤ) (hab : a ≤ b) :
    0 < μ.real (stripHorizontalCrossing n a b 0 ((2*n:ℕ):ℤ)) := by
  have hne := stripHorizontalCrossing_nonempty n a b hab
  rw [stripHorizontalCrossing_eq_confined] at hne ⊢
  exact strip_finiteSupport_event_pos θ n μ hμ _ _
    (stripConfinedConnection_mem_iff_of_agree n _ _ _)
    (stripConfinedConnection_isUpperSet n _ _ _) hne

/-- Strict positivity at each individual scale in the constructed self-dual
strip law. This is not a uniform RSW bound. -/
theorem selfDualStripHorizontalProbability_pos
    (q : Set.Ici (1:ℝ)) (k : ℝ) (hk : 0 ≤ k) (n : ℕ) :
    0 < selfDualStripHorizontalProbability q k n := by
  have hf : 0 ≤ ⌊k*(n:ℝ)⌋ := Int.floor_nonneg.mpr (mul_nonneg hk (Nat.cast_nonneg n))
  exact stripHorizontalCrossing_probability_pos (selfDualParameters q) n
    (selfDualStripMeasure q n) (selfDualStripMeasure_isLimit q n)
    _ _ (by omega)

end PottsContinuity.RSW
