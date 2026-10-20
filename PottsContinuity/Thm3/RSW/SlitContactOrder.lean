module

public import PottsContinuity.Thm3.RSW.FiniteSlitInterior
public import Mathlib.Combinatorics.SimpleGraph.Walk.Subwalks

@[expose] public section

namespace PottsContinuity.RSW
open PD.FK BD12 PlanarMixed.FiniteSlit
noncomputable section

/-- The explicit first-ray approach interface forces every prefix before the
first left-slit contact to avoid the marked ray. No probability is assumed. -/
theorem walk_prefix_avoids_ray_of_rayApproach
    {V : Type*} {G : SimpleGraph V} (X Y : V → ℤ) (x y : ℤ)
    {u v : V} (p : G.Walk u v) (hu : ¬ (X u = x ∧ y ≤ Y u))
    (k : ℕ) (hk : k ≤ p.length)
    (hfirst : ∀ j : ℕ, j < k → ¬ (X (p.getVert j) = x-1 ∧ y ≤ Y (p.getVert j)))
    (hrayApproach : ∀ m : ℕ, 0 < m → m ≤ p.length →
      (X (p.getVert m) = x ∧ y ≤ Y (p.getVert m)) →
      (∀ j : ℕ, j < m → ¬ (X (p.getVert j) = x ∧ y ≤ Y (p.getVert j))) →
      (X (p.getVert (m-1)) = x-1 ∧ y ≤ Y (p.getVert (m-1)))) :
    ∀ j : ℕ, j ≤ k → ¬ (X (p.getVert j) = x ∧ y ≤ Y (p.getVert j)) := by
  classical
  intro j hj hhit
  have hex : ∃ m : ℕ, m ≤ k ∧ (X (p.getVert m) = x ∧ y ≤ Y (p.getVert m)) :=
    ⟨j,hj,hhit⟩
  let m := Nat.find hex
  have hm := Nat.find_spec hex
  have hpos : 0 < m := by
    by_contra h
    have hm0 : m = 0 := by omega
    have hzero := hm.2
    change X (p.getVert m) = x ∧ y ≤ Y (p.getVert m) at hzero
    rw [hm0,SimpleGraph.Walk.getVert_zero] at hzero
    exact hu hzero
  have hminimal : ∀ i : ℕ, i < m →
      ¬ (X (p.getVert i) = x ∧ y ≤ Y (p.getVert i)) := by
    intro i hi hS
    exact Nat.find_min hex hi ⟨hi.le.trans hm.1,hS⟩
  exact hfirst (m-1) (by omega)
    (hrayApproach m hpos (hm.1.trans hk) hm.2 hminimal)

/-- Any entire source walk avoiding the marked ray lifts into the retained
finite slit graph, with exactly the original bonds and no beta vertices. -/
theorem sourceSquare_walk_in_finiteSlit_of_avoid_ray
    (n : ℕ) (x y : ℤ) (hx0 : 0 ≤ x) (hxn : x ≤ (2*n:ℕ))
    {u v : RectangleVertex (0,0) (2*n) (2*n)}
    (p : (rectangleGraph (0,0) (2*n) (2*n)).Walk u v)
    (havoid : ∀ w ∈ p.support, ¬ (w.val.1 = x ∧ y ≤ w.val.2)) :
    ∃ q : (graph (2*n+2) x y).Walk
      (sourceSquareSlitEmbedding n x hx0 hxn u) (sourceSquareSlitEmbedding n x hx0 hxn v),
      q.edges = p.edges.map (Sym2.map (sourceSquareSlitEmbedding n x hx0 hxn)) ∧
      ∀ w ∈ q.support, w ∉ beta (2*n+2) x y := by
  induction p with
  | @nil u =>
    refine ⟨.nil,rfl,?_⟩
    intro w hw
    have he : w = sourceSquareSlitEmbedding n x hx0 hxn u := by simpa using hw
    subst w
    exact fun hb => havoid u (by simp)
      ((sourceSquareSlitEmbedding_mem_beta_iff n x y hx0 hxn u).mp hb)
  | @cons u v w huv p ih =>
    have htail : ∀ z ∈ p.support, ¬ (z.val.1 = x ∧ y ≤ z.val.2) := by
      intro z hz
      exact havoid z (by simp only [SimpleGraph.Walk.support_cons,List.mem_cons]; exact Or.inr hz)
    obtain ⟨q,hqedges,hqavoid⟩ := ih htail
    have hu := havoid u (by simp)
    have hv := htail v p.start_mem_support
    have he := sourceSquareSlitEmbedding_adj_of_avoid_ray n x y hx0 hxn huv hu hv
    refine ⟨q.cons he,?_,?_⟩
    · simp only [SimpleGraph.Walk.edges_cons,List.map_cons,hqedges]
      rfl
    · intro z hz
      rcases List.mem_cons.mp hz with rfl | hz
      · exact fun hb => hu ((sourceSquareSlitEmbedding_mem_beta_iff n x y hx0 hxn u).mp hb)
      · exact hqavoid z hz

/-- The geometric ray-approach interface suffices to retain the COMPLETE
first-left-slit prefix, including its free terminal point. -/
theorem sourceSquare_leftSlit_prefix_in_finiteSlit_of_rayApproach
    (n : ℕ) (x y : ℤ) (hx0 : 0 ≤ x) (hxn : x ≤ (2*n:ℕ))
    {u v : RectangleVertex (0,0) (2*n) (2*n)}
    (p : (rectangleGraph (0,0) (2*n) (2*n)).Walk u v)
    (hu : ¬ (u.val.1 = x ∧ y ≤ u.val.2))
    (k : ℕ) (hk : k ≤ p.length)
    (hfirst : ∀ j : ℕ, j < k → ¬ ((p.getVert j).val.1 = x-1 ∧ y ≤ (p.getVert j).val.2))
    (hrayApproach : ∀ m : ℕ, 0 < m → m ≤ p.length →
      ((p.getVert m).val.1 = x ∧ y ≤ (p.getVert m).val.2) →
      (∀ j : ℕ, j < m → ¬ ((p.getVert j).val.1 = x ∧ y ≤ (p.getVert j).val.2)) →
      ((p.getVert (m-1)).val.1 = x-1 ∧ y ≤ (p.getVert (m-1)).val.2)) :
    ∃ q : (graph (2*n+2) x y).Walk
      (sourceSquareSlitEmbedding n x hx0 hxn u)
      (sourceSquareSlitEmbedding n x hx0 hxn (p.getVert k)),
      q.edges = (p.take k).edges.map (Sym2.map (sourceSquareSlitEmbedding n x hx0 hxn)) ∧
      ∀ w ∈ q.support, w ∉ beta (2*n+2) x y := by
  apply sourceSquare_walk_in_finiteSlit_of_avoid_ray n x y hx0 hxn (p.take k)
  have hav := walk_prefix_avoids_ray_of_rayApproach
    (fun w => w.val.1) (fun w => w.val.2) x y p hu k hk hfirst hrayApproach
  intro w hw
  obtain ⟨j,hj,_⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hw
  rw [SimpleGraph.Walk.take_getVert] at hj
  exact hj ▸ hav (min k j) (Nat.min_le_left k j)

end
end PottsContinuity.RSW
