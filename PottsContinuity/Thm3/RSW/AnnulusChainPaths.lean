module

public import PottsContinuity.Thm3.RSW.AdjacentAnnulusPolygons
public import PottsContinuity.Thm3.RSW.PolygonPaths
public import PottsContinuity.Thm3.RSW.PolygonHorizontalExtent

/-! # Actual confined paths along a chain of sampled annulus polygons -/

@[expose] public section

namespace PottsContinuity.RSW

/-- Any vertex on the last enclosing polygon is reachable from a vertex to
the left of the first center. The polygon at each preceding scale is taken
from its actual sampled annulus event, with no global witness selection. -/
theorem annulus_chain_left_to_polygon
    (V S : Finset (ℤ × ℤ))
    (ω : (squareLattice.induce (V : Set (ℤ × ℤ))).edgeSet → Bool)
    (r : ℕ) (hr : 1 ≤ r) (c : ℕ → ℤ × ℤ) (K : ℕ)
    (hstep : ∀ l < K, (c (l+1)).1 = (c l).1+(r:ℤ) ∧ (c (l+1)).2 = (c l).2)
    (hcircs : ∀ l < K, ω ∈ annulusCircuitEvent V (c l) r)
    (hS : ∀ l ≤ K, ∀ v : ℤ × ℤ,
      max |v.1-(c l).1| |v.2-(c l).2| ≤ 2*(r:ℤ) → v ∈ S)
    {m : ℕ} (P : FKC.LatticePolygon m)
    (hcenter : FKC.latticeEmbed ⟨1,zero_lt_one⟩ (c K) ∈ P.domain ⟨1,zero_lt_one⟩)
    (hann : ∀ i, (r:ℤ) < max |(P.vertex i).1-(c K).1| |(P.vertex i).2-(c K).2| ∧
      max |(P.vertex i).1-(c K).1| |(P.vertex i).2-(c K).2| ≤ 2*(r:ℤ))
    (hopen : ∀ i : ZMod (m+3), ∃ hi : P.vertex i ∈ V, ∃ hj : P.vertex (i+1) ∈ V,
      (rcOpenGraph V ω).Adj ⟨P.vertex i,hi⟩ ⟨P.vertex (i+1),hj⟩)
    (j : ZMod (m+3)) :
    ∃ x : ℤ × ℤ, x.1 < (c 0).1 ∧ ω ∈ finitePathEvent V S x (P.vertex j) := by
  induction K generalizing m with
  | zero =>
    obtain ⟨i,hi⟩ := latticePolygon_exists_vertex_left_of_center P (c 0) hcenter
    exact ⟨P.vertex i,hi,open_polygon_finitePathEvent V S ω P hopen
      (fun k => hS 0 (by omega) _ (hann k).2) i j⟩
  | succ K ih =>
    obtain ⟨t,Q,hQc,hQa,hQo⟩ := hcircs K (by omega)
    obtain ⟨iq,ip,hinter⟩ := adjacent_annulus_polygons_shared_vertex Q P (c K) (c (K+1))
      r hr (hstep K (by omega)).1 (hstep K (by omega)).2 hQc hcenter hQa hann
    obtain ⟨x,hx,hpath⟩ := ih
      (fun l hl => hstep l (by omega))
      (fun l hl => hcircs l (by omega))
      (fun l hl => hS l (by omega)) Q hQc hQa hQo iq
    rw [hinter] at hpath
    have hlast := open_polygon_finitePathEvent V S ω P hopen
      (fun k => hS (K+1) (by omega) _ (hann k).2) ip j
    exact ⟨x,hx,finitePathEvent_trans V S x (P.vertex ip) (P.vertex j) ⟨hpath,hlast⟩⟩

/-- The entire actual annulus chain contains a confined path from strictly
left of its first center to strictly right of its last center. K=0 is allowed. -/
theorem annulus_chain_spanning_path
    (V S : Finset (ℤ × ℤ))
    (ω : (squareLattice.induce (V : Set (ℤ × ℤ))).edgeSet → Bool)
    (r : ℕ) (hr : 1 ≤ r) (c : ℕ → ℤ × ℤ) (K : ℕ)
    (hstep : ∀ l < K, (c (l+1)).1 = (c l).1+(r:ℤ) ∧ (c (l+1)).2 = (c l).2)
    (hcircs : ∀ l ≤ K, ω ∈ annulusCircuitEvent V (c l) r)
    (hS : ∀ l ≤ K, ∀ v : ℤ × ℤ,
      max |v.1-(c l).1| |v.2-(c l).2| ≤ 2*(r:ℤ) → v ∈ S) :
    ∃ x y : ℤ × ℤ, x.1 < (c 0).1 ∧ (c K).1 < y.1 ∧ ω ∈ finitePathEvent V S x y := by
  obtain ⟨m,P,hc,ha,ho⟩ := hcircs K le_rfl
  obtain ⟨j,hj⟩ := latticePolygon_exists_vertex_right_of_center P (c K) hc
  obtain ⟨x,hx,hpath⟩ := annulus_chain_left_to_polygon V S ω r hr c K hstep
    (fun l hl => hcircs l (Nat.le_of_lt hl)) hS P hc ha ho j
  exact ⟨x,P.vertex j,hx,hj,hpath⟩

end PottsContinuity.RSW
