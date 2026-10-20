module

public import PottsContinuity.Thm3.RSW.OpenFourWalkAnnulus
public import PottsContinuity.Thm3.RSW.BoxCorridors
public import PottsContinuity.PlanarTopology.RectangleIntersection

@[expose] public section

namespace PottsContinuity.RSW
open PD.FK
noncomputable section

private theorem open_rectangle_common_vertex
    (V : Finset LatticeVertex)
    (ω : (PottsContinuity.squareLattice.induce (V : Set LatticeVertex)).edgeSet → Bool)
    {l r b t : ℤ} {u v u' v' : (V : Set LatticeVertex)}
    (p : (rcOpenGraph V ω).Walk u v) (q : (rcOpenGraph V ω).Walk u' v')
    (hlr : l ≤ r) (hbt : b ≤ t)
    (hp : ∀ x ∈ p.support, l ≤ x.val.1 ∧ x.val.1 ≤ r ∧ b ≤ x.val.2 ∧ x.val.2 ≤ t)
    (hq : ∀ x ∈ q.support, l ≤ x.val.1 ∧ x.val.1 ≤ r ∧ b ≤ x.val.2 ∧ x.val.2 ≤ t)
    (hu : u.val.1 = l) (hv : v.val.1 = r)
    (hu' : u'.val.2 = b) (hv' : v'.val.2 = t) :
    ∃ x, x ∈ p.support ∧ x ∈ q.support := by
  let φ := Thm3.Easy.p5ClosedWalkToSquareLattice V ω
  obtain ⟨x,hxp,hxq⟩ := PlanarTopology.rectangle_walks_common_vertex
    (p.map φ) (q.map φ) hlr hbt
    (by
      intro x hx
      rw [SimpleGraph.Walk.support_map,List.mem_map] at hx
      obtain ⟨v,hv,rfl⟩ := hx
      exact hp v hv)
    (by
      intro x hx
      rw [SimpleGraph.Walk.support_map,List.mem_map] at hx
      obtain ⟨v,hv,rfl⟩ := hx
      exact hq v hv) hu hv hu' hv'
  rw [SimpleGraph.Walk.support_map,List.mem_map] at hxp hxq
  obtain ⟨v,hvp,hvx⟩ := hxp
  obtain ⟨w,hwq,hwx⟩ := hxq
  have hvw : v = w := Subtype.ext (hvx.trans hwx.symm)
  exact ⟨v,hvp,hvw ▸ hwq⟩

/-- Four translated source corridors yield a genuine surrounding annulus
circuit in an arbitrary finite sampled ambient domain. -/
theorem fourCorridor_annulusCircuitEvent_centered
    (V : Finset LatticeVertex) (c : LatticeVertex) (n m : ℕ)
    (hn : 1 ≤ n) (_hm : 1 ≤ m) (hmn : m < n)
    (ω : (PottsContinuity.squareLattice.induce (V : Set LatticeVertex)).edgeSet → Bool)
    (hTop : horizontalCrossing V (c.1-2*n) (c.1+2*n)
      (c.2+n+1) (c.2+n+1+m) ω)
    (hBottom : horizontalCrossing V (c.1-2*n) (c.1+2*n)
      (c.2-n-1-m) (c.2-n-1) ω)
    (hLeft : finiteVerticalCrossing V (c.1-n-1-m) (c.1-n-1)
      (c.2-2*n) (c.2+2*n) ω)
    (hRight : finiteVerticalCrossing V (c.1+n+1) (c.1+n+1+m)
      (c.2-2*n) (c.2+2*n) ω) :
    ω ∈ annulusCircuitEvent V c n := by
  obtain ⟨uT,vT,pT,huT,hvT,hpT⟩ := hTop
  obtain ⟨uB,vB,pB,huB,hvB,hpB⟩ := hBottom
  obtain ⟨uL,vL,pL,huL,hvL,hpL⟩ := hLeft
  obtain ⟨uR,vR,pR,huR,hvR,hpR⟩ := hRight
  simp only [Set.mem_prod,Set.mem_singleton_iff,Set.mem_Icc] at huT hvT hpT huB hvB hpB huL hvL hpL huR hvR hpR
  have hnZ : (1:ℤ) ≤ n := by exact_mod_cast hn
  have hmnZ : (m:ℤ) < n := by exact_mod_cast hmn
  have hbT : ∀ x ∈ pT.support,
      c.1-2*(n:ℤ) ≤ x.val.1 ∧ x.val.1 ≤ c.1+2*(n:ℤ) ∧
      c.2-2*(n:ℤ) ≤ x.val.2 ∧ x.val.2 ≤ c.2+2*(n:ℤ) := by
    intro x hx
    have h := hpT x hx
    omega
  have hbB : ∀ x ∈ pB.support,
      c.1-2*(n:ℤ) ≤ x.val.1 ∧ x.val.1 ≤ c.1+2*(n:ℤ) ∧
      c.2-2*(n:ℤ) ≤ x.val.2 ∧ x.val.2 ≤ c.2+2*(n:ℤ) := by
    intro x hx
    have h := hpB x hx
    omega
  have hbL : ∀ x ∈ pL.support,
      c.1-2*(n:ℤ) ≤ x.val.1 ∧ x.val.1 ≤ c.1+2*(n:ℤ) ∧
      c.2-2*(n:ℤ) ≤ x.val.2 ∧ x.val.2 ≤ c.2+2*(n:ℤ) := by
    intro x hx
    have h := hpL x hx
    omega
  have hbR : ∀ x ∈ pR.support,
      c.1-2*(n:ℤ) ≤ x.val.1 ∧ x.val.1 ≤ c.1+2*(n:ℤ) ∧
      c.2-2*(n:ℤ) ≤ x.val.2 ∧ x.val.2 ≤ c.2+2*(n:ℤ) := by
    intro x hx
    have h := hpR x hx
    omega
  have hTR := open_rectangle_common_vertex _ ω pT pR (by omega) (by omega)
    hbT hbR huT.1 hvT.1 huR.2 hvR.2
  have hBR := open_rectangle_common_vertex _ ω pB pR (by omega) (by omega)
    hbB hbR huB.1 hvB.1 huR.2 hvR.2
  have hBL := open_rectangle_common_vertex _ ω pB pL (by omega) (by omega)
    hbB hbL huB.1 hvB.1 huL.2 hvL.2
  have hTL := open_rectangle_common_vertex _ ω pT pL (by omega) (by omega)
    hbT hbL huT.1 hvT.1 huL.2 hvL.2
  apply annulusCircuitEvent_of_fourIntersectingOpenWalks _ ω c n pT pR pB pL
    hTR (by obtain ⟨x,hxB,hxR⟩ := hBR; exact ⟨x,hxR,hxB⟩)
    hBL (by obtain ⟨x,hxT,hxL⟩ := hTL; exact ⟨x,hxL,hxT⟩)
  · intro v hv
    have := hpT v hv
    omega
  · intro v hv
    have := hpR v hv
    omega
  · intro v hv
    have := hpB v hv
    omega
  · intro v hv
    have := hpL v hv
    omega
  · intro v hv
    have hb : c.1-2*(n:ℤ) ≤ v.val.1 ∧ v.val.1 ≤ c.1+2*(n:ℤ) ∧
        c.2-2*(n:ℤ) ≤ v.val.2 ∧ v.val.2 ≤ c.2+2*(n:ℤ) := by
      rcases hv with hv | hv | hv | hv
      · exact hbT v hv
      · exact hbR v hv
      · exact hbB v hv
      · exact hbL v hv
    simp only [max_le_iff,abs_le]
    omega

end
end PottsContinuity.RSW
