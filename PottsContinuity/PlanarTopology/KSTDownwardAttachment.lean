module

public import PottsContinuity.PlanarTopology.KSTDownwardFunnel
public import PottsContinuity.PlanarTopology.KSTFunnelAttachment
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Paths

@[expose] public section

namespace PottsContinuity.PlanarTopology
open PD.FK BD12

/-- KST's long lower arm yields an actual open central m-path connected to its
lower endpoint, using only the original three open walks. If it hits a short
wall, that original wall is used; otherwise a contiguous part of the long arm
is used. No new edge or continuous-only connection is inserted. -/
theorem kst_mpath_attached_of_downward_funnel (k : ℕ) (hk : 1 ≤ k) (a : ℤ)
    (ha : 0 ≤ a ∧ a ≤ (k : ℤ)) (ω : LatticeConfiguration)
    {l₁ l₂ r₁ r₂ u v : LatticeVertex}
    (L : PD.squareLattice.Walk l₁ l₂) (R : PD.squareLattice.Walk r₁ r₂)
    (p : PD.squareLattice.Walk u v)
    (hL : kstMPath (12*k) L) (hR : kstMPath (12*k) R)
    (hLO : kstPathOpen ω L) (hRO : kstPathOpen ω R) (hpO : kstPathOpen ω p)
    (hLx : -(k : ℤ) ≤ l₁.1 ∧ l₁.1 ≤ -a)
    (hLx' : -(k : ℤ) ≤ l₂.1 ∧ l₂.1 ≤ -a)
    (hRx : a ≤ r₁.1 ∧ r₁.1 ≤ (k : ℤ))
    (hRx' : a ≤ r₂.1 ∧ r₂.1 ≤ (k : ℤ))
    (hp : p.IsPath) (hu : u.2 = 12*(k : ℤ) ∧ -a ≤ u.1 ∧ u.1 ≤ a)
    (hv : v.2 ≤ -12*(k : ℤ))
    (hupp : ∀ z ∈ p.support, z.2 ≤ 12*(k : ℤ)) :
    ∃ (x y : LatticeVertex) (g : PD.squareLattice.Walk x y) (C : PD.squareLattice.Walk v x),
      kstMPath (12*k) g ∧ kstPathOpen ω g ∧ kstPathOpen ω C ∧
      (∀ z ∈ g.support, z ∈ p.support ∨ z ∈ L.support ∨ z ∈ R.support) ∧
      (∀ z ∈ C.support, z ∈ p.support ∨ z ∈ L.support ∨ z ∈ R.support) := by
  have hLt : l₁.2 = 12*(k : ℤ) := by simpa only [Nat.cast_mul,Nat.cast_ofNat] using hL.2.1
  have hLb : l₂.2 = -12*(k : ℤ) := by simpa only [Nat.cast_mul,Nat.cast_ofNat,neg_mul] using hL.2.2.1
  have hRt : r₁.2 = 12*(k : ℤ) := by simpa only [Nat.cast_mul,Nat.cast_ofNat] using hR.2.1
  have hRb : r₂.2 = -12*(k : ℤ) := by simpa only [Nat.cast_mul,Nat.cast_ofNat,neg_mul] using hR.2.2.1
  have rev_mem {w : LatticeVertex} (hw : w ∈ p.reverse.support) : w ∈ p.support := by
    simpa only [SimpleGraph.Walk.support_reverse,List.mem_reverse] using hw
  have p_mem_rev {w : LatticeVertex} (hw : w ∈ p.support) : w ∈ p.reverse.support := by
    simpa only [SimpleGraph.Walk.support_reverse,List.mem_reverse] using hw
  have hpRevO := (kstPathOpen_reverse_iff ω p).mpr hpO
  have hfunnel := kst_funnel_extract_downward k hk a ha L R p
    (kst_mpath_integral_pathIn k L hL) (kst_mpath_integral_pathIn k R hR)
    hLt hLb hRt hRb hLx hLx' hRx hRx' hp hu hv hupp
  rcases hfunnel with ⟨x,y,g,hg,hsub⟩ | ⟨z,hzp,hz⟩
  · have hx : x ∈ p.support := hsub.support_subset g.start_mem_support
    let C := p.reverse.takeUntil x (p_mem_rev hx)
    have hCs := p.reverse.isSubwalk_takeUntil (p_mem_rev hx)
    refine ⟨x,y,g,C,hg,kstPathOpen_of_subwalk hsub hpO,
      kstPathOpen_of_subwalk hCs hpRevO,?_,?_⟩
    · exact fun z hz => Or.inl (hsub.support_subset hz)
    · exact fun z hz => Or.inl (rev_mem (hCs.support_subset hz))
  · have hzp' : z ∈ p.reverse.support := p_mem_rev hzp
    have wall_case {x y : LatticeVertex} (g : PD.squareLattice.Walk x y)
        (hg : kstMPath (12*k) g) (hgO : kstPathOpen ω g)
        (hgS : ∀ w ∈ g.support, w ∈ p.support ∨ w ∈ L.support ∨ w ∈ R.support)
        (hzg : z ∈ g.support) :
        ∃ (x y : LatticeVertex) (g : PD.squareLattice.Walk x y) (C : PD.squareLattice.Walk v x),
          kstMPath (12*k) g ∧ kstPathOpen ω g ∧ kstPathOpen ω C ∧
          (∀ w ∈ g.support, w ∈ p.support ∨ w ∈ L.support ∨ w ∈ R.support) ∧
          (∀ w ∈ C.support, w ∈ p.support ∨ w ∈ L.support ∨ w ∈ R.support) := by
      let P := p.reverse.takeUntil z hzp'
      let G := g.takeUntil z hzg
      have hPs := p.reverse.isSubwalk_takeUntil hzp'
      have hGs := g.isSubwalk_takeUntil hzg
      refine ⟨x,y,g,P.append G.reverse,hg,hgO,?_,hgS,?_⟩
      · exact kstPathOpen_append P _ (kstPathOpen_of_subwalk hPs hpRevO)
          ((kstPathOpen_reverse_iff ω G).mpr (kstPathOpen_of_subwalk hGs hgO))
      · intro w hw
        simp only [SimpleGraph.Walk.mem_support_append_iff,
          SimpleGraph.Walk.support_reverse,List.mem_reverse] at hw
        exact hw.elim (fun h => Or.inl (rev_mem (hPs.support_subset h)))
          (fun h => hgS w (hGs.support_subset h))
    rcases hz with hz | hz
    · exact wall_case L hL hLO (fun w hw => Or.inr (Or.inl hw)) hz
    · exact wall_case R hR hRO (fun w hw => Or.inr (Or.inr hw)) hz

end PottsContinuity.PlanarTopology
