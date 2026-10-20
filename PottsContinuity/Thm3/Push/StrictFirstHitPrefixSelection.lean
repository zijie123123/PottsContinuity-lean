module

public import PottsContinuity.Thm3.Push.CompletionFreePrefixSelection
public import PottsContinuity.Thm3.Push.FirstContactPrefix

@[expose] public section

namespace PottsContinuity.Push
open PD.FK BD12 Exploration PlanarMixed.FiniteSlit
noncomputable section
local instance strictHitVertexFintype {V : Type*} [Finite V] : Fintype V := Fintype.ofFinite _
local instance strictHitOpenAdj {V : Type*} {G : SimpleGraph V} (C : Configuration G) :
    DecidableRel (openGraph G C).Adj := fun _ _ => Classical.dec _
local instance strictHitOpenEdgeFintype {V : Type*} [Finite V] {G : SimpleGraph V}
    (C : Configuration G) : Fintype (openGraph G C).edgeSet := Fintype.ofFinite _
local instance strictHitPathFintype {V : Type*} [Finite V] [LinearOrder V] {G : SimpleGraph V}
    (C : Configuration G) (a b : V) : Fintype ((openGraph G C).Path a b) := Fintype.ofFinite _
local instance strictHitWitnessFintype {V : Type*} [Finite V] [LinearOrder V] {G : SimpleGraph V}
    (C : Configuration G) : Fintype (BoundaryClusterPathWitness (G := G) C) := Fintype.ofFinite _

/-- Keep only simple path codes already ending at their first target visit.
Eligibility requires no continuation past that visit. -/
def firstHitPrefixCodeSet {V : Type*} [Finite V] [LinearOrder V]
    {G : SimpleGraph V} (S T : Set V) (C : Configuration G) : Finset (List V) := by
  classical
  exact ((Finset.univ : Finset (BoundaryClusterPathWitness (G := G) C)).filter
    (fun p => p.1 ∈ S ∧ p.2.1 ∈ T ∧
      firstContactTrace T p.2.2.val.support = some p.2.2.val.support)).image (boundaryClusterPathCode C)

/-- Select directly among complete first-hit prefixes. This uses code order;
no planar leftmost or rightmost value locality is asserted. -/
def firstHitPrefixSelector {V : Type*} [Finite V] [LinearOrder V]
    {G : SimpleGraph V} (S T : Set V) (C : Configuration G) : Option (List V) := by
  classical
  let codes := firstHitPrefixCodeSet S T C
  exact if h : codes.Nonempty then some ((codes.min' h).drop 2) else none

private theorem firstContact_prefix_is_fixed {V : Type*} {G : SimpleGraph V} {a b : V}
    (p : G.Walk a b) (T : Set V) (k : ℕ) (hk : IsFirstContact p T k) :
    firstContactTrace T (p.take k).support = some (p.take k).support := by
  let q := p.take k
  have hlen : q.length = k := by
    simp only [q,SimpleGraph.Walk.take_length,Nat.min_eq_left hk.1]
  have hq : IsFirstContact q T q.length := by
    refine ⟨le_rfl,?_,?_⟩
    · rw [hlen]
      simpa only [q,SimpleGraph.Walk.take_getVert,Nat.min_self] using hk.2.1
    · intro j hj
      rw [hlen] at hj
      simpa only [q,SimpleGraph.Walk.take_getVert,Nat.min_eq_right hj.le] using hk.2.2 j hj
  have h := firstContactTrace_eq_support_take q T q.length hq
  have hs : (q.take q.length).support = q.support := by
    rw [SimpleGraph.Walk.support_take,← q.length_support,List.take_length]
  rw [hs] at h
  exact h

/-- Restricting candidates to first-hit prefixes preserves the exact
seed-to-target connection success event. -/
theorem firstHitPrefixSelector_isSome_iff
    {V : Type*} [Finite V] [LinearOrder V] {G : SimpleGraph V}
    (S T : Set V) (C : Configuration G) :
    (firstHitPrefixSelector S T C).isSome ↔ C ∈ arcsConnectionEvent G S T := by
  classical
  have hcodes : (firstHitPrefixCodeSet S T C).Nonempty ↔ C ∈ arcsConnectionEvent G S T := by
    constructor
    · rintro ⟨code,hcode⟩
      obtain ⟨p,hp,_⟩ := Finset.mem_image.mp hcode
      have hvalid := (Finset.mem_filter.mp hp).2
      exact ⟨p.1,hvalid.1,p.2.1,hvalid.2.1,p.2.2.val.reachable⟩
    · rintro ⟨a,ha,b,hb,hp⟩
      obtain ⟨p,hp⟩ := hp.exists_isPath
      obtain ⟨k,hk,_⟩ := firstContactTrace_exists_prefix p T hb
      let q : (openGraph G C).Path a (p.getVert k) := ⟨p.take k,hp.take k⟩
      let w : BoundaryClusterPathWitness (G := G) C := ⟨a,p.getVert k,q⟩
      refine ⟨boundaryClusterPathCode C w,Finset.mem_image.mpr ⟨w,?_,rfl⟩⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,ha,hk.2.1,firstContact_prefix_is_fixed p T k hk⟩
  unfold firstHitPrefixSelector
  dsimp only
  split_ifs with h
  · simpa only [Option.isSome_some,true_iff] using hcodes.mp h
  · simp only [Option.isSome_none,Bool.false_eq_true,false_iff]
    exact fun hC => h (hcodes.mpr hC)

/-- Every selected value is a genuine sampled simple path from S to T,
with no dependence on a suffix beyond its first target contact. -/
theorem firstHitPrefixSelector_spec
    {V : Type*} [Finite V] [LinearOrder V] {G : SimpleGraph V}
    (S T : Set V) (C : Configuration G) (trace : List V)
    (hsel : firstHitPrefixSelector S T C = some trace) :
    ∃ a ∈ S, ∃ b ∈ T, ∃ p : (openGraph G C).Path a b,
      p.val.support = trace ∧ firstContactTrace T trace = some trace := by
  classical
  unfold firstHitPrefixSelector at hsel
  dsimp only at hsel
  split_ifs at hsel with h
  · have he := Option.some.inj hsel
    have hm := Finset.min'_mem (firstHitPrefixCodeSet S T C) h
    obtain ⟨p,hp,hcode⟩ := Finset.mem_image.mp hm
    have hvalid := (Finset.mem_filter.mp hp).2
    have hs : p.2.2.val.support = trace := by
      have hd := congrArg (fun code : List V => code.drop 2) hcode
      exact hd.trans he
    refine ⟨p.1,hvalid.1,p.2.1,hvalid.2.1,p.2.2,hs,?_⟩
    exact hs ▸ hvalid.2.2

end
end PottsContinuity.Push
