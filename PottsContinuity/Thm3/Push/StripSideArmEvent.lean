module

public import PottsContinuity.Thm3.Push.StripSourceArmLimit
public import PottsContinuity.Thm3.Push.StripSourceVertexRange
public import PottsContinuity.Thm3.Push.WalkPullback

@[expose] public section

namespace PottsContinuity.Push
open PD.FK
noncomputable section

/-- A source side-arm cylinder is exactly the original strip path event,
with every path vertex confined to its specified physical rectangle. -/
theorem stripSourceSideArmEvent_eq_confined (n : ℕ) (x l r L R T : ℤ)
    (hL : 0 ≤ L) (hR : R ≤ 2*(n:ℤ)) :
    stripSourceSquareEvent n x (sourceSquareSideArmEvent (2*n) l r L R T) =
      RSW.stripConfinedConnection n
        (RSW.stripRectangleVertices n (x+L) (x+R) 0 (2*(n:ℤ)))
        {w | w.val ∈ Set.Icc (x+l) (x+r) ×ˢ ({0} : Set ℤ)}
        {w | w.val.1 = x+T} := by
  have hrect (w : RSW.stripVertices n) :
      w ∈ RSW.stripRectangleVertices n (x+L) (x+R) 0 (2*(n:ℤ)) ↔
        x+L ≤ w.val.1 ∧ w.val.1 ≤ x+R ∧ 0 ≤ w.val.2 ∧ w.val.2 ≤ 2*(n:ℤ) := by
    simp only [RSW.stripRectangleVertices,Finset.mem_preimage,
      PottsContinuity.latticeRectangle,Finset.mem_product,Finset.mem_Icc]
    tauto
  ext ω
  let j : openGraph (rectangleGraph (0,0) (2*n) (2*n)) (stripSourceSquareRestriction n x ω) ↪g
      RSW.stripOpenGraph n ω :=
    openStateEmbedding (intervalArmStripGraphEmbedding n x) _ ω (fun _ => rfl)
  constructor
  · rintro ⟨a,b,p,ha,hal,har,hb,hp⟩
    refine ⟨j a,j b,p.map j.toHom,?_,?_,?_⟩
    · change (x+a.val.1,a.val.2) ∈ Set.Icc (x+l) (x+r) ×ˢ ({0} : Set ℤ)
      exact ⟨⟨by omega,by omega⟩,ha⟩
    · change x+b.val.1=x+T
      omega
    · intro w hw
      rw [SimpleGraph.Walk.support_map] at hw
      obtain ⟨z,hz,rfl⟩ := List.mem_map.mp hw
      apply (hrect (j z)).mpr
      have hzx := hp z hz
      have hzbox := (PD.FK.mem_latticeRectangle (0,0) z.val (2*n) (2*n)).mp z.property
      change x+L ≤ x+z.val.1 ∧ x+z.val.1 ≤ x+R ∧ 0 ≤ z.val.2 ∧ z.val.2 ≤ 2*(n:ℤ)
      dsimp at hzbox
      exact ⟨by omega,by omega,by omega,by omega⟩
  · rintro ⟨a,b,p,ha,hb,hp⟩
    have hrange : ∀ w ∈ p.support, w ∈ Set.range j := by
      intro w hw
      apply (mem_range_intervalArmStripGraphEmbedding_iff n x w).mpr
      have hh := (hrect w).mp (hp w hw)
      exact ⟨by omega,by omega,hh.2.2.1,hh.2.2.2⟩
    obtain ⟨a',ha'⟩ := hrange a p.start_mem_support
    obtain ⟨b',hb'⟩ := hrange b p.end_mem_support
    let p₀ := p.copy ha'.symm hb'.symm
    have h₀ : ∀ w ∈ p₀.support, w ∈ Set.range j := by
      simpa only [p₀,SimpleGraph.Walk.support_copy] using hrange
    obtain ⟨q,hq⟩ := exists_walk_pullback_support j p₀ h₀
    have haCoord : (x+a'.val.1,a'.val.2) = a.val := congrArg Subtype.val ha'
    have hbCoord : (x+b'.val.1,b'.val.2) = b.val := congrArg Subtype.val hb'
    have hax := congrArg Prod.fst haCoord
    have hay := congrArg Prod.snd haCoord
    have hbx := congrArg Prod.fst hbCoord
    have ha0 : a.val.2 = 0 := ha.2
    have hal : x+l ≤ a.val.1 := ha.1.1
    have har : a.val.1 ≤ x+r := ha.1.2
    change b.val.1=x+T at hb
    change stripSourceSquareRestriction n x ω ∈ sourceSquareSideArmEvent (2*n) l r L R T
    refine ⟨a',b',q,?_,?_,?_,?_,?_⟩
    · simpa only [Prod.snd] using hay.trans ha0
    · dsimp at hax
      omega
    · dsimp at hax
      omega
    · dsimp at hbx
      omega
    · intro w hw
      have hwp : j w ∈ p.support := by
        simpa only [p₀,SimpleGraph.Walk.support_copy] using hq w hw
      have hh := (hrect (j w)).mp (hp (j w) hwp)
      change x+L ≤ x+w.val.1 ∧ x+w.val.1 ≤ x+R ∧ _ at hh
      exact ⟨by omega,by omega⟩

end
end PottsContinuity.Push
