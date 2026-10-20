module

public import PottsContinuity.Thm3.Push.SideCollarRawQueryIndex
public import PottsContinuity.Thm3.Push.SourceAlphaBarrierIndex
public import PottsContinuity.Thm3.Push.SourceBandEmbedding

@[expose] public section

namespace PottsContinuity.Push
open PD.FK PD.Duality PlanarMixed PlanarMixed.FiniteSlit
noncomputable section

/-- Raw queries in an actual open side arm cannot have an off-arm endpoint
in the opposite source alpha component. All source/exterior geometry and
both winding indices are proved from the literal sampled open walk. -/
theorem sourceBand_raw_query_off_trace_not_alpha
    (N a w : ℕ) (ha : 1 ≤ a) (hfit : a+w ≤ N)
    (A : Configuration (rectangleGraph (0,0) w N)) (r : ℤ)
    {b v : RectangleVertex (0,0) w N}
    (q : (openGraph (rectangleGraph (0,0) w N) A).Walk b v)
    (hb : b.val.2 = 0) (hbx : 0 < b.val.1) (hbr : b.val.1 ≤ r)
    (hv : v.val.1 = 0) (hy : 0 < v.val.2)
    (e : (rectangleGraph (0,0) w N).edgeSet) (he : e ∈ sideCollarRawLeftArmReveal w N r A)
    (u : RectangleVertex (0,0) w N) (hu : u ∈ e.val) (hucut : u ∉ q.support) :
    Sum.inl (sourceBandEmbedding N a w N hfit le_rfl u) ∉
      cutReachRegion (sourceExteriorGraph N N (a:ℤ) v.val.2)
        (Sum.inl '' (sourceBandEmbedding N a w N hfit le_rfl '' {z | z ∈ q.support}))
        (sourceAlpha N N (a:ℤ)) := by
  classical
  obtain ⟨Q,hQs,p,hallowed,hα,hβ,hraw⟩ :=
    sideCollar_exists_barrier_with_raw_query_endpoint_index w N A r q hb hbx hbr hv hy
  let M := sideCollarSize w N+2
  let d : ℤ := (a:ℤ)-2
  let f := sourceBandEmbedding N a w N hfit le_rfl
  let QG := Q.map (horizontalBarrierTranslationHom d)
  let PG := p.map (horizontalBarrierTranslationHom d)
  have hM : 2 ≤ M := by dsimp [M,sideCollarSize]; omega
  have hx : 2+d = (a:ℤ) := by dsimp [d]; omega
  have hallowedG := slitBarrierWalk_horizontalBarrierTranslation M 2 v.val.2 (b.val.1+2) d Q p hallowed
  rw [hx] at hallowedG
  have hαG := slitAlpha_index_horizontalBarrierTranslation M (by omega) 2 d p hα
  rw [hx] at hαG
  have hQG : QG.support = q.support.map (fun z => (f z).val) := by
    calc
      QG.support = Q.support.map (horizontalBarrierTranslationHom d) := SimpleGraph.Walk.support_map _ _
      _ = q.support.map (fun z => (f z).val) := by
        rw [hQs,List.map_map]
        congr 1
        funext z
        apply Prod.ext
        · change z.val.1+2+d = z.val.1+(a:ℤ)
          dsimp [d]
          omega
        · rfl
  have hsource : ∀ z ∈ QG.support, z ∈ PD.FK.latticeRectangle (0,0) N N := by
    intro z hz
    rw [hQG] at hz
    obtain ⟨t,_,rfl⟩ := List.mem_map.mp hz
    exact (f t).property
  have hcut : sourceCoordinateTrace N N {z | z ∈ QG.support} = f '' {z | z ∈ q.support} := by
    ext z
    change z.val ∈ QG.support ↔ ∃ t, t ∈ q.support ∧ f t = z
    rw [hQG,List.mem_map]
    constructor
    · rintro ⟨t,ht,heq⟩
      exact ⟨t,ht,Subtype.ext heq⟩
    · rintro ⟨t,ht,rfl⟩
      exact ⟨t,ht,rfl⟩
  intro hreach
  rw [← hcut] at hreach
  have hyN := ((PD.FK.mem_latticeRectangle _ _ _ _).mp v.property).2.2
  have hzero := sourceAlpha_cutReach_index_zero_of_slitBarrier M (a:ℤ) v.val.2 (b.val.1+2+d) N N
    hM (by omega) (by omega) (by dsimp [M,sideCollarSize]; omega)
    (by dsimp [M,sideCollarSize]; omega) (by dsimp [M,sideCollarSize]; omega)
    (by simpa only [zero_add] using hyN) QG hsource PG hallowedG hαG (f u) hreach
  have heq : ((sideCollarEmbedding w N u).val.1+d,(sideCollarEmbedding w N u).val.2) = (f u).val := by
    apply Prod.ext
    · change u.val.1+2+d = u.val.1+(a:ℤ)
      dsimp [d]
      omega
    · rfl
  have htrans := rayIndex_horizontalBarrierTranslation d (sideCollarEmbedding w N u).val p
  rw [heq] at htrans
  have hneg : rayIndex (f u).val PG = -1 := htrans.trans (hraw e he u hu hucut)
  omega

end
end PottsContinuity.Push
