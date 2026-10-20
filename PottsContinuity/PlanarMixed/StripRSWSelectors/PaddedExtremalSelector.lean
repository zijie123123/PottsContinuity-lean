module

public import PottsContinuity.PlanarMixed.StripRSWSelectors.PaddedDecode

@[expose] public section

namespace PottsContinuity.PlanarMixed.StripRSWSelectors
open PD.FK Push BD12 Exploration
noncomputable section
local instance prefixAuxEdgeEq (n : ℕ) : DecidableEq (prefixAuxGraph n).edgeSet := Classical.decEq _
local instance prefixAuxVertexOrder (n : ℕ) : LinearOrder (PrefixAuxVertex n) :=
  LinearOrder.lift' (fun v => toLex v.val) (fun _ _ he => Subtype.ext (toLex.injective he))

/-- Search only within the filled left frontier of the padded completion. -/
def prefixAuxExtremalTrace (n s : ℕ) (hfit : 9*s ≤ 2*n)
    (b : CaseTwoTipEndpointRecord n s) (C : Configuration (rectangleGraph (0,0) (2*n) (2*n))) :
    Option (List (PrefixAuxVertex n)) :=
  firstHitPrefixSelector (intervalArmBottomArc (2*n+1) (4*(s:ℤ)) (5*(s:ℤ)))
    (prefixAuxRay n s b)
    (intervalArmFilledLeftFrontier (2*n+1) (4*(s:ℤ)) (5*(s:ℤ)) (prefixAuxCompletion n s hfit b C))

/-- Every confined connection has a first-contact prefix on this extremal frontier. -/
theorem prefixAuxExtremalTrace_search (n s : ℕ) (hs : 1 ≤ s) (hfit : 9*s ≤ 2*n)
    (b : CaseTwoTipEndpointRecord n s) (C : Configuration (rectangleGraph (0,0) (2*n) (2*n)))
    (hC : caseTwoConfinedPrefixConfiguration n s hfit b C ∈
      arcsConnectionEvent (caseTwoConfinedPrefixGraph n s hfit b)
        (intervalArmBottomArc (2*n) (4*(s:ℤ)) (5*(s:ℤ)))
        {z | z.val.1=4*(s:ℤ)-1 ∧ b.2.val.2≤z.val.2}) :
    (prefixAuxExtremalTrace n s hfit b C).isSome := by
  have hA := prefixAuxCompletion_arm_of_confined_connection n s hfit b C hC
  obtain ⟨a,ha,t,ht,p⟩ := hA
  obtain ⟨p⟩ := p
  obtain ⟨u,v,hu,hul,hur,hv,q⟩ := intervalArmFilledLeftFrontier_contains_arm
    (2*n+1) (4*(s:ℤ)) (5*(s:ℤ)) (by omega) (by omega) (by omega)
    _ p ha.1 ht ha.2.1 ha.2.2
  obtain ⟨q⟩ := q
  have hne : u ≠ v := by
    intro he
    have heh := congrArg (fun z : PrefixAuxVertex n => z.val.2) he
    omega
  have hvq : (openGraph (prefixAuxGraph n) (prefixAuxCompletion n s hfit b C)).Adj v q.reverse.snd :=
    (openGraph_mono (fun e he =>
      (Finset.mem_inter.mp (intervalArmFilledLeftFrontier_subset_open_raw_record _ _ _ _ he)).1))
      (q.reverse.adj_snd (SimpleGraph.Walk.not_nil_of_ne hne.symm))
  apply (firstHitPrefixSelector_isSome_iff _ _ _).mpr
  exact ⟨u,⟨hu,hul,hur⟩,v,prefixAuxCompletion_top_open_vertex_on_ray n s hfit b C v _ hv hvq,q.reachable⟩

/-- The returned auxiliary prefix has a physical source first-contact trace. -/
theorem prefixAuxExtremalTrace_firstContact (n s : ℕ) (hs : 1 ≤ s) (hfit : 9*s ≤ 2*n)
    (b : CaseTwoTipEndpointRecord n s) (C : Configuration (rectangleGraph (0,0) (2*n) (2*n)))
    (trace : List (PrefixAuxVertex n)) (hsel : prefixAuxExtremalTrace n s hfit b C=some trace) :
    ConfinedPrefixFirstContact n s hfit C b (trace.map (prefixPaddingRetraction n)) := by
  obtain ⟨a,ha,t,ht,p,hp,hfirst⟩ := firstHitPrefixSelector_spec _ _ _ trace hsel
  have hsub : intervalArmFilledLeftFrontier (2*n+1) (4*(s:ℤ)) (5*(s:ℤ))
      (prefixAuxCompletion n s hfit b C) ⊆ prefixAuxCompletion n s hfit b C :=
    (intervalArmFilledLeftFrontier_subset_open_raw_record _ _ _ _).trans Finset.inter_subset_left
  let q := p.val.mapLe (openGraph_mono hsub)
  have hqs : q.support=trace := (SimpleGraph.Walk.support_mapLe_eq_support _ _).trans hp
  simpa only [hqs] using prefixAux_first_contact_decodes n s hs hfit b C q ha ht
    (by simpa only [hqs] using hfirst)

/-- A different physical selector: the first-contact portion of the filled
left frontier, rather than code order on the entire confined source graph. -/
def paddedExtremalConfinedPrefixSelector (n s : ℕ) (hs : 1 ≤ s) (hfit : 9*s ≤ 2*n) :
    ConfinedPrefixSelector n s hfit where
  selectPrefix b C := (prefixAuxExtremalTrace n s hfit b C).map (List.map (prefixPaddingRetraction n))
  search C b hC := by
    simpa only [Option.isSome_map] using prefixAuxExtremalTrace_search n s hs hfit b C hC
  firstContact C b trace hsel := by
    obtain ⟨aux,haux,rfl⟩ := Option.map_eq_some_iff.mp hsel
    exact prefixAuxExtremalTrace_firstContact n s hs hfit b C aux haux

end
end PottsContinuity.PlanarMixed.StripRSWSelectors
