-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/ParafermionicCoverTwoReturnFixedLoopData.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.ParafermionicCoverEdgeCutPrimalConnection
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

open PottsContinuity.FKC PottsContinuity.FKC.Medial
noncomputable section

private theorem twoReturn_fin3_eq_one (x : ThreeTerminal)
    (h0 : x ≠ 0) (h2 : x ≠ 2) : x = 1 := by
  have hxlt : x.val < 3 := x.isLt
  have hx0 : x.val ≠ 0 := fun h => h0 (Fin.ext h)
  have hx2 : x.val ≠ 2 := fun h => h2 (Fin.ext h)
  apply Fin.ext
  omega

private theorem twoReturn_fin3_eq_two (x : ThreeTerminal)
    (h0 : x ≠ 0) (h1 : x ≠ 1) : x = 2 := by
  have hxlt : x.val < 3 := x.isLt
  have hx0 : x.val ≠ 0 := fun h => h0 (Fin.ext h)
  have hx1 : x.val ≠ 1 := fun h => h1 (Fin.ext h)
  apply Fin.ext
  omega

private theorem twoReturn_permutation_fixed_swap
    (π : Equiv.Perm ThreeTerminal) (i : ThreeTerminal)
    (hπ0 : π 0 = i) (hi : i ≠ 0) (hπi : π i = 0) :
    π (threeTerminalSwap i) = threeTerminalSwap i := by
  fin_cases i
  · exact (hi rfl).elim
  · have h20 : π 2 ≠ 0 := by
      intro h
      have heq := π.injective (h.trans hπi.symm)
      norm_num at heq
    have h21 : π 2 ≠ 1 := by
      intro h
      have heq := π.injective (h.trans hπ0.symm)
      norm_num at heq
    have h22 : π 2 = 2 := twoReturn_fin3_eq_two (π 2) h20 h21
    simp [threeTerminalSwap, h22]
  · have h10 : π 1 ≠ 0 := by
      intro h
      have heq := π.injective (h.trans hπi.symm)
      norm_num at heq
    have h12 : π 1 ≠ 2 := by
      intro h
      have heq := π.injective (h.trans hπ0.symm)
      norm_num at heq
    have h11 : π 1 = 1 := twoReturn_fin3_eq_one (π 1) h10 h12
    simp [threeTerminalSwap, h11]

/-- In a closed two-return case, the unused swap terminal is nonzero and is a
fixed point of the actual routing successor. -/
theorem parafermionicCoverFiniteEdgeCutClosedTwoReturn_fixedSwap
    (n : ℕ) (hn : 1 ≤ n) (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet) (he : e ∉ A)
    (h0 : parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e 0 ≠ 0)
    (h1 : parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e
      (parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e 0) = 0) :
    let π := parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e
    let i := π 0
    let j := threeTerminalSwap i
    j ≠ 0 ∧ parafermionicCoverFiniteEdgeCutRoutingSuccessor n hn A e j = j := by
  dsimp only
  let π := parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e
  let i := π 0
  let j := threeTerminalSwap i
  have hi : i ≠ 0 := by simpa [i, π] using h0
  have hπi : π i = 0 := by simpa [i, π] using h1
  have hπj : π j = j := twoReturn_permutation_fixed_swap π i rfl hi hπi
  have hj : j ≠ 0 := by
    intro hj0
    have heq : threeTerminalSwap i = threeTerminalSwap 0 := by
      simpa [j, threeTerminalSwap_zero] using hj0
    have hi0 := threeTerminalSwap.injective heq
    exact h0 (by simpa [i, π] using hi0)
  refine ⟨hj, ?_⟩
  rw [parafermionicCoverFiniteEdgeCutRoutingSuccessor, ite_eq_right he]
  simpa [π, j] using hπj

/-- The selected actual queried edge has endpoints at the seed port's primal
vertex and its actual open-pair port's primal vertex. -/
theorem parafermionicCoverFiniteEdgeCutSelectedEdge_eq_seedOpenPort_endpoints
    (n : ℕ) (hn : 1 ≤ n) (e : (ParafermionicAmbientGraph n).edgeSet) :
    e.1 = s(
      parafermionicCoverFinitePortPrimalVertex n
        (parafermionicCoverFiniteEdgeCutSeedPort n hn e),
      parafermionicCoverFinitePortPrimalVertex n
        (parafermionicCoverFiniteEdgeCutSeedOrbit n hn e).openPort) := by
  let seed := parafermionicCoverFiniteEdgeCutSeedPort n hn e
  let orbit := parafermionicCoverFiniteEdgeCutSeedOrbit n hn e
  have hseedmem := (parafermionicCoverFiniteEdgeCutSeedPort_spec n hn e).1
  have hseedEdge : parafermionicCoverPortEdge seed.1 =
      parafermionicCoverFiniteEdgeEmbedding n e := by
    simpa [seed, parafermionicCoverFiniteEdgeCutQueriedPorts] using hseedmem
  have hopen : parafermionicCoverPortVertex orbit.openPort.1 =
      parafermionicCoverPortOtherVertex seed.1 := by
    rw [orbit.open_eq, parafermionicCoverOpenPair_vertex]
  let f := parafermionicCoverBoxVertexEmbedding n
  let u := parafermionicCoverFinitePortPrimalVertex n seed
  let v := parafermionicCoverFinitePortPrimalVertex n orbit.openPort
  have hu : f u = parafermionicCoverPortVertex seed.1 := rfl
  have hv : f v = parafermionicCoverPortOtherVertex seed.1 := by
    change parafermionicCoverPortVertex orbit.openPort.1 = _
    exact hopen
  have hport : (parafermionicCoverFiniteEdgeEmbedding n e).1 =
      s(parafermionicCoverPortVertex seed.1,
        parafermionicCoverPortOtherVertex seed.1) := by
    calc
      (parafermionicCoverFiniteEdgeEmbedding n e).1 =
          (parafermionicCoverPortEdge seed.1).1 := congrArg Subtype.val hseedEdge.symm
      _ = s(parafermionicCoverPortVertex seed.1,
          parafermionicCoverPortOtherVertex seed.1) :=
        parafermionicCoverPortEdge_eq_incident_pair seed.1
  have hmap : Sym2.map f e.1 = s(f u, f v) := by
    calc
      Sym2.map f e.1 = (parafermionicCoverFiniteEdgeEmbedding n e).1 := rfl
      _ = s(parafermionicCoverPortVertex seed.1,
          parafermionicCoverPortOtherVertex seed.1) := hport
      _ = s(f u, f v) := by rw [← hu, ← hv]
  apply Sym2.map.injective f.injective
  simpa [u, v, f, Function.Embedding.sym2Map_apply] using hmap

end
end PottsContinuity.FKC.FiniteFK
