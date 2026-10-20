module

public import PottsContinuity.Thm3.Prop4.TiltedWindow
public import PottsContinuity.Thm3.RSW.EmbeddedComparison
public import PottsContinuity.PD.FK.BoundaryPartitionLaw

/-!
# Intrinsic-top comparison for tilted box windows

Specializes the RSW.StripMonotone argument to actual tilted windows.
The top property is intrinsic to the infinite strip, so pulling its partition
back to an inner window gives exactly its intrinsic-top partition. Artificial
box-side wiring is intentionally excluded from this equality.
-/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4

open PD.FK PD.FK.FiniteProbability

noncomputable section

local instance tiltedMonotoneEdgeFintype (n m : ℕ) (t : ℝ) :
    Fintype (squareLattice.induce (tiltedWindow n m t : Set (ℤ × ℤ))).edgeSet :=
  Fintype.ofFinite _

/-- Literal inclusion of all original vertices of an inner tilted window. -/
def tiltedWindowEmbedding {n M N : ℕ} {t : ℝ} (hMN : M ≤ N) :
    (tiltedWindow n M t : Set (ℤ × ℤ)) ↪ (tiltedWindow n N t : Set (ℤ × ℤ)) where
  toFun v := ⟨v.1, tiltedWindow_mono n t hMN v.2⟩
  inj' := fun _ _ h => Subtype.ext
    (congrArg (fun w : (tiltedWindow n N t : Set (ℤ × ℤ)) => w.val) h)

/-- Every original edge is retained by the induced-graph inclusion. -/
theorem tiltedWindow_map_le {n M N : ℕ} {t : ℝ} (hMN : M ≤ N) :
    (squareLattice.induce (tiltedWindow n M t : Set (ℤ × ℤ))).map
        (tiltedWindowEmbedding (n := n) (t := t) hMN) ≤
      squareLattice.induce (tiltedWindow n N t : Set (ℤ × ℤ)) := by
  rw [SimpleGraph.map_le_iff_le_comap]
  intro u v huv
  exact huv

/-- Exact intrinsic-top partition pullback, valid at every real slope. -/
theorem tiltedWindow_top_pullback_partition {n M N : ℕ} {t : ℝ} (hMN : M ≤ N) :
    (isolatedExtensionPullbackBoundary (tiltedWindowEmbedding (n := n) (t := t) hMN)
      (tiltedWindowBoundary n N t 0)).partition =
        (tiltedWindowBoundary n M t 0).partition := by
  apply Setoid.ext
  intro u v
  change (tiltedWindowEmbedding hMN u = tiltedWindowEmbedding hMN v ∨
    tiltedWindowEmbedding hMN u ∈ tiltedWindowWiredVertices n N t 0 ∧
      tiltedWindowEmbedding hMN v ∈ tiltedWindowWiredVertices n N t 0) ↔
    (u = v ∨ u ∈ tiltedWindowWiredVertices n M t 0 ∧
      v ∈ tiltedWindowWiredVertices n M t 0)
  simp only [tiltedWindowWiredVertices, Set.mem_ofPred_eq, Fin.zero_ne_one,
    false_and, or_false]
  constructor
  · rintro (h | ⟨hu, hv⟩)
    · exact Or.inl ((tiltedWindowEmbedding hMN).injective h)
    · exact Or.inr ⟨hu, hv⟩
  · rintro (h | ⟨hu, hv⟩)
    · exact Or.inl (congrArg (tiltedWindowEmbedding hMN) h)
    · exact Or.inr ⟨hu, hv⟩

end

end PottsContinuity.Thm3.Prop4
