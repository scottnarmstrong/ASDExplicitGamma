module

public import ASDExplicitGamma.Inverse.StoppedWhitneyNeighborhood

/-! The stopped-chain induction establishes two-layer confinement before
lifting the whole component. No component finiteness is assumed. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization Algsuperdiff.Section3 Algsuperdiff.Section3.Provider
open Algsuperdiff.Section3.Provider.Whitney
noncomputable section

/-- Equal or neighboring occupied fine indices remain connected in the
actual induced graph, even when lifting collapses a touching step. -/
theorem fine_neighbor_reachable {O : Set BlockSite} {x y : O}
    (hxy : ∀ d, |y.val d-x.val d| ≤ 1) : (fineGraph.induce O).Reachable x y := by
  by_cases he : x.val = y.val
  · have hh : x = y := Subtype.ext he
    rw [hh]
  · exact SimpleGraph.Adj.reachable ⟨he,fun d => (hxy d).trans (by norm_num)⟩

end
end ASDExplicitGamma.Inverse
