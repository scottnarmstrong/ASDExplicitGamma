module

public import ASDExplicitGamma.Native.HeatVHEATBracketRefinedSupportGeometry
public import ASDExplicitGamma.Native.Q3GridOverlapGen

/-! The depth-ten refined-grid overlap count for every shell offset, including
shells wider than the output square (no hypothesis `n ≤ 10`). -/

@[expose] public section

namespace ASDExplicitGamma.Native

open Homogenization ASDExplicitGamma.Triadic ASDExplicitGamma.Gaussian

theorem nativeHeatQ3RefinedGridSupportOverlap_card_ratio_le_Gen
    (Q : TriadicCube 2) (n : ℕ) (hn : 1 ≤ n)
    (L : {l : ℝ // 0 < l})
    (hL : L.1 / cubeScaleFactor Q = (q3GridKernelScale 10 n).1)
    (x : Vec 2) :
    ((nativeHeatQ3RefinedGridActiveFinset Q L x).card : ℝ) /
        ((Finset.univ : Finset (Fin (3 ^ 10) × Fin (3 ^ 10))).card : ℝ) ≤
      q3GridOverlapFactor 10 n := by
  classical
  have hfilter :
      nativeHeatQ3RefinedGridActiveFinset Q L x =
      q3GridActiveFinset 10 n
        (fun a => (x a - cubeCorner Q a) / cubeScaleFactor Q) := by
    ext ij
    simp only [nativeHeatQ3RefinedGridActiveFinset,
      q3GridActiveFinset, Finset.mem_filter, Finset.mem_univ, true_and]
    exact nativeHeatQ3RefinedGridExpandedSupport_mem_iff Q n L hL ij x
  rw [hfilter]
  have hden :
      ((Finset.univ : Finset (Fin (3 ^ 10) × Fin (3 ^ 10))).card : ℝ) =
        ((3 : ℝ) ^ 10) ^ 2 := by
    simp only [Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
      Nat.cast_mul, Nat.cast_pow]
    ring
  rw [hden]
  exact q3GridActiveFinset_card_ratio_le_Gen 10 n hn _

end ASDExplicitGamma.Native
