module

public import ASDExplicitGamma.Gaussian.Q3Directions
public import ASDExplicitGamma.Inverse.PureFluxGeneratorHistory

/-! The physical full-shell bracket with its complete source-history maximum. -/

@[expose] public section
namespace ASDExplicitGamma.Gaussian
open Homogenization MeasureTheory ASDExplicitGamma.Inverse ASDExplicitGamma.Main
  ASDExplicitGamma.Response ASDExplicitGamma.Triadic ASDExplicitGamma.Variational
  ASDExplicitGamma.Model
noncomputable section

/-- The complete source history dominates the harmonic history used by
the closed Lemma V bracket, on every cell of the same aligned tiling. -/
theorem tile_history_le_source_history (Q : TriadicCube 2) (j : ℕ)
    (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (k : ResponseCoefficient (openCubeSet Q)) :
    lemmaVTileHistory Q j (responseFramePlanarCoefficientField ν σ k) ≤
      pureFluxSourceTileHistory Q j (responseFramePlanarCoefficientField ν σ k) := by
  let a := responseFramePlanarCoefficientField ν σ k
  have hEll := responseFramePlanarCoefficientField_isElliptic
    (measurableSet_openCubeSet Q) ν σ hν hσ k
  have hqSqrt : 1 < Real.sqrt 3 := by
    nlinarith only [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), Real.sqrt_nonneg (3 : ℝ)]
  have hqQuarter : 1 < (3 : ℝ) ^ (1 / 4 : ℝ) :=
    Real.one_lt_rpow (by norm_num) (by norm_num)
  have hqCompare : (3 : ℝ) ^ (1 / 4 : ℝ) ≤ Real.sqrt 3 := by
    calc
      (3 : ℝ) ^ (1 / 4 : ℝ) ≤ (3 : ℝ) ^ (1 / 2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = Real.sqrt 3 := (Real.sqrt_eq_rpow 3).symm
  have hinv : (Real.sqrt 3)⁻¹ ≤ ((3 : ℝ) ^ (1 / 4 : ℝ))⁻¹ :=
    (inv_le_inv₀ (by positivity) (by positivity)).mpr hqCompare
  apply Book.Ch02.finsetSupReal_le _ (descendantsAtDepth_nonempty Q j)
  intro R hR
  have hEllR := hEll.mono (measurableSet_openCubeSet R)
    (openCubeSet_subset_of_mem_descendantsAtDepth hR)
  exact (lemmaVInverseHistory_le_of_inverse_discount R hEllR hqSqrt hqQuarter hinv).trans
    (pureFlux_source_tile_history_member_le Q j a R hR)

end
end ASDExplicitGamma.Gaussian
