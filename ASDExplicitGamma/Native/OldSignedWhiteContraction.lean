module

public import ASDExplicitGamma.Native.OldSignedWhiteProjectedKernel
public import ASDExplicitGamma.Inverse.PureFluxGeneratorActualQ3
public import ASDExplicitGamma.Gaussian.H3Centering

/-! Exact same-point contractions over every physical white mode. The
signed quarter-turn contraction is the bulk term in AN (2.2) and (6.3). -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ASDExplicitGamma.Model ASDExplicitGamma.Gaussian ASDExplicitGamma.Response
noncomputable section

/-- The integral of each unrotated Helmholtz entry is half the variance on
the diagonal and zero off the diagonal. -/
theorem old_signed_helmholtz_entry_integral (b : ℝ) (i j : Fin 2) :
    (∫ xi, oldSignedHelmholtzEntry xi i j ∂q3SpectralMeasure b) =
      (b^2/2)*(if i=j then 1 else 0) := by
  have hm := Main.main_q3SpectralHelmholtz_matrix_mean b
  fin_cases i <;> fin_cases j
  all_goals norm_num [oldSignedHelmholtzEntry,oldSignedFrequency]
  · simpa only [pow_two] using hm.1
  · exact hm.2.1
  · simpa only [mul_comm] using hm.2.1
  · simpa only [pow_two] using hm.2.2

/-- The whole-plane projected physical white kernel has exactly its source
same-point covariance with the unprojected kernel. -/
theorem old_signed_projected_white_point_covariance (b : ℝ) (L : {l : ℝ // 0 < l})
    (x : Vec 2) (i j : Fin 2) :
    inner ℝ (q3Section b L h3Zero (L.1 • x)) (oldSignedProjectedWhiteKernel b L x i j) =
      (b^2/2)*(if i=j then 1 else 0) :=
  (old_signed_projected_white_covariance b L x i j).trans (old_signed_helmholtz_entry_integral b i j)

/-- The kernel obtained by quarter-turning both the input and the output of
the whole-plane projection. Both quarter-turns retain the source orientation. -/
def oldSignedRotatedWhiteKernel (b : ℝ) (L : {l : ℝ // 0 < l})
    (x : Vec 2) (i j : Fin 2) : WhiteNoise :=
  ∑ a : Fin 2, ∑ c : Fin 2,
    (responsePlanarJ i a*responsePlanarJ c j) • oldSignedProjectedWhiteKernel b L x a c

/-- Exact real white-space contraction with the two signed quarter-turns. -/
theorem old_signed_rotated_white_point_covariance (b : ℝ) (L : {l : ℝ // 0 < l})
    (x : Vec 2) (i j : Fin 2) :
    inner ℝ (q3Section b L h3Zero (L.1 • x)) (oldSignedRotatedWhiteKernel b L x i j) =
      -(b^2/2)*(if i=j then 1 else 0) := by
  simp only [oldSignedRotatedWhiteKernel,inner_sum,real_inner_smul_right,
    old_signed_projected_white_point_covariance]
  fin_cases i <;> fin_cases j <;> norm_num [responsePlanarJ,Fin.sum_univ_two]

end
end ASDExplicitGamma.Native
