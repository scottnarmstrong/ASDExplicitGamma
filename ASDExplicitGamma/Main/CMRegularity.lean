module

public import ASDExplicitGamma.Gaussian.Q3ConvolutionRegularity

/-! Classical spatial regularity of actual q3 covariance-factor directions. -/

@[expose] public section

namespace ASDExplicitGamma.Main

open Homogenization ASDExplicitGamma.Gaussian

/-- Each first derivative coordinate of a q3 covariance-factor direction
has a continuous classical derivative. -/
theorem main_q3_direction_contDiff_two (b : ℝ) (L : {l : ℝ // 0 < l}) (a : H3Index)
    (ha : a.1.1.val+a.1.2.val ≤ 1) (u : WhiteNoise) :
    ContDiff ℝ 2 (q3Convolution b L a u) := by
  have ha2 : a.1.1.val+a.1.2.val ≤ 2 := by omega
  have hn (i : Fin 2) :
      (h3Next a i ha2).1.1.val+(h3Next a i ha2).1.2.val ≤ 2 := by
    fin_cases i <;> simp only [h3Next] <;> split_ifs <;> simp_all <;> omega
  apply (contDiff_succ_iff_hasFDerivAt (n := 1)).mpr
  refine ⟨fun x =>
    q3Convolution b L (h3Next a 0 ha2) u x • (ContinuousLinearMap.proj 0 : Vec 2 →L[ℝ] ℝ) +
    q3Convolution b L (h3Next a 1 ha2) u x • (ContinuousLinearMap.proj 1 : Vec 2 →L[ℝ] ℝ), ?_, ?_⟩
  · exact ((q3Convolution_contDiff_one b L _ (hn 0) u).smul contDiff_const).add
      ((q3Convolution_contDiff_one b L _ (hn 1) u).smul contDiff_const)
  · exact q3Convolution_hasFDerivAt b L a ha2 u

/-- The actual value direction is C3, in particular C2 as needed by the
source multiplier products. No sample-path regularity premise is imposed. -/
theorem main_q3_value_direction_contDiff_three (b : ℝ) (L : {l : ℝ // 0 < l}) (u : WhiteNoise) :
    ContDiff ℝ 3 (q3Convolution b L h3Zero u) := by
  have hz : h3Zero.1.1.val+h3Zero.1.2.val ≤ 2 := by decide
  have hn (i : Fin 2) :
      (h3Next h3Zero i hz).1.1.val+(h3Next h3Zero i hz).1.2.val ≤ 1 := by
    fin_cases i <;> norm_num [h3Next, h3Zero]
  apply (contDiff_succ_iff_hasFDerivAt (n := 2)).mpr
  refine ⟨fun x =>
    q3Convolution b L (h3Next h3Zero 0 hz) u x • (ContinuousLinearMap.proj 0 : Vec 2 →L[ℝ] ℝ) +
    q3Convolution b L (h3Next h3Zero 1 hz) u x • (ContinuousLinearMap.proj 1 : Vec 2 →L[ℝ] ℝ), ?_, ?_⟩
  · exact ((main_q3_direction_contDiff_two b L _ (hn 0) u).smul contDiff_const).add
      ((main_q3_direction_contDiff_two b L _ (hn 1) u).smul contDiff_const)
  · exact q3Convolution_hasFDerivAt b L h3Zero hz u

end ASDExplicitGamma.Main
