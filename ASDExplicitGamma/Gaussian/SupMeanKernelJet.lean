module

public import ASDExplicitGamma.Gaussian.Q3ConvolutionRegularity
public import ASDExplicitGamma.Gaussian.SupMeanJetObservation

/-! The white-noise sections realize the literal scalar coordinate jets. -/
@[expose] public section
namespace ASDExplicitGamma.Gaussian
open Homogenization ASDExplicitGamma.Model
open scoped RealInnerProductSpace
noncomputable section

private theorem supMean_kernel_jet_count_le_two (o : Q3SpatialJet) (i : Fin 2) : o.count i ≤ 2 := by
  cases o with
  | value => norm_num [Q3SpatialJet.count]
  | first j => simp only [Q3SpatialJet.count]; split_ifs <;> omega
  | second j k => simp only [Q3SpatialJet.count]; split_ifs <;> omega

/-- The white-noise kernel index of each value, gradient or Hessian observation. -/
def supMeanKernelJetIndex (o : Q3SpatialJet) : H3Index :=
  ⟨(⟨o.count 0,by have hh := supMean_kernel_jet_count_le_two o 0; omega⟩,
    ⟨o.count 1,by have hh := supMean_kernel_jet_count_le_two o 1; omega⟩), by
      cases o with
      | value => norm_num [Q3SpatialJet.count]
      | first i => fin_cases i <;> norm_num [Q3SpatialJet.count]
      | second i j => fin_cases i <;> fin_cases j <;> norm_num [Q3SpatialJet.count]⟩

/-- The actual convolution has these ordinary coordinate derivatives globally. -/
theorem supMean_kernel_coordinate_derivative (β : ℝ) (L : {l : ℝ // 0 < l})
    (a : H3Index) (ha : a.1.1.val+a.1.2.val ≤ 2) (u : WhiteNoise) (x : Vec 2) (i : Fin 2) :
    supMeanCoordinateDerivative i (q3Convolution β L a u) x =
      q3Convolution β L (h3Next a i ha) u x := by
  have hl : HasDerivAt (fun t : ℝ => x+t • basisVec i) (basisVec i) 0 := by
    simpa only [id_eq, one_smul] using ((hasDerivAt_id (0:ℝ)).smul_const (basisVec i)).const_add x
  have hd := (q3Convolution_hasFDerivAt β L a ha u (x+(0:ℝ) • basisVec i)).comp_hasDerivAt (0:ℝ) hl
  simp only [zero_smul, add_zero, Function.comp_def] at hd
  change deriv (fun t : ℝ => q3Convolution β L a u (x+t • basisVec i)) 0 = _
  rw [hd.deriv]
  fin_cases i <;> norm_num [add_apply, smul_apply,
    ContinuousLinearMap.proj_apply, basisVec_apply, h3Next]

/-- Values, first derivatives and second derivatives of the deterministic
convolution are the corresponding Hilbert kernel coordinates. -/
theorem supMean_kernel_jet_observation (β : ℝ) (L : {l : ℝ // 0 < l})
    (o : Q3SpatialJet) (u : WhiteNoise) (x : Vec 2) :
    shellObservationApply (supMeanJetObservation o x) (q3Convolution β L h3Zero u) =
      q3Convolution β L (supMeanKernelJetIndex o) u x := by
  cases o with
  | value =>
    simp only [supMeanJetObservation, shellObservationApply]
    congr 1
  | first i =>
    change supMeanCoordinateDerivative i (q3Convolution β L h3Zero u) x = _
    rw [supMean_kernel_coordinate_derivative β L h3Zero (by norm_num [h3Zero])]
    congr 1
    fin_cases i <;> norm_num [h3Next, h3Zero, supMeanKernelJetIndex, Q3SpatialJet.count]
  | second i j =>
    rw [supMeanJetObservation, supMean_second_observation_apply]
    have hf : (fun z => supMeanCoordinateDerivative i (q3Convolution β L h3Zero u) z) =
        q3Convolution β L (h3Next h3Zero i (by norm_num [h3Zero])) u := by
      funext z
      exact supMean_kernel_coordinate_derivative β L h3Zero (by norm_num [h3Zero]) u z i
    rw [hf, supMean_kernel_coordinate_derivative β L _ (by
      fin_cases i <;> norm_num [h3Next, h3Zero])]
    congr 1
    fin_cases i <;> fin_cases j <;> norm_num [h3Next, h3Zero, supMeanKernelJetIndex, Q3SpatialJet.count]

end
end ASDExplicitGamma.Gaussian
