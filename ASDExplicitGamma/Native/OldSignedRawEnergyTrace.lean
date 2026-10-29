module

public import ASDExplicitGamma.Native.OldSignedComplementaryPhysicalField

/-! Complete normalized energy of the original physical q3 source modes,
including both source quarter-turn input loads. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ASDExplicitGamma.Model ASDExplicitGamma.Gaussian
open ASDExplicitGamma.Main ASDExplicitGamma.Response ASDExplicitGamma.Triadic
noncomputable section

/-- The actual scalar q3 mode energies sum to exactly one shell variance. -/
theorem old_signed_raw_scalar_energy_trace (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0 < l}) :
    HasSum (fun n : whiteBasisIndex => energy Q (q3Convolution b L h3Zero (whiteBasis n))) (b^2) := by
  let A := q3Section b L h3Zero
  have he : (fun x => ‖A x‖^2)=fun _ : Vec 2 => b^2 := by
    funext x
    exact old_signed_raw_white_norm_sq b L x
  have hI : Integrable (fun x => ‖A x‖^2) (normalizedCubeMeasure Q) := by
    rw [he]
    exact integrable_const _
  have hh := old_signed_white_energy_trace (normalizedCubeMeasure Q) whiteBasis A
    (q3Section_continuous b L h3Zero).aestronglyMeasurable hI
  rw [he,integral_const] at hh
  simpa only [A,q3Convolution,energy_eq_integral_sq,Measure.real_def,
    normalizedCubeMeasure_apply_univ,ENNReal.toReal_one,one_smul] using hh

/-- Both physical quarter-turn input loads have twice the scalar energy,
mode by mode, with no covariance limit involved. -/
theorem old_signed_rotated_raw_energy_sum (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0 < l}) (n : whiteBasisIndex) :
    (∑ i : Fin 2,∑ k : Fin 2,energy Q (fun x =>
      (q3Convolution b L h3Zero (whiteBasis n) x • mainFlatRotatedBasis i) k))=
      2*energy Q (q3Convolution b L h3Zero (whiteBasis n)) := by
  have hz : energy Q (fun _ : Vec 2 => (0:ℝ))=0 := by simp [energy,pairing,cubeAverage]
  simp only [Fin.sum_univ_two,old_signed_rotated_basis_zero,old_signed_rotated_basis_one]
  simp only [basisVec,Pi.single_apply,Pi.smul_apply,Pi.neg_apply,smul_eq_mul]
  norm_num
  simp only [hz,energy_neg]
  ring

/-- The complete actual two-load raw family has twice the shell variance. -/
theorem old_signed_rotated_raw_energy_trace (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0 < l}) :
    HasSum (fun n : whiteBasisIndex => ∑ i : Fin 2,∑ k : Fin 2,energy Q (fun x =>
      (q3Convolution b L h3Zero (whiteBasis n) x • mainFlatRotatedBasis i) k)) (2*b^2) :=
  ((old_signed_raw_scalar_energy_trace Q b L).mul_left 2).congr_fun
    (fun n => old_signed_rotated_raw_energy_sum Q b L n)

end
end ASDExplicitGamma.Native
