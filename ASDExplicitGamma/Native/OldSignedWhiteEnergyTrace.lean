module

public import ASDExplicitGamma.Native.OldSignedCovarianceIntegral
public import ASDExplicitGamma.Native.OldSignedProjectedKernelBounds
public import ASDExplicitGamma.Triadic.PoincareCell

/-! Exact complete-mode energy traces of the physical whole-plane fields,
with the source normalized spatial measure. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ASDExplicitGamma.Model ASDExplicitGamma.Gaussian
open ASDExplicitGamma.Triadic
noncomputable section

/-- Complete real white Parseval may be integrated under genuine L2 kernel
control, proved by quadratic dominated covariance passage. -/
theorem old_signed_white_energy_trace {X H I : Type*}
    [MeasurableSpace X] (mu : Measure X) [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] [Countable I]
    (e : HilbertBasis I ℝ H) (A : X → H) (hA : AEStronglyMeasurable A mu)
    (hI : Integrable (fun x => ‖A x‖^2) mu) :
    HasSum (fun n => ∫ x,inner ℝ (e n) (A x)^2 ∂mu) (∫ x,‖A x‖^2 ∂mu) := by
  have hi : Integrable (fun x => |(1:ℝ)| * (‖A x‖^2+‖A x‖^2)) mu := by
    have he : (fun x => |(1:ℝ)| * (‖A x‖^2+‖A x‖^2))=(fun x => (2:ℝ)*‖A x‖^2) := by
      funext x
      rw [abs_one,one_mul]
      ring
    rw [he]
    exact hI.const_mul 2
  have hs := old_signed_weighted_white_covariance mu e A A (fun _ => 1) hA hA
    aestronglyMeasurable_const hi
  simpa only [one_mul,pow_two,real_inner_self_eq_norm_sq] using hs

/-- Each physical projected matrix-entry mode has exactly the spectral
multiplier-square trace in normalized spatial energy. -/
theorem old_signed_projected_coordinate_energy_trace (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0 < l}) (i j : Fin 2) :
    HasSum (fun n : whiteBasisIndex => energy Q (fun x =>
      inner ℝ (whiteBasis n) (oldSignedProjectedWhiteKernel b L (L.1⁻¹ • x) i j)))
      (∫ xi,oldSignedHelmholtzEntry xi i j^2 ∂q3SpectralMeasure b) := by
  let A := fun x : Vec 2 => oldSignedProjectedWhiteKernel b L (L.1⁻¹ • x) i j
  have hx : Continuous (fun x : Vec 2 => L.1⁻¹ • x) := continuous_id.const_smul (L.1⁻¹)
  have hA : Continuous A := (old_signed_projected_white_continuous b L i j).comp hx
  have he : (fun x => ‖A x‖^2)=fun _ : Vec 2 =>
      ∫ xi,oldSignedHelmholtzEntry xi i j^2 ∂q3SpectralMeasure b := by
    funext x
    exact old_signed_projected_white_energy b L (L.1⁻¹ • x) i j
  have hI : Integrable (fun x => ‖A x‖^2) (normalizedCubeMeasure Q) := by
    rw [he]
    exact integrable_const _
  have hs := old_signed_white_energy_trace (normalizedCubeMeasure Q) whiteBasis A
    hA.aestronglyMeasurable hI
  rw [he,integral_const] at hs
  simpa only [energy_eq_integral_sq,A,Real.norm_eq_abs,sq_abs,
    Measure.real_def,normalizedCubeMeasure_apply_univ,ENNReal.toReal_one,one_smul] using hs

/-- The complete two-load, two-component whole-plane projected family has
exactly one shell variance of normalized spatial energy. -/
theorem old_signed_projected_total_spatial_energy_trace (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0 < l}) :
    HasSum (fun n : whiteBasisIndex => ∑ i : Fin 2,∑ j : Fin 2,energy Q (fun x =>
      inner ℝ (whiteBasis n) (oldSignedProjectedWhiteKernel b L (L.1⁻¹ • x) i j))) (b^2) := by
  have hs := hasSum_sum (s := Finset.univ) (fun i _ =>
    hasSum_sum (s := Finset.univ) (fun j _ => old_signed_projected_coordinate_energy_trace Q b L i j))
  have he := old_signed_projected_white_total_energy b L (0 : Vec 2)
  simp_rw [old_signed_projected_white_energy] at he
  rw [he] at hs
  exact hs

end
end ASDExplicitGamma.Native
