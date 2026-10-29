module

public import ASDExplicitGamma.Main.HilbertColumnProduct

/-! Jensen's inequality for the actual normalized Hilbert-valued cube mean. -/

@[expose] public section
namespace ASDExplicitGamma.Main
open Homogenization MeasureTheory ASDExplicitGamma.Triadic

/-- The root projection proves the genuine Hilbert mean-square inequality. -/
theorem main_hilbert_cube_mean_sq_le {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [CompleteSpace F] (Q : TriadicCube 2)
    {f : Vec 2 → F} (hf : MemLp f 2 (normalizedCubeMeasure Q)) :
    ‖hilbertCubeAverage Q f‖^2 ≤ hilbertEnergy Q f := by
  have he : hilbertEnergy Q (hilbertCubeProjection Q 0 f) = ‖hilbertCubeAverage Q f‖^2 := by
    unfold hilbertEnergy
    have ha : (fun x => ‖hilbertCubeProjection Q 0 f x‖^2) =ᵐ[normalizedCubeMeasure Q]
        (fun _ => ‖hilbertCubeAverage Q f‖^2) := by
      filter_upwards [hilbert_ae_cubeSet Q] with x hx
      rw [hilbertCubeProjection_eq_average Q 0 f (by simp) hx]
    rw [integral_congr_ae ha, integral_const]
    simp only [Measure.real_def, normalizedCubeMeasure_apply_univ, ENNReal.toReal_one, one_smul]
  rw [← he]
  exact hilbertEnergy_projection_le Q 0 hf

/-- The centered pointwise value is the mean of the genuine differences. -/
theorem main_hilbert_centered_value_sq_le {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [CompleteSpace F] (Q : TriadicCube 2)
    {f : Vec 2 → F} (hf : MemLp f 2 (normalizedCubeMeasure Q)) (x : Vec 2) :
    ‖f x-hilbertCubeAverage Q f‖^2 ≤
      ∫ y, ‖f x-f y‖^2 ∂normalizedCubeMeasure Q := by
  have h := main_hilbert_cube_mean_sq_le Q ((memLp_const (f x)).sub hf)
  have he : hilbertCubeAverage Q (fun y => f x-f y) = f x-hilbertCubeAverage Q f := by
    unfold hilbertCubeAverage
    rw [integral_sub (integrable_const _) (hf.integrable (by norm_num : (1:ENNReal) ≤ 2)), integral_const]
    simp only [Measure.real_def, normalizedCubeMeasure_apply_univ, ENNReal.toReal_one, one_smul]
  change ‖hilbertCubeAverage Q (fun y => f x-f y)‖^2 ≤
    ∫ y, ‖f x-f y‖^2 ∂normalizedCubeMeasure Q at h
  rwa [he] at h

end ASDExplicitGamma.Main
