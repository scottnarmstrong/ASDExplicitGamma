module

public import ASDExplicitGamma.Main.Q3ValueColumns
public import ASDExplicitGamma.Main.CubeDistanceMoment
public import ASDExplicitGamma.Main.HilbertCubeMean

/-! The exact centered covariance-column cap on the physical cell. -/

@[expose] public section
namespace ASDExplicitGamma.Main
open Homogenization MeasureTheory ASDExplicitGamma.Gaussian ASDExplicitGamma.Triadic

/-- A finite actual centered covariance column has squared norm at most
R² sigma²/3, where sigma² is the full two-coordinate derivative trace.
Spatial isotropy, the line-segment estimate and the cube moment are proved
internally; there is no frozen-source estimate premise. -/
theorem main_q3_centered_value_sq_le {ι : Type*} (e : HilbertBasis ι ℝ WhiteNoise)
    (s : Finset ι) (b : ℝ) (L : {l : ℝ // 0 < l}) (Q : TriadicCube 2)
    {x : Vec 2} (hx : x ∈ cubeSet Q) :
    ‖mainQ3FiniteValue e s b L x-hilbertCubeAverage Q (mainQ3FiniteValue e s b L)‖^2 ≤
      (cubeScaleFactor Q^2/3)*((156/5)*b^2/L.1^2) := by
  let f := mainQ3FiniteValue e s b L
  have hf : MemLp f 2 (normalizedCubeMeasure Q) :=
    (main_continuous_memLp_top Q (mainQ3FiniteValue_contDiff e s b L).continuous).mono_exponent
      (by simp : (2:ENNReal) ≤ ⊤)
  have hj := main_hilbert_centered_value_sq_le Q hf x
  have hdist : Integrable (mainSpatialDistanceSq x) (normalizedCubeMeasure Q) :=
    ((main_continuous_memLp_top Q (by unfold mainSpatialDistanceSq; fun_prop)).mono_exponent
      (by simp : (1:ENNReal) ≤ ⊤)).integrable (by norm_num)
  have hi := integral_mono_ae
    (((memLp_const (f x)).sub hf).integrable_norm_pow (by norm_num : 2 ≠ 0))
    (hdist.const_mul ((78/5)*b^2/L.1^2))
    (Filter.Eventually.of_forall (main_q3_value_difference_sq e s b L x))
  rw [integral_const_mul] at hi
  have hm := mul_le_mul_of_nonneg_left (main_cube_distance_moment_le Q hx)
    (by positivity : 0 ≤ (78/5:ℝ)*b^2/L.1^2)
  exact hj.trans (hi.trans (hm.trans_eq (by ring)))

end ASDExplicitGamma.Main
