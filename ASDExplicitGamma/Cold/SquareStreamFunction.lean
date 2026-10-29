module

public import ASDExplicitGamma.Cold.SquareStreamCoefficients

/-! # A mean-zero stream function for every divergence-free L² field on the square -/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology Homogenization
open ASDExplicitGamma.Triadic ASDExplicitGamma.Triadic.Torus
open scoped BigOperators ENNReal

namespace ASDExplicitGamma.Cold

/-- The weak Poincaré lemma on the square, proved from the actual gradient projection
and the complete mixed Fourier bases. The mode condition is used only as an intermediate
characterization; the stream theorem below derives it from distributional divergence. -/
theorem square_exists_potential_of_curl_coeff (Q : TriadicCube 2) {F : Vec 2 → Vec 2}
    (hF : MemVectorL2 (openCubeSet Q) F)
    (hcurl : ∀ p, cubeFreq Q p 1 * squareVectorCoeff Q F 0 p -
      cubeFreq Q p 0 * squareVectorCoeff Q F 1 p = 0) :
    ∃ w : H1Function (openCubeSet Q), MeanZeroOn (openCubeSet Q) w.toFun ∧
      w.grad =ᵐ[volume.restrict (openCubeSet Q)] F := by
  let hC := h1CoerciveEstimate_of_isOpenBoundedConvexDomain
    (isOpenBoundedConvexDomain_openCubeSet Q)
  let u := H1MeanZeroFunction.gradientProblemSolution hF hC
  let r : Vec 2 → Vec 2 := fun x => F x - u.toH1Function.grad x
  have hFn (i : Fin 2) := memLp_normalized_of_memL2On (hF.eval i)
  have hun (i : Fin 2) := memLp_normalized_of_memL2On (u.toH1Function.gradMemL2 i)
  have hrn (i : Fin 2) : MemLp (fun x => r x i) 2 (normalizedCubeMeasure Q) :=
    (hFn i).sub (hun i)
  have hdivr (p : Fin 2 → ℤ) : cubeFreq Q p 0 * squareVectorCoeff Q r 0 p +
      cubeFreq Q p 1 * squareVectorCoeff Q r 1 p = 0 := by
    dsimp only [r]
    rw [squareVectorCoeff_sub Q hFn hun, squareVectorCoeff_sub Q hFn hun]
    exact square_projection_div_coeff Q hF hC p
  have hcurlr (p : Fin 2 → ℤ) : cubeFreq Q p 1 * squareVectorCoeff Q r 0 p -
      cubeFreq Q p 0 * squareVectorCoeff Q r 1 p = 0 := by
    dsimp only [r]
    rw [squareVectorCoeff_sub Q hFn hun, squareVectorCoeff_sub Q hFn hun,
      squareVectorCoeff_grad, squareVectorCoeff_grad]
    linear_combination hcurl p
  have hrzero := square_vector_ae_zero_of_div_curl Q hrn hdivr hcurlr
  refine ⟨u.toH1Function, u.meanZero, ?_⟩
  apply (square_ae_normalized_iff Q).mp
  filter_upwards [hrzero] with x hx
  exact (sub_eq_zero.mp hx).symm

/-- Positive quarter-turn in the oriented plane. -/
def squareQuarterTurn (v : Vec 2) : Vec 2 := ![-v 1, v 0]

/-- CO-PLATEAU-STREAM-FUNCTION. Distributional divergence is expressed in the standard
weak H¹₀ test form. Every such L² flux has a mean-zero H¹ stream function; the identity is
a.e., as appropriate for L² fields. No boundary condition on the flux is imposed. -/
theorem square_stream_function (Q : TriadicCube 2) {j : Vec 2 → Vec 2}
    (hj : MemVectorL2 (openCubeSet Q) j) (hdiv : IsSolenoidalOn (openCubeSet Q) j) :
    ∃ w : H1Function (openCubeSet Q), MeanZeroOn (openCubeSet Q) w.toFun ∧
      j =ᵐ[volume.restrict (openCubeSet Q)] (fun x => squareQuarterTurn (w.grad x)) := by
  let F : Vec 2 → Vec 2 := fun x => ![j x 1, -j x 0]
  have hF : MemVectorL2 (openCubeSet Q) F := by
    apply MemLp.of_eval
    intro i
    fin_cases i
    · exact hj.eval 1
    · exact (hj.eval 0).neg
  have hjn (i : Fin 2) := memLp_normalized_of_memL2On (hj.eval i)
  have hcurl (p : Fin 2 → ℤ) : cubeFreq Q p 1 * squareVectorCoeff Q F 0 p -
      cubeFreq Q p 0 * squareVectorCoeff Q F 1 p = 0 := by
    have hid := square_solenoidal_sine_coeff Q hjn hdiv p
    have h0 : squareVectorCoeff Q F 0 p =
        ∫ x, cubeSin Q 0 p x * j x 1 ∂normalizedCubeMeasure Q := rfl
    have h1 : squareVectorCoeff Q F 1 p =
        -(∫ x, cubeSin Q 1 p x * j x 0 ∂normalizedCubeMeasure Q) := by
      unfold squareVectorCoeff
      simp only [F, Matrix.cons_val_one, Matrix.cons_val_zero, mul_neg, integral_neg]
    rw [h0, h1]
    linear_combination hid
  obtain ⟨w, hwmean, hwgrad⟩ := square_exists_potential_of_curl_coeff Q hF hcurl
  refine ⟨w, hwmean, ?_⟩
  filter_upwards [hwgrad] with x hx
  ext i
  fin_cases i
  · change j x 0 = -w.grad x 1
    have h1 : w.grad x 1 = -j x 0 := congrFun hx 1
    linarith only [h1]
  · change j x 1 = w.grad x 0
    have h0 : w.grad x 0 = j x 1 := congrFun hx 0
    exact h0.symm

end ASDExplicitGamma.Cold
