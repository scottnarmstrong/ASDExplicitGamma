module

public import ASDExplicitGamma.Cold.SquareStreamSpectral

/-! # Projection and divergence identities used by the square stream-function proof -/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology Homogenization
open ASDExplicitGamma.Triadic ASDExplicitGamma.Triadic.Torus
open scoped BigOperators ENNReal

namespace ASDExplicitGamma.Cold

/-- The square has finite Lebesgue measure, as required by the mean-zero solver. -/
instance instColdSquareFiniteMeasure (Q : TriadicCube 2) :
    IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) := by
  simpa only [volumeMeasureOn] using
    (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume

/-- Coefficients of an actual H¹ gradient. -/
theorem squareVectorCoeff_grad (Q : TriadicCube 2) (u : H1Function (openCubeSet Q))
    (i : Fin 2) (p : Fin 2 → ℤ) :
    squareVectorCoeff Q u.grad i p =
      -cubeFreq Q p i * ∫ x, cubeCos Q p x * u.toFun x ∂normalizedCubeMeasure Q :=
  h1_sine_derivative_coefficient Q u i p

/-- Coefficients respect subtraction of L² fields. -/
theorem squareVectorCoeff_sub (Q : TriadicCube 2) {F G : Vec 2 → Vec 2}
    (hF : ∀ i, MemLp (fun x => F x i) 2 (normalizedCubeMeasure Q))
    (hG : ∀ i, MemLp (fun x => G x i) 2 (normalizedCubeMeasure Q))
    (i : Fin 2) (p : Fin 2 → ℤ) :
    squareVectorCoeff Q (fun x => F x - G x) i p =
      squareVectorCoeff Q F i p - squareVectorCoeff Q G i p := by
  have hiF := memLp_mode_mul (m := cubeSin Q i p) (hF i)
    (continuous_boxMode _ _ _ _) (abs_boxMode_le _ _ _ _)
  have hiG := memLp_mode_mul (m := cubeSin Q i p) (hG i)
    (continuous_boxMode _ _ _ _) (abs_boxMode_le _ _ _ _)
  unfold squareVectorCoeff
  simp only [Pi.sub_apply, mul_sub]
  rw [integral_sub hiF hiG]

/-- Testing a vector field against a cosine gradient gives its divergence coefficients. -/
theorem integral_vecDot_cos_grad (Q : TriadicCube 2) {F : Vec 2 → Vec 2}
    (hF : ∀ i, MemLp (fun x => F x i) 2 (normalizedCubeMeasure Q)) (p : Fin 2 → ℤ) :
    ∫ x, vecDot (F x) ((cubeCosH1 Q p).grad x) ∂normalizedCubeMeasure Q =
      -cubeFreq Q p 0 * squareVectorCoeff Q F 0 p -
        cubeFreq Q p 1 * squareVectorCoeff Q F 1 p := by
  have hi0 := (memLp_mode_mul (m := cubeSin Q 0 p) (hF 0)
    (continuous_boxMode _ _ _ _) (abs_boxMode_le _ _ _ _)).const_mul (-cubeFreq Q p 0)
  have hi1 := (memLp_mode_mul (m := cubeSin Q 1 p) (hF 1)
    (continuous_boxMode _ _ _ _) (abs_boxMode_le _ _ _ _)).const_mul (-cubeFreq Q p 1)
  have heq : (fun x => vecDot (F x) ((cubeCosH1 Q p).grad x)) =
      (fun x => -cubeFreq Q p 0 * (cubeSin Q 0 p x * F x 0) +
        -cubeFreq Q p 1 * (cubeSin Q 1 p x * F x 1)) := by
    funext x
    simp only [vecDot, Fin.sum_univ_two, cubeCosH1_grad]
    ring
  rw [heq, integral_add hi0 hi1, integral_const_mul, integral_const_mul]
  unfold squareVectorCoeff
  ring

/-- A cosine gradient test of the variational projection gives the first residual equation. -/
theorem square_projection_div_coeff (Q : TriadicCube 2) {F : Vec 2 → Vec 2}
    (hF : MemVectorL2 (openCubeSet Q) F) (hC : H1CoerciveEstimate (openCubeSet Q))
    (p : Fin 2 → ℤ) :
    let u := H1MeanZeroFunction.gradientProblemSolution hF hC
    cubeFreq Q p 0 * (squareVectorCoeff Q F 0 p - squareVectorCoeff Q u.toH1Function.grad 0 p) +
      cubeFreq Q p 1 * (squareVectorCoeff Q F 1 p - squareVectorCoeff Q u.toH1Function.grad 1 p) = 0 := by
  let u := H1MeanZeroFunction.gradientProblemSolution hF hC
  have hvar := H1Function.gradientProblemSolution_firstVariation_eq_integral hF hC (cubeCosH1 Q p)
  have hnorm : ∫ x, vecDot (u.toH1Function.grad x) ((cubeCosH1 Q p).grad x)
      ∂normalizedCubeMeasure Q =
      ∫ x, vecDot (F x) ((cubeCosH1 Q p).grad x) ∂normalizedCubeMeasure Q := by
    rw [integral_normalized_eq_open, integral_normalized_eq_open]
    exact congrArg (fun t : ℝ => (cubeVolume Q)⁻¹ * t) hvar
  have hFn (i : Fin 2) := memLp_normalized_of_memL2On (hF.eval i)
  have hun (i : Fin 2) := memLp_normalized_of_memL2On (u.toH1Function.gradMemL2 i)
  rw [integral_vecDot_cos_grad Q hun, integral_vecDot_cos_grad Q hFn] at hnorm
  dsimp only
  change cubeFreq Q p 0 * (squareVectorCoeff Q F 0 p - squareVectorCoeff Q u.toH1Function.grad 0 p) +
    cubeFreq Q p 1 * (squareVectorCoeff Q F 1 p - squareVectorCoeff Q u.toH1Function.grad 1 p) = 0
  linear_combination hnorm

/-- Passing a null-set assertion between Lebesgue and normalized measure on the square. -/
theorem square_ae_normalized_iff (Q : TriadicCube 2) {P : Vec 2 → Prop} :
    (∀ᵐ x ∂normalizedCubeMeasure Q, P x) ↔ ∀ᵐ x ∂volume.restrict (openCubeSet Q), P x := by
  rw [normalizedCubeMeasure, cubeMeasure,
    Measure.ae_ennreal_smul_measure_iff (by
      exact ne_of_gt (ENNReal.ofReal_pos.mpr (inv_pos.mpr (cubeVolume_pos Q)))),
    volume_restrict_cubeSet_eq_volume_restrict_openCubeSet]

/-- The sine/sine divergence test is valid for every divergence-free L² field. -/
theorem square_solenoidal_sine_coeff (Q : TriadicCube 2) {j : Vec 2 → Vec 2}
    (hj : ∀ i, MemLp (fun x => j x i) 2 (normalizedCubeMeasure Q))
    (hdiv : IsSolenoidalOn (openCubeSet Q) j) (p : Fin 2 → ℤ) :
    cubeFreq Q p 0 * (∫ x, cubeSin Q 1 p x * j x 0 ∂normalizedCubeMeasure Q) +
      cubeFreq Q p 1 * (∫ x, cubeSin Q 0 p x * j x 1 ∂normalizedCubeMeasure Q) = 0 := by
  have hn : ∫ x, vecDot (j x) ((squareSineH10 Q p).toH1Function.grad x)
      ∂normalizedCubeMeasure Q = 0 := by
    rw [integral_normalized_eq_open, hdiv (squareSineH10 Q p), mul_zero]
  have hg0 := (square_ae_normalized_iff Q).mpr (squareSineH10_grad Q p 0)
  have hg1 := (square_ae_normalized_iff Q).mpr (squareSineH10_grad Q p 1)
  have heq : ∫ x, vecDot (j x) ((squareSineH10 Q p).toH1Function.grad x)
      ∂normalizedCubeMeasure Q =
      ∫ x, cubeFreq Q p 0 * (cubeSin Q 1 p x * j x 0) +
        cubeFreq Q p 1 * (cubeSin Q 0 p x * j x 1) ∂normalizedCubeMeasure Q := by
    apply integral_congr_ae
    filter_upwards [hg0, hg1] with x hx0 hx1
    simp only [vecDot, Fin.sum_univ_two, hx0, hx1]
    have hs0 : (Finset.univ : Finset (Fin 2)).erase 0 = {1} := by decide
    have hs1 : (Finset.univ : Finset (Fin 2)).erase 1 = {0} := by decide
    rw [hs0, hs1]
    unfold cubeSin
    ring
  have hi0 := (memLp_mode_mul (m := cubeSin Q 1 p) (hj 0)
    (continuous_boxMode _ _ _ _) (abs_boxMode_le _ _ _ _)).const_mul (cubeFreq Q p 0)
  have hi1 := (memLp_mode_mul (m := cubeSin Q 0 p) (hj 1)
    (continuous_boxMode _ _ _ _) (abs_boxMode_le _ _ _ _)).const_mul (cubeFreq Q p 1)
  rw [heq, integral_add hi0 hi1, integral_const_mul, integral_const_mul] at hn
  exact hn

end ASDExplicitGamma.Cold
