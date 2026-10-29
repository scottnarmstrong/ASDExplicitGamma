module

public import ASDExplicitGamma.Main.PathwiseHessianSignedCovariance
public import ASDExplicitGamma.Main.Q3ResidualCoordinates
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! Apply the exact signed q3 contraction to the actual localized DIAG gradients. -/

@[expose] public section

namespace ASDExplicitGamma.Main

open Homogenization ASDExplicitGamma.Gaussian ASDExplicitGamma.Native
  ASDExplicitGamma.Triadic ASDExplicitGamma.Variational MeasureTheory

noncomputable def mainDiagQ3SignedLocalizedGradientTerm
    (b : ℝ) (L : {l : ℝ // 0 < l}) (Q : TriadicCube 2) (mesh : ℕ)
    (φ : H1Function (openCubeSet Q)) (k : ℕ) (x : Vec 2) : ℝ :=
  q3Convolution b L h3Zero (gaussEnumerated whiteBasis k) x *
    inner ℝ (gaussEnumerated whiteBasis k)
      (∑ i : Fin 2, ∑ j : Fin 2,
        ((diagInterpolant Q mesh φ).grad x i *
          (φ - diagInterpolant Q mesh φ).grad x j) •
          oldSignedRotatedWhiteKernel b L (L.1⁻¹ • x) i j)

/-- The signed whole-plane q3 covariance cancellation with the actual
interpolant-gradient and zero-trace residual-gradient fields from the
localized DIAG trial. This is the pointwise signed input before its spatial
pairing and hot-patch error assembly. -/
theorem main_diag_q3_signed_localized_gradient_covariance
    (b : ℝ) (L : {l : ℝ // 0 < l}) (Q : TriadicCube 2) (mesh : ℕ)
    (φ : H1Function (openCubeSet Q)) (x : Vec 2) :
    let I := diagInterpolant Q mesh
    (∑' k : ℕ,
      q3Convolution b L h3Zero (gaussEnumerated whiteBasis k) x *
        inner ℝ (gaussEnumerated whiteBasis k)
          (∑ i : Fin 2, ∑ j : Fin 2,
            ((I φ).grad x i * (φ - I φ).grad x j) •
              oldSignedRotatedWhiteKernel b L (L.1⁻¹ • x) i j)) =
      -(b ^ 2 / 2) *
        (∑ i : Fin 2, (I φ).grad x i * (φ - I φ).grad x i) := by
  dsimp only
  exact main_q3_signed_projected_vector_covariance_enumerated b L x
    ((diagInterpolant Q mesh φ).grad x) ((φ - diagInterpolant Q mesh φ).grad x)

/-- Under the explicit `L¹` summability conditions required by Bochner Fubini,
the localized pointwise signed contraction also holds after integrating on a
source cell. This is the spatial-pairing interface for the pathwise trial. -/
theorem main_diag_q3_signed_localized_gradient_covariance_integral
    (b : ℝ) (L : {l : ℝ // 0 < l}) (Q : TriadicCube 2) (mesh : ℕ)
    (φ : H1Function (openCubeSet Q)) (U : TriadicCube 2)
    (hint : ∀ k : ℕ,
      Integrable (fun x => mainDiagQ3SignedLocalizedGradientTerm b L Q mesh φ k x)
        (normalizedCubeMeasure U))
    (hnorm : Summable (fun k : ℕ =>
      ∫ x, ‖mainDiagQ3SignedLocalizedGradientTerm b L Q mesh φ k x‖
        ∂(normalizedCubeMeasure U))) :
    (∑' k : ℕ,
      ∫ x, mainDiagQ3SignedLocalizedGradientTerm b L Q mesh φ k x
        ∂(normalizedCubeMeasure U)) =
      ∫ x, -(b ^ 2 / 2) *
        (∑ i : Fin 2, (diagInterpolant Q mesh φ).grad x i *
          (φ - diagInterpolant Q mesh φ).grad x i)
        ∂(normalizedCubeMeasure U) := by
  rw [integral_tsum_of_summable_integral_norm hint hnorm]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    simpa only [mainDiagQ3SignedLocalizedGradientTerm] using
      main_diag_q3_signed_localized_gradient_covariance b L Q mesh φ x

end ASDExplicitGamma.Main
