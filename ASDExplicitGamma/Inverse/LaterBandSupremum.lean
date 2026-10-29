module

public import ASDExplicitGamma.Inverse.LaterBandTensor
public import ASDExplicitGamma.Triadic.PlanarDirectionOperations

/-! Genuine essential-supremum derivative bounds for the actual later band,
with the exact full skew Frobenius factor sqrt(2). -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Model ASDExplicitGamma.Triadic
noncomputable section

/-- The actual half-open cube lies in the exact closed observation square. -/
theorem cube_subset_closed_observation (Q : TriadicCube 2) :
    cubeSet Q ⊆ supMeanClosedSquare (cubeCenter Q) (cubeScaleFactor Q) := by
  intro x hx d
  have hd := hx d
  change ((Q.index d:ℝ)-1/2)*(3:ℝ)^Q.scale ≤ x d ∧ x d < ((Q.index d:ℝ)+1/2)*(3:ℝ)^Q.scale at hd
  change |x d-(Q.index d:ℝ)*(3:ℝ)^Q.scale| ≤ (3:ℝ)^Q.scale/2
  rw [abs_le]
  constructor <;> linarith only [hd.1,hd.2]

/-- The Sobolev gradient supremum is paid by the full actual first-tensor
compact norms, on this same sample and this same physical cube. -/
theorem later_band_gradient_LInf_le (Q : TriadicCube 2) (n J : ℤ) (weights : ℤ → ℝ)
    (ω : Cutoff.CutoffSample 2) :
    Real.sqrt 2*planarGradientLInf (laterBandW2 Q n J weights ω) ≤
      ∑ k ∈ Finset.Ioc n J, |weights k| *
        ‖supMeanShellSquareTensor Q3SpatialJet.first (cubeCenter Q) (cubeScaleFactor Q) (ω.val k)‖ := by
  let B := ∑ k ∈ Finset.Ioc n J, |weights k| *
    ‖supMeanShellSquareTensor Q3SpatialJet.first (cubeCenter Q) (cubeScaleFactor Q) (ω.val k)‖
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hs : 0 < Real.sqrt (2:ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hh := planarW1ValueLInf_le_of_bound (laterBandW2 Q n J weights ω).gradient
    (div_nonneg hB hs.le) (by
      filter_upwards [normalized_cube_support Q] with x hx
      have hn := later_band_tensor_norm_le Q3SpatialJet.first n J weights ω
        (cubeCenter Q) (cubeScaleFactor Q) (cube_subset_closed_observation Q hx)
      rw [later_band_first_tensor_norm Q] at hn
      apply (le_div_iff₀ hs).mpr
      simpa only [mul_comm] using hn)
  change Real.sqrt 2*planarW1ValueLInf (laterBandW2 Q n J weights ω).gradient ≤ B
  calc
    _ ≤ Real.sqrt 2*(B/Real.sqrt 2) := mul_le_mul_of_nonneg_left hh hs.le
    _ = B := by field_simp

/-- The Sobolev Hessian supremum has the same exact compact tensor payment. -/
theorem later_band_hessian_LInf_le (Q : TriadicCube 2) (n J : ℤ) (weights : ℤ → ℝ)
    (ω : Cutoff.CutoffSample 2) :
    Real.sqrt 2*planarHessianFrobeniusLInf (laterBandW2 Q n J weights ω) ≤
      ∑ k ∈ Finset.Ioc n J, |weights k| *
        ‖supMeanShellSquareTensor (fun i : Fin 2 × Fin 2 => Q3SpatialJet.second i.1 i.2)
          (cubeCenter Q) (cubeScaleFactor Q) (ω.val k)‖ := by
  let B := ∑ k ∈ Finset.Ioc n J, |weights k| *
    ‖supMeanShellSquareTensor (fun i : Fin 2 × Fin 2 => Q3SpatialJet.second i.1 i.2)
      (cubeCenter Q) (cubeScaleFactor Q) (ω.val k)‖
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hs : 0 < Real.sqrt (2:ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hh := planarW1DerivativeFrobeniusLInf_le_of_bound (laterBandW2 Q n J weights ω).gradient
    (div_nonneg hB hs.le) (by
      filter_upwards [normalized_cube_support Q] with x hx
      have hn := later_band_tensor_norm_le (fun i : Fin 2 × Fin 2 => Q3SpatialJet.second i.1 i.2)
        n J weights ω (cubeCenter Q) (cubeScaleFactor Q) (cube_subset_closed_observation Q hx)
      rw [later_band_second_tensor_norm Q] at hn
      apply (le_div_iff₀ hs).mpr
      simpa only [mul_comm] using hn)
  change Real.sqrt 2*planarW1DerivativeFrobeniusLInf (laterBandW2 Q n J weights ω).gradient ≤ B
  calc
    _ ≤ Real.sqrt 2*(B/Real.sqrt 2) := mul_le_mul_of_nonneg_left hh hs.le
    _ = B := by field_simp

end
end ASDExplicitGamma.Inverse
