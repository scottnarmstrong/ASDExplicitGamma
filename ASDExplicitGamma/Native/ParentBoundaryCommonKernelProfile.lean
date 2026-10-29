module

public import ASDExplicitGamma.Native.ParentBoundaryCommonCoefficientSum

/-! The actual finite common-center heat coefficient has the source quartic profile. -/

@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Variational Gaussian Inverse Main Model Triadic Algsuperdiff.Section3
noncomputable section

/-- Exact source quartic kernel profile from the second/fourth covariance
clocks. A and B retain their distinct physical derivative trace constants. -/
def parentBoundaryCommonKernelProfile (A2 A4 z : ℝ) : ℝ :=
  (232/125:ℝ)*((Real.sqrt (39/5:ℝ)+(36/25:ℝ)*Real.sqrt (156/5:ℝ)*z)*Real.sqrt A2+
    (57/200:ℝ)*Real.sqrt (46488/25:ℝ)*z^2*Real.sqrt A4)^2+
  38*((Real.sqrt (39/5:ℝ)+(36/25:ℝ)*Real.sqrt (78/5:ℝ)*z)*Real.sqrt A2+
    (57/200:ℝ)*Real.sqrt (23244/25:ℝ)*z^2*Real.sqrt A4)^2

/-- Nonnegativity of the source kernel profile. -/
theorem parent_boundary_common_kernel_profile_nonneg (A2 A4 z : ℝ) :
    0 ≤ parentBoundaryCommonKernelProfile A2 A4 z := by
  unfold parentBoundaryCommonKernelProfile
  positivity

/-- The actual complete finite shell heat coefficient is controlled by
its exact second/fourth normalized spatial clocks and the source quartic
profile, with the true frame ratio retained. No covariance or clock cap
is assumed, and no shell-count factor is introduced. -/
theorem parent_boundary_common_shell_sum_kernel
    (M : ABKModel 2) (h : ℝ) (P Q : TriadicCube 2) (n : ℤ) (height : ℕ) :
    (∑ i : Fin height,parentBoundaryCommonShellCoefficient M h P Q n height i) ≤
      ((Annealed.sigmaBar M n:ℝ)/(Annealed.sigmaBar M Q.scale:ℝ))^2*
        parentBoundaryCommonKernelProfile (parentBoundaryCommonSpatialClock M h P n height 2)
          (parentBoundaryCommonSpatialClock M h P n height 4) (cubeScaleFactor Q/cubeScaleFactor P) := by
  let b := fun i : Fin height => q3ModelAmplitude M h (n+((i.val+1:ℕ):ℤ))/(Annealed.sigmaBar M n:ℝ)
  let L := fun i : Fin height => q3ModelLength (n+((i.val+1:ℕ):ℤ))
  let A := fun i : Fin height => parentBoundaryCommonRowCoefficient P Q (b i) (L i) 0
  let B := fun i : Fin height => b i*lemmaVH2Bn (cubeScaleFactor P/(L i).val) (diagMeshRadius Q 0/(L i).val)
  let z := cubeScaleFactor Q/cubeScaleFactor P
  let A2 := parentBoundaryCommonSpatialClock M h P n height 2
  let A4 := parentBoundaryCommonSpatialClock M h P n height 4
  let pa := (Real.sqrt (39/5:ℝ)+(36/25:ℝ)*Real.sqrt (156/5:ℝ)*z)*Real.sqrt A2+
    (57/200:ℝ)*Real.sqrt (46488/25:ℝ)*z^2*Real.sqrt A4
  let pb := (Real.sqrt (39/5:ℝ)+(36/25:ℝ)*Real.sqrt (78/5:ℝ)*z)*Real.sqrt A2+
    (57/200:ℝ)*Real.sqrt (23244/25:ℝ)*z^2*Real.sqrt A4
  have hA : Real.sqrt (∑ i,A i^2) ≤ pa := parent_boundary_common_band_row_norm_bound P Q b L
  have hB' := parent_boundary_common_band_bracket_norm_bound P Q b L
  have hBs : (∑ i : Fin height,B i^2)=
      (∑ i : Fin height,(|b i| *lemmaVH2Bn (cubeScaleFactor P/(L i).val) (diagMeshRadius Q 0/(L i).val))^2) := by
    apply Finset.sum_congr rfl
    intro i _
    dsimp only [B]
    rw [mul_pow,mul_pow,sq_abs]
  have hB : Real.sqrt (∑ i,B i^2) ≤ pb := by rw [hBs]; exact hB'
  have hAsq : (∑ i,A i^2) ≤ pa^2 := by
    have hh := pow_le_pow_left₀ (Real.sqrt_nonneg _) hA 2
    rw [Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg (A i)))] at hh
    exact hh
  have hBsq : (∑ i,B i^2) ≤ pb^2 := by
    have hh := pow_le_pow_left₀ (Real.sqrt_nonneg _) hB 2
    rw [Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg (B i)))] at hh
    exact hh
  rw [parent_boundary_common_shell_coefficient_sum]
  exact mul_le_mul_of_nonneg_left
    (add_le_add (mul_le_mul_of_nonneg_left hAsq (by norm_num))
      (mul_le_mul_of_nonneg_left hBsq (by norm_num))) (sq_nonneg _)

/-- The source profile is monotone in both nonnegative covariance clocks.
This permits insertion of the proved native shell clocks after the actual
finite covariance sum has been bounded. -/
theorem parent_boundary_common_kernel_profile_mono
    {A2 A4 B2 B4 z : ℝ} (h2 : A2 ≤ B2) (h4 : A4 ≤ B4) (hz : 0 ≤ z) :
    parentBoundaryCommonKernelProfile A2 A4 z ≤ parentBoundaryCommonKernelProfile B2 B4 z := by
  have hrow (c d : ℝ) (hc : 0 ≤ c) (hd : 0 ≤ d) :
      (c*Real.sqrt A2+d*Real.sqrt A4)^2 ≤ (c*Real.sqrt B2+d*Real.sqrt B4)^2 :=
    pow_le_pow_left₀ (add_nonneg (mul_nonneg hc (Real.sqrt_nonneg _)) (mul_nonneg hd (Real.sqrt_nonneg _)))
      (add_le_add (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt h2) hc)
        (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt h4) hd)) 2
  unfold parentBoundaryCommonKernelProfile
  exact add_le_add (mul_le_mul_of_nonneg_left (hrow _ _ (by positivity) (by positivity)) (by norm_num))
    (mul_le_mul_of_nonneg_left (hrow _ _ (by positivity) (by positivity)) (by norm_num))

end
end ASDExplicitGamma.Native
