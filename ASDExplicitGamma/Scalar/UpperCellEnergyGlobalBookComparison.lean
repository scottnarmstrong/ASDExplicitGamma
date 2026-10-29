module

public import ASDExplicitGamma.Scalar.UpperCellEnergyPhysicalOldBook
public import ASDExplicitGamma.Scalar.UpperCellEnergyScaledEnvelope
public import ASDExplicitGamma.Scalar.UpperCellEnergyBandDepthComparison

/-! The all-depth comparison for the actual OLD cutoff and actual fresh band,
with every local-smallness and OLD norm premise discharged. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Response Variational Triadic Inverse Algsuperdiff.Section3
noncomputable section

/-- Global centered Book comparison from actual physical data only, on every
sample and for every doubled load, without a small-event hypothesis. -/
theorem upper_cell_global_book_comparison
    (M : ABKModel 2) (n ell : ℤ) (height : ℕ) (ω : Cutoff.CutoffSample 2) :
    let Q := originCube 2 (n-ell)
    let sigma := (Annealed.sigmaBar M n:ℝ)
    let k := sigma⁻¹ • oldCutoffSkewCoefficient n Q ω
    let kH := laterResponseCoefficient Q n (n+(height:ℤ)) (fun _ => sigma⁻¹) ω
    let h := laterBandW2 Q n (n+(height:ℤ)) (fun _ => sigma⁻¹) ω
    let F := upperCellBandEnvelope (upperCellPhysicalBandLabel n height)
      (fun _ => sigma⁻¹) (cubeCenter Q) (cubeScaleFactor Q) (cubeScaleFactor Q) ((cubeScaleFactor Q)^2) ω
    let A := 1+2*(lagTraceHistory M n ell ω).toReal+Real.sqrt (2*(lagTraceHistory M n ell ω).toReal)
    ∀ P : BlockVec 2,
      blockVecDot P (blockMatVecMul
        (Book.Ch02.coarseBlockMatrix (Book.Ch02.cubeDomain Q)
          (sensitivityBookCoeffOn Q (M.nu/sigma) (div_pos M.nu_pos (Annealed.sigmaBar M n).property)
            (sensitivityResponseCoefficientPath k
              (kH+BoundedContinuousFunction.const (closure (openCubeSet Q))
                (-(cubeAverage Q h.value.toFun))) 1))) P) ≤
        A*(1+3*A*F)*(1+2*F+4*F^2)*blockVecDot P P := by
  dsimp only
  let Q := originCube 2 (n-ell)
  let sigma := (Annealed.sigmaBar M n:ℝ)
  let k := sigma⁻¹ • oldCutoffSkewCoefficient n Q ω
  let kH := laterResponseCoefficient Q n (n+(height:ℤ)) (fun _ => sigma⁻¹) ω
  let h := laterBandW2 Q n (n+(height:ℤ)) (fun _ => sigma⁻¹) ω
  let F := upperCellBandEnvelope (upperCellPhysicalBandLabel n height)
    (fun _ => sigma⁻¹) (cubeCenter Q) (cubeScaleFactor Q) (cubeScaleFactor Q) ((cubeScaleFactor Q)^2) ω
  let A := 1+2*(lagTraceHistory M n ell ω).toReal+Real.sqrt (2*(lagTraceHistory M n ell ω).toReal)
  let hp := div_pos M.nu_pos (Annealed.sigmaBar M n).property
  let theta := sensitivityPathLambdaInverse (M.nu/sigma) hp k kH (1/4) 0
  let x := sensitivityDsharp Q h * theta
  have hF : 0≤F := upper_cell_band_envelope_nonneg _ _ _ _ _ _
    (Homogenization.cubeScaleFactor_pos' Q).le (sq_nonneg _) ω
  have hA : 0≤A := by dsimp [A]; positivity
  have ht : 0≤theta := sensitivityPathLambdaInverse_nonneg _ hp k kH (by norm_num) 0
  have hx : 0≤x := mul_nonneg (sensitivityDsharp_nonneg Q h) ht
  have hxA : x≤A*F := by
    have hd := upper_cell_band_Dsharp_le_envelope Q n height (fun _ => sigma⁻¹) ω
    have htheta := upper_cell_physical_initial_lambda_majorant M n ell ω kH
    exact (mul_le_mul hd htheta ht hF).trans_eq (mul_comm F A)
  intro P
  let C := A*(1+2*F+4*F^2)*blockVecDot P P
  have hC : 0≤C := mul_nonneg (mul_nonneg hA (by positivity)) (blockVecDot_nonneg P)
  have hq : 1<Real.sqrt 3 := (Real.lt_sqrt (by norm_num : (0:ℝ)≤1)).2 (by norm_num)
  have hq2 : Real.sqrt 3≤2 := (Real.sqrt_le_iff).2 ⟨by norm_num,by norm_num⟩
  have he := upper_cell_scaled_history_envelope (E := blockVecDot P (blockMatVecMul
      (Book.Ch02.coarseBlockMatrix (Book.Ch02.cubeDomain Q) (sensitivityBookCoeffOn Q (M.nu/sigma) hp
        (sensitivityResponseCoefficientPath k (kH+BoundedContinuousFunction.const
          (closure (openCubeSet Q)) (-(cubeAverage Q h.value.toFun))) 1))) P))
    hC hx hq hq2 (by
      intro j hj
      have hh := upper_cell_band_depth_comparison Q (M.nu/sigma) hp k n height
        (fun _ => sigma⁻¹) ω j (Real.sqrt ((Real.sqrt 3)^j)*A)
        (fun R hR => upper_cell_physical_old_book_norm M n ell ω j R hR) hj P
      calc
        _ ≤ (1+(5/4:ℝ)*(x/(Real.sqrt 3)^j))*(Real.sqrt ((Real.sqrt 3)^j)*A)*
            (1+2*F+4*F^2)*blockVecDot P P := hh
        _ = C*(Real.sqrt ((Real.sqrt 3)^j)*(1+(5/4:ℝ)*(x/(Real.sqrt 3)^j))) := by
          dsimp [C]
          ring)
  have hb := mul_le_mul_of_nonneg_left
    (add_le_add (le_refl (1:ℝ)) (mul_le_mul_of_nonneg_left hxA (by norm_num : (0:ℝ)≤3))) hC
  apply he.trans
  apply hb.trans_eq
  change C*(1+3*(A*F)) = A*(1+3*A*F)*(1+2*F+4*F^2)*blockVecDot P P
  dsimp only [C]
  ring

end
end ASDExplicitGamma.Scalar
