module

public import ASDExplicitGamma.Scalar.UpperCellEnergyResetHistory
public import ASDExplicitGamma.Scalar.TopSourceResidualActual
public import ASDExplicitGamma.Inverse.FullResponseCoefficientTransport

/-! The terminal physical coefficient in the fixed OLD RESET frame. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization Response Variational MeasureTheory Triadic Algsuperdiff.Section3
open Native Inverse
noncomputable section

/-- The terminal cutoff is normalized by the OLD sigma_n, not sigma_terminal. -/
theorem upper_cell_reset_frame_coefficient
    (M : ABKModel 2) (n terminal : ℤ) (Q : TriadicCube 2)
    (ω : Cutoff.CutoffSample 2) {x : Vec 2} (hx : x ∈ openCubeSet Q) :
    responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M n:ℝ)
      (oldCutoffSkewCoefficient terminal Q ω) x =
      (Annealed.sigmaBar M n:ℝ)⁻¹ • Cutoff.coefficientCutoff M.nu terminal ω x := by
  rw [responseFramePlanarCoefficientField_apply,
    old_cutoff_skew_coefficient_value terminal Q ω hx,
    ←old_cutoff_coefficient_planar]
  rw [responsePlanarCoefficient]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.smul_apply,Matrix.add_apply,smul_eq_mul,responsePlanarJ,responsePlanarCoefficient] <;> ring

/-- The actual terminal realization and the normalized band coefficient give
identical response norms on every descendant of the physical cell. -/
theorem upper_cell_reset_descendant_norm
    (M : ABKModel 2) (n : ℤ) (height : ℕ) (Q R : TriadicCube 2)
    (ω : Cutoff.CutoffSample 2) (j : ℕ) (hR : R ∈ descendantsAtDepth Q j) :
    fullResponseOperatorNorm R
      (responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M n:ℝ)
        (oldCutoffSkewCoefficient (n+(height:ℤ)) Q ω)) =
    fullResponseOperatorNorm R ((Annealed.sigmaBar M n:ℝ)⁻¹ •
      attenuatedCoefficient M n (n+(height:ℤ)) (fun _ => 1) ω) := by
  rw [full_response_coefficient_unit M n _ (by omega)]
  have hae : responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M n:ℝ)
      (oldCutoffSkewCoefficient (n+(height:ℤ)) Q ω) =ᵐ[volume.restrict (openCubeSet R)]
      ((Annealed.sigmaBar M n:ℝ)⁻¹ • Cutoff.coefficientCutoff M.nu (n+(height:ℤ)) ω) := by
    filter_upwards [ae_restrict_mem (measurableSet_openCubeSet R)] with x hx
    exact upper_cell_reset_frame_coefficient M n _ Q ω
      (openCubeSet_subset_of_mem_descendantsAtDepth hR hx)
  have hm := coarseBlockMatrix_congr_of_ae_eq hae
  unfold fullResponseOperatorNorm
  rw [cube_coarseMatrix_eq_open R _,cube_coarseMatrix_eq_open R _,hm]

/-- Exact complete-history identification for the literal terminal RESET
realization in the original true frame. Every descendant is retained. -/
theorem upper_cell_reset_terminal_history
    (M : ABKModel 2) (n : ℤ) (height : ℕ) (Q : TriadicCube 2)
    (ω : Cutoff.CutoffSample 2) :
    completeFullResponseHistory Q
      (responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M n:ℝ)
        (oldCutoffSkewCoefficient (n+(height:ℤ)) Q ω)) =
    completeFullResponseHistory Q ((Annealed.sigmaBar M n:ℝ)⁻¹ •
      attenuatedCoefficient M n (n+(height:ℤ)) (fun _ => 1) ω) := by
  unfold completeFullResponseHistory
  apply congrArg (fun z => ENNReal.ofReal (1-inverseHistoryDiscount)*z)
  apply tsum_congr
  intro j
  apply congrArg ENNReal.ofReal
  apply congrArg (fun z : ℝ => inverseHistoryDiscount^j*z)
  apply Book.Ch02.finsetSupReal_congr
  intro R hR
  exact upper_cell_reset_descendant_norm M n height Q R ω j hR

/-- The literal terminal RESET realization in the OLD frame obeys m_new
in order64 and is almost surely finite. No normalization at the future label
or assumed operator/history bound enters this physical export. -/
theorem upper_cell_reset_terminal_history_L64
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (n : ℤ)
    (hpast : ∀ k < n, nativeInductionState M h k)
    (height : ℕ) (hb : M.gamma*(height:ℝ) ≤ 17/50) :
    let H := fun ω : Cutoff.CutoffSample 2 =>
      completeFullResponseHistory (originCube 2 (n-14))
        (responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M n:ℝ)
          (oldCutoffSkewCoefficient (n+(height:ℤ)) (originCube 2 (n-14)) ω))
    MeasureTheory.eLpNorm (fun ω => (H ω).toReal) 64
      (Cutoff.cutoffSampleLaw M).toMeasure ≤
      ENNReal.ofReal (upperCellHistoryProfile M.gamma (M.gamma*(height:ℝ))) ∧
      (∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure, H ω < ⊤) := by
  dsimp only
  simp_rw [upper_cell_reset_terminal_history]
  exact upper_cell_future_physical_history_L64 M h hM hg n hpast height hb
    (fun _ => 1) (fun _ _ => ⟨by norm_num,le_rfl⟩)

end
end ASDExplicitGamma.Scalar

