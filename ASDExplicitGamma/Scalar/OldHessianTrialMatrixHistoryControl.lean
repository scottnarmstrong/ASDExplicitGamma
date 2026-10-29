module

public import ASDExplicitGamma.Scalar.OldHessianTrialCellMatrixMoment
public import ASDExplicitGamma.Native.OldSignedMatrixHistoryControl

/-! Response and corrector histories in the original large-parent medium. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Native Response Triadic Variational Gaussian Inverse Main Cold Algsuperdiff.Section3
noncomputable section
attribute [local irreducible] Homogenization.descendantsAtDepth

/-- The bounded continuous scalar extension is elliptic on every measurable
carrier, including the boundary of a descendant. -/
theorem old_hessian_frame_elliptic_on {U V : Set (Vec 2)}
    (hV : MeasurableSet V) (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient U) :
    IsEllipticFieldOn (nu/sigma) (((nu/sigma)^2+(‖k‖/sigma)^2)/(nu/sigma)) V
      (responseFramePlanarCoefficientField nu sigma k) := by
  let a := responseFramePlanarCoefficientField nu sigma k
  have ha : ∀ i j,Continuous (fun x => a x i j) := by
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [a,responseFramePlanarCoefficientField,responsePlanarCoefficient,responsePlanarJ] <;> fun_prop
  refine ⟨?_,?_⟩
  · apply measurable_pi_iff.2
    intro i
    apply measurable_pi_iff.2
    intro j
    exact Measurable.ite hV (ha i j).measurable measurable_const
  · intro x _
    have hk : |responseCoefficientExtension k x/sigma|≤‖k‖/sigma := by
      rw [abs_div,abs_of_pos hsigma]
      apply div_le_div_of_nonneg_right _ hsigma.le
      calc
        |responseCoefficientExtension k x| = ‖responseCoefficientExtension k x‖ := by simp
        _ ≤ ‖responseCoefficientExtension k‖ := (responseCoefficientExtension k).norm_coe_le_norm x
        _ = ‖k‖ := responseCoefficientExtension_norm k
    exact responsePlanarCoefficient_isElliptic (nu/sigma) (‖k‖/sigma)
      (responseCoefficientExtension k x/sigma) (div_pos hnu hsigma) hk

/-- Both histories of each actual fine cell use the same completed-medium
maximum history; actual ellipticity supplies all infinite-series finiteness. -/
theorem old_hessian_cell_matrix_history_bounds (M : ABKModel 2) (m : ℤ)
    (U : TriadicCube 2) (ω : Cutoff.CutoffSample 2) :
    let a := responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M m)
      (oldHessianOldOpenCoefficient (m+129) m ω)
    oldSignedResponseHistory U a≤oldHessianCellMatrixMajorant M m U ω ∧
    oldSignedCorrectorHistory U a≤(1+inverseHistoryDiscount)*
      oldHessianCellMatrixMajorant M m U ω*oldHessianCellMaxTraceHistory M m U ω := by
  intro a
  have hEll := old_hessian_frame_elliptic_on (measurableSet_cubeSet U) M.nu (Annealed.sigmaBar M m)
    M.nu_pos (Annealed.sigmaBar_characterization M m).1 (oldHessianOldOpenCoefficient (m+129) m ω)
  have hpos := div_pos M.nu_pos (Annealed.sigmaBar_characterization M m).1
  exact ⟨old_signed_response_history_le_max_trace U a hpos hEll,
    old_signed_corrector_history_le_max_trace U a hpos hEll⟩

end
end ASDExplicitGamma.Scalar
