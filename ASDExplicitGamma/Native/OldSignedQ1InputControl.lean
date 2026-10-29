module

public import ASDExplicitGamma.Native.OldSignedQ1PaymentInputs

/-! All physical degree premises are discharged from the source state. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization Gaussian Main Triadic Cold Scalar Inverse Algsuperdiff.Section3 Numerics.Native Numerics.Mirror
noncomputable section

private theorem q1_degree_zero (θ x : ℝ) (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) (hx : 0 ≤ x) :
    NativeBoundaryDegreeControl (Real.sqrt θ) ⟨0,false⟩ (θ*x) x :=
  ⟨mul_nonneg hθ hx,hx,by simpa using mul_le_mul_of_nonneg_right hθ1 hx,by simp⟩

private theorem q1_degree_two (θ x y : ℝ) (hθ : 0 ≤ θ) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hh : x ≤ θ*y) : NativeBoundaryDegreeControl (Real.sqrt θ) ⟨2,false⟩ x y :=
  ⟨hx,hy,by simpa only [Real.sq_sqrt hθ] using hh,by simp⟩

private theorem q1_degree_one (θ x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hh : x ≤ Real.sqrt θ*y) : NativeBoundaryDegreeControl (Real.sqrt θ) ⟨1,false⟩ x y :=
  ⟨hx,hy,by simpa using hh,by simp⟩

private theorem q1_degree_fixed (θ x : ℝ) (hx : 0 ≤ x) :
    NativeBoundaryDegreeControl (Real.sqrt θ) ⟨0,true⟩ x x :=
  ⟨hx,hx,by simp,fun _ => rfl⟩

/-- The actual bill's input controls need only the previous native state. -/
theorem old_signed_q1_payment_input_control
    (M : ABKModel 2) (h : ℝ) (hg : M.gamma ≤ gammaZero) (n : ℤ)
    (hstate : nativeInductionState M h n) (t : ℝ) (ht : 0 ≤ t) :
    let b := q3ModelAmplitude M h (n+1)/(Annealed.sigmaBar M n:ℝ)
    let L := q3ModelLength (n+1)
    ∀ i, NativeBoundaryDegreeControl (Real.sqrt (theta M)) (oldSignedQ1PaymentTags i)
      (oldSignedQ1PaymentInputs M n t b L i) (oldSignedQ1PaymentEndpoint t i) := by
  intro b L i
  have hθ := (cold_theta_pos M).le
  have hθ1 := cold_theta_le_one M hg
  have hr : 0 ≤ cubeScaleFactor (originCube 2 n)/3^5 :=
    div_nonneg (Triadic.cubeScaleFactor_pos' _).le (by norm_num)
  have hC : 0 ≤ oldSignedQ1PanelHistory t := sq_nonneg _
  have hA : 0 ≤ oldSignedQ1PanelMatrix t := add_nonneg
    (add_nonneg (by norm_num) (mul_nonneg (by norm_num) hC)) (Real.sqrt_nonneg _)
  have hD : 0 ≤ 1+inverseHistoryDiscount :=
    add_nonneg (by norm_num) inverse_history_discount_range.1.le
  have hX : 0 ≤ oldSignedQ1PanelXi t := add_nonneg
    (old_signed_q1_setup_field_nonneg ⟨15,by omega⟩)
    (mul_nonneg ht (old_signed_q1_setup_field_nonneg ⟨12,by omega⟩))
  have ha : 0 ≤ oldSignedQ1PanelMean t := add_nonneg
    (old_signed_q1_setup_field_nonneg ⟨14,by omega⟩)
    (mul_nonneg ht (old_signed_q1_setup_field_nonneg ⟨11,by omega⟩))
  by_cases hi : i<16
  · interval_cases i
    · exact q1_degree_two _ _ _ hθ (sq_nonneg b) old_signed_q1_setup_variance_nonneg
        (old_signed_q1_model_variance M h hg n hstate)
    · exact q1_degree_one _ _ _ (abs_nonneg b) (Real.sqrt_nonneg _)
        (old_signed_q1_scaled_amplitude M h hg n hstate)
    · exact q1_degree_two _ _ _ hθ (descendantsAverage_nonneg _ _ _ (fun _ _ => sq_nonneg _))
        (sq_nonneg _) (old_signed_q1_scaled_plus_oscillation M h hg n hstate)
    · exact q1_degree_two _ _ _ hθ (descendantsAverage_nonneg _ _ _ (fun _ _ => sq_nonneg _))
        (sq_nonneg _) (old_signed_q1_scaled_minus_oscillation M h hg n hstate)
    · exact q1_degree_one _ _ _ (old_signed_source_multiplier_nonneg _ _ _ _)
        (old_signed_q1_setup_field_nonneg ⟨2,by omega⟩)
        (old_signed_q1_scaled_source_multiplier M h hg n hstate)
    · exact q1_degree_one _ _ _ (old_signed_q1_derivative_kappa_nonneg _ _ _ hr)
        (old_signed_q1_setup_field_nonneg ⟨3,by omega⟩)
        (old_signed_q1_scaled_derivative_multiplier M h hg n hstate)
    · apply q1_degree_two _ _ _ hθ
      · change 0 ≤ oldSignedQ1ReciprocalSpatialCap _ _ _ _ _
        unfold oldSignedQ1ReciprocalSpatialCap
        have hS : 0 ≤ mainFlatSigmaSq b L := by unfold mainFlatSigmaSq; positivity
        exact mul_nonneg (mul_nonneg (sq_nonneg _) hS)
          (add_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))
            (mul_nonneg (by norm_num) hA))
      · exact add_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))
          (mul_nonneg (mul_nonneg (by norm_num) hA) (sq_nonneg _))
      · exact old_signed_q1_scaled_reciprocal_profile M h hg n hstate t
    · apply q1_degree_two _ _ _ hθ
      · exact add_nonneg (sq_nonneg b) (mul_nonneg
          (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hr) (Real.sqrt_nonneg _))
            (abs_nonneg b)) (Real.sqrt_nonneg _))
      · exact old_signed_q1_setup_field_nonneg ⟨6,by omega⟩
      · exact old_signed_q1_scaled_boundary_profile M h hg n hstate
    · exact q1_degree_zero _ _ hθ hθ1 hX
    · exact q1_degree_zero _ _ hθ hθ1 (mul_nonneg (mul_nonneg hD hA) hC)
    · exact q1_degree_fixed _ _ hA
    · exact q1_degree_fixed _ _ hD
    · exact q1_degree_fixed _ _ (add_nonneg (Real.sqrt_nonneg _) (by norm_num))
    · exact q1_degree_zero _ _ hθ hθ1 ha
    · exact q1_degree_two _ _ _ hθ (div_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))
        (sq_nonneg _)) (old_signed_q1_setup_field_nonneg ⟨1,by omega⟩)
        (old_signed_q1_model_second_moment M h hg n hstate)
    · exact q1_degree_one _ _ _ (mul_nonneg (Real.sqrt_nonneg _)
        (old_signed_q1_derivative_kappa_nonneg _ _ _ hr))
        (old_signed_q1_setup_field_nonneg ⟨3,by omega⟩)
        (old_signed_q1_scaled_derivative_multiplier_sharp M h hg n hstate)
  · have hi' : ∃ j, i=16+j := ⟨i-16,by omega⟩
    obtain ⟨j,rfl⟩ := hi'
    simp only [Nat.add_comm 16,oldSignedQ1PaymentTags,oldSignedQ1PaymentInputs,oldSignedQ1PaymentEndpoint]
    exact ⟨le_refl 0,le_refl 0,by simp,by simp⟩

/-- Actual spatial and covariance caps imply the whole endpoint-scaled bill. -/
theorem old_signed_q1_payment_endpoint_bound
    (M : ABKModel 2) (h : ℝ) (hg : M.gamma ≤ gammaZero) (n : ℤ)
    (hstate : nativeInductionState M h n) (t : ℝ) (ht : 0 ≤ t) :
    let b := q3ModelAmplitude M h (n+1)/(Annealed.sigmaBar M n:ℝ)
    let L := q3ModelLength (n+1)
    oldSignedQ1AffineCap M n t b L+oldSignedQ1ErrorCap M n t b L ≤
      theta M*evalReal (oldSignedQ1PaymentEndpoint t) oldSignedQ1PaymentExpr := by
  intro b L
  rw [←old_signed_q1_payment_inputs_eval]
  exact old_signed_q1_payment_degree_bound (theta M) (cold_theta_pos M).le (cold_theta_le_one M hg)
    _ _ (old_signed_q1_payment_input_control M h hg n hstate t ht)

end
end ASDExplicitGamma.Native
