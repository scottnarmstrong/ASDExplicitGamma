module

public import ASDExplicitGamma.Scalar.OldHessianTrialGeneratorPointwise
public import ASDExplicitGamma.Scalar.OldHessianTrialSharpAffine
public import ASDExplicitGamma.Scalar.OldHessianTrialInverseTraceMean
public import ASDExplicitGamma.Inverse.BankHeatIntegrability
public import ASDExplicitGamma.Inverse.SourceQ3TraceRegularity

/-! Ten-term OLD-Hessian generator bound on the actual cutoff law. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Native Response Triadic Variational Gaussian Inverse Main Algsuperdiff.Section3
open Numerics.Mirror Numerics.Scalar
noncomputable section
attribute [local irreducible] Homogenization.descendantsAtDepth

theorem old_hessian_integral_add_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {f g : Ω → ℝ} {a c : ℝ} (hf : Integrable f μ) (hg : Integrable g μ)
    (h1 : ∫ ω,f ω ∂μ ≤ a) (h2 : ∫ ω,g ω ∂μ ≤ c) :
    ∫ ω,(f ω+g ω) ∂μ ≤ a+c := by
  rw [integral_add hf hg]
  exact add_le_add h1 h2

/-- Integrability and first moment of the ten-bill envelope sum, with the
sharp Dirichlet-energy affine cap. -/
theorem old_hessian_envelope_sum_moment
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma≤gammaZero) (N : ℤ)
    (hpast : ∀ l<N,nativeInductionState M h l) (m : ℤ) (hm : m<N) (b : ℝ) (hb : 0<b) :
    Integrable (oldHessianEnvelopeSum M m b) (Cutoff.cutoffSampleLaw M).toMeasure ∧
    (∫ ω,oldHessianEnvelopeSum M m b ω ∂(Cutoff.cutoffSampleLaw M).toMeasure)≤
      b^2*evalReal scalarRealEnv lowerTerm2Expr+
      ((431/500:ℝ)^2*((1+evalReal scalarRealEnv lowerA5Expr/2)*
        ∑' n,oldSignedFlatDirichletModeEnergy (originCube 2 (m+129)) b (q3ModelLength (m+1)) n)+
        b^2*evalReal scalarRealEnv lowerTerm1Expr)+
      (b^2*evalReal scalarRealEnv lowerTerm3Expr+b^2*evalReal scalarRealEnv lowerTerm5Expr+
        b^2*evalReal scalarRealEnv lowerTerm4Expr+b^2*evalReal scalarRealEnv lowerTerm7Expr)+
      b^2*evalReal scalarRealEnv lowerTerm9Expr+
      (b^2*evalReal scalarRealEnv lowerTerm6Expr+b^2*evalReal scalarRealEnv lowerTerm10Expr)+
      b^2*evalReal scalarRealEnv lowerTerm8Expr := by
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let L := q3ModelLength (m+1)
  have b1 := old_hessian_actual_first_bill M h hM hg N hpast m hm b
  have b2 := old_hessian_actual_second_bill M h hM hg N hpast m hm b
  have b3 := old_hessian_actual_third_bill M h hM hg N hpast m hm b
  have b4 := old_hessian_actual_fourth_bill M h hM hg N hpast m hm b
  have b5 := old_hessian_actual_fifth_bill M h hM hg N hpast m hm b hb
  have b610 := old_hessian_actual_sixth_tenth_bills M h hM hg N hpast m hm b
  have b7 := old_hessian_actual_seventh_bill M h hM hg N hpast m hm b
  have b8 := old_hessian_actual_eighth_bill M h hM hg N hpast m hm b hb
  have b9 := old_hessian_actual_ninth_bill M h hM hg N hpast m hm b
  have hA := old_hessian_minus_affine_energy_moment_sharp M h hM hg N hpast m hm b L
  have hIA : (∫ ω,(431/500:ℝ)^2*oldHessianMinusAffineEnergy M m b L ω ∂μ)≤
      (431/500:ℝ)^2*((1+evalReal scalarRealEnv lowerA5Expr/2)*
        ∑' n,oldSignedFlatDirichletModeEnergy (originCube 2 (m+129)) b L n) := by
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left hA.2.2 (sq_nonneg _)
  refine ⟨((((b2.1.add ((hA.2.1.const_mul _).add b1.1)).add
      (((b3.1.add b5.1).add b4.1).add b7.1)).add b9.1).add (b610.1.add b610.2.1)).add b8.1,?_⟩
  refine old_hessian_integral_add_le (((((b2.1.add ((hA.2.1.const_mul _).add b1.1)).add
    (((b3.1.add b5.1).add b4.1).add b7.1)).add b9.1).add (b610.1.add b610.2.1))) b8.1 ?_ b8.2.2
  refine old_hessian_integral_add_le ((((b2.1.add ((hA.2.1.const_mul _).add b1.1)).add
    (((b3.1.add b5.1).add b4.1).add b7.1)).add b9.1)) (b610.1.add b610.2.1) ?_
    (old_hessian_integral_add_le b610.1 b610.2.1 b610.2.2.2.1 b610.2.2.2.2)
  refine old_hessian_integral_add_le (((b2.1.add ((hA.2.1.const_mul _).add b1.1)).add
    (((b3.1.add b5.1).add b4.1).add b7.1))) b9.1 ?_ b9.2.2
  refine old_hessian_integral_add_le (b2.1.add ((hA.2.1.const_mul _).add b1.1))
    (((b3.1.add b5.1).add b4.1).add b7.1) ?_ ?_
  · exact old_hessian_integral_add_le b2.1 ((hA.2.1.const_mul _).add b1.1) b2.2.2
      (old_hessian_integral_add_le (hA.2.1.const_mul _) b1.1 hIA b1.2.2)
  · exact old_hessian_integral_add_le ((b3.1.add b5.1).add b4.1) b7.1
      (old_hessian_integral_add_le (b3.1.add b5.1) b4.1
        (old_hessian_integral_add_le b3.1 b5.1 b3.2.2 b5.2.2) b4.2.2) b7.2.2

/-- Pure real arithmetic of the ten-term base. -/
theorem old_hessian_ten_term_arith (G Pint Tint b2 Y q a5 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 : ℝ)
    (hG : G≤Pint-(431/500:ℝ)*b2*(Tint-2)-2*(431/500:ℝ)*Y)
    (hP : Pint≤b2*t2+((431/500:ℝ)^2*((1+a5/2)*Y)+b2*t1)+(b2*t3+b2*t5+b2*t4+b2*t7)+b2*t9+
      (b2*t6+b2*t10)+b2*t8)
    (hT : 2≤Tint) (hb2 : 0≤b2) (hY1 : b2*(1-q/2)≤Y) (hY2 : Y≤b2) (ha5 : 0≤a5) :
    G≤-(2*b2)*(((2*(431/500:ℝ)-(431/500:ℝ)^2)*(1/2-q/4))-((431/500:ℝ)^2*a5)/4-
      (t1+t2+t3+t4+t5+t6+t7+t8+t9+t10)/2) := by
  have hq1 := mul_nonneg (by norm_num : (0:ℝ)≤2*(431/500)-(431/500)^2) (sub_nonneg.mpr hY1)
  have hq2 := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ)≤(431/500)^2/2) ha5) (sub_nonneg.mpr hY2)
  have hTT : (431/500:ℝ)*b2*(Tint-2)≥0 := mul_nonneg (by positivity) (by linarith)
  nlinarith [hG,hP,hTT,hq1,hq2]

/-- The actual OLD cutoff generator of the normalized inverse trace obeys the
ten-term bound: with `b = amplitude / sigmaBar_m` the expected generator is at most
`-2 b^2 base`, i.e. twice the one-load rate (the trace has two loads). -/
theorem old_hessian_trial_ten_term_bound
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma≤gammaZero) (N : ℤ)
    (hpast : ∀ l<N,nativeInductionState M h l) (m : ℤ) (hm : m<N) :
    (1/2:ℝ)*modelHeatTraceAverage (closure (cubeSet (originCube 2 (m+129)))) M m
      (mainInverseObservable (m+129) M.nu (Annealed.sigmaBar M m : ℝ))
      (pureFluxMainCubeQ3Directions (m+129) (q3ModelAmplitude M h (m+1)) (q3ModelLength (m+1))) 0 ≤
    -(2*(q3ModelAmplitude M h (m+1)/(Annealed.sigmaBar M m : ℝ))^2)*
      evalReal scalarRealEnv lowerBaseExpr := by
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let σ : ℝ := Annealed.sigmaBar M m
  let amp := q3ModelAmplitude M h (m+1)
  let b := amp/σ
  let L := q3ModelLength (m+1)
  have hσ : 0<σ := (Annealed.sigmaBar_characterization M m).1
  have hamp : 0<amp := by
    unfold amp q3ModelAmplitude
    exact mul_pos hM.1 (Real.rpow_pos_of_pos (by norm_num : (0:ℝ)<3) _)
  have hb : 0<b := div_pos hamp hσ
  have hsb : σ*b=amp := by dsimp only [b]; field_simp
  let K := closure (cubeSet (originCube 2 (m+129)))
  obtain ⟨ell,hK⟩ := exists_originCube_containing_compact K
    (isBounded_cubeSet (originCube 2 (m+129))).isCompact_closure
  have hΦ := mainInverseObservable_hasPolynomiallyBoundedC2Derivatives (m+129) M.nu σ M.nu_pos hσ
  have htest := source_q3_covariance_trace_regular (m+129) amp L
    (mainInverseObservable (m+129) M.nu σ) hΦ
  have hGint := bank_model_heat_integrable K M h hM ell m hK
    (modelCovarianceTrace (mainInverseObservable (m+129) M.nu σ)
      (pureFluxMainCubeQ3Directions (m+129) amp L)) htest.1 htest.2 0
  have hpt (ω : Cutoff.CutoffSample 2) : (1/2:ℝ)*modelCovarianceTrace
      (mainInverseObservable (m+129) M.nu σ) (pureFluxMainCubeQ3Directions (m+129) amp L)
      (modelInsertedScalar K m 0 ω) = ∑' n,oldHessianActualHessianMode M m b n ω := by
    have hh := old_hessian_inverse_generator_physical (m+129) M.nu σ M.nu_pos hσ b L
      (modelInsertedScalar K m 0 ω)
    rw [hsb] at hh
    exact hh
  have hGi : Integrable (fun ω => ∑' n,oldHessianActualHessianMode M m b n ω) μ :=
    (hGint.const_mul (1/2:ℝ)).congr (Filter.Eventually.of_forall hpt)
  have hLHS : (1/2:ℝ)*modelHeatTraceAverage K M m (mainInverseObservable (m+129) M.nu σ)
      (pureFluxMainCubeQ3Directions (m+129) amp L) 0 =
      ∫ ω,∑' n,oldHessianActualHessianMode M m b n ω ∂μ := by
    unfold modelHeatTraceAverage modelHeatAverage
    rw [←integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall hpt)
  change (1/2:ℝ)*modelHeatTraceAverage K M m (mainInverseObservable (m+129) M.nu σ)
      (pureFluxMainCubeQ3Directions (m+129) amp L) 0 ≤ _
  rw [hLHS]
  have hpw := old_hessian_actual_generator_pointwise M h hM hg N hpast m hm b hb
  have hA := old_hessian_envelope_sum_moment M h hM hg N hpast m hm b hb
  have hT := old_hessian_inverse_trace_mean M m
  have hTi : Integrable (oldHessianInverseTrace M m) μ := hT.1
  let Y := ∑' n,oldSignedFlatDirichletModeEnergy (originCube 2 (m+129)) b L n
  let C0 : ℝ := 2*(431/500:ℝ)*(b^2-oldSignedFlatBoundaryEnergy (originCube 2 (m+129)) b L/2)
  have i1 : Integrable (fun ω => oldHessianInverseTrace M m ω-2) μ := hTi.sub (integrable_const 2)
  have i2 : Integrable (fun ω => (431/500:ℝ)*b^2*(oldHessianInverseTrace M m ω-2)) μ :=
    i1.const_mul _
  have i3 : Integrable (fun ω => oldHessianEnvelopeSum M m b ω-
      (431/500:ℝ)*b^2*(oldHessianInverseTrace M m ω-2)) μ := hA.1.sub i2
  have hcapi : Integrable (oldHessianPointwiseCap M m b) μ := i3.sub (integrable_const C0)
  have hmono : (∫ ω,∑' n,oldHessianActualHessianMode M m b n ω ∂μ) ≤
      ∫ ω,oldHessianPointwiseCap M m b ω ∂μ :=
    integral_mono_ae hGi hcapi (by filter_upwards [hpw] with ω hω using hω.2)
  have hcapint : (∫ ω,oldHessianPointwiseCap M m b ω ∂μ) =
      (∫ ω,oldHessianEnvelopeSum M m b ω ∂μ)-
        (431/500:ℝ)*b^2*((∫ ω,oldHessianInverseTrace M m ω ∂μ)-2)-C0 := by
    unfold oldHessianPointwiseCap
    rw [integral_sub i3 (integrable_const C0),integral_sub hA.1 i2,integral_const_mul,
      integral_sub hTi (integrable_const 2)]
    have h2 : (∫ _ : Cutoff.CutoffSample 2,(2:ℝ) ∂μ)=2 := by simp
    have hC0 : (∫ _ : Cutoff.CutoffSample 2,C0 ∂μ)=C0 := by simp
    rw [h2,hC0]
  have hYeq : b^2-oldSignedFlatBoundaryEnergy (originCube 2 (m+129)) b L/2=Y := by
    have hh : oldSignedFlatBoundaryEnergy (originCube 2 (m+129)) b L=2*(b^2-Y) := by
      unfold oldSignedFlatBoundaryEnergy
      exact (old_signed_flat_boundary_energy_trace (originCube 2 (m+129)) b L).tsum_eq
    rw [hh]; ring
  have hB := old_hessian_physical_flat_boundary m b hb
  have hB0 := (old_signed_flat_boundary_energy_bounds (originCube 2 (m+129)) b L).1
  have hBs : oldSignedFlatBoundaryEnergy (originCube 2 (m+129)) b L=2*(b^2-Y) := by
    unfold oldSignedFlatBoundaryEnergy
    exact (old_signed_flat_boundary_energy_trace (originCube 2 (m+129)) b L).tsum_eq
  have ha5 : 0≤evalReal scalarRealEnv lowerA5Expr := by norm_num [evalReal,lowerA5Expr,sc]
  have hbase : evalReal scalarRealEnv lowerBaseExpr=
      ((2*(431/500:ℝ)-(431/500:ℝ)^2)*(1/2-evalReal scalarRealEnv lowerFlatTailExpr/4))-
        ((431/500:ℝ)^2*evalReal scalarRealEnv lowerA5Expr)/4-
        (evalReal scalarRealEnv lowerTerm1Expr+evalReal scalarRealEnv lowerTerm2Expr+
          evalReal scalarRealEnv lowerTerm3Expr+evalReal scalarRealEnv lowerTerm4Expr+
          evalReal scalarRealEnv lowerTerm5Expr+evalReal scalarRealEnv lowerTerm6Expr+
          evalReal scalarRealEnv lowerTerm7Expr+evalReal scalarRealEnv lowerTerm8Expr+
          evalReal scalarRealEnv lowerTerm9Expr+evalReal scalarRealEnv lowerTerm10Expr)/2 := by
    simp only [lowerBaseExpr,lowerPrefactorExpr,lowerErrorExpr,evalReal]
    norm_num only [evalReal,sc]
    ring
  have hY1 : b^2*(1-evalReal scalarRealEnv lowerFlatTailExpr/2)≤Y := by nlinarith [hB,hBs]
  have hY2 : Y≤b^2 := by nlinarith [hB0,hBs]
  rw [hbase]
  have hCC : C0=2*(431/500:ℝ)*Y := by
    change 2*(431/500:ℝ)*(b^2-oldSignedFlatBoundaryEnergy (originCube 2 (m+129)) b L/2)=_
    rw [hYeq]
  rw [hcapint,hCC] at hmono
  have hT2 : 2≤∫ ω,oldHessianInverseTrace M m ω ∂μ := hT.2
  exact old_hessian_ten_term_arith _ _ _ (b^2) Y _ _ _ _ _ _ _ _ _ _ _ _
    hmono hA.2 hT2 (sq_nonneg b) hY1 hY2 ha5

end
end ASDExplicitGamma.Scalar
