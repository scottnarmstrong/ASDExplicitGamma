module

public import ASDExplicitGamma.Inverse.RawShellPureFluxRows
public import ASDExplicitGamma.Variational.AdapterShearTrace
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-! Exact reduction of the raw q3 mixed Hessian to a first variation of the
coarse shear coefficient. -/

@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory ASDExplicitGamma.Response ASDExplicitGamma.Variational
  ASDExplicitGamma.Gaussian ASDExplicitGamma.Model ASDExplicitGamma.Main
noncomputable section

/-- The signed shear coefficient of the actual compact-field trace response. -/
noncomputable def rawTraceModelShearLinear (n : ℤ) (ν : ℝ) :
    C(closure (cubeSet (originCube 2 n)), ℝ) → ℝ := fun k =>
  Variational.shearTraceLinear (coarseBlockMatrix (cubeSet (originCube 2 n))
    (responsePlanarCoefficientField ν
      (ContinuousMap.linearIsometryBoundedOfCompact
        (closure (cubeSet (originCube 2 n))) ℝ ℝ k)))

/-- A constant physical shear differentiates the true-frame trace to the
coarse shear coefficient. The direction carries the source frame factor σ. -/
theorem raw_trace_model_constantShear_fderiv
    (n : ℤ) (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (k : C(closure (cubeSet (originCube 2 n)), ℝ)) :
    fderiv ℝ (modelTraceObservable n ν σ) k
        (ContinuousMap.const (closure (cubeSet (originCube 2 n))) σ) =
      2 * rawTraceModelShearLinear n ν k := by
  let Q := originCube 2 n
  let K := closure (cubeSet Q)
  let T := modelTraceObservable n ν σ
  let L := ContinuousMap.linearIsometryBoundedOfCompact K ℝ ℝ
  let kB : ResponseCoefficient (cubeSet Q) := L k
  let e : C(K, ℝ) := ContinuousMap.const K σ
  let z := rawTraceModelShearLinear n ν
  let d := Matrix.trace (frameMatrix σ
    (coarseBlockMatrix (cubeSet Q) (responsePlanarCoefficientField ν kB))).lowerRight
  have hpath (t : ℝ) :
      T (k + t • e) = T k + 2 * t * z k + t ^ 2 * d := by
    have hcoeff (x : Vec 2) (hx : x ∈ cubeSet Q) :
        responseCoefficientExtension (L (k + t • e)) x =
          responseCoefficientExtension kB x + σ * t := by
      rw [responseCoefficientExtension_eq _ hx,
        responseCoefficientExtension_eq kB hx]
      change (L (k + t • e)) ⟨x, subset_closure hx⟩ =
        kB ⟨x, subset_closure hx⟩ + σ * t
      rw [map_add, map_smul]
      simp [L, kB, e, ContinuousMap.linearIsometryBoundedOfCompact_apply_apply,
        ContinuousMap.const_apply]
      change k ⟨x, subset_closure hx⟩ + t * σ =
        (L k) ⟨x, subset_closure hx⟩ + σ * t
      have hLk : (L k) ⟨x, subset_closure hx⟩ = k ⟨x, subset_closure hx⟩ := by
        change (ContinuousMap.linearIsometryBoundedOfCompact K ℝ ℝ k)
          ⟨x, subset_closure hx⟩ = _
        simp
      rw [hLk]
      ring
    have hae : (fun x => responsePlanarCoefficientField ν (L (k + t • e)) x) =ᵐ[
        volume.restrict (cubeSet Q)]
        fun x => responsePlanarCoefficient ν
          (responseCoefficientExtension kB x + σ * t) := by
      filter_upwards [ae_restrict_mem (μ := volume) (measurableSet_cubeSet Q)] with x hx
      change responsePlanarCoefficient ν
          (responseCoefficientExtension (L (k + t • e)) x) =
        responsePlanarCoefficient ν (responseCoefficientExtension kB x + σ * t)
      rw [hcoeff x hx]
    have hmodel : T (k + t • e) = traceDefect (cubeSet Q)
        (fun x => responsePlanarCoefficient ν
          (responseCoefficientExtension kB x + σ * t)) σ := by
      unfold T modelTraceObservable traceDefect
      rw [coarseBlockMatrix_congr_of_ae_eq hae]
    have hbaseEll := responsePlanarCoefficientField_isElliptic
      (measurableSet_cubeSet Q) ν hν kB
    have hsource := response_traceDefect_constantSkew_physical Q ν σ hν hσ kB (σ * t)
    rw [← hmodel] at hsource
    have hbase : T k = traceDefect (cubeSet Q)
        (responsePlanarCoefficientField ν kB) σ := rfl
    rw [← hbase] at hsource
    have hlin : (σ * t) / σ = t := by field_simp [hσ.ne']
    have hquad : (σ * t) ^ 2 *
        (Matrix.trace (frameMatrix σ
          (coarseBlockMatrix (cubeSet Q) (responsePlanarCoefficientField ν kB))).lowerRight /
          σ ^ 2) = t ^ 2 * d := by
      dsimp [d]
      field_simp [hσ.ne']
    rw [hlin, hquad] at hsource
    simpa [z, rawTraceModelShearLinear, d] using hsource
  have hT : DifferentiableAt ℝ T k := by
    have hcont : ContDiff ℝ 2 T := by
      simpa [T] using
        (modelTraceObservable_hasPolynomiallyBoundedC2Derivatives n ν σ hν hσ).1
    exact (hcont.differentiable (by norm_num)).differentiableAt
  have hline : HasDerivAt (fun t : ℝ => k + t • e) e 0 := by
    simpa [e] using (hasDerivAt_id (0 : ℝ)).smul_const
      (ContinuousMap.const (closure (cubeSet (originCube 2 n))) σ) |>.const_add k
  have hchain := hT.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hline (by simp [e])
  have hpoly : HasDerivAt (fun t : ℝ => T k + 2 * t * z k + t ^ 2 * d)
      (2 * z k) 0 := by
    have hlinear : HasDerivAt (fun t : ℝ => 2 * t * z k) (2 * z k) 0 := by
      have h := (hasDerivAt_id (0 : ℝ)).const_mul (2 * z k)
      convert h using 1
      · funext t
        simp [id_eq]
        ring
      · simp
    have hquad : HasDerivAt (fun t : ℝ => t ^ 2 * d) 0 0 := by
      have h := ((hasDerivAt_id (0 : ℝ)).pow 2).const_mul d
      convert h using 1
      · funext t
        simp [id_eq]
        ring
      · simp
    have hconst : HasDerivAt (fun _ : ℝ => T k) 0 0 := hasDerivAt_const 0 (T k)
    have h := hconst.add (hlinear.add hquad)
    convert h using 1
    · funext t
      simp
      ring
    · simp
  have hpathEq : (fun t : ℝ => T (k + t • e)) =
      fun t => T k + 2 * t * z k + t ^ 2 * d := funext hpath
  change HasDerivAt (fun t : ℝ => T (k + t • e)) _ _ at hchain
  rw [hpathEq] at hchain
  simpa [T, z] using hchain.unique hpoly

/-- The mixed Hessian paired with the constant-shear direction is the
directional derivative of the coarse shear coefficient. -/
theorem raw_trace_model_mixed_hessian_eq_shear_derivative
    (n : ℤ) (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (k d : C(closure (cubeSet (originCube 2 n)), ℝ)) :
    fderiv ℝ (fun y => fderiv ℝ (modelTraceObservable n ν σ) y
        (ContinuousMap.const (closure (cubeSet (originCube 2 n))) σ)) k d =
      2 * fderiv ℝ (rawTraceModelShearLinear n ν) k d := by
  let T := modelTraceObservable n ν σ
  let e : C(closure (cubeSet (originCube 2 n)), ℝ) :=
    ContinuousMap.const (closure (cubeSet (originCube 2 n))) σ
  let z := rawTraceModelShearLinear n ν
  have hfun : (fun y => fderiv ℝ T y e) = fun y => 2 * z y := by
    funext y
    exact raw_trace_model_constantShear_fderiv n ν σ hν hσ y
  have hTcont : ContDiff ℝ 2 T := by
    simpa [T] using (modelTraceObservable_hasPolynomiallyBoundedC2Derivatives n ν σ hν hσ).1
  have hFderiv : ContDiffAt ℝ 1 (fderiv ℝ T) k :=
    hTcont.contDiffAt.fderiv_right (m := 1) (by norm_num)
  have hDirectional : ContDiffAt ℝ 1 (fun y => fderiv ℝ T y e) k :=
    hFderiv.clm_apply contDiffAt_const
  have hdiff : DifferentiableAt ℝ (fun y => fderiv ℝ T y e) k :=
    hDirectional.differentiableAt (by norm_num)
  have hzEq : z = fun y => (fderiv ℝ T y e) * (1 / 2 : ℝ) := by
    funext y
    rw [raw_trace_model_constantShear_fderiv n ν σ hν hσ y]
    ring
  have hz : DifferentiableAt ℝ z k := by
    rw [hzEq]
    simpa [mul_comm] using hdiff.const_mul (1 / 2 : ℝ)
  rw [hfun, fderiv_const_mul hz 2]
  simp [smul_eq_mul, z]

/-- The actual q3 mixed generator is reduced to a source coefficient row:
only the localized bound for the shear-linear derivative remains. -/
theorem raw_trace_model_q3_mixed_generator_eq_shear_derivative
    (n : ℤ) (ν σ b : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (L : {l : ℝ // 0 < l})
    (x : C(closure (cubeSet (originCube 2 n)), ℝ)) :
    let K := closure (cubeSet (originCube 2 n))
    let center := pureFluxParentCenter n
    let defect : C(K, ℝ) := ⟨fun y : K =>
      q3CovarianceDefect L.1 center.1 y.1,
      (q3CovarianceDefect_contDiff L.1 center.1).continuous.comp
        continuous_subtype_val⟩
    mixedGenerator (pureFluxMainCubeQ3Directions n b L)
      (ContinuousLinearMap.pi fun _ => ContinuousMap.evalCLM ℝ center)
      ((ContinuousLinearMap.proj (0 : Fin 1)).smulRight (1 : C(K, ℝ)))
      (centeringMap center)
      (fderiv ℝ (fderiv ℝ (modelTraceObservable n ν σ)) x) =
      (2 * b ^ 2 / σ) * fderiv ℝ (rawTraceModelShearLinear n ν) x defect := by
  intro K center defect
  rw [raw_trace_model_q3_mixed_generator_eq_covariance_defect]
  have hT : ContDiff ℝ 2 (modelTraceObservable n ν σ) :=
    (modelTraceObservable_hasPolynomiallyBoundedC2Derivatives n ν σ hν hσ).1
  have hsym : IsSymmSndFDerivAt ℝ (modelTraceObservable n ν σ) x :=
    hT.contDiffAt.isSymmSndFDerivAt (by norm_num)
  let e : C(K, ℝ) := ContinuousMap.const K σ
  have hcomm := hsym.eq (b ^ 2 • defect) e
  have hrow := raw_trace_model_mixed_hessian_eq_shear_derivative n ν σ hν hσ x defect
  have he : e = σ • ContinuousMap.const K 1 := by
    ext y
    simp [e]
  have hrow' : fderiv ℝ (fderiv ℝ (modelTraceObservable n ν σ)) x defect e =
      2 * fderiv ℝ (rawTraceModelShearLinear n ν) x defect := by
    have hfd : DifferentiableAt ℝ (fderiv ℝ (modelTraceObservable n ν σ)) x := by
      have hcont : ContDiffAt ℝ 2 (modelTraceObservable n ν σ) x := hT.contDiffAt
      exact (hcont.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
    have heval := fderiv_clm_apply hfd (differentiableAt_const e)
    have hbase : fderiv ℝ (fun y => fderiv ℝ (modelTraceObservable n ν σ) y e)
        x defect = fderiv ℝ (fderiv ℝ (modelTraceObservable n ν σ)) x defect e := by
      rw [heval]
      simp
    rw [← hbase]
    exact hrow
  have hscaleOuter : fderiv ℝ (fderiv ℝ (modelTraceObservable n ν σ)) x
      (b ^ 2 • defect) e = b ^ 2 *
        fderiv ℝ (fderiv ℝ (modelTraceObservable n ν σ)) x defect e := by
    simp only [ContinuousLinearMap.map_smul, smul_apply, smul_eq_mul]
  have hscale : fderiv ℝ (fderiv ℝ (modelTraceObservable n ν σ)) x
      (1 : C(K, ℝ)) (b ^ 2 • defect) =
      (2 * b ^ 2 / σ) * fderiv ℝ (rawTraceModelShearLinear n ν) x defect := by
    have heq : fderiv ℝ (fderiv ℝ (modelTraceObservable n ν σ)) x e
        (b ^ 2 • defect) = σ *
          fderiv ℝ (fderiv ℝ (modelTraceObservable n ν σ)) x
            (1 : C(K, ℝ)) (b ^ 2 • defect) := by
      rw [he]
      have hconst : ContinuousMap.const K 1 = (1 : C(K, ℝ)) := by
        ext y
        rfl
      rw [hconst]
      simp only [ContinuousLinearMap.map_smul, smul_apply, smul_eq_mul]
    calc
      _ = (1 / σ) * fderiv ℝ (fderiv ℝ (modelTraceObservable n ν σ)) x
          e (b ^ 2 • defect) := by
            rw [heq]
            field_simp [hσ.ne']
      _ = (1 / σ) * fderiv ℝ (fderiv ℝ (modelTraceObservable n ν σ)) x
          (b ^ 2 • defect) e := by rw [hcomm.symm]
      _ = (1 / σ) * (b ^ 2 *
          fderiv ℝ (fderiv ℝ (modelTraceObservable n ν σ)) x defect e) := by
            rw [hscaleOuter]
      _ = _ := by rw [hrow']; ring
  exact hscale

end
end ASDExplicitGamma.Inverse
