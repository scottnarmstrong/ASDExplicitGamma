module

public import ASDExplicitGamma.Cold.NativeFrameTrace
public import ASDExplicitGamma.Inverse.PureFluxGeneratorActualQ3
public import ASDExplicitGamma.Inverse.PureFluxGeneratorSourceMap
public import ASDExplicitGamma.Variational.LemmaVTrace
public import Homogenization.CoarseGraining.CoarseBounds.AeBridge
public import Mathlib.Topology.ContinuousMap.Bounded.Normed

/-! Open-cube response adapter for the closed-cube heat trace. -/

@[expose] public section

open Homogenization MeasureTheory ASDExplicitGamma.Cold ASDExplicitGamma.Gaussian
  ASDExplicitGamma.Response ASDExplicitGamma.Variational ASDExplicitGamma.Triadic
  ASDExplicitGamma.Scalar

namespace ASDExplicitGamma.Inverse

noncomputable section

/-- Every actual response shear defines an L² pure-flux load. This supplies
the source-domain membership needed by the projected-source APIs. -/
theorem pureFluxResponseShearSourceField_memLp (Q : TriadicCube 2)
    (σ : ℝ) (hσ : 0 < σ) (H : ResponseCoefficient (openCubeSet Q))
    (X : HilbertBlockL2 (openCubeSet Q)) :
    MemLp (pureFluxResponseShearSourceField Q σ hσ H X) 2
      (normalizedCubeMeasure Q) := by
  let S := responseShearL2Operator σ hσ H X
  have hS : MemBlockL2 (openCubeSet Q) (hilbertBlockL2ToBlockL2 S) :=
    (hilbertBlockL2ToBlockL2 S).property
  have hFvec : MemVectorL2 (openCubeSet Q)
      (fun x => (hilbertBlockL2ToBlockL2 S x).2) :=
    memVectorL2_snd_of_memBlockL2 hS
  have hcoord (i : Fin 2) : MemLp
      (fun x => (hilbertBlockL2ToBlockL2 S x).2 i) 2 (normalizedCubeMeasure Q) :=
    memLp_normalized_of_memL2On (memScalarL2_coord_of_memVectorL2 hFvec i)
  have hF : MemLp (fun x => (hilbertBlockL2ToBlockL2 S x).2) 2
      (normalizedCubeMeasure Q) := memLp_pi_iff.mpr hcoord
  change MemLp (fun x => (hilbertBlockL2ToBlockL2 S x).2) 2
      (normalizedCubeMeasure Q)
  exact hF

local instance pureFluxOpenBridgeFiniteMeasure (q : ℤ) :
    IsFiniteMeasure (volumeMeasureOn (openCubeSet (originCube 2 q))) :=
  (isOpenBoundedConvexDomain_openCubeSet (originCube 2 q)).isFiniteMeasure_restrict_volume

private theorem pureFluxOpen_secondDirectionalDerivative_comp_linear
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : F → ℝ) (hf : ContDiff ℝ 2 f) (L : E →L[ℝ] F) (x v : E) :
    secondDirectionalDerivative (fun y => f (L y)) x v =
      secondDirectionalDerivative f (L x) (L v) := by
  have hfd : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hfirst (y : E) :
      fderiv ℝ (fun z => f (L z)) y = (fderiv ℝ f (L y)).comp L :=
    (hfd (L y)).hasFDerivAt.comp y L.hasFDerivAt |>.fderiv
  have hdir : (fun y => fderiv ℝ (fun z => f (L z)) y v) =
      fun y => fderiv ℝ f (L y) (L v) := by
    funext y
    rw [hfirst]
    rfl
  let g : F → ℝ := fun y => fderiv ℝ f y (L v)
  have hg : DifferentiableAt ℝ g (L x) :=
    ((hf.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).clm_apply
      contDiff_const).differentiable_one.differentiableAt
  have hsecond := hg.hasFDerivAt.comp x L.hasFDerivAt
  have hsecond' : fderiv ℝ (fun y : E => g (L y)) x =
      (fderiv ℝ g (L x)).comp L := by
    simpa only [Function.comp_def] using hsecond.fderiv
  unfold secondDirectionalDerivative
  rw [hdir]
  change fderiv ℝ (fun y => g (L y)) x v =
    fderiv ℝ (fun y => fderiv ℝ f y (L v)) (L x) (L v)
  rw [hsecond']
  rfl

private theorem pureFluxOpen_modelCovarianceTrace_comp_linear
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : F → ℝ) (hf : ContDiff ℝ 2 f) (L : E →L[ℝ] F)
    (H : ℕ → E) (x : E) :
    modelCovarianceTrace (fun y => f (L y)) H x =
      modelCovarianceTrace f (fun j => L (H j)) (L x) := by
  unfold modelCovarianceTrace
  apply tsum_congr
  intro j
  exact pureFluxOpen_secondDirectionalDerivative_comp_linear f hf L x (H j)

private theorem pureFluxOpen_modelCovarianceTrace_add
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (H : ℕ → E) (hH : Summable (fun j => ‖H j‖ ^ 2))
    {f g : E → ℝ} (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (x : E) :
    modelCovarianceTrace (fun y => f y + g y) H x =
      modelCovarianceTrace f H x + modelCovarianceTrace g H x := by
  have hfdF : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hfdG : Differentiable ℝ g := hg.differentiable (by norm_num)
  have hfirst : (fun y => fderiv ℝ (fun z => f z + g z) y) =
      fun y => fderiv ℝ f y + fderiv ℝ g y := by
    funext y
    exact fderiv_fun_add (hfdF y) (hfdG y)
  have hsecondF : Differentiable ℝ (fun y => fderiv ℝ f y) :=
    (hf.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).differentiable_one
  have hsecondG : Differentiable ℝ (fun y => fderiv ℝ g y) :=
    (hg.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).differentiable_one
  have hsecond :
      fderiv ℝ (fderiv ℝ (fun y => f y + g y)) x =
        fderiv ℝ (fderiv ℝ f) x + fderiv ℝ (fderiv ℝ g) x := by
    change fderiv ℝ (fun y => fderiv ℝ (fun z => f z + g z) y) x = _
    rw [hfirst, fderiv_fun_add (hsecondF x) (hsecondG x)]
  change modelCovarianceTrace (fun y => f y + g y) H x = _
  rw [modelCovarianceTrace_eq_bilinearTraceMap H hH (hf.add hg) x,
    modelCovarianceTrace_eq_bilinearTraceMap H hH hf x,
    modelCovarianceTrace_eq_bilinearTraceMap H hH hg x,
    hsecond]
  exact (bilinearTraceMap H hH).map_add _ _

/-- Inclusion of the open-cube closure into the closed-cube closure. -/
noncomputable def pureFluxOpenClosureInclusion (q : ℤ) :
    C(closure (openCubeSet (originCube 2 q)), closure (cubeSet (originCube 2 q))) := by
  let Q := originCube 2 q
  exact ⟨fun x => ⟨x.1, closure_mono (openCubeSet_subset_cubeSet Q) x.2⟩,
    continuous_subtype_val.subtype_mk _⟩

/-- Restrict a compact closed-cube coefficient to the response coefficient
carrier over the open cube. -/
noncomputable def pureFluxOpenResponseRestriction (q : ℤ) :
    C(closure (cubeSet (originCube 2 q)), ℝ) →L[ℝ]
      ResponseCoefficient (openCubeSet (originCube 2 q)) :=
  (BoundedContinuousFunction.compContinuousCLM ℝ ℝ
    (pureFluxOpenClosureInclusion q)).comp
      (ContinuousMap.linearIsometryBoundedOfCompact
        (closure (cubeSet (originCube 2 q))) ℝ ℝ).toContinuousLinearEquiv.toContinuousLinearMap

/-- Restriction preserves the scalar coefficient on the open observation
cube. -/
theorem pureFluxOpenResponseRestriction_value (q : ℤ)
    (k : C(closure (cubeSet (originCube 2 q)), ℝ)) {x : Vec 2}
    (hx : x ∈ openCubeSet (originCube 2 q)) :
    responseCoefficientExtension (pureFluxOpenResponseRestriction q k) x =
      k ⟨x, subset_closure (openCubeSet_subset_cubeSet (originCube 2 q) hx)⟩ := by
  rw [responseCoefficientExtension_eq _ hx]
  simp [pureFluxOpenResponseRestriction, pureFluxOpenClosureInclusion,
    BoundedContinuousFunction.compContinuousCLM_apply,
    ContinuousMap.linearIsometryBoundedOfCompact_apply_apply]

/-- The physical coefficient and its open-cube fixed-frame coefficient agree
after the scalar frame rescaling, almost everywhere on the observation cube. -/
theorem pureFluxOpenResponseRestriction_frame_ae (q : ℤ) (ν σ : ℝ)
    (k : C(closure (cubeSet (originCube 2 q)), ℝ)) (hσ : 0 < σ) :
    responseFramePlanarCoefficientField ν σ (pureFluxOpenResponseRestriction q k) =ᵐ[
      volume.restrict (openCubeSet (originCube 2 q))]
      σ⁻¹ • responsePlanarCoefficientField ν
        (ContinuousMap.linearIsometryBoundedOfCompact
          (closure (cubeSet (originCube 2 q))) ℝ ℝ k) := by
  filter_upwards [ae_restrict_mem (measurableSet_openCubeSet (originCube 2 q))]
    with x hx
  have hvalue := pureFluxOpenResponseRestriction_value q k hx
  have hclosed : responseCoefficientExtension
      (ContinuousMap.linearIsometryBoundedOfCompact
        (closure (cubeSet (originCube 2 q))) ℝ ℝ k) x =
      k ⟨x, subset_closure (openCubeSet_subset_cubeSet (originCube 2 q) hx)⟩ := by
    rw [responseCoefficientExtension_eq _ (openCubeSet_subset_cubeSet (originCube 2 q) hx)]
    simp only [ContinuousMap.linearIsometryBoundedOfCompact_apply_apply]
  change responsePlanarCoefficient (ν / σ)
      (responseCoefficientExtension (pureFluxOpenResponseRestriction q k) x / σ) =
    σ⁻¹ • responsePlanarCoefficient ν
      (responseCoefficientExtension
        (ContinuousMap.linearIsometryBoundedOfCompact
          (closure (cubeSet (originCube 2 q))) ℝ ℝ k) x)
  rw [hvalue, hclosed]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [responsePlanarCoefficient, responsePlanarJ, Matrix.smul_apply, smul_eq_mul] <;>
    field_simp [hσ.ne']

/-- The closed heat trace is the open-cube frozen Lemma-V trace after
restricting each physical coefficient direction. -/
theorem modelTraceObservable_eq_lemmaVTrace_openRestriction
    (q : ℤ) (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (k : C(closure (cubeSet (originCube 2 q)), ℝ)) :
    modelTraceObservable q ν σ k =
      lemmaVTrace q ν σ (pureFluxOpenResponseRestriction q k) := by
  let Q := originCube 2 q
  let U := openCubeSet Q
  let a := responsePlanarCoefficientField ν
    (ContinuousMap.linearIsometryBoundedOfCompact (closure (cubeSet Q)) ℝ ℝ k)
  let af := responseFramePlanarCoefficientField ν σ (pureFluxOpenResponseRestriction q k)
  have hEll : IsEllipticFieldOn ν
      ((ν ^ 2 + ‖ContinuousMap.linearIsometryBoundedOfCompact
        (closure (cubeSet Q)) ℝ ℝ k‖ ^ 2) / ν) (cubeSet Q) a := by
    simpa [a] using responsePlanarCoefficientField_isElliptic
      (measurableSet_cubeSet Q) ν hν
        (ContinuousMap.linearIsometryBoundedOfCompact (closure (cubeSet Q)) ℝ ℝ k)
  have hae := pureFluxOpenResponseRestriction_frame_ae q ν σ k hσ
  have htraceOpen :
      traceDefect (cubeSet Q) af 1 =
        traceDefect U (σ⁻¹ • a) 1 := by
    unfold traceDefect
    rw [coarseBlockMatrix_cubeSet_originCube_eq_openCubeSet]
    rw [coarseBlockMatrix_congr_of_ae_eq (U := U) hae]
  calc
    modelTraceObservable q ν σ k = traceDefect (cubeSet Q) a σ := rfl
    _ = traceDefect U (σ⁻¹ • a) 1 := (cold_trace_frame hν hEll hσ).symm
    _ = traceDefect (cubeSet Q) af 1 := htraceOpen.symm
    _ = lemmaVTrace q ν σ (pureFluxOpenResponseRestriction q k) := by
      rfl

/-- The actual heat covariance trace splits into the four open-cube affine
response Hessian traces. Each term is evaluated at the same restricted
coefficient and covariance directions. -/
theorem modelTrace_covarianceTrace_eq_open_four_load_hessians
    (q : ℤ) (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (H : ℕ → C(closure (cubeSet (originCube 2 q)), ℝ))
    (hH : Summable (fun j => ‖H j‖ ^ 2))
    (x : C(closure (cubeSet (originCube 2 q)), ℝ)) :
    modelCovarianceTrace (modelTraceObservable q ν σ) H x =
      (∑' j, pureFluxResponseHessianDiagonal
        (measurableSet_openCubeSet (originCube 2 q))
        (volume_openCubeSet_originCube_toReal_pos (d := 2) q)
        ν σ hν hσ (orthonormalFrameLoad 0 1)
        (pureFluxOpenResponseRestriction q x)
        (pureFluxOpenResponseRestriction q (H j))) +
      (∑' j, pureFluxResponseHessianDiagonal
        (measurableSet_openCubeSet (originCube 2 q))
        (volume_openCubeSet_originCube_toReal_pos (d := 2) q)
        ν σ hν hσ (orthonormalFrameLoad 0 (-1))
        (pureFluxOpenResponseRestriction q x)
        (pureFluxOpenResponseRestriction q (H j))) +
      (∑' j, pureFluxResponseHessianDiagonal
        (measurableSet_openCubeSet (originCube 2 q))
        (volume_openCubeSet_originCube_toReal_pos (d := 2) q)
        ν σ hν hσ (orthonormalFrameLoad 1 1)
        (pureFluxOpenResponseRestriction q x)
        (pureFluxOpenResponseRestriction q (H j))) +
      (∑' j, pureFluxResponseHessianDiagonal
        (measurableSet_openCubeSet (originCube 2 q))
        (volume_openCubeSet_originCube_toReal_pos (d := 2) q)
        ν σ hν hσ (orthonormalFrameLoad 1 (-1))
        (pureFluxOpenResponseRestriction q x)
        (pureFluxOpenResponseRestriction q (H j))) := by
  let U := openCubeSet (originCube 2 q)
  let L := pureFluxOpenResponseRestriction q
  let E (i : Fin 2) (r : ℝ) : ResponseCoefficient U → ℝ :=
    fun z => responseFrameEnergyObservable
      (measurableSet_openCubeSet (originCube 2 q))
      (volume_openCubeSet_originCube_toReal_pos (d := 2) q)
      ν σ hν hσ (orthonormalFrameLoad i r) z
  have htrace : modelTraceObservable q ν σ = fun z => lemmaVTrace q ν σ (L z) :=
    funext (modelTraceObservable_eq_lemmaVTrace_openRestriction q ν σ hν hσ)
  have hE (i : Fin 2) (r : ℝ) : ContDiff ℝ 2 (E i r) := by
    dsimp [E]
    exact responseFrameEnergyObservable_contDiff
      (measurableSet_openCubeSet (originCube 2 q))
      (volume_openCubeSet_originCube_toReal_pos (d := 2) q)
      ν σ hν hσ (orthonormalFrameLoad i r)
  have hEq : lemmaVTrace q ν σ = fun z =>
      ((E 0 1 z + E 0 (-1) z) + (E 1 1 z + E 1 (-1) z)) - 4 := by
    funext z
    rw [lemmaVTrace_eq_load_sum q ν σ hν hσ]
    simp [E, lemmaVLoadEnergy, lemmaVLoadSign, Fintype.sum_prod_type,
      Fin.sum_univ_two]
  have hcomp : modelCovarianceTrace (fun z => lemmaVTrace q ν σ (L z)) H x =
      modelCovarianceTrace (lemmaVTrace q ν σ) (fun j => L (H j)) (L x) := by
    exact pureFluxOpen_modelCovarianceTrace_comp_linear (lemmaVTrace q ν σ)
      (by rw [hEq]; fun_prop) L H x
  have hLnorm : ‖L‖ ≤ 1 := by
    apply L.opNorm_le_bound zero_le_one
    intro z
    change ‖(ContinuousMap.linearIsometryBoundedOfCompact
        (closure (cubeSet (originCube 2 q))) ℝ ℝ z).compContinuous
          (pureFluxOpenClosureInclusion q)‖ ≤ 1 * ‖z‖
    calc
      _ ≤ ‖ContinuousMap.linearIsometryBoundedOfCompact
            (closure (cubeSet (originCube 2 q))) ℝ ℝ z‖ :=
        BoundedContinuousFunction.norm_compContinuous_le _ _
      _ = 1 * ‖z‖ := by simp
  have hHL : Summable (fun j => ‖L (H j)‖ ^ 2) :=
    Summable.of_nonneg_of_le (fun _ => sq_nonneg _) (fun j => by
      have hj : ‖L (H j)‖ ≤ ‖H j‖ := by
        calc
          ‖L (H j)‖ ≤ ‖L‖ * ‖H j‖ := L.le_opNorm _
          _ ≤ 1 * ‖H j‖ := mul_le_mul_of_nonneg_right hLnorm (norm_nonneg _)
          _ = ‖H j‖ := one_mul _
      exact pow_le_pow_left₀ (norm_nonneg _) hj 2) hH
  have hAdd (f g : ResponseCoefficient U → ℝ)
      (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (z : ResponseCoefficient U) :=
    @pureFluxOpen_modelCovarianceTrace_add (ResponseCoefficient U) _ _
      (fun j => L (H j)) hHL f g hf hg z
  have hconst : modelCovarianceTrace (fun _ : ResponseCoefficient U => (-4 : ℝ))
      (fun j => L (H j)) (L x) = 0 := by
    simp [modelCovarianceTrace, secondDirectionalDerivative]
  rw [htrace, hcomp, hEq]
  have h0 : modelCovarianceTrace (fun z => E 0 1 z + E 0 (-1) z)
      (fun j => L (H j)) (L x) =
      modelCovarianceTrace (E 0 1) (fun j => L (H j)) (L x) +
        modelCovarianceTrace (E 0 (-1)) (fun j => L (H j)) (L x) :=
    hAdd (E 0 1) (E 0 (-1)) (hE 0 1) (hE 0 (-1)) (L x)
  have h1 : modelCovarianceTrace (fun z => E 1 1 z + E 1 (-1) z)
      (fun j => L (H j)) (L x) =
      modelCovarianceTrace (E 1 1) (fun j => L (H j)) (L x) +
        modelCovarianceTrace (E 1 (-1)) (fun j => L (H j)) (L x) :=
    hAdd (E 1 1) (E 1 (-1)) (hE 1 1) (hE 1 (-1)) (L x)
  have hout : modelCovarianceTrace
      (fun z => (E 0 1 z + E 0 (-1) z) + (E 1 1 z + E 1 (-1) z))
      (fun j => L (H j)) (L x) =
      modelCovarianceTrace (fun z => E 0 1 z + E 0 (-1) z)
        (fun j => L (H j)) (L x) +
      modelCovarianceTrace (fun z => E 1 1 z + E 1 (-1) z)
        (fun j => L (H j)) (L x) :=
    hAdd (fun z => E 0 1 z + E 0 (-1) z)
      (fun z => E 1 1 z + E 1 (-1) z)
      ((hE 0 1).add (hE 0 (-1))) ((hE 1 1).add (hE 1 (-1))) (L x)
  have houter : modelCovarianceTrace
      (fun z => ((E 0 1 z + E 0 (-1) z) + (E 1 1 z + E 1 (-1) z)) + (-4))
      (fun j => L (H j)) (L x) =
      modelCovarianceTrace
        (fun z => (E 0 1 z + E 0 (-1) z) + (E 1 1 z + E 1 (-1) z))
        (fun j => L (H j)) (L x) +
      modelCovarianceTrace (fun _ : ResponseCoefficient U => (-4 : ℝ))
        (fun j => L (H j)) (L x) :=
    hAdd (fun z => (E 0 1 z + E 0 (-1) z) + (E 1 1 z + E 1 (-1) z))
      (fun _ => -4) ((hE 0 1).add (hE 0 (-1)) |>.add ((hE 1 1).add (hE 1 (-1))))
      contDiff_const (L x)
  have hsub : (fun z : ResponseCoefficient U =>
      ((E 0 1 z + E 0 (-1) z) + (E 1 1 z + E 1 (-1) z)) - 4) =
      fun z => ((E 0 1 z + E 0 (-1) z) + (E 1 1 z + E 1 (-1) z)) + (-4) := by
    funext z
    ring
  rw [hsub, houter, hconst, hout, h0, h1]
  simp only [E]
  rw [responseFrameEnergyObservable_covarianceTrace_eq_hessianDiagonal_sum,
    responseFrameEnergyObservable_covarianceTrace_eq_hessianDiagonal_sum,
    responseFrameEnergyObservable_covarianceTrace_eq_hessianDiagonal_sum,
    responseFrameEnergyObservable_covarianceTrace_eq_hessianDiagonal_sum]
  ring

end
end ASDExplicitGamma.Inverse
