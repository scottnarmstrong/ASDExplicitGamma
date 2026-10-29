module

public import ASDExplicitGamma.Inverse.FullResponseDescendantSensitivity

/-! The actual descendant trace includes its local later-wave mean as an
explicit shear payment, while retaining the parent's sensitivity gate. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse

open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Triadic ASDExplicitGamma.Response ASDExplicitGamma.Variational

noncomputable section

/-- On every cube contained in a good parent, the actual attenuated response
trace is bounded by the old full trace and the exact local wave-mean shear
term, in the parent's completed-label frame. -/
theorem good_parent_descendant_actual_full_normalized_trace (M : ABKModel 2)
    {Q R : TriadicCube 2} {j : ℕ} (hR : R ∈ descendantsAtDepth Q j)
    (r : RootRow) (m J : ℤ) (hn : Q.scale + 40 ≤ m) (hm : m ≤ J)
    (weights : ℤ → ℝ)
    (hw : ∀ k ∈ Finset.Ioc m J, 0 ≤ weights k ∧ weights k ≤ 1)
    (ω : Cutoff.CutoffSample 2)
    (hgood : ω ∉ cellFailure M (rootTau r)
      (ASDExplicitGamma.Gaussian.waveGateEta (rootWaveTuple r)) Q) :
    let n := Q.scale + 40
    let h := laterBandW2 Q n J (sourceBandWeights m weights) ω
    let hR' := h.restrict hR
    let μ := cubeAverage R hR'.value.toFun
    let σ := (Annealed.sigmaBar M n : ℝ)
    let g := μ / σ
    let B := coarseBlockMatrix (cubeSet R) (Cutoff.coefficientCutoff M.nu n ω).toFun
    Matrix.trace (toFullBlockMat (frameMatrix σ
      (coarseBlockMatrix (cubeSet R) (attenuatedCoefficient M m J weights ω)))) / 4 ≤
      rootEdelta r * Matrix.trace (toFullBlockMat (frameMatrix σ B)) / 2 - 1 +
        g^2 * rootEdelta r * Matrix.trace (frameMatrix σ B).lowerRight / 2 := by
  dsimp only
  let n := Q.scale + 40
  let a := sourceBandWeights m weights
  let k := oldResponseCoefficient Q n ω
  let kH := laterResponseCoefficient Q n J a ω
  let h := laterBandW2 Q n J a ω
  let hR' := h.restrict hR
  let μ := cubeAverage R hR'.value.toFun
  let σ := (Annealed.sigmaBar M n : ℝ)
  let g := μ / σ
  let B := coarseBlockMatrix (cubeSet R) (Cutoff.coefficientCutoff M.nu n ω).toFun
  let kR := sensitivityResponseCoefficientRestrict k hR
  let kHR := sensitivityResponseCoefficientRestrict kH hR
  let kHR0 := kHR + BoundedContinuousFunction.const (closure (openCubeSet R)) (-μ)
  let kC := sensitivityResponseCoefficientPath kR kHR0 1
  let kClosed := responseCoefficientOnClosedCube R kC
  have hσ : 0 < σ := (Annealed.sigmaBar_characterization M n).1
  have hcenter := good_parent_descendant_centered_full_pair_response
    M hR r m J weights hw ω hgood
  have hcenterField : (fun x => responsePlanarCoefficientField M.nu kClosed x) =ᵐ[
      volume.restrict (openCubeSet R)] (sensitivityBaseRegField M.nu kC).toFun := by
    filter_upwards [ae_restrict_mem (measurableSet_openCubeSet R)] with x hx
    have hxR : x ∈ cubeSet R := openCubeSet_subset_cubeSet R hx
    have hext := responseCoefficientOnClosedCube_extension_eq R kC hxR
    have hh := congrArg (fun z : ℝ => responsePlanarCoefficient M.nu z) hext
    simpa [sensitivityBaseRegField, responseFramePlanarCoefficientField,
      responsePlanarCoefficientField] using hh
  have hcenterMatrix :
      coarseBlockMatrix (cubeSet R) (responsePlanarCoefficientField M.nu kClosed) =
        coarseBlockMatrix (cubeSet R) (sensitivityBaseRegField M.nu kC).toFun := by
    rw [coarseBlockMatrix_cubeSet_eq_openCubeSet_of_triadicCube R,
      coarseBlockMatrix_cubeSet_eq_openCubeSet_of_triadicCube R]
    exact coarseBlockMatrix_congr_of_ae_eq hcenterField
  have hpair : ∀ P : BlockVec 2,
      blockVecDot P (blockMatVecMul
        (coarseBlockMatrix (cubeSet R) (responsePlanarCoefficientField M.nu kClosed)) P) ≤
        rootEdelta r * blockVecDot P (blockMatVecMul B P) := by
    intro P
    rw [hcenterMatrix]
    exact hcenter P
  have hmeanShift : σ * g = μ := by
    dsimp only [g]
    field_simp [hσ.ne']
  have hcenterLoad (x : Vec 2) (hx : x ∈ openCubeSet R) :
      responseCoefficientExtension kC x =
        responseCoefficientExtension k x + responseCoefficientExtension kH x - μ := by
    have hxQ : x ∈ openCubeSet Q :=
      openCubeSet_subset_of_mem_descendantsAtDepth hR hx
    have hext : responseCoefficientExtension kR x = responseCoefficientExtension k x := by
      let hsub := openCubeSet_subset_of_mem_descendantsAtDepth hR
      let incl : C(closure (openCubeSet R), closure (openCubeSet Q)) :=
        ⟨fun z => ⟨z.1, (closure_mono hsub) z.2⟩,
          continuous_subtype_val.subtype_mk fun z => (closure_mono hsub) z.2⟩
      rw [responseCoefficientExtension_eq kR hx,
        responseCoefficientExtension_eq k hxQ]
      change (k.compContinuous incl) ⟨x, subset_closure hx⟩ =
        k ⟨x, subset_closure (hsub hx)⟩
      rw [BoundedContinuousFunction.compContinuous_apply]
      congr 1
    have hextH : responseCoefficientExtension kHR x = responseCoefficientExtension kH x := by
      let hsub := openCubeSet_subset_of_mem_descendantsAtDepth hR
      let incl : C(closure (openCubeSet R), closure (openCubeSet Q)) :=
        ⟨fun z => ⟨z.1, (closure_mono hsub) z.2⟩,
          continuous_subtype_val.subtype_mk fun z => (closure_mono hsub) z.2⟩
      rw [responseCoefficientExtension_eq kHR hx,
        responseCoefficientExtension_eq kH hxQ]
      change (kH.compContinuous incl) ⟨x, subset_closure hx⟩ =
        kH ⟨x, subset_closure (hsub hx)⟩
      rw [BoundedContinuousFunction.compContinuous_apply]
      congr 1
    change responseCoefficientExtension (sensitivityResponseCoefficientPath kR kHR0 1) x = _
    rw [sensitivityResponseCoefficientPath, one_smul,
      responseCoefficientExtension_add_on kR kHR0 hx,
      responseCoefficientExtension_add_on kHR
        (BoundedContinuousFunction.const (closure (openCubeSet R)) (-μ)) hx,
      responseCoefficientExtension_eq
        (BoundedContinuousFunction.const (closure (openCubeSet R)) (-μ)) hx]
    simp only [BoundedContinuousFunction.const_apply]
    rw [hext, hextH]
    ring
  have hfield : (fun x => responsePlanarCoefficient M.nu
      (responseCoefficientExtension kClosed x + σ * g)) =ᵐ[
        volume.restrict (openCubeSet R)] attenuatedCoefficient M m J weights ω := by
    filter_upwards [ae_restrict_mem (measurableSet_openCubeSet R)] with x hx
    have hxQ : x ∈ openCubeSet Q :=
      openCubeSet_subset_of_mem_descendantsAtDepth hR hx
    have hext := responseCoefficientOnClosedCube_extension_eq R kC
      (openCubeSet_subset_cubeSet R hx)
    have hsum : responseCoefficientExtension kClosed x + σ * g =
        responseCoefficientExtension k x + responseCoefficientExtension kH x := by
      rw [hext, hmeanShift, hcenterLoad x hx]
      ring
    have hpath := sensitivity_path_represents_attenuated M Q n m J hn hm weights ω hxQ
    simp only [sensitivityBaseRegField, responseFramePlanarCoefficientField,
      div_one] at hpath
    rw [hsum, ← responseCoefficientExtension_add_on k kH hxQ]
    exact hpath
  have hactualMatrix :
      coarseBlockMatrix (cubeSet R) (attenuatedCoefficient M m J weights ω) =
        coarseBlockMatrix (cubeSet R) (fun x => responsePlanarCoefficient M.nu
          (responseCoefficientExtension kClosed x + σ * g)) := by
    rw [coarseBlockMatrix_cubeSet_eq_openCubeSet_of_triadicCube R,
      coarseBlockMatrix_cubeSet_eq_openCubeSet_of_triadicCube R]
    exact coarseBlockMatrix_congr_of_ae_eq hfield.symm
  have hdefect : traceDefect (cubeSet R) (attenuatedCoefficient M m J weights ω) σ =
      traceDefect (cubeSet R)
        (fun x => responsePlanarCoefficient M.nu
          (responseCoefficientExtension kClosed x + σ * g)) σ := by
    unfold traceDefect
    rw [hactualMatrix]
  have htrace := traceDefect_eq_full_framedTrace (cubeSet R)
    (attenuatedCoefficient M m J weights ω) σ
  have hdef := full_response_shear_trace_bound_of_pair_control R M.nu σ g
    (rootEdelta r) M.nu_pos hσ kClosed B hpair
  rw [← hdefect] at hdef
  have htrace' : Matrix.trace (toFullBlockMat (frameMatrix σ
      (coarseBlockMatrix (cubeSet R) (attenuatedCoefficient M m J weights ω)))) =
      traceDefect (cubeSet R) (attenuatedCoefficient M m J weights ω) σ + 4 := by
    linarith only [htrace]
  nlinarith only [hdef, htrace']

end
end ASDExplicitGamma.Inverse
