module

public import ASDExplicitGamma.Scalar.OldHessianTrialUnitHeat
public import ASDExplicitGamma.Main.DirectionalSymmetry
public import ASDExplicitGamma.Inverse.BankHeatIntegrability

/-! Isotropy of the OLD heat average of `e . D e`: coordinate swap and sign flip
of the cutoff sample force the expected matrix to be a multiple of the identity. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Native Response Triadic Variational Gaussian Inverse Main Algsuperdiff.Section3
open Set
noncomputable section

private theorem old_hessian_swap_matrix : Matrix.swap ℝ (0:Fin 2) 1 = !![0,1;1,0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.swap]

theorem old_hessian_quad_swap (X : Mat 2) (e : Vec 2) :
    vecDot e (matVecMul (Matrix.swap ℝ 0 1 * X * Matrix.swap ℝ 0 1) e) =
      vecDot ![e 1,e 0] (matVecMul X ![e 1,e 0]) := by
  rw [old_hessian_swap_matrix]
  simp [vecDot,matVecMul,Matrix.mul_apply,Fin.sum_univ_two,Matrix.vecMul,dotProduct]
  ring

theorem old_hessian_quad_flip (X : Mat 2) (e : Vec 2) :
    vecDot e (matVecMul (signFlipMatrix 0 * X * signFlipMatrix 0) e) =
      vecDot ![-e 0,e 1] (matVecMul X ![-e 0,e 1]) := by
  simp [vecDot,matVecMul,Matrix.mul_apply,Fin.sum_univ_two,signFlipMatrix]
  ring

theorem old_hessian_quad_expand (X : Mat 2) (e : Vec 2) :
    vecDot e (matVecMul X e) = e 0^2*vecDot ![1,0] (matVecMul X ![1,0])+
      e 1^2*vecDot ![0,1] (matVecMul X ![0,1])+
      e 0*e 1*(vecDot ![1,1] (matVecMul X ![1,1])-vecDot ![1,0] (matVecMul X ![1,0])-
        vecDot ![0,1] (matVecMul X ![0,1])) := by
  simp [vecDot,matVecMul,Fin.sum_univ_two]
  ring

/-- Matrix of the unit observable for the partially inserted OLD coefficient. -/
def oldHessianUnitMatrix (M : ABKModel 2) (m n : ℤ) (t : ℝ) (ω : Cutoff.CutoffSample 2) : Mat 2 :=
  (Annealed.sigmaBar M m : ℝ)•(coarseBlockMatrix (openCubeSet (originCube 2 n))
    (Model.partialInsertedCoefficient M m t ω).toFun).lowerRight

private theorem old_hessian_symm_inserted (M : ABKModel 2) (m : ℤ) (t : ℝ)
    (ω : Cutoff.CutoffSample 2) (x : Vec 2) :
    symmPart (Model.partialInsertedCoefficient M m t ω x) = M.nu • (1 : Mat 2) := by
  have ha := Cutoff.symmPart_coefficientCutoff M.nu m ω x
  ext i j
  have hb := congrFun (congrFun ha i) j
  have hj := (ω.1 (m + 1)).skew_entry x i j
  change (Cutoff.coefficientCutoff M.nu m ω x i j +
    Cutoff.coefficientCutoff M.nu m ω x j i) / 2 = (M.nu • (1 : Mat 2)) i j at hb
  change ((Cutoff.coefficientCutoff M.nu m ω x i j + Real.sqrt t * ω.1 (m + 1) x i j) +
    (Cutoff.coefficientCutoff M.nu m ω x j i + Real.sqrt t * ω.1 (m + 1) x j i)) / 2 = _
  rw [hj]
  linarith

theorem old_hessian_unit_observable_inserted (M : ABKModel 2) (n m : ℤ) (t : ℝ)
    (ω : Cutoff.CutoffSample 2) (e : Vec 2) :
    oldHessianUnitObservable n M.nu (Annealed.sigmaBar M m : ℝ) e
      (modelInsertedScalar (closure (cubeSet (originCube 2 n))) m t ω) =
      vecDot e (matVecMul (oldHessianUnitMatrix M m n t ω) e) := by
  obtain ⟨ell,hK⟩ := exists_originCube_containing_compact _
    (isBounded_cubeSet (originCube 2 n)).isCompact_closure
  have heq : ∀ x ∈ cubeSet (originCube 2 n),
      responsePlanarCoefficientField M.nu
        (ContinuousMap.linearIsometryBoundedOfCompact _ ℝ ℝ
          (modelInsertedScalar (closure (cubeSet (originCube 2 n))) m t ω)) x =
        Model.partialInsertedCoefficient M m t ω x := by
    intro x hx
    rw [responsePlanarCoefficientField,responseCoefficientExtension_eq _ hx,
      ContinuousMap.linearIsometryBoundedOfCompact_apply_apply,
      modelInsertedScalar_apply _ M ell m hK]
    exact planar_coefficient_eq_of_symmPart M.nu _ (old_hessian_symm_inserted M m t ω x)
  have hae := (ae_restrict_mem (μ := volume) (measurableSet_cubeSet (originCube 2 n))).mono heq
  unfold oldHessianUnitObservable oldHessianUnitMatrix
  rw [coarseBlockMatrix_congr_of_ae_eq hae,coarseBlockMatrix_cubeSet_eq_openCubeSet_of_triadicCube]
  simp [vecDot,matVecMul,Matrix.smul_apply,Fin.sum_univ_two]
  ring

/-- Heat average of the unit observable. -/
def oldHessianUnitHeat (M : ABKModel 2) (n m : ℤ) (e : Vec 2) (t : ℝ) : ℝ :=
  ∫ ω,vecDot e (matVecMul (oldHessianUnitMatrix M m n t ω) e) ∂(Cutoff.cutoffSampleLaw M).toMeasure

theorem old_hessian_unit_heat_eq (M : ABKModel 2) (n m : ℤ) (e : Vec 2) :
    oldHessianUnitHeat M n m e = modelHeatAverage (closure (cubeSet (originCube 2 n))) M m
      (oldHessianUnitObservable n M.nu (Annealed.sigmaBar M m : ℝ) e) := by
  funext t
  unfold oldHessianUnitHeat modelHeatAverage
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun ω => (old_hessian_unit_observable_inserted M n m t ω e).symm)

theorem old_hessian_unit_integrable (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (n m : ℤ) (e : Vec 2) (t : ℝ) :
    Integrable (fun ω => vecDot e (matVecMul (oldHessianUnitMatrix M m n t ω) e))
      (Cutoff.cutoffSampleLaw M).toMeasure := by
  obtain ⟨ell,hK⟩ := exists_originCube_containing_compact _
    (isBounded_cubeSet (originCube 2 n)).isCompact_closure
  have hΦ := old_hessian_unit_observable_C2 n M.nu (Annealed.sigmaBar M m : ℝ) M.nu_pos
    (Annealed.sigmaBar_characterization M m).1 e
  have hg : HasPolynomialGrowth (oldHessianUnitObservable n M.nu (Annealed.sigmaBar M m : ℝ) e) := by
    obtain ⟨_,C,hC,d,hv,_,_⟩ := hΦ
    exact ⟨C,hC,d,hv⟩
  have hi := bank_model_heat_integrable (closure (cubeSet (originCube 2 n))) M h hM ell m hK _
    hΦ.1.continuous.measurable hg t
  refine hi.congr (Filter.Eventually.of_forall (fun ω => ?_))
  exact old_hessian_unit_observable_inserted M n m t ω e

theorem old_hessian_vecDot_smul (c : ℝ) (X : Mat 2) (e : Vec 2) :
    vecDot e (matVecMul (c•X) e) = c*vecDot e (matVecMul X e) := by
  simp [vecDot,matVecMul,Matrix.smul_apply,Fin.sum_univ_two]
  ring

theorem old_hessian_integral_rotate (M : ABKModel 2) (R : Mat 2) (hR : IsSignedPermutationMatrix R)
    (f : Cutoff.CutoffSample 2 → ℝ)
    (hf : AEStronglyMeasurable f (Cutoff.cutoffSampleLaw M).toMeasure) :
    ∫ ω,f (Cutoff.rotateCutoffSample R hR ω) ∂(Cutoff.cutoffSampleLaw M).toMeasure =
      ∫ ω,f ω ∂(Cutoff.cutoffSampleLaw M).toMeasure := by
  have hmap := Cutoff.map_rotateCutoffSample_cutoffSampleLaw M R hR
  have hmeas := Cutoff.measurable_rotateCutoffSample R hR
  have hf' : AEStronglyMeasurable f (Measure.map (Cutoff.rotateCutoffSample R hR)
      (Cutoff.cutoffSampleLaw M).toMeasure) := by rw [hmap]; exact hf
  calc _ = ∫ ω,f ω ∂(Measure.map (Cutoff.rotateCutoffSample R hR) (Cutoff.cutoffSampleLaw M).toMeasure) :=
        (integral_map hmeas.aemeasurable hf').symm
    _ = _ := by rw [hmap]

/-- Heat averages of the unit observable are invariant under coordinate swap and
sign flip of the direction, hence isotropic. -/
theorem old_hessian_unit_heat_isotropic (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (n m : ℤ) (t : ℝ) (ht : 0≤t ∧ t≤1) (e : Vec 2) (he : e 0^2+e 1^2=1) :
    oldHessianUnitHeat M n m e t = oldHessianUnitHeat M n m ![1,0] t ∧
    oldHessianUnitHeat M n m ![0,1] t = oldHessianUnitHeat M n m ![1,0] t := by
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let g := fun (e : Vec 2) (ω : Cutoff.CutoffSample 2) => vecDot e (matVecMul (oldHessianUnitMatrix M m n t ω) e)
  let H := fun e : Vec 2 => ∫ ω,g e ω ∂μ
  have hH : ∀ e, oldHessianUnitHeat M n m e t=H e := fun e => rfl
  have hint (e : Vec 2) : Integrable (g e) μ := old_hessian_unit_integrable M h hM n m e t
  have hS : ∀ e : Vec 2, H ![e 1,e 0]=H e := by
    intro e
    have hcov (ω : Cutoff.CutoffSample 2) : g e (Cutoff.rotateCutoffSample (Matrix.swap ℝ 0 1)
        (isSignedPermutationMatrix_swap 0 1) ω) = g ![e 1,e 0] ω := by
      have h1 := main_partialInsertedCoefficient_rotateCutoffSample M m t ω (Matrix.swap ℝ 0 1)
        (isSignedPermutationMatrix_swap 0 1)
      have h2 := mainInsertion_coarseBlockMatrix_swap M m n t ω ht 0 1
      have h3 : oldHessianUnitMatrix M m n t (Cutoff.rotateCutoffSample (Matrix.swap ℝ 0 1)
          (isSignedPermutationMatrix_swap 0 1) ω) =
          (Annealed.sigmaBar M m : ℝ)•(Matrix.swap ℝ 0 1*(coarseBlockMatrix (openCubeSet (originCube 2 n))
            (Model.partialInsertedCoefficient M m t ω).toFun).lowerRight*Matrix.swap ℝ 0 1) := by
        unfold oldHessianUnitMatrix
        rw [h1,h2]
        simp [blockMatConj]
      change vecDot e (matVecMul (oldHessianUnitMatrix M m n t _) e) = _
      rw [h3,old_hessian_vecDot_smul,old_hessian_quad_swap,←old_hessian_vecDot_smul]
      rfl
    calc H ![e 1,e 0] = ∫ ω,g ![e 1,e 0] ω ∂μ := rfl
      _ = ∫ ω,g e (Cutoff.rotateCutoffSample (Matrix.swap ℝ 0 1) (isSignedPermutationMatrix_swap 0 1) ω) ∂μ :=
        integral_congr_ae (Filter.Eventually.of_forall (fun ω => (hcov ω).symm))
      _ = H e := old_hessian_integral_rotate M _ _ (g e) (hint e).aestronglyMeasurable
  have hF : ∀ e : Vec 2, H ![-e 0,e 1]=H e := by
    intro e
    have hcov (ω : Cutoff.CutoffSample 2) : g e (Cutoff.rotateCutoffSample (signFlipMatrix 0)
        (isSignedPermutationMatrix_signFlipMatrix 0) ω) = g ![-e 0,e 1] ω := by
      have h1 := main_partialInsertedCoefficient_rotateCutoffSample M m t ω (signFlipMatrix 0)
        (isSignedPermutationMatrix_signFlipMatrix 0)
      have h2 := mainInsertion_coarseBlockMatrix_signFlip M m n t ω ht 0
      have h3 : oldHessianUnitMatrix M m n t (Cutoff.rotateCutoffSample (signFlipMatrix 0)
          (isSignedPermutationMatrix_signFlipMatrix 0) ω) =
          (Annealed.sigmaBar M m : ℝ)•(signFlipMatrix 0*(coarseBlockMatrix (openCubeSet (originCube 2 n))
            (Model.partialInsertedCoefficient M m t ω).toFun).lowerRight*signFlipMatrix 0) := by
        unfold oldHessianUnitMatrix
        rw [h1,h2]
        simp [blockMatConj]
      change vecDot e (matVecMul (oldHessianUnitMatrix M m n t _) e) = _
      rw [h3,old_hessian_vecDot_smul,old_hessian_quad_flip,←old_hessian_vecDot_smul]
      rfl
    calc H ![-e 0,e 1] = ∫ ω,g ![-e 0,e 1] ω ∂μ := rfl
      _ = ∫ ω,g e (Cutoff.rotateCutoffSample (signFlipMatrix 0) (isSignedPermutationMatrix_signFlipMatrix 0) ω) ∂μ :=
        integral_congr_ae (Filter.Eventually.of_forall (fun ω => (hcov ω).symm))
      _ = H e := old_hessian_integral_rotate M _ _ (g e) (hint e).aestronglyMeasurable
  have hq (e : Vec 2) : H e = e 0^2*H ![1,0]+e 1^2*H ![0,1]+e 0*e 1*(H ![1,1]-H ![1,0]-H ![0,1]) := by
    have hpt (ω : Cutoff.CutoffSample 2) : g e ω = e 0^2*g ![1,0] ω+e 1^2*g ![0,1] ω+
        e 0*e 1*(g ![1,1] ω-g ![1,0] ω-g ![0,1] ω) := by
      change vecDot e (matVecMul (oldHessianUnitMatrix M m n t ω) e) = _
      rw [old_hessian_quad_expand]
    have h0 := hint ![1,0]
    have h1 := hint ![0,1]
    have h2 := hint ![1,1]
    calc H e = ∫ ω,(e 0^2*g ![1,0] ω+e 1^2*g ![0,1] ω+e 0*e 1*(g ![1,1] ω-g ![1,0] ω-g ![0,1] ω)) ∂μ :=
          integral_congr_ae (Filter.Eventually.of_forall hpt)
      _ = _ := by
        have i0 : Integrable (fun ω => e 0^2*g ![1,0] ω) μ := h0.const_mul _
        have i1 : Integrable (fun ω => e 1^2*g ![0,1] ω) μ := h1.const_mul _
        have i01 : Integrable (fun ω => e 0^2*g ![1,0] ω+e 1^2*g ![0,1] ω) μ := i0.add i1
        have i21 : Integrable (fun ω => g ![1,1] ω-g ![1,0] ω) μ := h2.sub h0
        have i210 : Integrable (fun ω => g ![1,1] ω-g ![1,0] ω-g ![0,1] ω) μ := i21.sub h1
        have i3 : Integrable (fun ω => e 0*e 1*(g ![1,1] ω-g ![1,0] ω-g ![0,1] ω)) μ := i210.const_mul _
        rw [integral_add i01 i3,integral_add i0 i1,integral_const_mul,integral_const_mul,
          integral_const_mul,integral_sub i21 h1,integral_sub h2 h0]
  have hswap : H ![0,1]=H ![1,0] := by simpa using hS ![1,0]
  have hflip : H ![-1,1]=H ![1,1] := by simpa using hF ![1,1]
  have hq' : H ![-1,1]=H ![1,0]+H ![0,1]-(H ![1,1]-H ![1,0]-H ![0,1]) := by
    have hh := hq ![-1,1]
    simp at hh
    linarith
  have hb : H ![1,1]-H ![1,0]-H ![0,1]=0 := by linarith
  have hq1 := hq e
  refine ⟨?_,?_⟩
  · rw [hH,hH]
    rw [hb] at hq1
    have : e 1^2 = 1-e 0^2 := by linarith
    rw [hq1,hswap]
    have h2 : e 0^2*H ![1,0]+e 1^2*H ![1,0]=H ![1,0] := by rw [← add_mul,he,one_mul]
    linarith
  · rw [hH,hH]; exact hswap

theorem old_hessian_inverse_observable_unit_sum (n : ℤ) (nu sigma : ℝ)
    (x : C(closure (cubeSet (originCube 2 n)),ℝ)) :
    mainInverseObservable n nu sigma x =
      oldHessianUnitObservable n nu sigma ![1,0] x+oldHessianUnitObservable n nu sigma ![0,1] x := by
  simp [mainInverseObservable,oldHessianUnitObservable,Matrix.trace,vecDot,matVecMul,Fin.sum_univ_two]
  ring

/-- By the sample symmetries, the generator of `e . D e` is half the generator of the trace. -/
theorem old_hessian_unit_generator_half_trace (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (n m : ℤ) (e : Vec 2) (he : e 0^2+e 1^2=1) :
    (1/2:ℝ)*modelHeatTraceAverage (closure (cubeSet (originCube 2 n))) M m
      (oldHessianUnitObservable n M.nu (Annealed.sigmaBar M m : ℝ) e)
      (pureFluxMainCubeQ3Directions n (q3ModelAmplitude M h (m+1)) (q3ModelLength (m+1))) 0 =
    (1/2:ℝ)*((1/2:ℝ)*modelHeatTraceAverage (closure (cubeSet (originCube 2 n))) M m
      (mainInverseObservable n M.nu (Annealed.sigmaBar M m : ℝ))
      (pureFluxMainCubeQ3Directions n (q3ModelAmplitude M h (m+1)) (q3ModelLength (m+1))) 0) := by
  let σ : ℝ := Annealed.sigmaBar M m
  let K := closure (cubeSet (originCube 2 n))
  let Φ := fun v : Vec 2 => oldHessianUnitObservable n M.nu σ v
  have hC2 := fun v => old_hessian_unit_observable_C2 n M.nu σ M.nu_pos (Annealed.sigmaBar_characterization M m).1 v
  have hd := fun v => old_hessian_heat_deriv M h hM n m (Φ v) (hC2 v)
  have hinvC2 := mainInverseObservable_hasPolynomiallyBoundedC2Derivatives n M.nu σ M.nu_pos
    (Annealed.sigmaBar_characterization M m).1
  have hdt := old_hessian_heat_deriv M h hM n m _ hinvC2
  have hiso := fun t (ht : 0≤t∧t≤1) => old_hessian_unit_heat_isotropic M h hM n m t ht e he
  have hiso0 := fun t (ht : 0≤t∧t≤1) => old_hessian_unit_heat_isotropic M h hM n m t ht ![1,0] (by simp)
  have hnhd : Icc (0:ℝ) 1 ∈ nhdsWithin (0:ℝ) (Ici 0) := Icc_mem_nhdsGE (by norm_num)
  have hEq (v : Vec 2) : modelHeatAverage K M m (Φ v) = oldHessianUnitHeat M n m v :=
    (old_hessian_unit_heat_eq M n m v).symm
  -- trace heat average
  have hint := fun v t => old_hessian_unit_integrable M h hM n m v t
  have hTr : modelHeatAverage K M m (mainInverseObservable n M.nu σ) =
      fun t => oldHessianUnitHeat M n m ![1,0] t+oldHessianUnitHeat M n m ![0,1] t := by
    funext t
    unfold modelHeatAverage
    simp_rw [old_hessian_inverse_observable_unit_sum]
    rw [integral_add]
    · exact congrArg₂ (·+·) (congrFun (old_hessian_unit_heat_eq M n m ![1,0]) t).symm
        (congrFun (old_hessian_unit_heat_eq M n m ![0,1]) t).symm
    · exact (hint ![1,0] t).congr (Filter.Eventually.of_forall (fun ω =>
        (old_hessian_unit_observable_inserted M n m t ω ![1,0]).symm))
    · exact (hint ![0,1] t).congr (Filter.Eventually.of_forall (fun ω =>
        (old_hessian_unit_observable_inserted M n m t ω ![0,1]).symm))
  have hde := hd e
  have hd0 := hd ![1,0]
  rw [hEq] at hde hd0
  rw [hTr] at hdt
  have hfe : oldHessianUnitHeat M n m e =ᶠ[nhdsWithin (0:ℝ) (Ici 0)] oldHessianUnitHeat M n m ![1,0] := by
    filter_upwards [hnhd] with t ht
    exact (hiso t ht).1
  have h1 := hde.congr_of_eventuallyEq hfe.symm (hfe.self_of_nhdsWithin (Set.mem_Ici.mpr le_rfl) |>.symm)
  have h2 := (uniqueDiffWithinAt_Ici (0:ℝ)).eq_deriv _ h1 hd0
  have hf1 : (fun t => oldHessianUnitHeat M n m ![1,0] t+oldHessianUnitHeat M n m ![0,1] t) =ᶠ[nhdsWithin (0:ℝ) (Ici 0)]
      fun t => oldHessianUnitHeat M n m ![1,0] t+oldHessianUnitHeat M n m ![1,0] t := by
    filter_upwards [hnhd] with t ht
    rw [(hiso0 t ht).2]
  have hsum : HasDerivWithinAt (fun t => oldHessianUnitHeat M n m ![1,0] t+oldHessianUnitHeat M n m ![1,0] t)
      ((1/2:ℝ)*modelHeatTraceAverage K M m (Φ ![1,0])
        (pureFluxMainCubeQ3Directions n (q3ModelAmplitude M h (m+1)) (q3ModelLength (m+1))) 0+
       (1/2:ℝ)*modelHeatTraceAverage K M m (Φ ![1,0])
        (pureFluxMainCubeQ3Directions n (q3ModelAmplitude M h (m+1)) (q3ModelLength (m+1))) 0) (Ici 0) 0 :=
    hd0.add hd0
  have h3 := hsum.congr_of_eventuallyEq hf1 (hf1.self_of_nhdsWithin (Set.mem_Ici.mpr le_rfl))
  have h4 := (uniqueDiffWithinAt_Ici (0:ℝ)).eq_deriv _ hdt h3
  linarith [h2,h4]

end
end ASDExplicitGamma.Scalar
