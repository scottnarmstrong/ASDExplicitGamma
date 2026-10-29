module

public import ASDExplicitGamma.Scalar.PairInnerMain

/-! Source-faithful flat reference, step 0: the carrier identity `σ V_H^* e = −F(H)` and the
exact flat response at `k = 0`. -/

@[expose] public section

namespace ASDExplicitGamma.Scalar

open Homogenization MeasureTheory ASDExplicitGamma.Response ASDExplicitGamma.Triadic
  ASDExplicitGamma.Variational ASDExplicitGamma.Gaussian ASDExplicitGamma.Main
open Algsuperdiff.Section3 ASDExplicitGamma.Native ASDExplicitGamma.Inverse
open scoped BigOperators InnerProductSpace

noncomputable section

theorem inner_smul_adj {X Y : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    [CompleteSpace X] [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
    (A : X →L[ℝ] Y) (c : ℝ) (y : Y) (x : X) :
    ⟪c • (ContinuousLinearMap.adjoint A) y, x⟫_ℝ = c * ⟪y, A x⟫_ℝ := by
  rw [real_inner_smul_left, ContinuousLinearMap.adjoint_inner_left]

namespace Cfg''

variable (C : Cfg'')

theorem flat_carrier_identity (hQo : openCubeSet C.Q ⊆ openRectangle C.a C.b C.c C.d)
    (H : C(closedRectangle C.a C.b C.c C.d, ℝ)) :
    C.σ • (ContinuousLinearMap.adjoint (C.Vm H)) (physicalConstantLoad C.Q C.e) = - C.Fl H := by
  classical
  letI : IsFiniteMeasure (volumeMeasureOn (openCubeSet C.Q)) :=
    (isOpenBoundedConvexDomain_openCubeSet C.Q).isFiniteMeasure_restrict_volume
  apply ext_inner_right ℝ
  intro x
  obtain ⟨u, hu⟩ := (PotentialSolenoidalExact.mem_potentialZeroTrace_iff
    (x : HilbertVectorL2 (openCubeSet C.Q))).1 x.2
  have hc : MemVectorL2 (openCubeSet C.Q) (fun _ : Vec 2 => C.e) := memVectorL2_const C.e
  have he' : physicalConstantLoad C.Q C.e = toHilbertVectorL2OfVecField hc := rfl
  have hflux := physicalConstantLoad_mem_fluxSpace C.Q C.e
  -- left side
  have hL : ⟪C.σ • (ContinuousLinearMap.adjoint (C.Vm H)) (physicalConstantLoad C.Q C.e), x⟫_ℝ =
      C.σ * ⟪physicalConstantLoad C.Q C.e, (C.Vm H x : HilbertVectorL2 (openCubeSet C.Q))⟫_ℝ := by
    exact inner_smul_adj (C.Vm H) C.σ _ x
  have hVx : (C.Vm H x : HilbertVectorL2 (openCubeSet C.Q)) =
      (physicalFluxSpace C.Q).toSubmodule.starProjection
        (physicalPositiveShear C.Q C.σ C.hσ (C.Rest H) (x : HilbertVectorL2 (openCubeSet C.Q))) := by
    rw [Vm_apply]
    rfl
  have hproj : ⟪physicalConstantLoad C.Q C.e, (C.Vm H x : HilbertVectorL2 (openCubeSet C.Q))⟫_ℝ =
      ⟪physicalConstantLoad C.Q C.e,
        physicalPositiveShear C.Q C.σ C.hσ (C.Rest H) (x : HilbertVectorL2 (openCubeSet C.Q))⟫_ℝ := by
    rw [hVx, real_inner_comm, Submodule.inner_starProjection_left_eq_right,
      (Submodule.starProjection_eq_self_iff).2 hflux, real_inner_comm]
  have hint : ⟪physicalConstantLoad C.Q C.e,
        physicalPositiveShear C.Q C.σ C.hσ (C.Rest H) (x : HilbertVectorL2 (openCubeSet C.Q))⟫_ℝ =
      ∫ z in openCubeSet C.Q, vecDot C.e ((responseCoefficientExtension (C.Rest H) z / C.σ) •
        matVecMul responsePlanarJ (u.toH1Function.grad z)) ∂volume := by
    rw [inner_rep]
    refine integral_congr_ae ?_
    have h1 := positiveShear_toPlain_ae C.Q C.σ C.hσ (C.Rest H)
      (x : HilbertVectorL2 (openCubeSet C.Q))
    have h2 : hilbertVectorL2ToVectorL2 (x : HilbertVectorL2 (openCubeSet C.Q)) =ᵐ[
        volumeMeasureOn (openCubeSet C.Q)] u.toH1Function.grad := by
      rw [← hu]
      filter_upwards [coeFn_hilbertVectorL2ToVectorL2 u.toH1Function.gradToHilbertVectorL2,
        u.toH1Function.coeFn_gradToHilbertVectorL2] with z a b
      rw [a, b]; simp [hilbertifyVecField]
    have h3 : rep' (physicalConstantLoad C.Q C.e) =ᵐ[volumeMeasureOn (openCubeSet C.Q)]
        fun _ => C.e := by
      apply ae_of_toHilbert_eq (rep_memL2 _) hc
      rw [hilbert_rebuild]; rfl
    filter_upwards [h1, h2, h3] with z a b c
    change vecDot (rep' (physicalConstantLoad C.Q C.e) z)
      (hilbertVectorL2ToVectorL2 (physicalPositiveShear C.Q C.σ C.hσ (C.Rest H)
        (x : HilbertVectorL2 (openCubeSet C.Q))) z : Vec 2) = _
    rw [a, b, c]
  -- right side
  have hFl : ((C.Fl H : C.Xs) : HilbertVectorL2 (openCubeSet C.Q)) =
      (lambda8H10GradientRange (isOpenBoundedConvexDomain_openCubeSet C.Q)).toSubmodule.starProjection
        (lambda8Q3LoadClass (isOpenBoundedConvexDomain_openCubeSet C.Q).1.measurableSet C.a C.b C.c C.d
          C.hab C.hcd C.e H) := rfl
  have hR : ⟪((C.Fl H : C.Xs) : HilbertVectorL2 (openCubeSet C.Q)), (x : HilbertVectorL2 (openCubeSet C.Q))⟫_ℝ =
      ⟪lambda8Q3LoadClass (isOpenBoundedConvexDomain_openCubeSet C.Q).1.measurableSet C.a C.b C.c C.d
          C.hab C.hcd C.e H, (x : HilbertVectorL2 (openCubeSet C.Q))⟫_ℝ := by
    have h := lambda8DirichletProjection_residual_orthogonal
      (isOpenBoundedConvexDomain_openCubeSet C.Q)
      (lambda8Q3LoadClass (isOpenBoundedConvexDomain_openCubeSet C.Q).1.measurableSet C.a C.b C.c C.d
          C.hab C.hcd C.e H) u
    rw [hu, inner_sub_left, sub_eq_zero] at h
    rw [hFl]
    exact h.symm
  have hLoadField := lambda8Q3LoadField_memVectorL2 (isOpenBoundedConvexDomain_openCubeSet C.Q).1.measurableSet
    C.a C.b C.c C.d C.hab C.hcd C.e H
  have hR2 : ⟪lambda8Q3LoadClass (isOpenBoundedConvexDomain_openCubeSet C.Q).1.measurableSet C.a C.b C.c C.d
          C.hab C.hcd C.e H, (x : HilbertVectorL2 (openCubeSet C.Q))⟫_ℝ =
      ∫ z in openCubeSet C.Q, vecDot (responseCoefficientExtension (C.Rest H) z •
        matVecMul responsePlanarJ C.e) (u.toH1Function.grad z) ∂volume := by
    have hcls : lambda8Q3LoadClass (isOpenBoundedConvexDomain_openCubeSet C.Q).1.measurableSet C.a C.b C.c C.d
          C.hab C.hcd C.e H = toHilbertVectorL2OfVecField hLoadField := rfl
    rw [hcls, ← hu]
    change ⟪toHilbertVectorL2OfVecField hLoadField, toHilbertVectorL2OfVecField
      u.toH1Function.grad_memVectorL2⟫_ℝ = _
    rw [inner_ofField]
    refine setIntegral_congr_fun (measurableSet_openCubeSet C.Q) fun z hz => ?_
    have hk : responseCoefficientExtension (C.Rest H) z =
        H ⟨z, ⟨Set.Ioo_subset_Icc_self (hQo hz).1, Set.Ioo_subset_Icc_self (hQo hz).2⟩⟩ := by
      rw [responseCoefficientExtension_eq _ hz]
      rfl
    rw [hk]
    unfold lambda8Q3LoadField
    rw [lambda8CovarianceClamp_eq_of_mem C.a C.b C.c C.d C.hab C.hcd (hQo hz)]
  have hFx : ⟪C.Fl H, x⟫_ℝ = ⟪((C.Fl H : C.Xs) : HilbertVectorL2 (openCubeSet C.Q)),
    (x : HilbertVectorL2 (openCubeSet C.Q))⟫_ℝ := rfl
  rw [hL, hproj, hint, inner_neg_left, hFx, hR, hR2]
  have hgrad : MemVectorL2 (openCubeSet C.Q) u.toH1Function.grad := u.toH1Function.grad_memVectorL2
  rw [← integral_neg, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  simp only [vecDot_smul_left, vecDot_smul_right]
  have hsk := vecDot_J_skew C.e (u.toH1Function.grad z)
  have hsk' : vecDot C.e (matVecMul responsePlanarJ (u.toH1Function.grad z)) =
      -vecDot (matVecMul responsePlanarJ C.e) (u.toH1Function.grad z) := by linarith
  rw [hsk']
  field_simp [C.hσ.ne']

end Cfg''

end

end ASDExplicitGamma.Scalar
