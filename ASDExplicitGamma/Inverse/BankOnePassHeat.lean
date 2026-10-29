module

public import ASDExplicitGamma.Inverse.BankResponseQuadratic
public import ASDExplicitGamma.Gaussian.ModelHeatResponse
public import ASDExplicitGamma.Main.PartialInsertion
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-! Gaussian heat differentiation of the actual lower-right trace in a fixed frame. -/
@[expose] public section

namespace ASDExplicitGamma.Inverse

open Homogenization MeasureTheory Filter Set Algsuperdiff.Section3
open ASDExplicitGamma.Response ASDExplicitGamma.Variational ASDExplicitGamma.Gaussian
open scoped Topology

noncomputable def bankInverseTrace (q : ℤ) (a : CoeffField 2) (σ : ℝ) : ℝ :=
  ∑ i : Fin 2, σ*(coarseBlockMatrix (cubeSet (originCube 2 q)) a).lowerRight i i

noncomputable def bankInverseTraceObservable (q : ℤ) (ν σ : ℝ)
    (hν : 0 < ν) (hσ : 0 < σ) :
    C(closure (cubeSet (originCube 2 q)), ℝ) → ℝ := fun k =>
  ∑ i : Fin 2, responseFrameEnergyObservable
    (measurableSet_cubeSet (originCube 2 q)) (volume_cubeSet_toReal_pos (originCube 2 q))
    ν σ hν hσ (0, Pi.single i 1)
    (ContinuousMap.linearIsometryBoundedOfCompact _ ℝ ℝ k)

theorem bank_inverse_trace_observable_eq (q : ℤ) (ν σ : ℝ)
    (hν : 0 < ν) (hσ : 0 < σ)
    (k : C(closure (cubeSet (originCube 2 q)), ℝ)) :
    bankInverseTraceObservable q ν σ hν hσ k =
      bankInverseTrace q (responsePlanarCoefficientField ν
        (ContinuousMap.linearIsometryBoundedOfCompact _ ℝ ℝ k)) σ := by
  unfold bankInverseTraceObservable bankInverseTrace
  apply Finset.sum_congr rfl
  intro i hi
  rw [bank_responseFrameEnergyObservable_eq_frameCoarseQuadratic]
  simp [blockVecDot, blockMatVecMul, frameMatrix, vecDot, matVecMul,
    Pi.single_apply]

theorem bank_inverse_trace_observable_C2 (q : ℤ) (ν σ : ℝ)
    (hν : 0 < ν) (hσ : 0 < σ) :
    HasPolynomiallyBoundedC2Derivatives (bankInverseTraceObservable q ν σ hν hσ) := by
  let L := (ContinuousMap.linearIsometryBoundedOfCompact
    (closure (cubeSet (originCube 2 q))) ℝ ℝ).toLinearIsometry
  let E (i : Fin 2) : C(closure (cubeSet (originCube 2 q)), ℝ) → ℝ := fun k =>
    responseFrameEnergyObservable (measurableSet_cubeSet (originCube 2 q))
      (volume_cubeSet_toReal_pos (originCube 2 q)) ν σ hν hσ (0, Pi.single i 1) (L k)
  have hE (i : Fin 2) : HasPolynomiallyBoundedC2Derivatives (E i) :=
    hasPolynomiallyBoundedC2Derivatives_comp_isometry L
      (responseFrameEnergyObservable_hasPolynomiallyBoundedC2Derivatives
        (measurableSet_cubeSet (originCube 2 q)) (volume_cubeSet_toReal_pos (originCube 2 q))
        ν σ hν hσ (0, Pi.single i 1))
  have heq : bankInverseTraceObservable q ν σ hν hσ = fun k => E 0 k+E 1 k := by
    funext k
    simp only [bankInverseTraceObservable, Fin.sum_univ_two, E, L,
      LinearIsometryEquiv.coe_toLinearIsometry]
  rw [heq]
  exact hasPolynomiallyBoundedC2Derivatives_add (hE 0) (hE 1)

private theorem bank_planarCoefficient_eq_of_symmPart (ν : ℝ) (A : Mat 2)
    (hA : symmPart A = ν • (1 : Mat 2)) : responsePlanarCoefficient ν (A 1 0) = A := by
  have h00 := congrFun (congrFun hA 0) 0
  have h11 := congrFun (congrFun hA 1) 1
  have h01 := congrFun (congrFun hA 0) 1
  norm_num [symmPart, Matrix.smul_apply, Matrix.one_apply] at h00 h11 h01
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [responsePlanarCoefficient, responsePlanarJ] <;> linarith

private theorem bank_symmPart_modelInserted (M : ABKModel 2) (m : ℤ) (t : ℝ)
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


theorem bank_inverse_trace_observable_inserted (q : ℤ) (M : ABKModel 2) (ell m : ℤ)
    (hK : closure (cubeSet (originCube 2 q)) ⊆ openCubeSet (originCube 2 ell))
    (σ : ℝ) (hσ : 0 < σ) (t : ℝ) (ω : Cutoff.CutoffSample 2) :
    bankInverseTraceObservable q M.nu σ M.nu_pos hσ
      (modelInsertedScalar (closure (cubeSet (originCube 2 q))) m t ω) =
      bankInverseTrace q (Model.partialInsertedCoefficient M m t ω).toFun σ := by
  rw [bank_inverse_trace_observable_eq]
  have heq : ∀ x ∈ cubeSet (originCube 2 q),
      responsePlanarCoefficientField M.nu
        (ContinuousMap.linearIsometryBoundedOfCompact _ ℝ ℝ
          (modelInsertedScalar (closure (cubeSet (originCube 2 q))) m t ω)) x =
        Model.partialInsertedCoefficient M m t ω x := by
    intro x hx
    rw [responsePlanarCoefficientField, responseCoefficientExtension_eq _ hx,
      ContinuousMap.linearIsometryBoundedOfCompact_apply_apply,
      modelInsertedScalar_apply _ M ell m hK]
    exact bank_planarCoefficient_eq_of_symmPart M.nu _ (bank_symmPart_modelInserted M m t ω x)
  have hae := (ae_restrict_mem (μ := volume) (measurableSet_cubeSet (originCube 2 q))).mono heq
  unfold bankInverseTrace
  rw [coarseBlockMatrix_congr_of_ae_eq hae]

noncomputable def bankInverseTraceHeatAverage (q : ℤ) (M : ABKModel 2)
    (m : ℤ) (σ t : ℝ) : ℝ :=
  ∫ ω, bankInverseTrace q (Model.partialInsertedCoefficient M m t ω).toFun σ
    ∂(Cutoff.cutoffSampleLaw M).toMeasure

theorem bank_inverse_trace_heat_average_eq (q : ℤ) (M : ABKModel 2) (m : ℤ)
    (σ : ℝ) (hσ : 0 < σ) :
    bankInverseTraceHeatAverage q M m σ = modelHeatAverage
      (closure (cubeSet (originCube 2 q))) M m (bankInverseTraceObservable q M.nu σ M.nu_pos hσ) := by
  obtain ⟨ell,hK⟩ := exists_originCube_containing_compact _
    (isBounded_cubeSet (originCube 2 q)).isCompact_closure
  funext t
  apply integral_congr_ae
  exact Eventually.of_forall fun ω => (bank_inverse_trace_observable_inserted q M ell m hK σ hσ t ω).symm

/-- Actual product-q3 heat calculus for the inverse trace, with arbitrary
positive deterministic frame. No generator inequality or inverse moment is assumed. -/
theorem bank_inverse_trace_heat_identity (q : ℤ) (M : ABKModel 2)
    (h : ℝ) (hM : PlanarQ3Gaussian M h) (m : ℤ) (σ : ℝ) (hσ : 0 < σ) :
    ∃ (T : GaussianFactorL2 ℕ →L[ℝ] C(closure (cubeSet (originCube 2 q)), ℝ))
      (v : ℕ → GaussianFactorL2 ℕ) (hA : Summable (fun j => ‖v j‖ ^ 2)),
      (Cutoff.cutoffSampleLaw M).toMeasure.map
        (fun ω : Cutoff.CutoffSample 2 =>
          shellFieldScalarRestriction (closure (cubeSet (originCube 2 q))) (ω.1 (m+1))) =
        standardGaussianInfinitePi.map (gaussianSeriesLimitE hA T) ∧
      ContinuousOn (bankInverseTraceHeatAverage q M m σ) (Ici 0) ∧
      ContinuousOn (fun t => (1/2:ℝ)*modelHeatTraceAverage
        (closure (cubeSet (originCube 2 q))) M m (bankInverseTraceObservable q M.nu σ M.nu_pos hσ)
          (fun j => T (v j)) t) (Ici 0) ∧
      (∀ t ∈ Ioi 0, HasDerivAt (bankInverseTraceHeatAverage q M m σ)
        ((1/2:ℝ)*modelHeatTraceAverage (closure (cubeSet (originCube 2 q))) M m
          (bankInverseTraceObservable q M.nu σ M.nu_pos hσ) (fun j => T (v j)) t) t) ∧
      HasDerivWithinAt (bankInverseTraceHeatAverage q M m σ)
        ((1/2:ℝ)*modelHeatTraceAverage (closure (cubeSet (originCube 2 q))) M m
          (bankInverseTraceObservable q M.nu σ M.nu_pos hσ) (fun j => T (v j)) 0) (Ici 0) 0 := by
  obtain ⟨ell,hK⟩ := exists_originCube_containing_compact _
    (isBounded_cubeSet (originCube 2 q)).isCompact_closure
  rw [bank_inverse_trace_heat_average_eq q M m σ hσ]
  exact exists_c1On_modelHeatAverage _ M h hM ell m hK _
    (bank_inverse_trace_observable_C2 q M.nu σ M.nu_pos hσ)


noncomputable def bankCompletedInverseTraceMean (q : ℤ) (M : ABKModel 2)
    (m : ℤ) (σ : ℝ) : ℝ :=
  ∫ ω, bankInverseTrace q (Cutoff.coefficientCutoff M.nu m ω).toFun σ
    ∂(Cutoff.cutoffSampleLaw M).toMeasure

theorem bank_inverse_trace_heat_zero (q : ℤ) (M : ABKModel 2) (m : ℤ) (σ : ℝ) :
    bankInverseTraceHeatAverage q M m σ 0 = bankCompletedInverseTraceMean q M m σ := by
  apply integral_congr_ae
  exact Eventually.of_forall fun ω => by
    have he : Model.partialInsertedCoefficient M m 0 ω = Cutoff.coefficientCutoff M.nu m ω := by
      ext x i j
      simp [Model.partialInsertedCoefficient, RegCoeffField.add_apply, RegCoeffField.smul_apply]
    exact congrArg (fun a : RegCoeffField 2 => bankInverseTrace q a.toFun σ) he

theorem bank_inverse_trace_heat_one (q : ℤ) (M : ABKModel 2) (m : ℤ) (σ : ℝ) :
    bankInverseTraceHeatAverage q M m σ 1 = bankCompletedInverseTraceMean q M (m+1) σ := by
  apply integral_congr_ae
  exact Eventually.of_forall fun ω =>
    congrArg (fun a : RegCoeffField 2 => bankInverseTrace q a.toFun σ)
      (Main.mainInsertion_coefficient_one M m ω)

/-- Integrate the actual heat identity against a signed expected-generator
bound. This helper does not assert that bound; the source generator supplies it. -/
theorem bank_inverse_trace_heat_increment_of_generator
    (q : ℤ) (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (m : ℤ) (σ : ℝ) (hσ : 0 < σ) (C : ℝ)
    (hgen : ∀ (T : GaussianFactorL2 ℕ →L[ℝ] C(closure (cubeSet (originCube 2 q)), ℝ))
      (v : ℕ → GaussianFactorL2 ℕ) (hA : Summable (fun j => ‖v j‖ ^ 2)),
      (Cutoff.cutoffSampleLaw M).toMeasure.map
        (fun ω : Cutoff.CutoffSample 2 => shellFieldScalarRestriction
          (closure (cubeSet (originCube 2 q))) (ω.1 (m+1))) =
          standardGaussianInfinitePi.map (gaussianSeriesLimitE hA T) →
      ∀ t ∈ Ioo (0:ℝ) 1, (1/2:ℝ)*modelHeatTraceAverage
        (closure (cubeSet (originCube 2 q))) M m
        (bankInverseTraceObservable q M.nu σ M.nu_pos hσ) (fun j => T (v j)) t ≤ C) :
    bankCompletedInverseTraceMean q M (m+1) σ ≤ bankCompletedInverseTraceMean q M m σ+C := by
  obtain ⟨T,v,hA,hlaw,hcont,_,hderiv,_⟩ := bank_inverse_trace_heat_identity q M h hM m σ hσ
  have hc : ContinuousOn (bankInverseTraceHeatAverage q M m σ) (Icc 0 1) :=
    hcont.mono (fun _ hx => hx.1)
  have hd : DifferentiableOn ℝ (bankInverseTraceHeatAverage q M m σ) (interior (Icc 0 1)) := by
    rw [interior_Icc]
    intro t ht
    exact (hderiv t ht.1).differentiableAt.differentiableWithinAt
  have hb : ∀ t ∈ interior (Icc (0:ℝ) 1), deriv (bankInverseTraceHeatAverage q M m σ) t ≤ C := by
    rw [interior_Icc]
    intro t ht
    rw [(hderiv t ht.1).deriv]
    exact hgen T v hA hlaw t ht
  have hh := (convex_Icc (0:ℝ) 1).image_sub_le_mul_sub_of_deriv_le hc hd hb
    0 ⟨le_rfl,zero_le_one⟩ 1 ⟨zero_le_one,le_rfl⟩ zero_le_one
  rw [bank_inverse_trace_heat_zero,bank_inverse_trace_heat_one] at hh
  linarith only [hh]

end ASDExplicitGamma.Inverse
