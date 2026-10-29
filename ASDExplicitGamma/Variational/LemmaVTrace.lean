module

public import ASDExplicitGamma.Variational.LemmaVLoadBounds

/-! Identification of the differentiated four-load sum with the frozen trace. -/

@[expose] public section

namespace ASDExplicitGamma.Variational

open Homogenization MeasureTheory ASDExplicitGamma.Response

noncomputable section

/-- The four physical load energies in the fixed normalized frame. -/
def lemmaVLoadEnergy (m : ℤ) (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (p : Fin 2 × Bool) : ResponseCoefficient (openCubeSet (originCube 2 m)) → ℝ :=
  responseFrameEnergyObservable (measurableSet_openCubeSet (originCube 2 m))
    (volume_openCubeSet_originCube_toReal_pos (d := 2) m) ν σ hν hσ
    (orthonormalFrameLoad p.1 (lemmaVLoadSign p.2))

/-- The actual frozen trace defect, with the coefficient already divided by σ. -/
def lemmaVTrace (m : ℤ) (ν σ : ℝ) :
    ResponseCoefficient (openCubeSet (originCube 2 m)) → ℝ :=
  fun k => traceDefect (cubeSet (originCube 2 m)) (responseFramePlanarCoefficientField ν σ k) 1

/-- The continuous coefficient extension is qualitatively elliptic on every
measurable observation set, including the boundary of its response domain. -/
theorem lemmaV_frameCoefficient_isEllipticOn {U V : Set (Vec 2)} (hV : MeasurableSet V)
    (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ) (k : ResponseCoefficient U) :
    IsEllipticFieldOn (ν / σ) (((ν / σ) ^ 2 + (‖k‖ / σ) ^ 2) / (ν / σ)) V
      (responseFramePlanarCoefficientField ν σ k) := by
  have ha (i j : Fin 2) : Continuous (fun x => responseFramePlanarCoefficientField ν σ k x i j) := by
    fin_cases i <;> fin_cases j <;>
      simp [responseFramePlanarCoefficientField, responsePlanarCoefficient, responsePlanarJ] <;> fun_prop
  refine ⟨?_, ?_⟩
  · apply measurable_pi_iff.mpr
    intro i
    apply measurable_pi_iff.mpr
    intro j
    exact Measurable.ite hV (ha i j).measurable measurable_const
  · intro x _
    apply responsePlanarCoefficient_isElliptic (ν / σ) (‖k‖ / σ) _ (div_pos hν hσ)
    rw [abs_div, abs_of_pos hσ]
    apply div_le_div_of_nonneg_right _ hσ.le
    calc
      |responseCoefficientExtension k x| = ‖responseCoefficientExtension k x‖ := by simp
      _ ≤ ‖responseCoefficientExtension k‖ := (responseCoefficientExtension k).norm_coe_le_norm x
      _ = ‖k‖ := responseCoefficientExtension_norm k

/-- Exact four-load decomposition of the normalized frozen trace. -/
theorem lemmaVTrace_eq_load_sum (m : ℤ) (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (k : ResponseCoefficient (openCubeSet (originCube 2 m))) :
    lemmaVTrace m ν σ k = (∑ p : Fin 2 × Bool, lemmaVLoadEnergy m ν σ hν hσ p k) - 4 := by
  let Q := originCube 2 m
  let U := openCubeSet Q
  let a := responseFramePlanarCoefficientField ν σ k
  let hv := volume_openCubeSet_originCube_toReal_pos (d := 2) m
  have hEllO := responseFramePlanarCoefficientField_isElliptic (measurableSet_openCubeSet Q) ν σ hν hσ k
  have hE (P : BlockVec 2) :
      responseFrameEnergyObservable (measurableSet_openCubeSet Q) hv ν σ hν hσ P k =
        2 * Mu U P a := by
    rw [lemmaV_observable_eq_twice_muCandidate, ← lemmaV_responseSystem_eq_canonical]
    congr 1
    exact lemmaV_canonical_muCandidate_eq_Mu (isOpenBoundedConvexDomain_openCubeSet Q) hEllO hv P
  have hEll := lemmaV_frameCoefficient_isEllipticOn (measurableSet_cubeSet Q) ν σ hν hσ k
  have ht := lemmaV_traceDefect_eq_sum_load_defects (div_pos hν hσ) hEll
  simp_rw [Mu_cubeSet_originCube_eq_openCubeSet] at ht
  dsimp only [U, Q, a, hv] at hE
  simp_rw [← hE] at ht
  unfold lemmaVTrace
  rw [ht]
  simp [lemmaVLoadEnergy, Fintype.sum_prod_type, lemmaVLoadSign,
    Fin.sum_univ_two]
  ring

/-- The derivative of the actual frozen trace is the sum of its four physical
load derivatives. -/
theorem lemmaVTrace_fderiv_eq_load_sum (m : ℤ) (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (k H : ResponseCoefficient (openCubeSet (originCube 2 m))) :
    fderiv ℝ (lemmaVTrace m ν σ) k H =
      ∑ p : Fin 2 × Bool, fderiv ℝ (lemmaVLoadEnergy m ν σ hν hσ p) k H := by
  have hEq : lemmaVTrace m ν σ = fun z => (∑ p : Fin 2 × Bool,
      lemmaVLoadEnergy m ν σ hν hσ p z) - 4 :=
    funext (lemmaVTrace_eq_load_sum m ν σ hν hσ)
  have hD (p : Fin 2 × Bool) : DifferentiableAt ℝ (lemmaVLoadEnergy m ν σ hν hσ p) k :=
    ((responseFrameEnergyObservable_contDiff (measurableSet_openCubeSet (originCube 2 m))
      (volume_openCubeSet_originCube_toReal_pos (d := 2) m) ν σ hν hσ _).differentiable
        (by norm_num)).differentiableAt
  have hder := (HasFDerivAt.sum (fun p (_ : p ∈ Finset.univ) => (hD p).hasFDerivAt)).sub_const 4
  rw [hEq]
  have he := hder.fderiv
  exact congrArg (fun L => L H) he

end

end ASDExplicitGamma.Variational
