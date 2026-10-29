module

public import ASDExplicitGamma.Native.ParentBoundaryCommonSingletonBank
public import ASDExplicitGamma.Native.ParentBoundaryCommonPhysicalYoung

/-! Actual translated inverse traces in the exact protected singleton frame. -/

@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Variational Gaussian Inverse Main Triadic Algsuperdiff.Section3
noncomputable section

/-- The physical inverse trace on any observed descendant is bounded by
twice the SAME original local bank, with its exact true-frame ratio. -/
theorem parent_boundary_common_protected_inverse_bank
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (hg : M.gamma ≤ gammaZero)
    (Q : TriadicCube 2) (m n : ℤ) (hQm : Q.scale ≤ m) (hgap : m-Q.scale ≤ 5) (hmn : m ≤ n) (height : ℕ)
    (hpast : ∀ k<n,nativeInductionState M h k) (t : ℝ) (ht : t ≤ 1) :
    ∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      Matrix.trace (frameMatrix (Annealed.sigmaBar M n:ℝ) (coarseBlockMatrix (cubeSet Q)
        (attenuatedCoefficient M n (n+(height:ℤ)) (fun _ => Real.sqrt t) ω))).lowerRight ≤
      2*((Annealed.sigmaBar M n:ℝ)/(Annealed.sigmaBar M m:ℝ))*
        parentBoundaryCommonSingletonHistory M Q m n height t ω := by
  have hb := parent_boundary_common_singleton_bank M h hM hg Q m n hQm hgap hmn height hpast t ht
  filter_upwards [hb.history_finite] with ω hfinite
  let J := n+(height:ℤ)
  let weights := parentBoundaryObserverBandWeights n t
  let a := attenuatedCoefficient M n J (fun _ => Real.sqrt t) ω
  let A := (coarseBlockMatrix (cubeSet Q) a).lowerRight
  let sigma : ℝ := Annealed.sigmaBar M n
  let sigmaQ : ℝ := Annealed.sigmaBar M m
  have hsigma : 0 < sigma := (Annealed.sigmaBar_characterization M n).1
  have hsigmaQ : 0 < sigmaQ := (Annealed.sigmaBar_characterization M m).1
  have hpromote : attenuatedCoefficient M m J weights ω=a :=
    full_response_coefficient_promote M m n J hmn (by dsimp [J]; omega) _ ω
  obtain ⟨Lam,_hLam,hEll⟩ := parent_boundary_band_elliptic_cube M n J (fun _ => Real.sqrt t) ω Q
  have hEllOpen := hEll.mono (measurableSet_openCubeSet Q) (openCubeSet_subset_cubeSet Q)
  change IsEllipticFieldOn M.nu Lam (openCubeSet Q) a at hEllOpen
  rw [←hpromote] at hEllOpen
  have hroot := bank_root_response_le_history Q M m J weights ω hEllOpen
  have hmax := bank_member_history_le M ({Q}:Finset (TriadicCube 2)) Q (by simp)
    m J weights ω
  have hn := ENNReal.toReal_mono hfinite.ne (hroot.trans hmax)
  dsimp only [rootInverseResponse] at hn
  rw [ENNReal.toReal_ofReal (mul_nonneg hsigmaQ.le (norm_nonneg _))] at hn
  rw [hpromote] at hn
  have htrace : Matrix.trace A ≤ 2*‖Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) A‖ := by
    have h0 := (le_abs_self (A 0 0)).trans (clipped_matrix_entry_abs_le_norm A 0 0)
    have h1 := (le_abs_self (A 1 1)).trans (clipped_matrix_entry_abs_le_norm A 1 1)
    simp only [Matrix.trace,Fin.sum_univ_two,Matrix.diag_apply]
    linarith only [h0,h1]
  have hscaled := mul_le_mul_of_nonneg_left hn (div_nonneg hsigma.le hsigmaQ.le)
  have he : (sigma/sigmaQ)*(sigmaQ*‖Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) A‖)=
      sigma*‖Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) A‖ := by field_simp
  rw [he] at hscaled
  calc
    _ = sigma*Matrix.trace A := by simp only [frameMatrix,Matrix.trace_smul,smul_eq_mul]; rfl
    _ ≤ sigma*(2*‖Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) A‖) := mul_le_mul_of_nonneg_left htrace hsigma.le
    _ ≤ _ := by
      change sigma*(2*‖Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) A‖) ≤
        2*(sigma/sigmaQ)*(bankFiniteRootHistoryMax ({Q}:Finset (TriadicCube 2)) M m J weights ω).toReal
      linarith only [hscaled]

/-- Sharp actual common-center full-trace split with the inverse trace paid
by the SAME original local bank. No moment estimate or independence is a premise. -/
theorem parent_boundary_common_protected_full_bank_young
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (hg : M.gamma ≤ gammaZero)
    {P Q : TriadicCube 2} {d : ℕ} (hQ : Q ∈ descendantsAtDepth P d)
    (m n : ℤ) (hQm : Q.scale ≤ m) (hgap : m-Q.scale ≤ 5) (hmn : m ≤ n) (height : ℕ)
    (hpast : ∀ k<n,nativeInductionState M h k) (t : ℝ) (ht : t ≤ 1) (eta : ℝ) (heta : 0 < eta) :
    ∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      squareTrace Q M.nu (Annealed.sigmaBar M n) (parentBoundaryCommonCubeObserved hQ n height t ω)+4 ≤
        (1+eta)*nativeSourceFullResponseTrace M Q n (n+(height:ℤ)) (fun _ => Real.sqrt t) ω+
          (2*(1+1/eta)*((Annealed.sigmaBar M n:ℝ)/(Annealed.sigmaBar M m:ℝ)))*
            (parentBoundaryCommonCubeCenterValue P n height t ω/(Annealed.sigmaBar M n:ℝ))^2*
              parentBoundaryCommonSingletonHistory M Q m n height t ω := by
  filter_upwards [parent_boundary_common_protected_inverse_bank M h hM hg Q m n hQm hgap hmn height hpast t ht] with ω hω
  have hy := parent_boundary_common_cube_full_young M hQ n height t ω eta heta
  dsimp only at hy
  apply hy.trans
  refine add_le_add le_rfl ?_
  have hc : 0 ≤ (1+1/eta)*(parentBoundaryCommonCubeCenterValue P n height t ω/(Annealed.sigmaBar M n:ℝ))^2 :=
    mul_nonneg (add_nonneg (by norm_num) (one_div_nonneg.mpr heta.le)) (sq_nonneg _)
  exact (mul_le_mul_of_nonneg_left hω hc).trans_eq (by ring)

end
end ASDExplicitGamma.Native
