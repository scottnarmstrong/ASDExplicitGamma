module

public import ASDExplicitGamma.Inverse.HistoryInverse
public import ASDExplicitGamma.Inverse.RawHistoryReal
public import ASDExplicitGamma.Inverse.ContainedTriangleHistory
public import ASDExplicitGamma.Triadic.SensitivityLambda

/-! Good actual raw history controls the genuine quarter-scale inverse
lambda in the same true frame, with the source factor two. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Variational ASDExplicitGamma.Triadic
noncomputable section

/-- No depthwise response bound is supplied: each is derived from the actual
same-frame operator defect, then maximized over the genuine descendants. -/
theorem actual_inverse_depth_max_le_raw (M : ABKModel 2) (n : ℤ) (Q : TriadicCube 2)
    (r : ℕ) (ω : Cutoff.CutoffSample 2) :
    (Annealed.sigmaBar M n:ℝ)*lemmaVInverseDepthMax Q (Cutoff.coefficientCutoff M.nu n ω).toFun r ≤
      2*(1+rawDefectDepthMax M n Q r ω) := by
  have hσ : 0 < (Annealed.sigmaBar M n:ℝ) := (Annealed.sigmaBar_characterization M n).1
  unfold lemmaVInverseDepthMax
  rw [← ASDExplicitGamma.Scalar.inverse_history_finset_max_mul _ (descendantsAtDepth_nonempty Q r) _ _ hσ]
  apply Book.Ch02.finsetSupReal_le _ (descendantsAtDepth_nonempty Q r)
  intro R hR
  exact (actual_inverse_response_le_defect M n R ω).trans
    (by linarith only [operator_defect_le_depth_max M n Q r ω hR])

/-- Literal good raw history gives the protected inverse history cap before
any later-band sensitivity estimate. Its frame is sigmaBar_n, not nu. -/
theorem good_inverse_history_bound (M : ABKModel 2) (n : ℤ) (Q : TriadicCube 2)
    (τ : ℝ) (hτ : 0 ≤ τ) (ω : Cutoff.CutoffSample 2) (hgood : ω ∈ clippedCellGoodEvent M n Q τ) :
    (Annealed.sigmaBar M n:ℝ)*lemmaVInverseHistory Q (Cutoff.coefficientCutoff M.nu n ω).toFun (Real.sqrt 3) ≤
      2*(1+τ) := by
  let a := (Real.sqrt 3)⁻¹
  let D := fun r => rawDefectDepthMax M n Q r ω
  let I := fun r => lemmaVInverseDepthMax Q (Cutoff.coefficientCutoff M.nu n ω).toFun r
  let σ := (Annealed.sigmaBar M n:ℝ)
  have hσ : 0 < σ := (Annealed.sigmaBar_characterization M n).1
  have hroot : 1 < Real.sqrt (3:ℝ) := by
    have hh := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)
    have h0 := Real.sqrt_nonneg (3:ℝ)
    nlinarith only [hh,h0]
  have ha0 : 0 ≤ a := inv_nonneg.mpr (by positivity)
  have ha1 : a < 1 := (inv_lt_one₀ (by positivity : 0 < Real.sqrt (3:ℝ))).mpr hroot
  have hgeom := hasSum_geometric_of_lt_one ha0 ha1
  have hnorm := good_raw_history_real_series M n Q τ hτ ω hgood
  have hweight (r : ℕ) : (3:ℝ)^(-(1/2:ℝ)*r)=a^r := by
    rw [show -(1/2:ℝ)*(r:ℝ)= -(r:ℝ)/2 by ring]
    simpa only [a,one_div] using history_weight_eq r
  have hD : Summable (fun r => a^r*D r) := by simpa only [hweight,D] using hnorm.1
  have hDs : (∑' r, a^r*D r) ≤ τ := by simpa only [hweight,D] using hnorm.2
  obtain ⟨Lam,hEll⟩ := cutoff_isEllipticFieldOn_cube M n ω Q
  have hI := lemmaVInverseHistory_summable Q
    (hEll.mono (measurableSet_openCubeSet Q) (openCubeSet_subset_cubeSet Q)) hroot
  have hS : Summable (fun r => a^r*(σ*I r)) := by
    simpa only [a,I,σ,mul_left_comm] using hI.mul_left σ
  have hB : Summable (fun r => 2*(a^r+a^r*D r)) := (hgeom.summable.add hD).mul_left 2
  have hh := hS.tsum_le_tsum (fun r => by
    have hx := mul_le_mul_of_nonneg_left (actual_inverse_depth_max_le_raw M n Q r ω) (pow_nonneg ha0 r)
    apply hx.trans_eq
    dsimp only [D]
    ring) hB
  have heB : (∑' r, 2*(a^r+a^r*D r))=2*((1-a)⁻¹+∑' r, a^r*D r) := by
    rw [tsum_mul_left,hgeom.summable.tsum_add hD,hgeom.tsum_eq]
  rw [heB] at hh
  have hpay : (1-a)*(∑' r, a^r*D r) ≤ τ := by
    have hd0 : 0 ≤ ∑' r, a^r*D r := tsum_nonneg (fun r => mul_nonneg (pow_nonneg ha0 r) ENNReal.toReal_nonneg)
    exact (mul_le_of_le_one_left hd0 (by linarith only [ha0])).trans hDs
  have he : σ*lemmaVInverseHistory Q (Cutoff.coefficientCutoff M.nu n ω).toFun (Real.sqrt 3) =
      (1-a)*(∑' r, a^r*(σ*I r)) := by
    have hf : (fun r => a^r*(σ*I r))=(fun r => σ*(a^r*I r)) := by funext r; ring
    rw [hf,tsum_mul_left]
    unfold lemmaVInverseHistory
    dsimp only [a,I]
    ring
  rw [he]
  apply (mul_le_mul_of_nonneg_left hh (sub_nonneg.mpr ha1.le)).trans
  have hne : 1-a≠0 := (sub_pos.mpr ha1).ne'
  have hc : (1-a)*(2*((1-a)⁻¹+∑' r, a^r*D r))=2+2*((1-a)*(∑' r, a^r*D r)) := by
    field_simp
  rw [hc]
  linarith only [hpay]

/-- Exact source convention: lambdaSqFinite at u=1/4 and exponent two on
the actual completed-cutoff family, rather than a molecular surrogate. -/
theorem good_inverse_lambda_quarter_bound (M : ABKModel 2) (n : ℤ) (Q : TriadicCube 2)
    (τ : ℝ) (hτ : 0 ≤ τ) (ω : Cutoff.CutoffSample 2) (hgood : ω ∈ clippedCellGoodEvent M n Q τ) :
    (Annealed.sigmaBar M n:ℝ)*(Book.Ch02.lambdaSqFinite Q (1/4) 2
      (Book.Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField (Cutoff.coefficientCutoff M.nu n ω)
        (Cutoff.coefficientCutoff_aeLocallyUniformlyEllipticField M n ω)))⁻¹ ≤ 2*(1+τ) := by
  rw [sensitivity_inverse_lambda_quarter_eq_history]
  exact good_inverse_history_bound M n Q τ hτ ω hgood

end
end ASDExplicitGamma.Inverse
