module

public import ASDExplicitGamma.Inverse.AssemblyDefinitions
public import ASDExplicitGamma.Inverse.SensitivityGate
public import ASDExplicitGamma.Inverse.GoodCellResponse
public import ASDExplicitGamma.Inverse.DescendantResponse
public import ASDExplicitGamma.Inverse.DescendantLinearCap
public import ASDExplicitGamma.Inverse.TriangleResponseBudget

/-! The source all-order sensitivity gate for actual good cells. -/

@[expose] public section
namespace ASDExplicitGamma.Inverse

open Homogenization MeasureTheory Algsuperdiff.Section3
open Algsuperdiff.Section3.Provider
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Model ASDExplicitGamma.Response
open ASDExplicitGamma.Triadic

noncomputable section

/-- The all-order local sensitivity size is the exact source value `10/37`;
the looser value relative to the full tuple is not used. -/
theorem all_order_sensitivity_budget :
    2 * (1 + resetAllOrderTau) * (10 * waveGateEta .allOrder) = 10/37 := by
  norm_num [resetAllOrderTau, waveGateEta, Numerics.Wave.allOrderTau,
    Numerics.Wave.allOrderEta]

/-- The actual good-cell event supplies both sensitivity ODE hypotheses.
Only the source all-order tuple and its actual local failure event are used. -/
theorem reset_good_cell_sensitivity_ode_gate (M : ABKModel 2) (Q : TriadicCube 2)
    (ω : Cutoff.CutoffSample 2)
    (hgood : ω ∉ cellFailure M resetAllOrderTau (waveGateEta .allOrder) Q)
    (J : ℤ) (weights : ℤ → ℝ)
    (hw : ∀ k ∈ Finset.Ioc (Q.scale+40) J, 0 ≤ weights k ∧ weights k ≤ 1) :
    let x := sensitivityDsharp Q (laterBandW2 Q (Q.scale+40) J weights ω) *
      sensitivityPathLambdaInverse M.nu M.nu_pos (oldResponseCoefficient Q (Q.scale+40) ω)
        (laterResponseCoefficient Q (Q.scale+40) J weights ω) (1/4) 0
    sensitivityB2*x < 1 ∧ x ≤ sensitivityCloc := by
  have hτ : 0 ≤ resetAllOrderTau := by
    norm_num [resetAllOrderTau, Numerics.Wave.allOrderTau]
  have hη : 0 ≤ waveGateEta .allOrder :=
    (wave_gate_eta_pos .allOrder).le
  have hx := (good_cell_sensitivity_size_bound M Q resetAllOrderTau
    (waveGateEta .allOrder) hτ hη ω hgood J weights hw).trans_eq
      all_order_sensitivity_budget
  dsimp only
  constructor
  · have hB0 : 0 ≤ sensitivityB2 := by unfold sensitivityB2; positivity
    have hh := mul_le_mul_of_nonneg_left hx hB0
    have hB := sensitivityB2_lt_45016
    nlinarith only [hh, hB]
  · exact hx.trans (by norm_num [sensitivityCloc])

/-- The local response exponential is bounded by the exact sensitivity
prefactor used in the positive finite-energy comparison. -/
theorem reset_root_sensitivity_exponential_le {x : ℝ}
    (hx : x ≤ 2 * (1 + resetAllOrderTau) * (10 * waveGateEta .allOrder)) :
    Real.exp (sensitivityCA*x) ≤ rootAssemblySensitivity := by
  apply Real.exp_le_exp.mpr
  have hc : 0 ≤ sensitivityCA := by norm_num [sensitivityCA]
  have hh := mul_le_mul_of_nonneg_left hx hc
  have hscale : sensitivityCA *
      (2 * (1 + resetAllOrderTau) * (10 * waveGateEta .allOrder)) =
      (17444/10000:ℝ) * (1 + resetAllOrderTau) * (10 * waveGateEta .allOrder) := by
    norm_num [sensitivityCA]
    ring
  calc
    sensitivityCA*x ≤ sensitivityCA *
        (2 * (1 + resetAllOrderTau) * (10 * waveGateEta .allOrder)) := hh
    _ = (17444/10000:ℝ) * (1 + resetAllOrderTau) *
        (10 * waveGateEta .allOrder) := hscale

/-- Actual good-cell sensitivity compares every deterministic attenuated
future law to the same old completed-cutoff matrix in the true old frame. -/
theorem reset_good_cell_pure_flux_response (M : ABKModel 2) (Q : TriadicCube 2)
    (m J : ℤ) (hn : Q.scale+40 ≤ m) (hm : m ≤ J) (weights : ℤ → ℝ)
    (hw : ∀ k ∈ Finset.Ioc m J, 0 ≤ weights k ∧ weights k ≤ 1)
    (ω : Cutoff.CutoffSample 2)
    (hgood : ω ∉ cellFailure M resetAllOrderTau (waveGateEta .allOrder) Q)
    (v : Vec 2) :
    dotProduct v ((coarseBlockMatrix (cubeSet Q)
      (attenuatedCoefficient M m J weights ω)).lowerRight.mulVec v) ≤
      rootAssemblySensitivity * dotProduct v ((coarseBlockMatrix (cubeSet Q)
        (Cutoff.coefficientCutoff M.nu (Q.scale+40) ω).toFun).lowerRight.mulVec v) := by
  let n := Q.scale+40
  let a := sourceBandWeights m weights
  let k := oldResponseCoefficient Q n ω
  let kH := laterResponseCoefficient Q n J a ω
  let h := laterBandW2 Q n J a ω
  have ha := source_band_weights_bounds n m J weights hw
  have hgate := reset_good_cell_sensitivity_ode_gate M Q ω hgood J a ha
  have hs : sensitivityB2 * sensitivityDsharp Q h *
      sensitivityPathLambdaInverse M.nu M.nu_pos k kH (1/4) 0 < 1 := by
    simpa only [mul_assoc] using hgate.1
  have hh := sensitivity_pure_flux_upper Q M.nu M.nu_pos k kH h
    (later_response_coefficient_represents Q n J a ω) hs hgate.2 v
  change dotProduct v ((Book.Ch02.coarseBlockMatrix _
    (sensitivityBookCoeffOn Q M.nu M.nu_pos
      (oldResponseCoefficient Q n ω+laterResponseCoefficient Q n J a ω))).lowerRight.mulVec v) ≤ _ at hh
  rw [attenuated_sensitivity_matrix_eq M Q n m J hn hm weights ω,
    old_sensitivity_matrix_eq M Q n ω] at hh
  have ht : 0 ≤ resetAllOrderTau := by
    norm_num [resetAllOrderTau, Numerics.Wave.allOrderTau]
  have hη : 0 ≤ waveGateEta .allOrder := (wave_gate_eta_pos .allOrder).le
  have hx := good_cell_sensitivity_size_bound M Q resetAllOrderTau
    (waveGateEta .allOrder) ht hη ω hgood J a ha
  have hfactor := reset_root_sensitivity_exponential_le hx
  exact hh.trans (mul_le_mul_of_nonneg_right hfactor
    (old_pure_flux_nonneg M Q n ω v))

/-- Every triadic descendant of an actual good parent obeys the same
attenuated pure-flux cap in the parent's fixed completed-cutoff frame. -/
theorem reset_good_parent_descendant_pure_flux_response (M : ABKModel 2)
    {Q R : TriadicCube 2} {j : ℕ} (hR : R ∈ descendantsAtDepth Q j)
    (m J : ℤ) (hn : Q.scale+40 ≤ m) (hm : m ≤ J) (weights : ℤ → ℝ)
    (hw : ∀ k ∈ Finset.Ioc m J, 0 ≤ weights k ∧ weights k ≤ 1)
    (ω : Cutoff.CutoffSample 2)
    (hgood : ω ∉ cellFailure M resetAllOrderTau (waveGateEta .allOrder) Q)
    (v : Vec 2) :
    dotProduct v ((coarseBlockMatrix (cubeSet R)
      (attenuatedCoefficient M m J weights ω)).lowerRight.mulVec v) ≤
      rootAssemblySensitivity * dotProduct v ((coarseBlockMatrix (cubeSet R)
        (Cutoff.coefficientCutoff M.nu (Q.scale+40) ω).toFun).lowerRight.mulVec v) := by
  let n := Q.scale+40
  let a := sourceBandWeights m weights
  let k := oldResponseCoefficient Q n ω
  let kH := laterResponseCoefficient Q n J a ω
  let h := laterBandW2 Q n J a ω
  let kr := sensitivityResponseCoefficientRestrict k hR
  let kHr := sensitivityResponseCoefficientRestrict kH hR
  let x := sensitivityDsharp R (h.restrict hR) *
    sensitivityPathLambdaInverse M.nu M.nu_pos kr kHr (1/4) 0
  have ha := source_band_weights_bounds n m J weights hw
  have hdesc : x ≤ sensitivityDsharp Q h *
      sensitivityPathLambdaInverse M.nu M.nu_pos k kH (1/4) 0 :=
    sensitivityDsharp_mul_descendant_lambda_inv_le M.nu M.nu_pos k kH h hR
      (1/4) (by norm_num) le_rfl 0
  have hτ : 0 ≤ resetAllOrderTau := by
    norm_num [resetAllOrderTau, Numerics.Wave.allOrderTau]
  have hη : 0 ≤ waveGateEta .allOrder := (wave_gate_eta_pos .allOrder).le
  have hx := hdesc.trans (good_cell_sensitivity_size_bound M Q resetAllOrderTau
    (waveGateEta .allOrder) hτ hη ω hgood J a ha)
  have hsmall : sensitivityB2 * x < 1 := by
    have hB0 : 0 ≤ sensitivityB2 := by unfold sensitivityB2; positivity
    have hh := mul_le_mul_of_nonneg_left hx hB0
    have hB := sensitivityB2_lt_45016
    rw [all_order_sensitivity_budget] at hh
    nlinarith only [hh, hB]
  have hsmall' : sensitivityB2 * sensitivityDsharp R (h.restrict hR) *
      sensitivityPathLambdaInverse M.nu M.nu_pos kr kHr (1/4) 0 < 1 := by
    simpa only [x, mul_assoc] using hsmall
  have hloc : x ≤ sensitivityCloc :=
    hx.trans (by rw [all_order_sensitivity_budget]; norm_num [sensitivityCloc])
  have hh := sensitivity_pure_flux_upper R M.nu M.nu_pos kr kHr (h.restrict hR)
    (sensitivityResponseCoefficientRestrict_represents kH h
      (later_response_coefficient_represents Q n J a ω) hR) hsmall' hloc v
  have hadd : kr+kHr=sensitivityResponseCoefficientRestrict (k+kH) hR := by
    ext z
    rfl
  rw [hadd, sensitivity_restrict_matrix_eq M.nu M.nu_pos (k+kH) hR,
    sensitivity_restrict_matrix_eq M.nu M.nu_pos k hR] at hh
  have hnew : coarseBlockMatrix (cubeSet R)
      (sensitivityBaseRegField M.nu (k+kH)).toFun =
      coarseBlockMatrix (cubeSet R) (attenuatedCoefficient M m J weights ω) := by
    rw [coarseBlockMatrix_cubeSet_eq_openCubeSet_of_triadicCube R,
      coarseBlockMatrix_cubeSet_eq_openCubeSet_of_triadicCube R]
    apply coarseBlockMatrix_congr_of_ae_eq
    filter_upwards [ae_restrict_mem (measurableSet_openCubeSet R)] with z hz
    exact sensitivity_path_represents_attenuated M Q n m J hn hm weights ω
      (openCubeSet_subset_of_mem_descendantsAtDepth hR hz)
  have hold : coarseBlockMatrix (cubeSet R)
      (sensitivityBaseRegField M.nu k).toFun =
      coarseBlockMatrix (cubeSet R)
        (Cutoff.coefficientCutoff M.nu n ω).toFun := by
    rw [coarseBlockMatrix_cubeSet_eq_openCubeSet_of_triadicCube R,
      coarseBlockMatrix_cubeSet_eq_openCubeSet_of_triadicCube R]
    apply coarseBlockMatrix_congr_of_ae_eq
    filter_upwards [ae_restrict_mem (measurableSet_openCubeSet R)] with z hz
    exact old_response_coefficient_represents M Q n ω
      (openCubeSet_subset_of_mem_descendantsAtDepth hR hz)
  rw [hnew, hold] at hh
  have hfactor := reset_root_sensitivity_exponential_le hx
  exact hh.trans (mul_le_mul_of_nonneg_right hfactor
    (old_pure_flux_nonneg M R n ω v))

/-- The true-frame linear defect cap on each contained descendant. -/
theorem reset_good_parent_descendant_linear_cap (M : ABKModel 2)
    {Q R : TriadicCube 2} {j : ℕ} (hR : R ∈ descendantsAtDepth Q j)
    (m J : ℤ) (hn : Q.scale+40 ≤ m) (hm : m ≤ J) (weights : ℤ → ℝ)
    (hw : ∀ k ∈ Finset.Ioc m J, 0 ≤ weights k ∧ weights k ≤ 1)
    (ω : Cutoff.CutoffSample 2)
    (hgood : ω ∉ cellFailure M resetAllOrderTau (waveGateEta .allOrder) Q)
    (v : Vec 2) :
    (Annealed.sigmaBar M (Q.scale+40):ℝ) * dotProduct v
      ((coarseBlockMatrix (cubeSet R)
        (attenuatedCoefficient M m J weights ω)).lowerRight.mulVec v) ≤
      rootAssemblySensitivity *
        (2 * (1 + historyOperatorDefect M (Q.scale+40) R ω) * dotProduct v v) := by
  have hh := mul_le_mul_of_nonneg_left
    (reset_good_parent_descendant_pure_flux_response M hR m J hn hm weights hw ω hgood v)
    (Annealed.sigmaBar_characterization M (Q.scale+40)).1.le
  have hE : 0 ≤ rootAssemblySensitivity :=
    root_assembly_sensitivity_pos.le
  have hb := mul_le_mul_of_nonneg_left
    (old_pure_flux_linear_cap M R (Q.scale+40) ω v) hE
  exact hh.trans (by simpa only [mul_left_comm] using hb)

/-- The actual good parent has finite contained-triangle response energy;
the source `g(6 tau)` cap is derived from the same positive history field. -/
theorem reset_good_parent_triangle_response_budget (M : ABKModel 2)
    {Q U : TriadicCube 2} {a : ℕ} (hU : U ∈ descendantsAtDepth Q a)
    (ha : a ≤ 2) (pi : Equiv.Perm (Fin 2))
    (m J : ℤ) (hn : Q.scale+40 ≤ m) (hm : m ≤ J) (weights : ℤ → ℝ)
    (hw : ∀ k ∈ Finset.Ioc m J, 0 ≤ weights k ∧ weights k ≤ 1)
    (ω : Cutoff.CutoffSample 2)
    (hgood : ω ∉ cellFailure M resetAllOrderTau (waveGateEta .allOrder) Q)
    (v : Vec 2) :
    let C := fun i : ℕ => ∑ P ∈ triangleFirstCubes U.scale pi i,
      ((volume (openCubeSet (rootTranslateCube U P))).toReal /
        (volume (Whitney.KuhnCell.mk U pi).openCarrier).toReal) *
          ((Annealed.sigmaBar M (Q.scale+40):ℝ) *
            dotProduct v ((coarseBlockMatrix (cubeSet (rootTranslateCube U P))
              (attenuatedCoefficient M m J weights ω)).lowerRight.mulVec v))
    Summable C ∧ (∑' i, C i) ≤
      rootAssemblySensitivity * rootResponseEnvelope (6*resetAllOrderTau) *
        dotProduct v v := by
  classical
  let n := Q.scale+40
  let w := fun P : TriadicCube 2 =>
    (volume (openCubeSet (rootTranslateCube U P))).toReal /
      (volume (Whitney.KuhnCell.mk U pi).openCarrier).toReal
  let D := fun P => historyOperatorDefect M n (rootTranslateCube U P) ω
  let B := fun i : ℕ => ∑ P ∈ triangleFirstCubes U.scale pi i, w P*D P
  let C := fun i : ℕ => ∑ P ∈ triangleFirstCubes U.scale pi i,
    w P*((Annealed.sigmaBar M n:ℝ)*dotProduct v ((coarseBlockMatrix
      (cubeSet (rootTranslateCube U P)) (attenuatedCoefficient M m J weights ω)).lowerRight.mulVec v))
  let mass := fun i : ℕ => 2*(1/3:ℝ)^(i+1)
  have hτ : 1 ≤ resetAllOrderTau := by
    norm_num [resetAllOrderTau, Numerics.Wave.allOrderTau]
  have hB := triangle_good_parent_history_budget M n hU ha pi resetAllOrderTau
    (le_trans (by norm_num) hτ) ω (good_cell_raw_history M Q resetAllOrderTau
      (waveGateEta .allOrder) ω hgood)
  have hE : 0 ≤ rootAssemblySensitivity := root_assembly_sensitivity_pos.le
  have hv : 0 ≤ dotProduct v v :=
    Finset.sum_nonneg (fun _ _ => mul_self_nonneg _)
  have hw0 (P : TriadicCube 2) : 0 ≤ w P :=
    div_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
  have hC0 (i : ℕ) : 0 ≤ C i := by
    apply Finset.sum_nonneg
    intro P hP
    have hd := mem_descendantsAtDepth_add hU (triangle_first_root_descendant U pi i hP)
    exact mul_nonneg (hw0 P)
      (mul_nonneg (Annealed.sigmaBar_characterization M n).1.le
        (attenuated_descendant_pure_flux_nonneg M hd n m J hn hm weights ω v))
  have hC (i : ℕ) : C i ≤ rootAssemblySensitivity *
      (2*(mass i+B i)*dotProduct v v) := by
    calc
      C i ≤ ∑ P ∈ triangleFirstCubes U.scale pi i,
        rootAssemblySensitivity * (2*(w P+w P*D P)*dotProduct v v) := by
        apply Finset.sum_le_sum
        intro P hP
        have hd := mem_descendantsAtDepth_add hU
          (triangle_first_root_descendant U pi i hP)
        have hh := mul_le_mul_of_nonneg_left
          (reset_good_parent_descendant_linear_cap M hd m J hn hm weights hw ω hgood v)
          (hw0 P)
        exact hh.trans_eq (by dsimp only [D, n]; ring)
      _ = rootAssemblySensitivity *
          (2*((∑ P ∈ triangleFirstCubes U.scale pi i, w P)+B i)*dotProduct v v) := by
        dsimp only [B]
        rw [← Finset.mul_sum, ← Finset.sum_mul, ← Finset.mul_sum, Finset.sum_add_distrib]
      _ = _ := by
        rw [show (∑ P ∈ triangleFirstCubes U.scale pi i, w P)=mass i from
          triangle_root_first_weights U pi i]
  have hmaj : Summable (fun i => rootAssemblySensitivity *
      (2*(mass i+B i)*dotProduct v v)) :=
    (((triangle_first_masses_hasSum.summable.add hB.1).mul_left 2).mul_right (dotProduct v v)).mul_left _
  have hCs := hmaj.of_nonneg_of_le hC0 hC
  refine ⟨hCs, ?_⟩
  apply (hCs.tsum_le_tsum hC hmaj).trans
  have he : (∑' i, rootAssemblySensitivity *
      (2*(mass i+B i)*dotProduct v v)) =
      rootAssemblySensitivity * (2*(1+∑' i, B i)*dotProduct v v) := by
    rw [tsum_mul_left, tsum_mul_right, tsum_mul_left,
      triangle_first_masses_hasSum.summable.tsum_add hB.1,
      triangle_first_masses_hasSum.tsum_eq]
  rw [he]
  have hadd : 1+(∑' i, B i) ≤ 1+2*Real.sqrt 3*resetAllOrderTau := by
    linarith only [hB.2]
  have hbudget := (mul_le_mul_of_nonneg_left hadd (by norm_num : (0:ℝ) ≤ 2)).trans
    (planar_linear_average_le_envelope resetAllOrderTau hτ)
  have hh := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right hbudget hv) hE
  simpa only [mul_assoc] using hh

end
end ASDExplicitGamma.Inverse
