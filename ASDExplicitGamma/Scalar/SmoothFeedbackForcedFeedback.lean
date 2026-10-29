/-
Copyright (c) 2026 Scott N. Armstrong. All rights reserved.
-/
module

public import ASDExplicitGamma.Scalar.SmoothFeedbackForcedCell
public import ASDExplicitGamma.Scalar.SmoothFeedbackJointCell
public import ASDExplicitGamma.Scalar.SmoothFeedbackJointFeedback
public import ASDExplicitGamma.Scalar.SmoothFeedbackSourceCharge
public import ASDExplicitGamma.Scalar.SmoothFeedbackActualQuantities
public import ASDExplicitGamma.Scalar.SmoothFeedbackGapMeasurable

/-! Joint smooth feedback `F_w` of the actual OLD maximizers: the lift part
(affine, oscillatory) plus the forced difference `Z* - Z_lift` (Λ8.3). -/

@[expose] public section

namespace ASDExplicitGamma.Scalar

open MeasureTheory Homogenization Response Triadic Variational
open ASDExplicitGamma.Native
open Algsuperdiff.Section3
open scoped BigOperators

noncomputable section

/-- Two-stage Euclidean aggregation of five cellwise bounds. -/
theorem joint_weighted_five_minkowski
    {ι κ : Type*} [Fintype κ] (S : Finset ι) (c : ℝ) (hc : 0 ≤ c)
    (s g r d e h : ι → κ → ℝ)
    (hs : ∀ i U, 0 ≤ s i U) (hg : ∀ i U, 0 ≤ g i U) (hr : ∀ i U, 0 ≤ r i U)
    (hd : ∀ i U, 0 ≤ d i U) (he : ∀ i U, 0 ≤ e i U) (hh : ∀ i U, 0 ≤ h i U)
    (hle : ∀ i U, s i U ≤ g i U + r i U + d i U + e i U + h i U) :
    Real.sqrt (∑ i ∈ S, c * ∑ U, s i U ^ 2) ≤
      Real.sqrt (∑ i ∈ S, c * ∑ U, g i U ^ 2) +
      Real.sqrt (∑ i ∈ S, c * ∑ U, r i U ^ 2) +
      Real.sqrt (∑ i ∈ S, c * ∑ U, d i U ^ 2) +
      Real.sqrt (∑ i ∈ S, c * ∑ U, e i U ^ 2) +
      Real.sqrt (∑ i ∈ S, c * ∑ U, h i U ^ 2) := by
  have h1 := joint_weighted_three_minkowski S c hc s g r (fun i U => d i U + e i U + h i U)
    hs hg hr (fun i U => add_nonneg (add_nonneg (hd i U) (he i U)) (hh i U))
    (fun i U => by have := hle i U; linarith)
  have h2 := joint_weighted_three_minkowski S c hc (fun i U => d i U + e i U + h i U) d e h
    (fun i U => add_nonneg (add_nonneg (hd i U) (he i U)) (hh i U)) hd he hh
    (fun i U => le_rfl)
  linarith

theorem memLp_coord {U : TriadicCube 2} {g : Vec 2 → Vec 2}
    (h : MemVectorL2 (openCubeSet U) g) (i : Fin 2) :
    MemLp (fun x => g x i) 2 (normalizedCubeMeasure U) :=
  memLp_normalized_of_memL2On (h.eval i)

/-- Joint smooth feedback `F_w` of the actual global maximizers `Z*`:
the lift part plus the forced difference. -/
theorem smooth_feedback_h2_joint_feedback_star
    {ι : Type*} (S : Finset ι)
    (M : ABKModel 2) (m : ℤ) (Q : TriadicCube 2) (depth : ℕ)
    (ω : Cutoff.CutoffSample 2)
    (u : ι → H10Function (openCubeSet Q))
    (hcenterQuarter : ∀ i, ∀ U : TriadicCube 2,
      U ∈ descendantsAtDepth Q depth →
        ScalarQuarterHaarAdmissible U (fun x j =>
          (u i).toH1Function.grad x j -
            cubeAverage U (fun y => (u i).toH1Function.grad y j)))
    (Z : ι → Vec 2 → BlockVec 2)
    (hZ : ∀ i, IsScalarOldMaximizer Q M.nu
      (Annealed.sigmaBar M m : ℝ) (oldCutoffSkewCoefficient m Q ω)
      (fun x => (u i).toH1Function.grad x) (Z i)) :
    let σ : ℝ := Annealed.sigmaBar M m
    let k : ResponseCoefficient (openCubeSet Q) := oldCutoffSkewCoefficient m Q ω
    let f : ι → Vec 2 → Vec 2 := fun i x => (u i).toH1Function.grad x
    let F : ι → Vec 2 → BlockVec 2 := fun i x => (f i x, 0)
    let hF : ∀ i, MemBlockL2 (openCubeSet Q) (F i) := fun i =>
      memBlockL2_blockField (u i).toH1Function.grad_memVectorL2 MemLp.zero
    let Y : ι → Vec 2 → BlockVec 2 := fun i =>
      oldSignedLocalResidual Q depth M.nu σ M.nu_pos
        (Annealed.sigmaBar M m).property k (F i) (hF i)
    let Gap : ℝ := ∑ i ∈ S, scalarFieldEnergy M.nu σ k (Z i - Y i)
    let B : ℝ := smoothFeedbackSourceHistoryMaximum Q depth M.nu σ k
    let deltaSq : ℝ := ∑ i ∈ S, oldSignedCellAverage Q depth (fun U =>
      vectorPositiveHaarEnergy U.val
        (fun x j => f i x j - cubeAverage U.val (fun y => f i y j)))
    let R_K : ℝ := ∑ i ∈ S, oldSignedCellAverage Q depth (fun U =>
      let hU := openCubeSet_subset_of_mem_descendantsAtDepth U.property
      let mean : Vec 2 := fun j => cubeAverage U.val (fun x => f i x j)
      let C : Vec 2 → BlockVec 2 := fun x => (fun j => f i x j - mean j, 0)
      let hC : MemBlockL2 (openCubeSet Q) C := by
        have hsub : MemLp (fun x => F i x - (mean, 0)) 2
            (volumeMeasureOn (openCubeSet Q)) :=
          (hF i).sub (memLp_const (mean, 0))
        convert hsub using 1
        ext x j
        · simp [C, F, f]
        · change (0 : Vec 2) j = (0 - 0 : Vec 2) j
          simp
      let YC := oldSignedCellResidual Q U.val hU M.nu σ M.nu_pos
        (Annealed.sigmaBar M m).property k C hC
      oldSignedEnergyPairing U.val M.nu σ
        (oldSignedCellCoefficient Q U.val hU k) YC YC)
    let ThetaGamma : ℝ := ∑ i ∈ S, oldSignedCellAverage Q depth (fun U =>
      let mean : Vec 2 := fun j => cubeAverage U.val (fun x => f i x j)
      smoothFeedbackCellDirectionalGamma M m U.val mean ω)
    let FwSq : ℝ := ∑ i ∈ S, oldSignedCellAverage Q depth (fun U =>
      let hU := openCubeSet_subset_of_mem_descendantsAtDepth U.property
      let aU := responseFramePlanarCoefficientField M.nu σ
        (oldSignedCellCoefficient Q U.val hU k)
      vectorWeakHaarEnergy U.val (fun x j => (Z i x).1 j - f i x j) +
        vectorWeakHaarEnergy U.val (fun x => (scalarCoefficientFlux aU (Z i) x).2))
    Real.sqrt FwSq ≤ Real.sqrt ThetaGamma + Real.sqrt (B * R_K) +
      Real.sqrt (B * Gap) +
        (1 + Scalar.inverseHistoryDiscount * B) * Real.sqrt deltaSq := by
  classical
  intro σ k f F hF Y Gap B deltaSq R_K ThetaGamma FwSq
  have hσ : 0 < σ := (Annealed.sigmaBar M m).property
  let c : ℝ := ((descendantsAtDepth Q depth).card : ℝ)⁻¹
  have hc : 0 ≤ c := by positivity
  let c0 : ℝ := Scalar.inverseHistoryDiscount
  have hc0 : 0 ≤ c0 := Scalar.inverse_history_discount_range.1.le
  let fwq : ι → OldSignedCellIndex Q depth → ℝ := fun i U =>
    let hU := openCubeSet_subset_of_mem_descendantsAtDepth U.property
    let aU := responseFramePlanarCoefficientField M.nu σ
      (oldSignedCellCoefficient Q U.val hU k)
    vectorWeakHaarEnergy U.val (fun x j => (Z i x).1 j - f i x j) +
      vectorWeakHaarEnergy U.val (fun x => (scalarCoefficientFlux aU (Z i) x).2)
  let fwl : ι → OldSignedCellIndex Q depth → ℝ := fun i U =>
    let hU := openCubeSet_subset_of_mem_descendantsAtDepth U.property
    let YU := oldSignedCellResidual Q U.val hU M.nu σ M.nu_pos
      (Annealed.sigmaBar M m).property k (F i) (hF i)
    let aU := responseFramePlanarCoefficientField M.nu σ
      (oldSignedCellCoefficient Q U.val hU k)
    vectorWeakHaarEnergy U.val (fun x j => (YU x).1 j - f i x j) +
      vectorWeakHaarEnergy U.val (fun x => (scalarCoefficientFlux aU YU x).2)
  let gam : ι → OldSignedCellIndex Q depth → ℝ := fun i U =>
    let mean : Vec 2 := fun j => cubeAverage U.val (fun x => f i x j)
    smoothFeedbackCellDirectionalGamma M m U.val mean ω
  let dl : ι → OldSignedCellIndex Q depth → ℝ := fun i U =>
    vectorPositiveHaarEnergy U.val
      (fun x j => f i x j - cubeAverage U.val (fun y => f i y j))
  let hist : OldSignedCellIndex Q depth → ℝ := fun U =>
    lemmaVInverseHistory U.val
      (responseFramePlanarCoefficientField M.nu σ
        (oldSignedCellCoefficient Q U.val
          (openCubeSet_subset_of_mem_descendantsAtDepth U.property) k))
      ((3 : ℝ) ^ (1 / 4 : ℝ))
  let rK : ι → OldSignedCellIndex Q depth → ℝ := fun i U =>
    let hU := openCubeSet_subset_of_mem_descendantsAtDepth U.property
    let mean : Vec 2 := fun j => cubeAverage U.val (fun x => f i x j)
    let C : Vec 2 → BlockVec 2 := fun x => (fun j => f i x j - mean j, 0)
    let hC : MemBlockL2 (openCubeSet Q) C := by
      have hsub : MemLp (fun x => F i x - (mean, 0)) 2
          (volumeMeasureOn (openCubeSet Q)) :=
        (hF i).sub (memLp_const (mean, 0))
      convert hsub using 1
      ext x j
      · simp [C, F, f]
      · change (0 : Vec 2) j = (0 - 0 : Vec 2) j
        simp
    let YC := oldSignedCellResidual Q U.val hU M.nu σ M.nu_pos
      (Annealed.sigmaBar M m).property k C hC
    oldSignedEnergyPairing U.val M.nu σ
      (oldSignedCellCoefficient Q U.val hU k) YC YC
  let En : ι → OldSignedCellIndex Q depth → ℝ := fun i U =>
    let hU := openCubeSet_subset_of_mem_descendantsAtDepth U.property
    let YU := oldSignedCellResidual Q U.val hU M.nu σ M.nu_pos
      (Annealed.sigmaBar M m).property k (F i) (hF i)
    oldSignedEnergyPairing U.val M.nu σ (oldSignedCellCoefficient Q U.val hU k)
      (fun x => Z i x - YU x) (fun x => Z i x - YU x)
  have hfwq : ∀ i U, 0 ≤ fwq i U := fun i U =>
    add_nonneg (vectorWeakHaarEnergy_nonneg _ _) (vectorWeakHaarEnergy_nonneg _ _)
  have hgam : ∀ i U, 0 ≤ gam i U := fun i U =>
    smooth_feedback_cell_directional_gamma_nonneg M m U.val _ ω
  have hdl : ∀ i U, 0 ≤ dl i U := fun i U => vectorPositiveHaarEnergy_nonneg _ _
  have hhist : ∀ U, 0 ≤ hist U := fun U =>
    lemmaVInverseHistory_nonneg U.val _
      (Real.one_lt_rpow (by norm_num) (by norm_num))
  have hrK : ∀ i U, 0 ≤ rK i U := fun i U =>
    old_signed_energy_pairing_nonneg U.val M.nu σ M.nu_pos
      (Annealed.sigmaBar M m).property _ _
  have hEn : ∀ i U, 0 ≤ En i U := fun i U =>
    old_signed_energy_pairing_nonneg U.val M.nu σ M.nu_pos
      (Annealed.sigmaBar M m).property _ _
  have hcellZ : ∀ i (U : OldSignedCellIndex Q depth),
      Real.sqrt (fwq i U) ≤ Real.sqrt (gam i U) + Real.sqrt (hist U * rK i U) +
        Real.sqrt (dl i U) + Real.sqrt (hist U * En i U) +
        c0 * hist U * Real.sqrt (dl i U) := by
    intro i U
    have hU := openCubeSet_subset_of_mem_descendantsAtDepth U.property
    have hlift : Real.sqrt (fwl i U) ≤ Real.sqrt (gam i U) +
        Real.sqrt (hist U * rK i U) + Real.sqrt (dl i U) := by
      have h1 := smooth_feedback_cell_joint_feedback Q U.val hU M.nu σ M.nu_pos
        (Annealed.sigmaBar M m).property k (u i) (hcenterQuarter i U.val U.property)
      have h2 := smooth_feedback_cell_affine_pair_eq_gamma M m Q U.val hU ω
        (fun j => cubeAverage U.val (fun x => (u i).toH1Function.grad x j))
      dsimp only at h1 h2
      rw [h2] at h1
      exact h1
    have hdiff := cell_forced_difference Q U.val hU M.nu σ M.nu_pos
      (Annealed.sigmaBar M m).property k (u i) (Z i) (hZ i)
      (hcenterQuarter i U.val U.property)
    dsimp only at hdiff
    let YU : BlockL2 (openCubeSet U.val) := oldSignedCellResidual Q U.val hU M.nu σ M.nu_pos
      (Annealed.sigmaBar M m).property k (F i) (hF i)
    have hYmem : MemBlockL2 (openCubeSet U.val) YU := YU.property
    let aU := responseFramePlanarCoefficientField M.nu σ
      (oldSignedCellCoefficient Q U.val hU k)
    have hEllU := responseFramePlanarCoefficientField_isElliptic
      (measurableSet_openCubeSet U.val) M.nu σ M.nu_pos hσ
      (oldSignedCellCoefficient Q U.val hU k)
    have hZmemU : MemBlockL2 (openCubeSet U.val) (Z i) :=
      (hZ i).1.1.mono_measure (Measure.restrict_mono_set volume hU)
    have hwU : MemVectorL2 (openCubeSet U.val) (f i) :=
      (u i).toH1Function.grad_memVectorL2.mono_measure (Measure.restrict_mono_set volume hU)
    have hDmem : MemBlockL2 (openCubeSet U.val) (fun x => Z i x - YU x) := hZmemU.sub hYmem
    have hv1 : MemVectorL2 (openCubeSet U.val) (fun x j => (YU x).1 j - f i x j) :=
      (memVectorL2_fst_of_memBlockL2 hYmem).sub hwU
    have hv2 : MemVectorL2 (openCubeSet U.val) (fun x => (Z i x - YU x).1) :=
      memVectorL2_fst_of_memBlockL2 hDmem
    have hv3 : MemVectorL2 (openCubeSet U.val) (fun x => (scalarCoefficientFlux aU YU x).2) :=
      memVectorL2_snd_of_memBlockL2 (scalar_coefficient_flux_memL2 U.val aU hEllU hYmem)
    have hv4 : MemVectorL2 (openCubeSet U.val)
        (fun x => (scalarCoefficientFlux aU (fun y => Z i y - YU y) x).2) :=
      memVectorL2_snd_of_memBlockL2 (scalar_coefficient_flux_memL2 U.val aU hEllU hDmem)
    have htri := joint_pair_weak_triangle U.val
      (memLp_coord hv1) (memLp_coord hv2) (memLp_coord hv3) (memLp_coord hv4)
    have e1 : (fun x => (fun x j => (YU x).1 j - f i x j) x + (fun x => (Z i x - YU x).1) x) =
        fun x j => (Z i x).1 j - f i x j := by
      funext x
      ext j
      simp
    have e2 : (fun x => (fun x => (scalarCoefficientFlux aU YU x).2) x +
        (fun x => (scalarCoefficientFlux aU (fun y => Z i y - YU y) x).2) x) =
        fun x => (scalarCoefficientFlux aU (Z i) x).2 := by
      funext x
      beta_reduce
      have hb : scalarCoefficientFlux aU (fun y => Z i y - YU y) x =
          scalarCoefficientFlux aU (Z i) x - scalarCoefficientFlux aU YU x := by
        unfold scalarCoefficientFlux
        exact bmv_sub _ _ _
      rw [hb]
      ext j
      simp
    rw [e1, e2] at htri
    have hfinal : Real.sqrt (fwq i U) ≤ Real.sqrt (fwl i U) +
        Real.sqrt (vectorWeakHaarEnergy U.val (fun x j => (Z i x - YU x).1 j) +
          vectorWeakHaarEnergy U.val
            (fun x => (scalarCoefficientFlux aU (fun y => Z i y - YU y) x).2)) := htri
    have hcd : c0 = (3 : ℝ) ^ (-(1 / 4 : ℝ)) := rfl
    have hEn' : En i U = oldSignedEnergyPairing U.val M.nu σ
        (oldSignedCellCoefficient Q U.val hU k) (fun x => Z i x - YU x)
        (fun x => Z i x - YU x) := rfl
    have hdiff' : Real.sqrt (vectorWeakHaarEnergy U.val (fun x j => (Z i x - YU x).1 j) +
          vectorWeakHaarEnergy U.val
            (fun x => (scalarCoefficientFlux aU (fun y => Z i y - YU y) x).2)) ≤
        Real.sqrt (hist U * En i U) + c0 * hist U * Real.sqrt (dl i U) := hdiff
    linarith
  have hagg := joint_weighted_five_minkowski S c hc
    (fun i U => Real.sqrt (fwq i U)) (fun i U => Real.sqrt (gam i U))
    (fun i U => Real.sqrt (hist U * rK i U)) (fun i U => Real.sqrt (dl i U))
    (fun i U => Real.sqrt (hist U * En i U)) (fun i U => c0 * hist U * Real.sqrt (dl i U))
    (fun i U => Real.sqrt_nonneg _) (fun i U => Real.sqrt_nonneg _)
    (fun i U => Real.sqrt_nonneg _) (fun i U => Real.sqrt_nonneg _)
    (fun i U => Real.sqrt_nonneg _)
    (fun i U => mul_nonneg (mul_nonneg hc0 (hhist U)) (Real.sqrt_nonneg _)) hcellZ
  have hsq (q : ι → OldSignedCellIndex Q depth → ℝ) (hq : ∀ i U, 0 ≤ q i U) :
      (∑ i ∈ S, c * ∑ U, Real.sqrt (q i U) ^ 2) = ∑ i ∈ S, c * ∑ U, q i U := by
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    apply Finset.sum_congr rfl
    intro U _
    exact Real.sq_sqrt (hq i U)
  rw [hsq fwq hfwq, hsq gam hgam, hsq dl hdl,
    hsq (fun i U => hist U * rK i U) (fun i U => mul_nonneg (hhist U) (hrK i U)),
    hsq (fun i U => hist U * En i U) (fun i U => mul_nonneg (hhist U) (hEn i U))] at hagg
  have hFw : FwSq = ∑ i ∈ S, c * ∑ U, fwq i U := rfl
  have hTh : ThetaGamma = ∑ i ∈ S, c * ∑ U, gam i U := rfl
  have hDe : deltaSq = ∑ i ∈ S, c * ∑ U, dl i U := rfl
  have hRK : R_K = ∑ i ∈ S, c * ∑ U, rK i U := rfl
  have hBge : ∀ U, hist U ≤ B := fun U =>
    smooth_feedback_source_history_maximum_member_le Q depth M.nu σ k U.val U.property
  have hB0 : 0 ≤ B := smooth_feedback_source_history_maximum_nonneg Q depth M.nu σ k
  have hmulle (q : ι → OldSignedCellIndex Q depth → ℝ) (hq : ∀ i U, 0 ≤ q i U) :
      (∑ i ∈ S, c * ∑ U, hist U * q i U) ≤ B * ∑ i ∈ S, c * ∑ U, q i U := by
    have hper : ∀ i ∈ S, c * (∑ U, hist U * q i U) ≤ B * (c * ∑ U, q i U) := by
      intro i _
      have hsum : (∑ U, hist U * q i U) ≤ B * ∑ U, q i U := by
        rw [Finset.mul_sum]
        exact Finset.sum_le_sum fun U _ => mul_le_mul_of_nonneg_right (hBge U) (hq i U)
      calc
        c * (∑ U, hist U * q i U) ≤ c * (B * ∑ U, q i U) :=
          mul_le_mul_of_nonneg_left hsum hc
        _ = B * (c * ∑ U, q i U) := by ring
    calc
      _ ≤ ∑ i ∈ S, B * (c * ∑ U, q i U) := Finset.sum_le_sum hper
      _ = B * ∑ i ∈ S, c * ∑ U, q i U := by rw [Finset.mul_sum]
  have hBR : (∑ i ∈ S, c * ∑ U, hist U * rK i U) ≤ B * R_K := by
    rw [hRK]; exact hmulle rK hrK
  have hGapEq : (∑ i ∈ S, c * ∑ U, En i U) = Gap := by
    apply Finset.sum_congr rfl
    intro i _
    have hZY : MemBlockL2 (openCubeSet Q) (Z i - Y i) :=
      (hZ i).1.1.sub (old_signed_local_residual_memLp Q depth M.nu σ M.nu_pos hσ k (F i) (hF i))
    change c * ∑ U, En i U = scalarFieldEnergy M.nu σ k (Z i - Y i)
    rw [scalarFieldEnergy_eq_pairing Q M.nu σ M.nu_pos hσ k,
      old_signed_energy_pairing_partition Q depth M.nu σ M.nu_pos hσ k hZY hZY]
    unfold oldSignedCellAverage
    congr 1
    refine Finset.sum_congr rfl fun U _ => ?_
    have hae : (fun x => Z i x - (oldSignedCellResidual Q U.val
        (openCubeSet_subset_of_mem_descendantsAtDepth U.property) M.nu σ M.nu_pos
        (Annealed.sigmaBar M m).property k (F i) (hF i)) x) =ᵐ[
        volumeMeasureOn (openCubeSet U.val)] (Z i - Y i) := by
      filter_upwards [old_signed_local_residual_restrict Q depth M.nu σ M.nu_pos hσ k (F i)
        (hF i) U.val U.property] with x hx
      change Z i x - _ = Z i x - oldSignedLocalResidual Q depth M.nu σ M.nu_pos hσ k
        (F i) (hF i) x
      rw [hx]
    exact old_signed_energy_pairing_congr_ae U.val M.nu σ _ hae hae
  have hBG : (∑ i ∈ S, c * ∑ U, hist U * En i U) ≤ B * Gap := by
    rw [← hGapEq]; exact hmulle En hEn
  have hGap0 : 0 ≤ Gap := Finset.sum_nonneg fun i _ =>
    smooth_feedback_scalar_field_energy_nonneg Q M.nu σ M.nu_pos hσ k _
  have hh2 : (∑ i ∈ S, c * ∑ U, (c0 * hist U * Real.sqrt (dl i U)) ^ 2) ≤
      (c0 * B) ^ 2 * deltaSq := by
    rw [hDe, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    calc c * ∑ U, (c0 * hist U * Real.sqrt (dl i U)) ^ 2
        ≤ c * ∑ U, (c0 * B) ^ 2 * dl i U := by
          refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun U _ => ?_) hc
          rw [mul_pow, Real.sq_sqrt (hdl i U)]
          have : (c0 * hist U) ^ 2 ≤ (c0 * B) ^ 2 :=
            pow_le_pow_left₀ (mul_nonneg hc0 (hhist U)) (mul_le_mul_of_nonneg_left (hBge U) hc0) 2
          exact mul_le_mul_of_nonneg_right this (hdl i U)
      _ = (c0 * B) ^ 2 * (c * ∑ U, dl i U) := by rw [← Finset.mul_sum]; ring
  have hdelta0 : 0 ≤ Real.sqrt deltaSq := Real.sqrt_nonneg _
  have hhroot : Real.sqrt (∑ i ∈ S, c * ∑ U, (c0 * hist U * Real.sqrt (dl i U)) ^ 2) ≤
      c0 * B * Real.sqrt deltaSq := by
    refine (Real.sqrt_le_sqrt hh2).trans (le_of_eq ?_)
    rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (mul_nonneg hc0 hB0)]
  have hRtail : Real.sqrt (∑ i ∈ S, c * ∑ U, hist U * rK i U) ≤ Real.sqrt (B * R_K) :=
    Real.sqrt_le_sqrt hBR
  have hGtail : Real.sqrt (∑ i ∈ S, c * ∑ U, hist U * En i U) ≤ Real.sqrt (B * Gap) :=
    Real.sqrt_le_sqrt hBG
  rw [hFw, hTh]
  have hDe' : (∑ i ∈ S, c * ∑ U, dl i U) = deltaSq := hDe.symm
  rw [hDe'] at hagg
  nlinarith [hagg, hRtail, hGtail, hhroot, hdelta0]

section Named

variable {ι : Type*} (S : Finset ι) (M : ABKModel 2) (m : ℤ) (Q : TriadicCube 2)
  (depth : ℕ) (u : ι → H10Function (openCubeSet Q))

/-- `F_w²` of the actual global maximizers `Z*`: the weak-Haar charge of
`(p_w - w, g_w)` on the child cells, with `p_w` the first component of `Z*` and
`g_w` the reciprocal gradient `(A Z*)₂`. -/
def fwStar (Z : Cutoff.CutoffSample 2 → ι → Vec 2 → BlockVec 2)
    (ω : Cutoff.CutoffSample 2) : ℝ := ∑ i ∈ S,
  oldSignedCellAverage Q depth (fun U =>
    vectorWeakHaarEnergy U.val (fun x j => (Z ω i x).1 j - (u i).toH1Function.grad x j) +
      vectorWeakHaarEnergy U.val (fun x => (scalarCoefficientFlux
        (responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M m : ℝ)
          (oldSignedCellCoefficient Q U.val
            (openCubeSet_subset_of_mem_descendantsAtDepth U.property)
            (oldCutoffSkewCoefficient m Q ω))) (Z ω i) x).2))

/-- The joint smooth feedback of the actual maximizers (Λ8.4). -/
theorem actual_fw_star_le
    (H : ∀ i, HasWeakHessianOn (openCubeSet Q) (u i).toH1Function)
    (Z : Cutoff.CutoffSample 2 → ι → Vec 2 → BlockVec 2)
    (hZ : ∀ ω i, IsScalarOldMaximizer Q M.nu (Annealed.sigmaBar M m : ℝ)
      (oldCutoffSkewCoefficient m Q ω) (fun x => (u i).toH1Function.grad x) (Z ω i))
    (ω : Cutoff.CutoffSample 2) :
    Real.sqrt (fwStar S M m Q depth u Z ω) ≤
      Real.sqrt (theta'' S M m Q depth u ω) +
      Real.sqrt (bhist M m Q depth ω * rK' S M m Q depth u ω) +
      Real.sqrt (bhist M m Q depth ω * gap' S M m Q depth u Z ω) +
      (1 + Scalar.inverseHistoryDiscount * bhist M m Q depth ω) *
        Real.sqrt (deltaSq' S Q depth u) := by
  have := smooth_feedback_h2_joint_feedback_star S M m Q depth ω u
    (fun i U hU => (smooth_feedback_h2_projected_source_admissible Q U
      (openCubeSet_subset_of_mem_descendantsAtDepth hU) (u i) (H i)).2.2.1)
    (Z ω) (hZ ω)
  exact this

end Named

section Diff

variable {ι : Type*} (S : Finset ι) (M : ABKModel 2) (m : ℤ) (Q : TriadicCube 2)
  (depth : ℕ) (u : ι → H10Function (openCubeSet Q))

/-- The cell residual of the actual top load `(w_i, 0)`: `Z_lift|_U = Q_{a,U}(w_i,0)`. -/
def cellLift (ω : Cutoff.CutoffSample 2) (i : ι) (U : OldSignedCellIndex Q depth) :
    Vec 2 → BlockVec 2 :=
  oldSignedCellResidual Q U.val
    (openCubeSet_subset_of_mem_descendantsAtDepth U.property)
    M.nu (Annealed.sigmaBar M m : ℝ) M.nu_pos (Annealed.sigmaBar M m).property
    (oldCutoffSkewCoefficient m Q ω) (topLoad Q u i) (topLoad_memL2 Q u i)

/-- The energy `‖Z* - Z_lift‖²_{A,U}` on a child cell. -/
def cellDiffEnergy (Z : Cutoff.CutoffSample 2 → ι → Vec 2 → BlockVec 2)
    (ω : Cutoff.CutoffSample 2) (i : ι) (U : OldSignedCellIndex Q depth) : ℝ :=
  oldSignedEnergyPairing U.val M.nu (Annealed.sigmaBar M m : ℝ)
    (oldSignedCellCoefficient Q U.val
      (openCubeSet_subset_of_mem_descendantsAtDepth U.property)
      (oldCutoffSkewCoefficient m Q ω))
    (fun x => Z ω i x - cellLift M m Q depth u ω i U x)
    (fun x => Z ω i x - cellLift M m Q depth u ω i U x)

/-- `F_diff²`: the weak-Haar charge of `(p_diff, g_diff)` on the child cells. -/
def fwDiff (Z : Cutoff.CutoffSample 2 → ι → Vec 2 → BlockVec 2)
    (ω : Cutoff.CutoffSample 2) : ℝ := ∑ i ∈ S,
  oldSignedCellAverage Q depth (fun U =>
    vectorWeakHaarEnergy U.val
        (fun x j => (Z ω i x - cellLift M m Q depth u ω i U x).1 j) +
      vectorWeakHaarEnergy U.val (fun x => (scalarCoefficientFlux
        (responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M m : ℝ)
          (oldSignedCellCoefficient Q U.val
            (openCubeSet_subset_of_mem_descendantsAtDepth U.property)
            (oldCutoffSkewCoefficient m Q ω)))
        (fun y => Z ω i y - cellLift M m Q depth u ω i U y) x).2))

/-- The gap is the cell average of the cell energies of the forced difference. -/
theorem gap_eq_cell_diff_energy
    (Z : Cutoff.CutoffSample 2 → ι → Vec 2 → BlockVec 2)
    (hZ : ∀ ω i, IsScalarOldMaximizer Q M.nu (Annealed.sigmaBar M m : ℝ)
      (oldCutoffSkewCoefficient m Q ω) (fun x => (u i).toH1Function.grad x) (Z ω i))
    (ω : Cutoff.CutoffSample 2) :
    gap' S M m Q depth u Z ω = ∑ i ∈ S,
      oldSignedCellAverage Q depth (fun U => cellDiffEnergy M m Q depth u Z ω i U) := by
  classical
  have hσ : 0 < (Annealed.sigmaBar M m : ℝ) := (Annealed.sigmaBar M m).property
  apply Finset.sum_congr rfl
  intro i _
  have hZY : MemBlockL2 (openCubeSet Q) (Z ω i - oldSignedLocalResidual Q depth M.nu
      (Annealed.sigmaBar M m : ℝ) M.nu_pos hσ (oldCutoffSkewCoefficient m Q ω)
      (topLoad Q u i) (topLoad_memL2 Q u i)) :=
    (hZ ω i).1.1.sub (old_signed_local_residual_memLp Q depth M.nu (Annealed.sigmaBar M m : ℝ)
      M.nu_pos hσ (oldCutoffSkewCoefficient m Q ω) (topLoad Q u i) (topLoad_memL2 Q u i))
  rw [scalarFieldEnergy_eq_pairing Q M.nu (Annealed.sigmaBar M m : ℝ) M.nu_pos hσ,
    old_signed_energy_pairing_partition Q depth M.nu (Annealed.sigmaBar M m : ℝ) M.nu_pos hσ _ hZY hZY]
  unfold oldSignedCellAverage
  congr 1
  refine Finset.sum_congr rfl fun U _ => ?_
  have hae : (Z ω i - oldSignedLocalResidual Q depth M.nu (Annealed.sigmaBar M m : ℝ)
      M.nu_pos hσ (oldCutoffSkewCoefficient m Q ω) (topLoad Q u i)
      (topLoad_memL2 Q u i)) =ᵐ[volumeMeasureOn (openCubeSet U.val)]
      (fun x => Z ω i x - cellLift M m Q depth u ω i U x) := by
    filter_upwards [old_signed_local_residual_restrict Q depth M.nu
      (Annealed.sigmaBar M m : ℝ) M.nu_pos hσ (oldCutoffSkewCoefficient m Q ω)
      (topLoad Q u i) (topLoad_memL2 Q u i) U.val U.property] with x hx
    change Z ω i x - _ = Z ω i x - _
    rw [hx]
    rfl
  exact old_signed_energy_pairing_congr_ae U.val M.nu (Annealed.sigmaBar M m : ℝ) _ hae hae

/-- Λ8.3: the joint forced difference of the actual maximizer and the actual lift. -/
theorem actual_forced_difference
    (H : ∀ i, HasWeakHessianOn (openCubeSet Q) (u i).toH1Function)
    (Z : Cutoff.CutoffSample 2 → ι → Vec 2 → BlockVec 2)
    (hZ : ∀ ω i, IsScalarOldMaximizer Q M.nu (Annealed.sigmaBar M m : ℝ)
      (oldCutoffSkewCoefficient m Q ω) (fun x => (u i).toH1Function.grad x) (Z ω i))
    (ω : Cutoff.CutoffSample 2) :
    Real.sqrt (fwDiff S M m Q depth u Z ω) ≤
      Real.sqrt (bhist M m Q depth ω * gap' S M m Q depth u Z ω) +
        Scalar.inverseHistoryDiscount * bhist M m Q depth ω *
          Real.sqrt (deltaSq' S Q depth u) := by
  classical
  have hσ : 0 < (Annealed.sigmaBar M m : ℝ) := (Annealed.sigmaBar M m).property
  let c : ℝ := ((descendantsAtDepth Q depth).card : ℝ)⁻¹
  have hc : 0 ≤ c := by positivity
  let c0 : ℝ := Scalar.inverseHistoryDiscount
  have hc0 : 0 ≤ c0 := Scalar.inverse_history_discount_range.1.le
  let B : ℝ := bhist M m Q depth ω
  have hB0 : 0 ≤ B := smooth_feedback_source_history_maximum_nonneg Q depth M.nu (Annealed.sigmaBar M m : ℝ) _
  let hist : OldSignedCellIndex Q depth → ℝ := fun U =>
    lemmaVInverseHistory U.val
      (responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M m : ℝ)
        (oldSignedCellCoefficient Q U.val
          (openCubeSet_subset_of_mem_descendantsAtDepth U.property)
          (oldCutoffSkewCoefficient m Q ω)))
      ((3 : ℝ) ^ (1 / 4 : ℝ))
  have hhist : ∀ U, 0 ≤ hist U := fun U =>
    lemmaVInverseHistory_nonneg U.val _ (Real.one_lt_rpow (by norm_num) (by norm_num))
  have hBge : ∀ U, hist U ≤ B := fun U =>
    smooth_feedback_source_history_maximum_member_le Q depth M.nu
      (Annealed.sigmaBar M m : ℝ) (oldCutoffSkewCoefficient m Q ω) U.val U.property
  let dl : ι → OldSignedCellIndex Q depth → ℝ := fun i U =>
    vectorPositiveHaarEnergy U.val
      (fun x j => (u i).toH1Function.grad x j -
        cubeAverage U.val (fun y => (u i).toH1Function.grad y j))
  have hdl : ∀ i U, 0 ≤ dl i U := fun i U => vectorPositiveHaarEnergy_nonneg _ _
  let En : ι → OldSignedCellIndex Q depth → ℝ := fun i U =>
    cellDiffEnergy M m Q depth u Z ω i U
  have hEn : ∀ i U, 0 ≤ En i U := fun i U =>
    old_signed_energy_pairing_nonneg U.val M.nu (Annealed.sigmaBar M m : ℝ) M.nu_pos hσ _ _
  let fd : ι → OldSignedCellIndex Q depth → ℝ := fun i U =>
    vectorWeakHaarEnergy U.val
        (fun x j => (Z ω i x - cellLift M m Q depth u ω i U x).1 j) +
      vectorWeakHaarEnergy U.val (fun x => (scalarCoefficientFlux
        (responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M m : ℝ)
          (oldSignedCellCoefficient Q U.val
            (openCubeSet_subset_of_mem_descendantsAtDepth U.property)
            (oldCutoffSkewCoefficient m Q ω)))
        (fun y => Z ω i y - cellLift M m Q depth u ω i U y) x).2)
  have hfd : ∀ i U, 0 ≤ fd i U := fun i U =>
    add_nonneg (vectorWeakHaarEnergy_nonneg _ _) (vectorWeakHaarEnergy_nonneg _ _)
  have hcell : ∀ i (U : OldSignedCellIndex Q depth),
      Real.sqrt (fd i U) ≤ Real.sqrt (hist U * En i U) + c0 * hist U * Real.sqrt (dl i U) := by
    intro i U
    have hU := openCubeSet_subset_of_mem_descendantsAtDepth U.property
    have hdiff := cell_forced_difference Q U.val hU M.nu (Annealed.sigmaBar M m : ℝ) M.nu_pos hσ
      (oldCutoffSkewCoefficient m Q ω) (u i) (Z ω i) (hZ ω i)
      (smooth_feedback_h2_projected_source_admissible Q U.val hU (u i) (H i)).2.2.1
    dsimp only at hdiff
    exact hdiff
  have hagg := joint_weighted_three_minkowski S c hc
    (fun i U => Real.sqrt (fd i U)) (fun i U => Real.sqrt (hist U * En i U))
    (fun i U => c0 * hist U * Real.sqrt (dl i U)) (fun i U => 0)
    (fun i U => Real.sqrt_nonneg _) (fun i U => Real.sqrt_nonneg _)
    (fun i U => mul_nonneg (mul_nonneg hc0 (hhist U)) (Real.sqrt_nonneg _))
    (fun i U => le_rfl) (fun i U => by have := hcell i U; linarith)
  have hsq (q : ι → OldSignedCellIndex Q depth → ℝ) (hq : ∀ i U, 0 ≤ q i U) :
      (∑ i ∈ S, c * ∑ U, Real.sqrt (q i U) ^ 2) = ∑ i ∈ S, c * ∑ U, q i U := by
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    apply Finset.sum_congr rfl
    intro U _
    exact Real.sq_sqrt (hq i U)
  rw [hsq fd hfd, hsq (fun i U => hist U * En i U) (fun i U => mul_nonneg (hhist U) (hEn i U))]
    at hagg
  have hmulle : (∑ i ∈ S, c * ∑ U, hist U * En i U) ≤ B * ∑ i ∈ S, c * ∑ U, En i U := by
    have hper : ∀ i ∈ S, c * (∑ U, hist U * En i U) ≤ B * (c * ∑ U, En i U) := by
      intro i _
      have hsum : (∑ U, hist U * En i U) ≤ B * ∑ U, En i U := by
        rw [Finset.mul_sum]
        exact Finset.sum_le_sum fun U _ => mul_le_mul_of_nonneg_right (hBge U) (hEn i U)
      calc
        c * (∑ U, hist U * En i U) ≤ c * (B * ∑ U, En i U) :=
          mul_le_mul_of_nonneg_left hsum hc
        _ = B * (c * ∑ U, En i U) := by ring
    calc
      _ ≤ ∑ i ∈ S, B * (c * ∑ U, En i U) := Finset.sum_le_sum hper
      _ = B * ∑ i ∈ S, c * ∑ U, En i U := by rw [Finset.mul_sum]
  have hgap := gap_eq_cell_diff_energy S M m Q depth u Z hZ ω
  have hGapEq : (∑ i ∈ S, c * ∑ U, En i U) = gap' S M m Q depth u Z ω := by
    rw [hgap]; rfl
  have hh2 : (∑ i ∈ S, c * ∑ U, (c0 * hist U * Real.sqrt (dl i U)) ^ 2) ≤
      (c0 * B) ^ 2 * deltaSq' S Q depth u := by
    unfold deltaSq'
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    calc c * ∑ U, (c0 * hist U * Real.sqrt (dl i U)) ^ 2
        ≤ c * ∑ U, (c0 * B) ^ 2 * dl i U := by
          refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun U _ => ?_) hc
          rw [mul_pow, Real.sq_sqrt (hdl i U)]
          have : (c0 * hist U) ^ 2 ≤ (c0 * B) ^ 2 :=
            pow_le_pow_left₀ (mul_nonneg hc0 (hhist U)) (mul_le_mul_of_nonneg_left (hBge U) hc0) 2
          exact mul_le_mul_of_nonneg_right this (hdl i U)
      _ = (c0 * B) ^ 2 * oldSignedCellAverage Q depth (fun U => dl i U) := by
          unfold oldSignedCellAverage; rw [← Finset.mul_sum]; ring
  have hhroot : Real.sqrt (∑ i ∈ S, c * ∑ U, (c0 * hist U * Real.sqrt (dl i U)) ^ 2) ≤
      c0 * B * Real.sqrt (deltaSq' S Q depth u) := by
    refine (Real.sqrt_le_sqrt hh2).trans (le_of_eq ?_)
    rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (mul_nonneg hc0 hB0)]
  have hGtail : Real.sqrt (∑ i ∈ S, c * ∑ U, hist U * En i U) ≤
      Real.sqrt (B * gap' S M m Q depth u Z ω) := by
    refine Real.sqrt_le_sqrt ?_
    rw [← hGapEq]; exact hmulle
  have hFd : fwDiff S M m Q depth u Z ω = ∑ i ∈ S, c * ∑ U, fd i U := rfl
  rw [hFd]
  have h0 : Real.sqrt (∑ i ∈ S, c * ∑ U, (fun (i : ι) (U : OldSignedCellIndex Q depth) =>
      (0 : ℝ)) i U ^ 2) = 0 := by simp
  rw [h0] at hagg
  nlinarith [hagg, hGtail, hhroot]

end Diff

end

end ASDExplicitGamma.Scalar

