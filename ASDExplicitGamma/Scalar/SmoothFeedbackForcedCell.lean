/-
Copyright (c) 2026 Scott N. Armstrong. All rights reserved.
-/
module

public import ASDExplicitGamma.Scalar.SmoothFeedbackJointCell
public import ASDExplicitGamma.Scalar.SmoothFeedbackJointPaired
public import ASDExplicitGamma.Scalar.SmoothFeedbackGapIdentity
public import ASDExplicitGamma.Inverse.PureFluxGeneratorTiledFeedback

/-! The cellwise forced difference `Z* - Z_lift` of the smooth-feedback
estimate (Λ8.3): the restriction of the global maximizer to a child cell, minus
the cell residual of the top load, is a forced response with forcing the load. -/

@[expose] public section

namespace ASDExplicitGamma.Scalar

open MeasureTheory Homogenization Response Triadic Variational
open ASDExplicitGamma.Native
open Algsuperdiff.Section3
open scoped BigOperators

noncomputable section

/-- The Euler equation of the global maximizer, tested against a variation
supported in a child cell, in the cell's own normalization. -/
theorem cell_euler
    (Q U : TriadicCube 2) (hUQ : openCubeSet U ⊆ openCubeSet Q)
    (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (k : ResponseCoefficient (openCubeSet Q)) (w : Vec 2 → Vec 2)
    (hw : MemVectorL2 (openCubeSet Q) w)
    (Z : Vec 2 → BlockVec 2) (hZ : IsScalarOldMaximizer Q ν σ k w Z)
    (T : Vec 2 → BlockVec 2) (hT : ScalarVariation (openCubeSet U) T) :
    volumeAverage (openCubeSet U) (fun x => blockVecDot (T x)
        (blockMatVecMul (blockCoeffField (responseFramePlanarCoefficientField ν σ
          (oldSignedCellCoefficient Q U hUQ k)) x) (Z x))) =
      volumeAverage (openCubeSet U) (fun x => vecDot (w x) (T x).1) := by
  classical
  have hTt : ScalarVariation (openCubeSet Q) ((openCubeSet U).indicator T) :=
    scalar_variation_zero_extension (isOpen_openCubeSet U) (isOpen_openCubeSet Q) hUQ hT
  have hEuler := smooth_feedback_maximizer_variation_euler Q ν σ hν hσ k w hw Z _ hZ hTt
  have hsymm := old_signed_energy_pairing_symm Q ν σ k Z ((openCubeSet U).indicator T)
  have hvolU : (volume (openCubeSet U)).toReal ≠ 0 := by
    rw [volume_openCubeSet_toReal]; exact (cubeVolume_pos U).ne'
  have hvolQ : (volume (openCubeSet Q)).toReal ≠ 0 := by
    rw [volume_openCubeSet_toReal]; exact (cubeVolume_pos Q).ne'
  have hmeasU := (isOpen_openCubeSet U).measurableSet
  have hsetint {f : Vec 2 → ℝ} :
      ∫ x in openCubeSet Q, (openCubeSet U).indicator f x = ∫ x in openCubeSet U, f x := by
    rw [integral_indicator hmeasU, Measure.restrict_restrict hmeasU,
      Set.inter_eq_left.mpr hUQ]
  -- source side
  have hsrc : scalarSourcePairing (openCubeSet Q) w ((openCubeSet U).indicator T) =
      (volume (openCubeSet Q)).toReal⁻¹ * ∫ x in openCubeSet U, vecDot (w x) (T x).1 := by
    unfold scalarSourcePairing volumeAverage
    congr 1
    rw [← hsetint (f := fun x => vecDot (w x) (T x).1)]
    congr 1
    funext x
    by_cases hx : x ∈ openCubeSet U <;> simp [Set.indicator, hx, vecDot]
  -- energy side
  have hen : oldSignedEnergyPairing Q ν σ k ((openCubeSet U).indicator T) Z =
      (volume (openCubeSet Q)).toReal⁻¹ * ∫ x in openCubeSet U, blockVecDot (T x)
        (blockMatVecMul (blockCoeffField (responseFramePlanarCoefficientField ν σ
          (oldSignedCellCoefficient Q U hUQ k)) x) (Z x)) := by
    unfold oldSignedEnergyPairing volumeAverage
    congr 1
    rw [← hsetint (f := fun x => blockVecDot (T x)
        (blockMatVecMul (blockCoeffField (responseFramePlanarCoefficientField ν σ
          (oldSignedCellCoefficient Q U hUQ k)) x) (Z x)))]
    congr 1
    funext x
    by_cases hx : x ∈ openCubeSet U
    · have hco : responseFramePlanarCoefficientField ν σ (oldSignedCellCoefficient Q U hUQ k) x =
          responseFramePlanarCoefficientField ν σ k x := by
        unfold responseFramePlanarCoefficientField
        rw [old_signed_cell_coefficient_extension_eq Q U hUQ k hx]
      simp only [Set.indicator, hx, if_true, blockCoeffField, hco]
    · simp [Set.indicator, hx, blockVecDot, vecDot]
  have hfinal : (volume (openCubeSet Q)).toReal⁻¹ * ∫ x in openCubeSet U, vecDot (w x) (T x).1 =
      (volume (openCubeSet Q)).toReal⁻¹ * ∫ x in openCubeSet U, blockVecDot (T x)
        (blockMatVecMul (blockCoeffField (responseFramePlanarCoefficientField ν σ
          (oldSignedCellCoefficient Q U hUQ k)) x) (Z x)) := by
    rw [← hsrc, hEuler, hsymm, hen]
  have hcancel := mul_left_cancel₀ (inv_ne_zero hvolQ) hfinal
  unfold volumeAverage
  rw [hcancel]

/-- The reciprocal gradient `g = (A Z*)₂` of the global maximizer is a gradient. -/
theorem maximizer_lower_potential
    (Q : TriadicCube 2) (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (k : ResponseCoefficient (openCubeSet Q)) (w : Vec 2 → Vec 2)
    (hw : MemVectorL2 (openCubeSet Q) w)
    (Z : Vec 2 → BlockVec 2) (hZ : IsScalarOldMaximizer Q ν σ k w Z) :
    MemVectorL2 (openCubeSet Q) (fun x => (blockMatVecMul (blockCoeffField
        (responseFramePlanarCoefficientField ν σ k) x) (Z x)).2) ∧
    IsPotentialOn (openCubeSet Q) (fun x => (blockMatVecMul (blockCoeffField
        (responseFramePlanarCoefficientField ν σ k) x) (Z x)).2) := by
  classical
  let U := openCubeSet Q
  let a := responseFramePlanarCoefficientField ν σ k
  have hEll := responseFramePlanarCoefficientField_isElliptic
    (measurableSet_openCubeSet Q) ν σ hν hσ k
  have hflux := scalar_coefficient_flux_memL2 Q a hEll hZ.1.1
  have hLower : MemVectorL2 U (fun x => (blockMatVecMul (blockCoeffField a x) (Z x)).2) :=
    memVectorL2_snd_of_memBlockL2 hflux
  refine ⟨hLower, ?_⟩
  letI : IsFiniteMeasure (volumeMeasureOn U) :=
    (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume
  have hv : (volume U).toReal ≠ 0 := by
    rw [volume_openCubeSet_toReal]; exact (cubeVolume_pos Q).ne'
  apply IsPotentialOn.of_orthogonal_to_solenoidalZeroNormalTrace_of_memVectorL2_of_hodgeConverseCriterion
    (hodgeConverseCriterion_of_isOpenBoundedConvexDomain
      (isOpenBoundedConvexDomain_openCubeSet Q)) hLower
  intro g hg hsol
  have hT : ScalarVariation U (fun x => ((0 : Vec 2), g x)) :=
    ⟨memBlockL2_blockField (memVectorL2_const 0) hg, ⟨0, rfl⟩, hsol⟩
  have hEuler := smooth_feedback_maximizer_variation_euler Q ν σ hν hσ k w hw Z _ hZ hT
  have hsymm := old_signed_energy_pairing_symm Q ν σ k Z (fun x => ((0 : Vec 2), g x))
  have hsrc : scalarSourcePairing U w (fun x => ((0 : Vec 2), g x)) = 0 := by
    unfold scalarSourcePairing volumeAverage
    simp [vecDot]
  rw [hsrc] at hEuler
  rw [hsymm] at hEuler
  unfold oldSignedEnergyPairing volumeAverage at hEuler
  have h0 := (mul_eq_zero.mp hEuler.symm).resolve_left (inv_ne_zero hv)
  simpa [blockVecDot, vecDot] using h0

theorem bmv_sub (A : BlockMat 2) (X Y : BlockVec 2) :
    blockMatVecMul A (X - Y) = blockMatVecMul A X - blockMatVecMul A Y := by
  have h := blockMatVecMul_add A (X - Y) Y
  rw [sub_add_cancel] at h
  rw [h]
  abel

/-- Cellwise forced difference (Λ8.3): the restriction of the global maximizer to a
child cell, minus the actual cell residual of the top load, has joint weak-Haar
charge at most `√(B_U E_U) + 3^{-1/4} B_U P_{1/4,U}(w - w_U)`. -/
theorem cell_forced_difference
    (Q U : TriadicCube 2) (hUQ : openCubeSet U ⊆ openCubeSet Q)
    (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (k : ResponseCoefficient (openCubeSet Q))
    (u : H10Function (openCubeSet Q))
    (Z : Vec 2 → BlockVec 2)
    (hZ : IsScalarOldMaximizer Q ν σ k (fun x => u.toH1Function.grad x) Z)
    (hQ : ScalarQuarterHaarAdmissible U (fun x i =>
      u.toH1Function.grad x i - cubeAverage U (fun y => u.toH1Function.grad y i))) :
    let f : Vec 2 → Vec 2 := u.toH1Function.grad
    let F : Vec 2 → BlockVec 2 := fun x => (f x, 0)
    let hF : MemBlockL2 (openCubeSet Q) F :=
      memBlockL2_blockField u.toH1Function.grad_memVectorL2 MemLp.zero
    let kU := oldSignedCellCoefficient Q U hUQ k
    let aU := responseFramePlanarCoefficientField ν σ kU
    let Y := oldSignedCellResidual Q U hUQ ν σ hν hσ k F hF
    let D : Vec 2 → BlockVec 2 := fun x => Z x - Y x
    Real.sqrt (vectorWeakHaarEnergy U (fun x j => (D x).1 j) +
        vectorWeakHaarEnergy U (fun x => (scalarCoefficientFlux aU D x).2)) ≤
      Real.sqrt (lemmaVInverseHistory U aU ((3 : ℝ) ^ (1 / 4 : ℝ)) *
        oldSignedEnergyPairing U ν σ kU D D) +
      (3 : ℝ) ^ (-(1 / 4 : ℝ)) * lemmaVInverseHistory U aU ((3 : ℝ) ^ (1 / 4 : ℝ)) *
        Real.sqrt (vectorPositiveHaarEnergy U (fun x i =>
          f x i - cubeAverage U (fun y => f y i))) := by
  classical
  intro f F hF kU aU Y D
  have hEllU := responseFramePlanarCoefficientField_isElliptic
    (measurableSet_openCubeSet U) ν σ hν hσ kU
  have hEllQ := responseFramePlanarCoefficientField_isElliptic
    (measurableSet_openCubeSet Q) ν σ hν hσ k
  have hw : MemVectorL2 (openCubeSet Q) f := u.toH1Function.grad_memVectorL2
  have hWvar : ScalarVariation (openCubeSet Q) F :=
    ⟨hF, by simpa [F, f] using u.isPotentialZeroTraceOn, isSolenoidalZeroNormalTraceOn_zero⟩
  -- the actual cell residual of the top load
  have hYmem : MemBlockL2 (openCubeSet U) Y := (oldSignedCellResidual Q U hUQ ν σ hν hσ k F hF).property
  have hFR : MemBlockL2 (openCubeSet U) F :=
    hF.mono_measure (Measure.restrict_mono_set volume hUQ)
  have hRemoved := old_signed_cell_removed_variation Q U hUQ ν σ hν hσ k F hF
  have hCorrection : ScalarCompatible (openCubeSet U) (fun x => F x - Y x) :=
    scalar_variation_compatible hRemoved
  have hFcell : ScalarCompatible (openCubeSet U) F :=
    old_signed_compatible_restrict Q U hUQ (scalar_variation_compatible hWvar)
  have hYcompat : ScalarCompatible (openCubeSet U) Y := by
    have hsub := old_signed_compatible_sub hFcell hCorrection
    change ScalarCompatible (openCubeSet U) (fun x => F x - (F x - Y x)) at hsub
    simpa only [sub_sub_cancel] using hsub
  have hdual : ScalarCompatible (openCubeSet U) (fun x =>
      (blockMatVecMul (blockCoeffField aU x) (Y x)).swap) := by
    change ScalarCompatible (openCubeSet U) (oldSignedDualReflection U ν σ kU Y)
    simpa [oldSignedDualReflection, oldSignedCellResidual, aU, kU, Y] using
      old_signed_reflected_residual_compatible U ν σ hν hσ kU
        (toHilbertBlockL2OfBlockField hFR)
  let WY : BlockState 2 := ⟨fun x => (Y x).1, fun x => (Y x).2⟩
  have hWY : BlockResponseSpace aU (openCubeSet U) WY := by
    simpa [WY] using smooth_feedback_response_of_primal_dual_compatible
      (openCubeSet U) aU Y hYcompat hdual
  have hZcell : ScalarCompatible (openCubeSet U) Z :=
    old_signed_compatible_restrict Q U hUQ (scalar_variation_compatible hZ.1)
  have hDcompat : ScalarCompatible (openCubeSet U) D :=
    old_signed_compatible_sub hZcell hYcompat
  let W : BlockState 2 := ⟨fun x => (D x).1, fun x => (D x).2⟩
  have hWeval : W.eval = D := by
    funext x
    exact Prod.eta (D x)
  have hWYeval : WY.eval = Y := by
    funext x
    exact Prod.eta (Y x)
  have hWpot : IsBlockPotentialOn (openCubeSet U) W := hDcompat.2.1
  have hWsol : IsBlockSolenoidalOn (openCubeSet U) W := hDcompat.2.2
  have hWmem : MemBlockL2 (openCubeSet U) W.eval := by
    rw [hWeval]; exact hDcompat.1
  have hWlower : MemVectorL2 (openCubeSet U)
      (fun x => (blockMatVecMul (blockCoeffField aU x) (W.eval x)).2) := by
    have := scalar_coefficient_flux_memL2 U aU hEllU hWmem
    exact memVectorL2_snd_of_memBlockL2 this
  -- the reciprocal gradient of the difference is a gradient
  have hlowerQ := maximizer_lower_potential Q ν σ hν hσ k f hw Z hZ
  have hlowerU : IsPotentialOn (openCubeSet U)
      (fun x => (blockMatVecMul (blockCoeffField aU x) (Z x)).2) := by
    have h1 := hlowerQ.2.restrict_of_isOpen_of_memVectorL2 (isOpen_openCubeSet Q)
      (isOpen_openCubeSet U) hUQ (hlowerQ.1.mono_measure (Measure.restrict_mono_set volume hUQ))
    refine old_signed_isPotentialOn_congr_ae h1 ?_
    filter_upwards [old_signed_cell_frame_coefficient_ae Q U hUQ ν σ k] with x hx
    simp only [blockCoeffField, aU, kU, hx]
  have hlowerY : IsPotentialOn (openCubeSet U)
      (fun x => (blockMatVecMul (blockCoeffField aU x) (Y x)).2) := by
    have := hdual.2.1
    simpa using this
  have hPotW : IsPotentialOn (openCubeSet U)
      (fun x => (blockMatVecMul (blockCoeffField aU x) (W.eval x)).2) := by
    have hfun : (fun x => (blockMatVecMul (blockCoeffField aU x) (W.eval x)).2) =
        (fun x => (blockMatVecMul (blockCoeffField aU x) (Z x)).2) +
          (-1 : ℝ) • (fun x => (blockMatVecMul (blockCoeffField aU x) (Y x)).2) := by
      funext x
      rw [hWeval]
      have hx : (blockMatVecMul (blockCoeffField aU x) (D x)).2 =
          (blockMatVecMul (blockCoeffField aU x) (Z x)).2 -
            (blockMatVecMul (blockCoeffField aU x) (Y x)).2 := by
        simp only [D, bmv_sub]
        rfl
      rw [hx]
      ext i
      simp [sub_eq_add_neg]
    rw [hfun]
    exact isPotentialOn_add hlowerU (isPotentialOn_smul hlowerY (-1))
  obtain ⟨ug, hug⟩ := hPotW
  have hu : (fun x => (blockMatVecMul (blockCoeffField aU x) (W.eval x)).2) =ᵐ[
      volumeMeasureOn (openCubeSet U)] ug.grad :=
    Filter.Eventually.of_forall fun x => (congrFun hug x).symm
  -- the forced equation
  let G : Vec 2 → Vec 2 := fun x i => f x i - cubeAverage U (fun y => f y i)
  let hfin : IsFiniteMeasure (volumeMeasureOn (openCubeSet U)) :=
    (isOpenBoundedConvexDomain_openCubeSet U).isFiniteMeasure_restrict_volume
  have hforced : ∀ T : BlockState 2, ScalarVariation (openCubeSet U) T.eval →
      volumeAverage (openCubeSet U) (blockPairingIntegrand aU T W) =
        volumeAverage (openCubeSet U) (fun x => vecDot (T.potential x) (G x)) := by
    intro T hT
    have hTmem : MemBlockL2 (openCubeSet U) T.eval := hT.1
    have hZmem : MemBlockL2 (openCubeSet U) Z := hZcell.1
    have hint1 := old_signed_energy_pairing_integrable U ν σ hν hσ kU hTmem hZmem
    have hint2 := old_signed_energy_pairing_integrable U ν σ hν hσ kU hTmem hYmem
    have hEul := cell_euler Q U hUQ ν σ hν hσ k f hw Z hZ T.eval hT
    have hYo := hWY.2.2 T ⟨hT.2.1, hT.2.2⟩
    rw [hWYeval] at hYo
    have h1 : blockPairingIntegrand aU T W = fun x =>
        blockVecDot (T.eval x) (blockMatVecMul (blockCoeffField aU x) (Z x)) -
          blockVecDot (T.eval x) (blockMatVecMul (blockCoeffField aU x) (Y x)) := by
      funext x
      unfold blockPairingIntegrand
      rw [hWeval]
      simp only [D, bmv_sub, blockVecDot_sub_right]
    have hv : (volume (openCubeSet U)).toReal ≠ 0 := by
      rw [volume_openCubeSet_toReal]; exact (cubeVolume_pos U).ne'
    have hT1mem : MemVectorL2 (openCubeSet U) T.potential := memVectorL2_fst_of_memBlockL2 hTmem
    have hwU : MemVectorL2 (openCubeSet U) f :=
      hw.mono_measure (Measure.restrict_mono_set volume hUQ)
    have hfT : IntegrableOn (fun x => vecDot (f x) (T.eval x).1) (openCubeSet U) :=
      integrableOn_vecDot_of_memVectorL2 hwU hT1mem
    have hTm : IntegrableOn (fun x => vecDot (T.potential x)
        (fun i => cubeAverage U (fun y => f y i))) (openCubeSet U) :=
      integrableOn_vecDot_of_memVectorL2 hT1mem (memVectorL2_const _)
    have hzero : ∫ x in openCubeSet U, vecDot (fun i => cubeAverage U (fun y => f y i))
        (T.potential x) = 0 :=
      Homogenization.CorrectionFieldData.integral_vecDot_const_left_eq_zero_of_integral_eq_zero_coords
        _ hT1mem
        (IsPotentialZeroTraceOn.integral_eq_zero hT.2.1)
    have hdot : (fun x => vecDot (T.potential x) (G x)) = fun x => vecDot (f x) (T.eval x).1 -
        vecDot (T.potential x) (fun i => cubeAverage U (fun y => f y i)) := by
      funext x
      simp only [G, vecDot, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib, BlockState.eval]
      congr 1
      refine Finset.sum_congr rfl fun i _ => by ring
    have hmean0 : ∫ x in openCubeSet U, vecDot (T.potential x)
        (fun i => cubeAverage U (fun y => f y i)) = 0 := by
      rw [← hzero]
      congr 1
      funext x
      exact vecDot_comm _ _
    unfold volumeAverage at hEul ⊢
    rw [h1, hdot, integral_sub hint1 hint2, integral_sub hfT hTm, hmean0, hYo]
    have hEul' := mul_left_cancel₀ (inv_ne_zero hv) hEul
    rw [hEul']
  have hwG : MemLp G 2 (normalizedCubeMeasure U) := hQ.memLp
  have hmain := ASDExplicitGamma.Inverse.pureFlux_forced_pair_joint_bound U hEllU W hWpot hWsol
    hWmem hWlower hwG hQ.increments hforced ug hu
  obtain ⟨X, hX0, hXE, hXg⟩ := hmain
  have hEeq : oldSignedEnergyPairing U ν σ kU D D = blockPairingAverage (openCubeSet U) aU W W := by
    change volumeAverage (openCubeSet U) (fun x => blockVecDot (D x)
      (blockMatVecMul (blockCoeffField aU x) (D x))) =
      volumeAverage (openCubeSet U) (fun x => blockVecDot (W.eval x)
        (blockMatVecMul (blockCoeffField aU x) (W.eval x)))
    rw [hWeval]
  have hwg : vectorWeakHaarEnergy U (fun x => (scalarCoefficientFlux aU D x).2) =
      vectorWeakHaarEnergy U ug.grad := by
    apply smooth_feedback_vector_weak_energy_congr_ae
    have : (fun x => (scalarCoefficientFlux aU D x).2) =
        fun x => (blockMatVecMul (blockCoeffField aU x) (W.eval x)).2 := by
      funext x
      rw [hWeval]
      rfl
    rw [this]
    exact hu
  rw [hwg, hEeq]
  have hB0 : 0 ≤ lemmaVInverseHistory U aU ((3 : ℝ) ^ (1 / 4 : ℝ)) :=
    lemmaVInverseHistory_nonneg U aU (Real.one_lt_rpow (by norm_num) (by norm_num))
  have hE0 : 0 ≤ blockPairingAverage (openCubeSet U) aU W W :=
    compatible_blockPairingAverage_nonneg hEllU W
  have hWp0 := vectorWeakHaarEnergy_nonneg U (fun x j => (D x).1 j)
  have hWg0 := vectorWeakHaarEnergy_nonneg U ug.grad
  have hcirc := ASDExplicitGamma.Inverse.pureFlux_forcedSourceCircleEnergy_le U G
  have hc0 : 0 ≤ (3 : ℝ) ^ (-(1 / 4 : ℝ)) := by positivity
  set B := lemmaVInverseHistory U aU ((3 : ℝ) ^ (1 / 4 : ℝ)) with hBdef
  set E := blockPairingAverage (openCubeSet U) aU W W with hEdef
  set c := (3 : ℝ) ^ (-(1 / 4 : ℝ)) with hcdef
  set δ := c * B * Real.sqrt (vectorPositiveHaarEnergy U G) with hδ
  have hδ0 : 0 ≤ δ := by positivity
  have hXBE : X ≤ B * E := by
    have : vectorWeakHaarEnergy U W.potential ≥ 0 := vectorWeakHaarEnergy_nonneg U _
    linarith
  have hg' : Real.sqrt (vectorWeakHaarEnergy U ug.grad) ≤ Real.sqrt X + δ := by
    refine hXg.trans ?_
    refine add_le_add le_rfl ?_
    have := Real.sqrt_le_sqrt hcirc
    rw [hδ]
    have hcB : 0 ≤ c * B := mul_nonneg hc0 hB0
    nlinarith [this, hcB]
  have hwg2 : vectorWeakHaarEnergy U ug.grad ≤ (Real.sqrt X + δ) ^ 2 := by
    calc vectorWeakHaarEnergy U ug.grad = Real.sqrt (vectorWeakHaarEnergy U ug.grad) ^ 2 :=
          (Real.sq_sqrt hWg0).symm
      _ ≤ (Real.sqrt X + δ) ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) hg' 2
  have hsX : Real.sqrt X ≤ Real.sqrt (B * E) := Real.sqrt_le_sqrt hXBE
  have hsq : Real.sqrt X ^ 2 = X := Real.sq_sqrt hX0
  have hsqBE : Real.sqrt (B * E) ^ 2 = B * E := Real.sq_sqrt (mul_nonneg hB0 hE0)
  have hp : vectorWeakHaarEnergy U (fun x j => (D x).1 j) ≤ B * E - X := by
    have : vectorWeakHaarEnergy U W.potential = vectorWeakHaarEnergy U (fun x j => (D x).1 j) :=
      rfl
    linarith
  have hfin : vectorWeakHaarEnergy U (fun x j => (D x).1 j) + vectorWeakHaarEnergy U ug.grad ≤
      (Real.sqrt (B * E) + δ) ^ 2 := by
    nlinarith [hp, hwg2, hsX, hsq, hsqBE, mul_nonneg (Real.sqrt_nonneg X) hδ0,
      mul_le_mul_of_nonneg_right hsX hδ0]
  calc _ ≤ Real.sqrt ((Real.sqrt (B * E) + δ) ^ 2) := Real.sqrt_le_sqrt hfin
    _ = Real.sqrt (B * E) + δ := Real.sqrt_sq (add_nonneg (Real.sqrt_nonneg _) hδ0)

end

end ASDExplicitGamma.Scalar
