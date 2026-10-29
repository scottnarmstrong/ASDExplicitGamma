/-
Copyright (c) 2026 Scott N. Armstrong. All rights reserved.
-/
module

public import ASDExplicitGamma.Gaussian.BandModelLaw
public import ASDExplicitGamma.Gaussian.RectangleClosure
public import ASDExplicitGamma.Scalar.ChaosHilbertEnvelope
public import ASDExplicitGamma.Scalar.DefectResolventCarriers
public import ASDExplicitGamma.Scalar.Lambda8CovarianceAdapter

import ASDExplicitGamma.Scalar.CutoffMeasurability
import ASDExplicitGamma.Scalar.ChaosMultiShellTransfer

set_option linter.style.haveILetI false

/-! The physical OLD/fresh defect envelope and its multi-shell Gaussian transfer. -/

@[expose] public section

open MeasureTheory ProbabilityTheory ASDExplicitGamma.Gaussian
  ASDExplicitGamma.Response ASDExplicitGamma.Variational ASDExplicitGamma.Scalar
  Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3 Homogenization
open scoped ENNReal

namespace ASDExplicitGamma.Scalar

local instance defectEnvelopeOpenCubeFiniteMeasure (Q : TriadicCube 2) :
    IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
  (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume

/-- Restrict a continuous fresh band to the actual OLD response square. -/
noncomputable def freshResponseCoefficientCLM (Q : TriadicCube 2)
    (a₀ b₀ c₀ d₀ : ℝ) (hab : a₀ < b₀) (hcd : c₀ < d₀)
    (hQ : openCubeSet Q ⊆ openRectangle a₀ b₀ c₀ d₀) :
    C(closedRectangle a₀ b₀ c₀ d₀, ℝ) →L[ℝ]
      ResponseCoefficient (openCubeSet Q) := by
  let ι : C(closure (openCubeSet Q), closedRectangle a₀ b₀ c₀ d₀) :=
    ⟨fun x => ⟨x.1, by
      rw [← rectangle_closure a₀ b₀ c₀ d₀ hab hcd]
      exact closure_mono hQ x.2⟩, by
      fun_prop⟩
  exact (BoundedContinuousFunction.compContinuousCLM ℝ ℝ ι).comp
    (ContinuousMap.linearIsometryBoundedOfCompact
      (closedRectangle a₀ b₀ c₀ d₀) ℝ ℝ).toContinuousLinearEquiv.toContinuousLinearMap

/-- The local flat input is the actual Dirichlet projection of the fresh scalar
field times the rotated source direction. -/
noncomputable def freshFlatInputCLM (Q : TriadicCube 2)
    (a₀ b₀ c₀ d₀ : ℝ) (hab : a₀ < b₀) (hcd : c₀ < d₀) (e : Vec 2) :
    C(closedRectangle a₀ b₀ c₀ d₀, ℝ) →L[ℝ]
      HilbertVectorL2 (openCubeSet Q) :=
  lambda8Q3ProjectedLoadClass (isOpenBoundedConvexDomain_openCubeSet Q)
    a₀ b₀ c₀ d₀ hab hcd e

/-- A continuous-linear presentation of the OLD first response as a map
of the coefficient direction. -/
noncomputable def oldFirstResponseCLM {U : Set (Vec 2)}
    [IsFiniteMeasure (volumeMeasureOn U)]
    (hU : MeasurableSet U) (hvol : 0 < (volume U).toReal)
    (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (k : ResponseCoefficient U) (P : BlockVec 2) :
    ResponseCoefficient U →L[ℝ]
      EnergyCarrier (responseFrameEnergyData hU hvol ν σ hν hσ k) := by
  let D := responseFrameEnergyData hU hvol ν σ hν hσ k
  let M := (responseFrameMuOperatorSystemData hU hvol ν σ hν hσ k).toMuHilbertRealization
  let u₀ := responseFrameEnergyBaseMinimizer hU hvol ν σ hν hσ k P
  let C := responseFrameEnergyShearFamily hU hvol ν σ hν hσ k
  exact (responseEnergyUpCLM D).comp
    ((M.correctionSpace.correctionSpace.subtypeL).comp
      ((oldResolvent M).comp
        ((responseEnergyDownCLM D).comp
          ((ContinuousLinearMap.apply ℝ (Fₗ := EnergyCarrier D) u₀).comp C))))

theorem old_first_response_clm_apply {U : Set (Vec 2)}
    [IsFiniteMeasure (volumeMeasureOn U)]
    (hU : MeasurableSet U) (hvol : 0 < (volume U).toReal)
    (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (k : ResponseCoefficient U) (P : BlockVec 2) (H : ResponseCoefficient U) :
    oldFirstResponseCLM hU hvol ν σ hν hσ k P H =
      oldFirstResponse hU hvol ν σ hν hσ k P H := by
  simp only [oldFirstResponseCLM, ContinuousLinearMap.comp_apply,
    responseEnergyUpCLM_apply, responseEnergyDownCLM_apply]
  rfl

/-- The flat first response as a continuous-linear function of its actual
local Dirichlet-projected input. -/
noncomputable def flatFirstResponseCLM {U : Set (Vec 2)}
    [IsFiniteMeasure (volumeMeasureOn U)]
    (hU : MeasurableSet U) (hvol : 0 < (volume U).toReal)
    (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (k : ResponseCoefficient U) :
    HilbertVectorL2 U →L[ℝ]
      EnergyCarrier (responseFrameEnergyData hU hvol ν σ hν hσ k) :=
  (responseEnergyUpCLM (responseFrameEnergyData hU hvol ν σ hν hσ k)).comp
    ((hilbertPureSecondL2 U).comp (-ContinuousLinearMap.id ℝ (HilbertVectorL2 U)))

theorem flat_first_response_clm_apply {U : Set (Vec 2)}
    [IsFiniteMeasure (volumeMeasureOn U)]
    (hU : MeasurableSet U) (hvol : 0 < (volume U).toReal)
    (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (k : ResponseCoefficient U) (w : HilbertVectorL2 U) :
    flatFirstResponseCLM hU hvol ν σ hν hσ k w =
      flatFirstResponse hU hvol ν σ hν hσ k w := by
  rfl

/-- The fresh-field bilinear map for the actual second defect source
`C_H δu₁`. Its first slot makes the OLD shear; its second slot makes the actual
OLD-minus-flat first-response defect. -/
noncomputable def secondDefectFieldBilinear (Q : TriadicCube 2)
    (a₀ b₀ c₀ d₀ : ℝ) (hab : a₀ < b₀) (hcd : c₀ < d₀)
    (hQ : openCubeSet Q ⊆ openRectangle a₀ b₀ c₀ d₀)
    (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (k : ResponseCoefficient (openCubeSet Q)) (P : BlockVec 2) (e : Vec 2) :
    let hU := measurableSet_openCubeSet Q
    let hvol := by rw [volume_openCubeSet_toReal]; exact cubeVolume_pos Q
    C(closedRectangle a₀ b₀ c₀ d₀, ℝ) →L[ℝ]
      C(closedRectangle a₀ b₀ c₀ d₀, ℝ) →L[ℝ]
        EnergyCarrier (responseFrameEnergyData hU hvol ν σ hν hσ k) := by
  let hU := measurableSet_openCubeSet Q
  let hvol : 0 < (volume (openCubeSet Q)).toReal := by
    rw [volume_openCubeSet_toReal]
    exact cubeVolume_pos Q
  let D := responseFrameEnergyData hU hvol ν σ hν hσ k
  let H := σ • freshResponseCoefficientCLM Q a₀ b₀ c₀ d₀ hab hcd hQ
  let w := freshFlatInputCLM Q a₀ b₀ c₀ d₀ hab hcd e
  let δ := (oldFirstResponseCLM hU hvol ν σ hν hσ k P).comp H -
    (flatFirstResponseCLM hU hvol ν σ hν hσ k).comp w
  let C : ResponseCoefficient (openCubeSet Q) →L[ℝ]
      (EnergyCarrier D →L[ℝ] EnergyCarrier D) :=
    responseFrameEnergyShearFamily hU hvol ν σ hν hσ k
  let f : C(closedRectangle a₀ b₀ c₀ d₀, ℝ) →ₗ[ℝ]
      C(closedRectangle a₀ b₀ c₀ d₀, ℝ) →ₗ[ℝ] EnergyCarrier D :=
    { toFun := fun x =>
        { toFun := fun y => C (H x) (δ y)
          map_add' := by
            intro y z
            rw [map_add δ]
            exact map_add (C (H x)) (δ y) (δ z)
          map_smul' := by
            intro r y
            rw [map_smul δ]
            exact map_smul (C (H x)) r (δ y) }
      map_add' := by
        intro x y
        ext z
        change C (H (x + y)) (δ z) = C (H x) (δ z) + C (H y) (δ z)
        rw [map_add H, map_add C]
        rfl
      map_smul' := by
        intro r x
        ext z
        change C (H (r • x)) (δ z) = r • C (H x) (δ z)
        rw [map_smul H, map_smul C]
        rfl }
  have hbound (x y : C(closedRectangle a₀ b₀ c₀ d₀, ℝ)) :
      ‖f x y‖ ≤ (‖H‖ / ν * ‖δ‖) * ‖x‖ * ‖y‖ := by
    change ‖C (H x) (δ y)‖ ≤ _
    calc
      ‖C (H x) (δ y)‖ ≤ ‖H x‖ / ν * ‖δ y‖ := by
        change ‖responseEnergyShearFamilyLinear hU σ hσ
          (responseEnergyHilbertData
            ((responseFrameMuOperatorSystemData hU hvol ν σ hν hσ k).toMuHilbertRealization))
          (H x) (δ y)‖ ≤ _
        exact responseFrameEnergyShearFamily_apply_norm_le
          hU hvol ν σ hν hσ k (H x) (δ y)
      _ ≤ ‖H x‖ / ν * (‖δ‖ * ‖y‖) :=
        mul_le_mul_of_nonneg_left (δ.le_opNorm y)
          (div_nonneg (norm_nonneg _) hν.le)
      _ ≤ (‖H‖ * ‖x‖) / ν * (‖δ‖ * ‖y‖) :=
        mul_le_mul_of_nonneg_right
          (div_le_div_of_nonneg_right (H.le_opNorm x) hν.le)
          (mul_nonneg (norm_nonneg δ) (norm_nonneg y))
      _ = (‖H‖ / ν * ‖δ‖) * ‖x‖ * ‖y‖ := by ring
  exact LinearMap.mkContinuous₂ f (‖H‖ / ν * ‖δ‖) hbound

/-- The exact physical second-source action supplied to the quartic envelope. -/
noncomputable def secondDefectSourceOfBandField (Q : TriadicCube 2)
    (a₀ b₀ c₀ d₀ : ℝ) (hab : a₀ < b₀) (hcd : c₀ < d₀)
    (hQ : openCubeSet Q ⊆ openRectangle a₀ b₀ c₀ d₀)
    (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (k : ResponseCoefficient (openCubeSet Q)) (P : BlockVec 2) (e : Vec 2)
    (f : C(closedRectangle a₀ b₀ c₀ d₀, ℝ)) :
    EnergyCarrier (responseFrameEnergyData
      (isOpenBoundedConvexDomain_openCubeSet Q).isOpen.measurableSet
      (by rw [volume_openCubeSet_toReal]; exact cubeVolume_pos Q)
      ν σ hν hσ k) :=
  secondDefectSource
    (isOpenBoundedConvexDomain_openCubeSet Q).isOpen.measurableSet
    (by rw [volume_openCubeSet_toReal]; exact cubeVolume_pos Q)
    ν σ hν hσ k P
    ((σ • freshResponseCoefficientCLM Q a₀ b₀ c₀ d₀ hab hcd hQ) f)
    ((freshFlatInputCLM Q a₀ b₀ c₀ d₀ hab hcd e) f)

/-- The second-source energy as a scalar function of the actual fresh
continuous field. -/
noncomputable def secondDefectEnvelopeOfBandField (Q : TriadicCube 2)
    (a₀ b₀ c₀ d₀ : ℝ) (hab : a₀ < b₀) (hcd : c₀ < d₀)
    (hQ : openCubeSet Q ⊆ openRectangle a₀ b₀ c₀ d₀)
    (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (k : ResponseCoefficient (openCubeSet Q)) (P : BlockVec 2) (e : Vec 2)
    (f : C(closedRectangle a₀ b₀ c₀ d₀, ℝ)) : ℝ :=
  ‖secondDefectSourceOfBandField Q a₀ b₀ c₀ d₀ hab hcd hQ
    ν σ hν hσ k P e f‖ ^ 2

/-- The bilinear diagonal is exactly the source `C_H δu₁`, with the same
fresh field in the response shear and in the local Dirichlet flat mode. -/
theorem second_defect_field_bilinear_diagonal (Q : TriadicCube 2)
    (a₀ b₀ c₀ d₀ : ℝ) (hab : a₀ < b₀) (hcd : c₀ < d₀)
    (hQ : openCubeSet Q ⊆ openRectangle a₀ b₀ c₀ d₀)
    (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (k : ResponseCoefficient (openCubeSet Q)) (P : BlockVec 2) (e : Vec 2)
    (f : C(closedRectangle a₀ b₀ c₀ d₀, ℝ)) :
    secondDefectFieldBilinear Q a₀ b₀ c₀ d₀ hab hcd hQ ν σ hν hσ k P e f f =
      secondDefectSourceOfBandField Q a₀ b₀ c₀ d₀ hab hcd hQ
        ν σ hν hσ k P e f := by
  simp only [secondDefectFieldBilinear, LinearMap.mkContinuous₂_apply,
    secondDefectSourceOfBandField,
    sub_apply, ContinuousLinearMap.comp_apply,
    old_first_response_clm_apply, flat_first_response_clm_apply,
    secondDefectSource, firstResponseDefect, oldInsertion]
  rfl

/-- The actual quartic defect observable for one fixed OLD coefficient. -/
noncomputable def secondDefectEnvelopeFunction (Q : TriadicCube 2)
    (a₀ b₀ c₀ d₀ : ℝ) (hab : a₀ < b₀) (hcd : c₀ < d₀)
    (hQ : openCubeSet Q ⊆ openRectangle a₀ b₀ c₀ d₀)
    (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (k : ResponseCoefficient (openCubeSet Q)) (P : BlockVec 2) (e : Vec 2) :
    C(closedRectangle a₀ b₀ c₀ d₀, ℝ) → ℝ :=
  secondDefectEnvelopeOfBandField Q a₀ b₀ c₀ d₀ hab hcd hQ
    ν σ hν hσ k P e

/-- The physical OLD/fresh defect envelope on a pair of scalar fields.
The OLD rectangle field supplies the actual response coefficient, while the
fresh rectangle field enters both the response shear and its local Dirichlet
flat mode. -/
noncomputable def physicalOldFreshDefectEnvelope (Q : TriadicCube 2)
    (a₀ b₀ c₀ d₀ : ℝ) (hab : a₀ < b₀) (hcd : c₀ < d₀)
    (hQ : openCubeSet Q ⊆ openRectangle a₀ b₀ c₀ d₀)
    (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ) (P : BlockVec 2) (e : Vec 2) :
    C(closedRectangle a₀ b₀ c₀ d₀, ℝ) ×
      C(closedRectangle a₀ b₀ c₀ d₀, ℝ) → ℝ := fun z =>
  secondDefectEnvelopeFunction Q a₀ b₀ c₀ d₀ hab hcd hQ
    ν σ hν hσ
    (freshResponseCoefficientCLM Q a₀ b₀ c₀ d₀ hab hcd hQ z.1) P e z.2

/-- On an actual cutoff sample, the OLD rectangle field induces exactly the
literal old cutoff skew coefficient on the response square. -/
theorem oldField_responseCoefficient_eq_cutoff
    (Q : TriadicCube 2) (a₀ b₀ c₀ d₀ : ℝ)
    (hab : a₀ < b₀) (hcd : c₀ < d₀)
    (hQ : openCubeSet Q ⊆ openRectangle a₀ b₀ c₀ d₀)
    (M : ABKModel 2) (ell m : ℤ)
    (hRect : closedRectangle a₀ b₀ c₀ d₀ ⊆ openCubeSet (originCube 2 ell))
    (ω : Cutoff.CutoffSample 2) :
    freshResponseCoefficientCLM Q a₀ b₀ c₀ d₀ hab hcd hQ
        (olderField (closedRectangle a₀ b₀ c₀ d₀) m ω) =
      oldCutoffSkewCoefficient m Q ω := by
  ext x
  have hxRect : (x : Vec 2) ∈ closedRectangle a₀ b₀ c₀ d₀ := by
    rw [← rectangle_closure a₀ b₀ c₀ d₀ hab hcd]
    exact closure_mono hQ x.2
  change olderField (closedRectangle a₀ b₀ c₀ d₀) m ω ⟨x, hxRect⟩ =
    Cutoff.cutoff m ω x 1 0
  rw [olderField_apply_eq_coefficientCutoff
    (closedRectangle a₀ b₀ c₀ d₀) M ell m hRect ω ⟨x, hxRect⟩]
  rw [Cutoff.coefficientCutoff_apply]
  simp only [Matrix.add_apply, Matrix.smul_apply,
    Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0),
    smul_eq_mul, mul_zero, zero_add]

/-- The physical defect source, represented on the fixed L² carrier below
its response-energy lift. -/
noncomputable def secondDefectSourceDown (Q : TriadicCube 2)
    (a₀ b₀ c₀ d₀ : ℝ) (hab : a₀ < b₀) (hcd : c₀ < d₀)
    (hQ : openCubeSet Q ⊆ openRectangle a₀ b₀ c₀ d₀)
    (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (k : ResponseCoefficient (openCubeSet Q)) (P : BlockVec 2) (e : Vec 2)
    (f : C(closedRectangle a₀ b₀ c₀ d₀, ℝ)) :
    HilbertBlockL2 (openCubeSet Q) := by
  let hU := measurableSet_openCubeSet Q
  let hvol : 0 < (volume (openCubeSet Q)).toReal := by
    rw [volume_openCubeSet_toReal]
    exact cubeVolume_pos Q
  let M := (responseFrameMuOperatorSystemData hU hvol ν σ hν hσ k).toMuHilbertRealization
  let K := M.correctionSpace.correctionSpace
  let H := σ • freshResponseCoefficientCLM Q a₀ b₀ c₀ d₀ hab hcd hQ f
  let w := freshFlatInputCLM Q a₀ b₀ c₀ d₀ hab hcd e f
  let oldFirst := Homogenization.correctionMap K M.energyBilin M.energyCoercive
    (responseShearL2Operator σ hσ H (M.minimizerMap P))
  let flatFirst := hilbertPureSecondL2 (openCubeSet Q) (-w)
  exact responseShearL2Operator σ hσ H (oldFirst - flatFirst)

private theorem old_first_response_down_eq_correction
    (Q : TriadicCube 2) (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (k : ResponseCoefficient (openCubeSet Q)) (P : BlockVec 2)
    (H : ResponseCoefficient (openCubeSet Q)) :
    (oldFirstResponse (measurableSet_openCubeSet Q)
      (by rw [volume_openCubeSet_toReal]; exact cubeVolume_pos Q)
      ν σ hν hσ k P H).down =
      (Homogenization.correctionMap
        ((responseFrameMuOperatorSystemData (measurableSet_openCubeSet Q)
          (by rw [volume_openCubeSet_toReal]; exact cubeVolume_pos Q)
          ν σ hν hσ k).toMuHilbertRealization.correctionSpace.correctionSpace)
        ((responseFrameMuOperatorSystemData (measurableSet_openCubeSet Q)
          (by rw [volume_openCubeSet_toReal]; exact cubeVolume_pos Q)
          ν σ hν hσ k).toMuHilbertRealization.energyBilin)
        ((responseFrameMuOperatorSystemData (measurableSet_openCubeSet Q)
          (by rw [volume_openCubeSet_toReal]; exact cubeVolume_pos Q)
          ν σ hν hσ k).toMuHilbertRealization.energyCoercive)
        (responseShearL2Operator σ hσ H
          ((responseFrameMuOperatorSystemData (measurableSet_openCubeSet Q)
            (by rw [volume_openCubeSet_toReal]; exact cubeVolume_pos Q)
            ν σ hν hσ k).toMuHilbertRealization.minimizerMap P)) :
        HilbertBlockL2 (openCubeSet Q)) := by
  let hU := measurableSet_openCubeSet Q
  let hvol : 0 < (volume (openCubeSet Q)).toReal := by
    rw [volume_openCubeSet_toReal]
    exact cubeVolume_pos Q
  let M := (responseFrameMuOperatorSystemData hU hvol ν σ hν hσ k).toMuHilbertRealization
  let D := responseFrameEnergyData hU hvol ν σ hν hσ k
  have hInsertion : (oldInsertion hU hvol ν σ hν hσ k H
      (responseFrameEnergyBaseMinimizer hU hvol ν σ hν hσ k P)).down =
      responseShearL2Operator σ hσ H (M.minimizerMap P) := by
    change (responseEnergyConjugateOperator D
      (responseShearL2Operator σ hσ H)
      (responseEnergyUp D (M.minimizerMap P))).down = _
    rw [responseEnergyConjugateOperator_apply]
    rfl
  change (oldResolvent M
      ((oldInsertion hU hvol ν σ hν hσ k H
        (responseFrameEnergyBaseMinimizer hU hvol ν σ hν hσ k P)).down) :
        HilbertBlockL2 (openCubeSet Q)) = _
  rw [old_resolvent_eq_correctionMap, hInsertion]

private theorem old_insertion_down
    (Q : TriadicCube 2) (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (k H : ResponseCoefficient (openCubeSet Q))
    (Z : EnergyCarrier (responseFrameEnergyData
      (measurableSet_openCubeSet Q)
      (by rw [volume_openCubeSet_toReal]; exact cubeVolume_pos Q)
      ν σ hν hσ k)) :
    (oldInsertion (measurableSet_openCubeSet Q)
      (by rw [volume_openCubeSet_toReal]; exact cubeVolume_pos Q)
      ν σ hν hσ k H Z).down =
      responseShearL2Operator σ hσ H Z.down := by
  let hU := measurableSet_openCubeSet Q
  let hvol : 0 < (volume (openCubeSet Q)).toReal := by
    rw [volume_openCubeSet_toReal]
    exact cubeVolume_pos Q
  let D := responseFrameEnergyData hU hvol ν σ hν hσ k
  change (responseEnergyConjugateOperator D
    (responseShearL2Operator σ hσ H) Z).down = _
  rw [responseEnergyConjugateOperator_apply]

private theorem second_defect_source_down
    (Q : TriadicCube 2) (a₀ b₀ c₀ d₀ : ℝ)
    (hab : a₀ < b₀) (hcd : c₀ < d₀)
    (hQ : openCubeSet Q ⊆ openRectangle a₀ b₀ c₀ d₀)
    (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (k : ResponseCoefficient (openCubeSet Q)) (P : BlockVec 2) (e : Vec 2)
    (f : C(closedRectangle a₀ b₀ c₀ d₀, ℝ)) :
    (secondDefectSourceOfBandField Q a₀ b₀ c₀ d₀ hab hcd hQ
      ν σ hν hσ k P e f).down =
      secondDefectSourceDown Q a₀ b₀ c₀ d₀ hab hcd hQ
        ν σ hν hσ k P e f := by
  let hU := measurableSet_openCubeSet Q
  let hvol : 0 < (volume (openCubeSet Q)).toReal := by
    rw [volume_openCubeSet_toReal]
    exact cubeVolume_pos Q
  let H := σ • freshResponseCoefficientCLM Q a₀ b₀ c₀ d₀ hab hcd hQ f
  let w := freshFlatInputCLM Q a₀ b₀ c₀ d₀ hab hcd e f
  let M := (responseFrameMuOperatorSystemData hU hvol ν σ hν hσ k).toMuHilbertRealization
  change (oldInsertion hU hvol ν σ hν hσ k H
      (firstResponseDefect hU hvol ν σ hν hσ k P H w)).down = _
  rw [old_insertion_down]
  change responseShearL2Operator σ hσ H
      ((oldFirstResponse hU hvol ν σ hν hσ k P H).down -
        (flatFirstResponse hU hvol ν σ hν hσ k w).down) = _
  rw [old_first_response_down_eq_correction]
  simp [secondDefectSourceDown, flatFirstResponse, H, w]

private theorem second_defect_envelope_eq_energy
    (Q : TriadicCube 2) (a₀ b₀ c₀ d₀ : ℝ)
    (hab : a₀ < b₀) (hcd : c₀ < d₀)
    (hQ : openCubeSet Q ⊆ openRectangle a₀ b₀ c₀ d₀)
    (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (k : ResponseCoefficient (openCubeSet Q)) (P : BlockVec 2) (e : Vec 2)
    (f : C(closedRectangle a₀ b₀ c₀ d₀, ℝ)) :
    secondDefectEnvelopeFunction Q a₀ b₀ c₀ d₀ hab hcd hQ
      ν σ hν hσ k P e f =
      ((responseFrameMuOperatorSystemData (measurableSet_openCubeSet Q)
        (by rw [volume_openCubeSet_toReal]; exact cubeVolume_pos Q)
        ν σ hν hσ k).toMuHilbertRealization.energyBilin)
        (secondDefectSourceDown Q a₀ b₀ c₀ d₀ hab hcd hQ
          ν σ hν hσ k P e f)
        (secondDefectSourceDown Q a₀ b₀ c₀ d₀ hab hcd hQ
          ν σ hν hσ k P e f) := by
  change ‖secondDefectSourceOfBandField Q a₀ b₀ c₀ d₀
    hab hcd hQ ν σ hν hσ k P e f‖ ^ 2 = _
  rw [energyCarrier_norm_sq (responseFrameEnergyData
    (measurableSet_openCubeSet Q)
    (by rw [volume_openCubeSet_toReal]; exact cubeVolume_pos Q)
    ν σ hν hσ k)]
  rw [second_defect_source_down]
  rfl

private theorem bilin_polarization' {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (B : V →L[ℝ] V →L[ℝ] ℝ) (hB : ∀ x y, B x y = B y x) (x y : V) :
    4 * B x y = B (x + y) (x + y) - B (x - y) (x - y) := by
  have hp : B (x + y) (x + y) = B x x + B x y + B y x + B y y := by
    rw [B.map_add₂]
    rw [(B x).map_add, (B y).map_add]
    ring
  have hm : B (x - y) (x - y) = B x x - B x y - B y x + B y y := by
    rw [B.map_sub₂]
    rw [(B x).map_sub, (B y).map_sub]
    ring
  rw [hp, hm, hB y x]
  ring

private noncomputable def pullbackBilin' {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (B : V →L[ℝ] V →L[ℝ] ℝ) (T : V →L[ℝ] V) :
    V →L[ℝ] V →L[ℝ] ℝ :=
  ((ContinuousLinearMap.precompR V B).flip T).comp T

private theorem continuous_pullbackBilin' {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (B : V →L[ℝ] V →L[ℝ] ℝ) :
    Continuous (fun T : V →L[ℝ] V => pullbackBilin' B T) := by
  fun_prop [pullbackBilin']

private theorem responseFrame_energyBilin_eq_pullback
    (Q : TriadicCube 2) (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (k : ResponseCoefficient (openCubeSet Q)) :
    (responseFrameMuOperatorSystemData (measurableSet_openCubeSet Q)
      (by rw [volume_openCubeSet_toReal]; exact cubeVolume_pos Q)
      ν σ hν hσ k).toMuHilbertRealization.energyBilin =
      pullbackBilin'
        ((responseFrameMuOperatorSystemData (measurableSet_openCubeSet Q)
          (by rw [volume_openCubeSet_toReal]; exact cubeVolume_pos Q)
          ν σ hν hσ (0 : ResponseCoefficient (openCubeSet Q))).toMuHilbertRealization.energyBilin)
        (1 + responseShearL2Operator σ hσ k) := by
  let hU := measurableSet_openCubeSet Q
  let hvol : 0 < (volume (openCubeSet Q)).toReal := by
    rw [volume_openCubeSet_toReal]
    exact cubeVolume_pos Q
  let Bk := (responseFrameMuOperatorSystemData hU hvol ν σ hν hσ k).toMuHilbertRealization.energyBilin
  let B0 := (responseFrameMuOperatorSystemData hU hvol ν σ hν hσ
    (0 : ResponseCoefficient (openCubeSet Q))).toMuHilbertRealization.energyBilin
  let T := (1 : HilbertBlockL2 (openCubeSet Q) →L[ℝ] HilbertBlockL2 (openCubeSet Q)) +
    responseShearL2Operator σ hσ k
  have hBk : ∀ x y, Bk x y = Bk y x := by
    exact (responseFrameMuOperatorSystemData hU hvol ν σ hν hσ k).toMuHilbertRealization.energySymm
  have hB0 : ∀ x y, B0 x y = B0 y x := by
    exact (responseFrameMuOperatorSystemData hU hvol ν σ hν hσ
      (0 : ResponseCoefficient (openCubeSet Q))).toMuHilbertRealization.energySymm
  have hdiag (x : HilbertBlockL2 (openCubeSet Q)) : Bk x x = B0 (T x) (T x) := by
    change (responseFrameMuOperatorSystemData hU hvol ν σ hν hσ k).toMuHilbertRealization.energyBilin x x =
      (responseFrameMuOperatorSystemData hU hvol ν σ hν hσ
        (0 : ResponseCoefficient (openCubeSet Q))).toMuHilbertRealization.energyBilin
        (T x) (T x)
    have hshear := responseFrameMu_energy_shear_identity hU hvol ν σ hν hσ
      (0 : ResponseCoefficient (openCubeSet Q)) k x
    rw [zero_add] at hshear
    have hT : T x = x + responseShearL2Operator σ hσ k x := by
      simp [T]
    simpa only [hT] using hshear.symm
  have hpair (x y : HilbertBlockL2 (openCubeSet Q)) :
      Bk x y = B0 (T x) (T y) := by
    have hleft := bilin_polarization' Bk hBk x y
    have hright := bilin_polarization' B0 hB0 (T x) (T y)
    have hadd : T (x + y) = T x + T y := T.map_add x y
    have hsub : T (x - y) = T x - T y := T.map_sub x y
    rw [hdiag (x + y), hdiag (x - y)] at hleft
    rw [hadd, hsub] at hleft
    calc
      Bk x y = (4 * Bk x y) / 4 := by ring
      _ = (4 * B0 (T x) (T y)) / 4 := by rw [hleft, ← hright]
      _ = B0 (T x) (T y) := by ring
  ext x y
  change Bk x y = B0 (T x) (T y)
  exact hpair x y

private theorem continuous_responseFrame_energyBilin
    (Q : TriadicCube 2) (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ) :
    Continuous fun k : ResponseCoefficient (openCubeSet Q) =>
      (responseFrameMuOperatorSystemData (measurableSet_openCubeSet Q)
        (by rw [volume_openCubeSet_toReal]; exact cubeVolume_pos Q)
        ν σ hν hσ k).toMuHilbertRealization.energyBilin := by
  let U := openCubeSet Q
  let hU := measurableSet_openCubeSet Q
  let hvol : 0 < (volume U).toReal := by
    rw [volume_openCubeSet_toReal]
    exact cubeVolume_pos Q
  let B0 := (responseFrameMuOperatorSystemData hU hvol ν σ hν hσ
    (0 : ResponseCoefficient U)).toMuHilbertRealization.energyBilin
  have hS : Continuous fun k : ResponseCoefficient U =>
      responseShearL2Operator σ hσ k :=
    (responseShearL2Family hU σ hσ).continuous
  have hT : Continuous fun k : ResponseCoefficient U =>
      (1 : HilbertBlockL2 U →L[ℝ] HilbertBlockL2 U) +
        responseShearL2Operator σ hσ k := continuous_const.add hS
  have hPull : Continuous fun T : HilbertBlockL2 U →L[ℝ] HilbertBlockL2 U =>
      pullbackBilin' B0 T := continuous_pullbackBilin' B0
  have hCont : Continuous fun k : ResponseCoefficient U =>
      pullbackBilin' B0
        ((1 : HilbertBlockL2 U →L[ℝ] HilbertBlockL2 U) +
          responseShearL2Operator σ hσ k) := hPull.comp hT
  have hEq : (fun k : ResponseCoefficient U =>
      (responseFrameMuOperatorSystemData hU hvol ν σ hν hσ k).toMuHilbertRealization.energyBilin) =
      fun k => pullbackBilin' B0
        ((1 : HilbertBlockL2 U →L[ℝ] HilbertBlockL2 U) +
          responseShearL2Operator σ hσ k) := by
    funext k
    exact responseFrame_energyBilin_eq_pullback Q ν σ hν hσ k
  rw [hEq]
  exact hCont

private theorem responseCorrectionSpace_eq_zero
    (Q : TriadicCube 2) (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (k : ResponseCoefficient (openCubeSet Q)) :
    (responseFrameMuOperatorSystemData (measurableSet_openCubeSet Q)
      (by rw [volume_openCubeSet_toReal]; exact cubeVolume_pos Q)
      ν σ hν hσ k).toMuHilbertRealization.correctionSpace.correctionSpace =
    (responseFrameMuOperatorSystemData (measurableSet_openCubeSet Q)
      (by rw [volume_openCubeSet_toReal]; exact cubeVolume_pos Q)
      ν σ hν hσ (0 : ResponseCoefficient (openCubeSet Q))).toMuHilbertRealization.correctionSpace.correctionSpace := by
  let hU := measurableSet_openCubeSet Q
  let hvol : 0 < (volume (openCubeSet Q)).toReal := by
    rw [volume_openCubeSet_toReal]
    exact cubeVolume_pos Q
  let M₁ := responseFrameMuOperatorSystemData hU hvol ν σ hν hσ k
  let M₀ := responseFrameMuOperatorSystemData hU hvol ν σ hν hσ
    (0 : ResponseCoefficient (openCubeSet Q))
  have hsys : M₁.toMuHilbertRealization.correctionSpace =
      M₀.toMuHilbertRealization.correctionSpace := by
    change (PotentialSolenoidalL2Data.ofSubmoduleClosures (openCubeSet Q)).toMuCorrectionSpaceData =
      (PotentialSolenoidalL2Data.ofSubmoduleClosures (openCubeSet Q)).toMuCorrectionSpaceData
    rfl
  change M₁.toMuHilbertRealization.correctionSpace.correctionSpace =
    M₀.toMuHilbertRealization.correctionSpace.correctionSpace
  rw [hsys]

private noncomputable def restrictBilinCLM' {V : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (K : ClosedSubmodule ℝ V) :
    (V →L[ℝ] V →L[ℝ] ℝ) →L[ℝ]
      (K.toSubmodule →L[ℝ] K.toSubmodule →L[ℝ] ℝ) := by
  let i : K.toSubmodule →L[ℝ] V := K.toSubmodule.subtypeL
  let hOuter : (V →L[ℝ] V →L[ℝ] ℝ) →L[ℝ]
      (K.toSubmodule →L[ℝ] V →L[ℝ] ℝ) :=
    (ContinuousLinearMap.compL ℝ K.toSubmodule V (V →L[ℝ] ℝ)).flip i
  let hInner : (V →L[ℝ] ℝ) →L[ℝ] (K.toSubmodule →L[ℝ] ℝ) :=
    (ContinuousLinearMap.compL ℝ K.toSubmodule V ℝ).flip i
  exact (ContinuousLinearMap.compL ℝ K.toSubmodule
    (V →L[ℝ] ℝ) (K.toSubmodule →L[ℝ] ℝ) hInner).comp hOuter

private theorem restrictBilinCLM_apply' {V : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (K : ClosedSubmodule ℝ V) (B : V →L[ℝ] V →L[ℝ] ℝ) :
    restrictBilinCLM' K B = Homogenization.restrictBilin K B := by
  ext x y
  rfl

private noncomputable def restrictedBilinOperatorCLM' {V : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    (K : ClosedSubmodule ℝ V) :
    (K.toSubmodule →L[ℝ] K.toSubmodule →L[ℝ] ℝ) →L[ℝ]
      (K.toSubmodule →L[ℝ] K.toSubmodule) :=
  ContinuousLinearMap.compL ℝ K.toSubmodule (K.toSubmodule →L[ℝ] ℝ)
    K.toSubmodule
    (((InnerProductSpace.toDual ℝ K.toSubmodule).symm).toContinuousLinearEquiv
      |>.toContinuousLinearMap)

private theorem restrictedBilinOperatorCLM_apply' {V : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    (K : ClosedSubmodule ℝ V) (B : V →L[ℝ] V →L[ℝ] ℝ) :
    restrictedBilinOperatorCLM' K (restrictBilinCLM' K B) =
      InnerProductSpace.continuousLinearMapOfBilin
        (Homogenization.restrictBilin K B) := by
  simp [restrictedBilinOperatorCLM', InnerProductSpace.continuousLinearMapOfBilin,
    restrictBilinCLM_apply']

private theorem subspaceRhs_eq_eval {V : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    (K : ClosedSubmodule ℝ V) (B : V →L[ℝ] V →L[ℝ] ℝ) (x : V) :
    Homogenization.subspaceRhs K B x =
      Homogenization.subspaceRieszMap K
        (-((B x).comp K.toSubmodule.subtypeL)) := by
  apply congrArg (Homogenization.subspaceRieszMap K)
  ext y
  simp [Homogenization.subspaceRhsBilin_apply]

private theorem continuous_subspaceRhs_joint {V : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    (K : ClosedSubmodule ℝ V) :
    Continuous fun p : (V →L[ℝ] V →L[ℝ] ℝ) × V =>
      Homogenization.subspaceRhs K p.1 p.2 := by
  have hEval : Continuous fun p : (V →L[ℝ] V →L[ℝ] ℝ) × V => p.1 p.2 := by
    fun_prop
  have hRhs : Continuous fun p : (V →L[ℝ] V →L[ℝ] ℝ) × V =>
      Homogenization.subspaceRieszMap K
        (-((p.1 p.2).comp K.toSubmodule.subtypeL)) := by
    fun_prop
  have hEq : (fun p : (V →L[ℝ] V →L[ℝ] ℝ) × V =>
      Homogenization.subspaceRhs K p.1 p.2) = fun p =>
      Homogenization.subspaceRieszMap K
        (-((p.1 p.2).comp K.toSubmodule.subtypeL)) := by
    funext p
    exact subspaceRhs_eq_eval K p.1 p.2
  rw [hEq]
  exact hRhs

private theorem continuous_clm_eval' {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] :
    Continuous fun p : (V →L[ℝ] V) × V => p.1 p.2 := by
  exact (isBoundedBilinearMap_apply (𝕜 := ℝ) (E := V) (F := V)).continuous

private theorem continuous_bilin_eval {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] :
    Continuous fun p : (V →L[ℝ] V →L[ℝ] ℝ) × (V × V) =>
      p.1 p.2.1 p.2.2 := by
  fun_prop

private theorem measurable_bilin_eval {Ω V : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [MeasurableSpace V] [BorelSpace V]
    [OpensMeasurableSpace ((V →L[ℝ] V →L[ℝ] ℝ) × (V × V))]
    {B : Ω → V →L[ℝ] V →L[ℝ] ℝ} {x y : Ω → V}
    (hB : Measurable B) (hx : Measurable x) (hy : Measurable y) :
    Measurable fun z => B z (x z) (y z) := by
  let pair : Ω → (V →L[ℝ] V →L[ℝ] ℝ) × (V × V) :=
    fun z => (B z, (x z, y z))
  have hp : Measurable pair := hB.prodMk (hx.prodMk hy)
  exact continuous_bilin_eval.measurable.comp hp

private theorem measurable_clm_apply {Ω V : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [MeasurableSpace V] [BorelSpace V]
    [OpensMeasurableSpace ((V →L[ℝ] V) × V)]
    {f : Ω → V →L[ℝ] V} {g : Ω → V}
    (hf : Measurable f) (hg : Measurable g) :
    Measurable fun z => f z (g z) := by
  exact continuous_clm_eval'.measurable.comp (hf.prodMk hg)

private theorem measurable_subspaceRhs_joint {Ω V : Type*}
    [MeasurableSpace Ω] [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] [MeasurableSpace V]
    (K : ClosedSubmodule ℝ V) [BorelSpace K.toSubmodule]
    [OpensMeasurableSpace ((V →L[ℝ] V →L[ℝ] ℝ) × V)]
    {B : Ω → V →L[ℝ] V →L[ℝ] ℝ} {x : Ω → V}
    (hB : Measurable B) (hx : Measurable x) :
    Measurable fun z => Homogenization.subspaceRhs K (B z) (x z) := by
  let F : (V →L[ℝ] V →L[ℝ] ℝ) × V → K.toSubmodule := fun p =>
    Homogenization.subspaceRhs K p.1 p.2
  let pair : Ω → (V →L[ℝ] V →L[ℝ] ℝ) × V := fun z => (B z, x z)
  have hF : Continuous F := continuous_subspaceRhs_joint (V := V) K
  have hFm : Measurable F := hF.measurable
  have hp : Measurable pair := hB.prodMk hx
  change Measurable (F ∘ pair)
  exact hFm.comp hp

private theorem measurable_correctionMap_apply {Ω V : Type*}
    [MeasurableSpace Ω] [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] [MeasurableSpace V]
    (K : ClosedSubmodule ℝ V) [BorelSpace K.toSubmodule]
    [OpensMeasurableSpace
      ((K.toSubmodule →L[ℝ] K.toSubmodule) × K.toSubmodule)]
    {B : Ω → V →L[ℝ] V →L[ℝ] ℝ} {hB : ∀ z, IsCoercive (B z)}
    {x : Ω → V}
    (hSharp : Measurable fun z =>
      InnerProductSpace.continuousLinearMapOfBilin
        (Homogenization.restrictBilin K (B z)))
    (hRhs : Measurable fun z => Homogenization.subspaceRhs K (B z) (x z)) :
    Measurable fun z => Homogenization.correctionMap K (B z) (hB z) (x z) := by
  exact Measurable.correctionMap_apply K hSharp hRhs

private theorem measurable_baseData {Ω V : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V]
    [MeasurableAdd₂ V]
    (K : ClosedSubmodule ℝ V) [BorelSpace K.toSubmodule]
    [SecondCountableTopology K.toSubmodule]
    [OpensMeasurableSpace ((K.toSubmodule →L[ℝ] K.toSubmodule) × K.toSubmodule)]
    [OpensMeasurableSpace ((V →L[ℝ] V →L[ℝ] ℝ) × V)]
    {B : Ω → V →L[ℝ] V →L[ℝ] ℝ} {hB : ∀ z, IsCoercive (B z)}
    (hBmeas : Measurable B) (x₀ : V) :
    Measurable (fun z =>
        InnerProductSpace.continuousLinearMapOfBilin
          (Homogenization.restrictBilin K (B z))) ∧
      Measurable (fun z =>
        Homogenization.affineMinimizerMap K (B z) (hB z) x₀) := by
  let sharpMap : (V →L[ℝ] V →L[ℝ] ℝ) →L[ℝ]
      (K.toSubmodule →L[ℝ] K.toSubmodule) :=
    (restrictedBilinOperatorCLM' K).comp (restrictBilinCLM' K)
  have hSharp : Measurable fun z =>
      InnerProductSpace.continuousLinearMapOfBilin
        (Homogenization.restrictBilin K (B z)) := by
    have hm : Measurable fun z => sharpMap (B z) :=
      sharpMap.continuous.measurable.comp hBmeas
    have heq : (fun z => sharpMap (B z)) = fun z =>
        InnerProductSpace.continuousLinearMapOfBilin
          (Homogenization.restrictBilin K (B z)) := by
      funext z
      exact restrictedBilinOperatorCLM_apply' K (B z)
    rw [← heq]
    exact hm
  have hRhs : Measurable fun z => Homogenization.subspaceRhs K (B z) x₀ :=
    measurable_subspaceRhs_joint K hBmeas measurable_const
  exact ⟨hSharp,
    Measurable.affineMinimizerMap_apply (K := K) (hB := hB)
      (x := fun _ => x₀) measurable_const hSharp hRhs⟩

/-- The physical OLD/fresh envelope is jointly measurable. Its OLD
dependence passes through the actual coercive frame form, affine minimizer,
and correction resolvent; its fresh dependence uses the actual local
Dirichlet projection. -/
theorem measurable_physical_old_fresh_defect_envelope
    (Q : TriadicCube 2) (a₀ b₀ c₀ d₀ : ℝ)
    (hab : a₀ < b₀) (hcd : c₀ < d₀)
    (hQ : openCubeSet Q ⊆ openRectangle a₀ b₀ c₀ d₀)
    (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ) (P : BlockVec 2) (e : Vec 2) :
    Measurable (physicalOldFreshDefectEnvelope Q a₀ b₀ c₀ d₀
      hab hcd hQ ν σ hν hσ P e) := by
  let U := openCubeSet Q
  let R := closedRectangle a₀ b₀ c₀ d₀
  let Ω := C(R, ℝ) × C(R, ℝ)
  let V := HilbertBlockL2 U
  let hU := measurableSet_openCubeSet Q
  let hvol : 0 < (volume U).toReal := by
    rw [volume_openCubeSet_toReal]
    exact cubeVolume_pos Q
  let k : Ω → ResponseCoefficient U := fun z =>
    freshResponseCoefficientCLM Q a₀ b₀ c₀ d₀ hab hcd hQ z.1
  let H : Ω → ResponseCoefficient U := fun z =>
    σ • freshResponseCoefficientCLM Q a₀ b₀ c₀ d₀ hab hcd hQ z.2
  let w : Ω → HilbertVectorL2 U := fun z =>
    freshFlatInputCLM Q a₀ b₀ c₀ d₀ hab hcd e z.2
  let B : Ω → V →L[ℝ] V →L[ℝ] ℝ := fun z =>
    (responseFrameMuOperatorSystemData hU hvol ν σ hν hσ (k z)).toMuHilbertRealization.energyBilin
  let K := (responseFrameMuOperatorSystemData hU hvol ν σ hν hσ
    (0 : ResponseCoefficient U)).toMuHilbertRealization.correctionSpace.correctionSpace
  let hCoercive : ∀ z : Ω, IsCoercive (B z) := fun z =>
    (responseFrameMuOperatorSystemData hU hvol ν σ hν hσ
      (k z)).toMuHilbertRealization.energyCoercive
  let base : Ω → V := fun z =>
    Homogenization.affineMinimizerMap K (B z) (hCoercive z)
      ((responseFrameMuOperatorSystemData hU hvol ν σ hν hσ
        (0 : ResponseCoefficient U)).toMuHilbertRealization.constantField P)
  let op : Ω → V →L[ℝ] V := fun z => responseShearL2Operator σ hσ (H z)
  let force : Ω → V := fun z => op z (base z)
  let x₀ := (responseFrameMuOperatorSystemData hU hvol ν σ hν hσ
    (0 : ResponseCoefficient U)).toMuHilbertRealization.constantField P
  let flatCLM : HilbertVectorL2 U →L[ℝ] V :=
    (hilbertPureSecondL2 U).comp (-ContinuousLinearMap.id ℝ (HilbertVectorL2 U))
  let flat : Ω → V := fun z => flatCLM (w z)
  let μphys := physicalOldFreshDefectEnvelope Q a₀ b₀ c₀ d₀
    hab hcd hQ ν σ hν hσ P e
  have hfst : Continuous fun z : Ω => z.1 := continuous_fst
  have hsnd : Continuous fun z : Ω => z.2 := continuous_snd
  have hk : Measurable k :=
    ((freshResponseCoefficientCLM Q a₀ b₀ c₀ d₀ hab hcd hQ).continuous.comp
      hfst).measurable
  have hB : Measurable B :=
    (continuous_responseFrame_energyBilin Q ν σ hν hσ).measurable.comp hk
  have hH : Measurable H := by
    change Measurable (fun z : Ω => σ •
      freshResponseCoefficientCLM Q a₀ b₀ c₀ d₀ hab hcd hQ z.2)
    have hσc : Continuous fun _ : Ω => σ := continuous_const
    exact (hσc.smul
      ((freshResponseCoefficientCLM Q a₀ b₀ c₀ d₀ hab hcd hQ).continuous.comp
        hsnd)).measurable
  have hw : Measurable w :=
    ((freshFlatInputCLM Q a₀ b₀ c₀ d₀ hab hcd e).continuous.comp
      hsnd).measurable
  have hOp : Measurable op :=
    (responseShearL2Family hU σ hσ).continuous.measurable.comp hH
  letI : IsSeparable (volumeMeasureOn U) := inferInstance
  letI : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
  letI : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by simp⟩
  letI : SecondCountableTopology V := inferInstance
  letI : BorelSpace K.toSubmodule := inferInstance
  letI : SecondCountableTopology K.toSubmodule := inferInstance
  letI : OpensMeasurableSpace
      ((K.toSubmodule →L[ℝ] K.toSubmodule) × K.toSubmodule) := inferInstance
  letI : OpensMeasurableSpace ((V →L[ℝ] V) × V) := inferInstance
  letI : OpensMeasurableSpace
      ((V →L[ℝ] V →L[ℝ] ℝ) × V) := inferInstance
  have hBaseData :=
    measurable_baseData (K := K) (hB := hCoercive) hB x₀
  have hSharp := hBaseData.1
  have hBase : Measurable base := by
    change Measurable (fun z : Ω =>
      Homogenization.affineMinimizerMap K (B z) (hCoercive z) x₀)
    exact hBaseData.2
  have hForce : Measurable force := by
    change Measurable (fun z : Ω => op z (base z))
    exact measurable_clm_apply hOp hBase
  have hRhs : Measurable fun z : Ω => Homogenization.subspaceRhs K (B z) (force z) :=
    measurable_subspaceRhs_joint K hB hForce
  have hCorr : Measurable (fun z : Ω =>
      Homogenization.correctionMap K (B z) (hCoercive z) (force z)) :=
    measurable_correctionMap_apply K hSharp hRhs
  have hCorrV : Measurable fun z : Ω =>
      (Homogenization.correctionMap K (B z) (hCoercive z) (force z) : V) :=
    measurable_subtype_coe.comp hCorr
  have hflat : Measurable flat := flatCLM.continuous.measurable.comp hw
  have hInput : Measurable fun z : Ω =>
      Homogenization.correctionMap K (B z) (hCoercive z) (force z) - flat z :=
    hCorrV.sub hflat
  have hSrc : Measurable (fun z : Ω => op z
      (Homogenization.correctionMap K (B z) (hCoercive z) (force z) - flat z)) :=
    measurable_clm_apply hOp hInput
  have hSrcEq (z : Ω) :
      secondDefectSourceDown Q a₀ b₀ c₀ d₀ hab hcd hQ
        ν σ hν hσ (k z) P e z.2 =
      op z (Homogenization.correctionMap K (B z) (hCoercive z)
        (op z (base z)) - flat z) := by
    change responseShearL2Operator σ hσ (H z)
        (Homogenization.correctionMap
          ((responseFrameMuOperatorSystemData hU hvol ν σ hν hσ
            (k z)).toMuHilbertRealization.correctionSpace.correctionSpace)
          (B z) (hCoercive z) (op z (base z)) - flat z) =
      op z (Homogenization.correctionMap K (B z) (hCoercive z)
        (op z (base z)) - flat z)
    rw [responseCorrectionSpace_eq_zero Q ν σ hν hσ (k z)]
  have hSourceDown : Measurable fun z : Ω =>
      secondDefectSourceDown Q a₀ b₀ c₀ d₀ hab hcd hQ
        ν σ hν hσ (k z) P e z.2 := by
    have hEq : (fun z : Ω => secondDefectSourceDown Q a₀ b₀ c₀ d₀
        hab hcd hQ ν σ hν hσ (k z) P e z.2) = fun z =>
        op z (Homogenization.correctionMap K (B z) (hCoercive z)
          (op z (base z)) - flat z) := by
      funext z
      exact hSrcEq z
    rw [hEq]
    exact hSrc
  have hEnergy : μphys = fun z : Ω =>
      B z
        (secondDefectSourceDown Q a₀ b₀ c₀ d₀ hab hcd hQ
          ν σ hν hσ (k z) P e z.2)
        (secondDefectSourceDown Q a₀ b₀ c₀ d₀ hab hcd hQ
          ν σ hν hσ (k z) P e z.2) := by
    funext z
    change secondDefectEnvelopeFunction Q a₀ b₀ c₀ d₀
      hab hcd hQ ν σ hν hσ (k z) P e z.2 = _
    rw [second_defect_envelope_eq_energy]
  change Measurable μphys
  rw [hEnergy]
  exact measurable_bilin_eval hB hSourceDown hSourceDown

/-- Compose a source bilinear map with a realization factor. -/
noncomputable def composeDefectBilinear {X V W : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] [SecondCountableTopology V] [MeasurableSpace V]
    [BorelSpace V] [OpensMeasurableSpace V]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    (B : X →L[ℝ] X →L[ℝ] W) (T : V →L[ℝ] X) :
    V →L[ℝ] V →L[ℝ] W := by
  let f : V →ₗ[ℝ] V →ₗ[ℝ] W :=
    { toFun := fun x =>
        { toFun := fun y => B (T x) (T y)
          map_add' := by
            intro y z
            rw [map_add T]
            exact map_add (B (T x)) (T y) (T z)
          map_smul' := by
            intro r y
            change B (T x) (T (r • y)) = _
            rw [map_smul T]
            exact map_smul (B (T x)) r (T y) }
      map_add' := by
        intro x y
        ext z
        change B (T (x + y)) (T z) = _
        rw [map_add T, map_add B]
        rfl
      map_smul' := by
        intro r x
        ext z
        change B (T (r • x)) (T z) = _
        rw [map_smul T, map_smul B]
        rfl }
  have hbound (x y : V) :
      ‖f x y‖ ≤ (‖B‖ * ‖T‖ ^ 2) * ‖x‖ * ‖y‖ := by
    change ‖B (T x) (T y)‖ ≤ _
    calc
      ‖B (T x) (T y)‖ ≤ ‖B (T x)‖ * ‖T y‖ := (B (T x)).le_opNorm _
      _ ≤ ‖B (T x)‖ * (‖T‖ * ‖y‖) :=
        mul_le_mul_of_nonneg_left (T.le_opNorm y) (norm_nonneg (B (T x)))
      _ ≤ (‖B‖ * ‖T x‖) * (‖T‖ * ‖y‖) :=
        mul_le_mul_of_nonneg_right (B.le_opNorm (T x))
          (mul_nonneg (norm_nonneg T) (norm_nonneg y))
      _ ≤ (‖B‖ * (‖T‖ * ‖x‖)) * (‖T‖ * ‖y‖) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (T.le_opNorm x) (norm_nonneg B))
          (mul_nonneg (norm_nonneg T) (norm_nonneg y))
      _ = (‖B‖ * ‖T‖ ^ 2) * ‖x‖ * ‖y‖ := by ring
  exact LinearMap.mkContinuous₂ f (‖B‖ * ‖T‖ ^ 2) hbound

/-- The source's fresh-band envelope at a fixed OLD coefficient. It uses the
actual defect source in both fresh slots, with the response coefficient
held fixed while the physical finite band is sampled. -/
theorem defect_envelope_cutoff_conjugate_bound_of_multishell_ga_cm
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    {b : ℕ} [NeZero b] (shellIndex : Fin b → ℤ)
    (hshell : Function.Injective shellIndex)
    (Q : TriadicCube 2) (a₀ b₀ c₀ d₀ : ℝ)
    (hab : a₀ < b₀) (hcd : c₀ < d₀)
    (hQ : openCubeSet Q ⊆ openRectangle a₀ b₀ c₀ d₀)
    (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (k : ResponseCoefficient (openCubeSet Q)) (P : BlockVec 2) (e : Vec 2)
    (p : ℝ) (hp : 2 ≤ p) :
    ∃ (T : BandHilbert b →L[ℝ]
        C(closedRectangle a₀ b₀ c₀ d₀, ℝ))
      (v : ℕ → BandHilbert b)
      (hA : Summable (fun j => ‖v j‖ ^ 2)),
      let B := composeDefectBilinear
        (secondDefectFieldBilinear Q a₀ b₀ c₀ d₀ hab hcd hQ
          ν σ hν hσ k P e) T
      let c := gaussianBilinearTrace B v
      (Cutoff.cutoffSampleLaw M).toMeasure.map (modelBand
          (closedRectangle a₀ b₀ c₀ d₀) shellIndex) =
        Gaussian.standardGaussianInfinitePi.map (gaussianSeriesLimitE hA T) ∧
      eLpNorm
        (fun ω : Cutoff.CutoffSample 2 =>
          secondDefectEnvelopeFunction Q a₀ b₀ c₀ d₀ hab hcd hQ
            ν σ hν hσ k P e
            (modelBand (closedRectangle a₀ b₀ c₀ d₀) shellIndex ω))
        (ENNReal.ofReal (p / (p - 1))) (Cutoff.cutoffSampleLaw M).toMeasure ≤
        ENNReal.ofReal ((1 + Real.sqrt 15) ^ (2 / p) *
          ∫ ω, gaussianHilbertEnvelope c B v hA ω
            ∂Gaussian.standardGaussianInfinitePi) := by
  obtain ⟨T, v, hA, hlaw⟩ := exists_modelBand_realization
    (closedRectangle a₀ b₀ c₀ d₀) M h hM shellIndex hshell
  let Bf := secondDefectFieldBilinear Q a₀ b₀ c₀ d₀ hab hcd hQ
    ν σ hν hσ k P e
  let B := composeDefectBilinear Bf T
  let c := gaussianBilinearTrace B v
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let X : Cutoff.CutoffSample 2 → C(closedRectangle a₀ b₀ c₀ d₀, ℝ) :=
    modelBand (closedRectangle a₀ b₀ c₀ d₀) shellIndex
  let G : (ℕ → ℝ) → C(closedRectangle a₀ b₀ c₀ d₀, ℝ) :=
    gaussianSeriesLimitE hA T
  let F : C(closedRectangle a₀ b₀ c₀ d₀, ℝ) → ℝ :=
    secondDefectEnvelopeFunction Q a₀ b₀ c₀ d₀ hab hcd hQ
      ν σ hν hσ k P e
  have hdiag : F = fun f => ‖Bf f f‖ ^ 2 := by
    funext f
    change ‖secondDefectSourceOfBandField Q a₀ b₀ c₀ d₀
      hab hcd hQ ν σ hν hσ k P e f‖ ^ 2 = ‖Bf f f‖ ^ 2
    rw [← second_defect_field_bilinear_diagonal Q a₀ b₀ c₀ d₀
      hab hcd hQ ν σ hν hσ k P e f]
  have hX : Measurable X := measurable_modelBand _ shellIndex
  have hG : StronglyMeasurable G := stronglyMeasurable_gaussianSeriesLimitE hA T
  have hFcont : Continuous F := by
    rw [hdiag]
    fun_prop
  have hF : Measurable F := hFcont.measurable
  have hFleft : AEStronglyMeasurable F (μ.map X) := hF.aestronglyMeasurable
  have hFright : AEStronglyMeasurable F
      (Gaussian.standardGaussianInfinitePi.map G) := hF.aestronglyMeasurable
  have hleft := eLpNorm_map_measure
    (p := ENNReal.ofReal (p / (p - 1))) (μ := μ) (f := X)
    hFleft hX.aemeasurable
  have hright := eLpNorm_map_measure
    (p := ENNReal.ofReal (p / (p - 1)))
    (μ := Gaussian.standardGaussianInfinitePi) (f := G)
    hFright hG.aemeasurable
  have hfactor (ω : ℕ → ℝ) :
      F (G ω) = gaussianHilbertEnvelope c B v hA ω := by
    rw [hdiag]
    simp [gaussianHilbertEnvelope, gaussianBilinearChaos, B, c,
      composeDefectBilinear, gaussianSeriesLimitE,
      gaussianBilinearTrace, G, LinearMap.mkContinuous₂_apply]
  have hgaussian := gaussian_hilbert_envelope_conjugate_bound c B v hA p hp
  refine ⟨T, v, hA, ?_⟩
  refine ⟨hlaw, ?_⟩
  calc
    _ = eLpNorm F (ENNReal.ofReal (p / (p - 1))) (μ.map X) := by
      change eLpNorm (F ∘ X) (ENNReal.ofReal (p / (p - 1))) μ = _
      exact hleft.symm
    _ = eLpNorm F (ENNReal.ofReal (p / (p - 1)))
        (Gaussian.standardGaussianInfinitePi.map G) := by rw [hlaw]
    _ = eLpNorm (F ∘ G) (ENNReal.ofReal (p / (p - 1)))
        Gaussian.standardGaussianInfinitePi := hright
    _ = eLpNorm (gaussianHilbertEnvelope c B v hA)
        (ENNReal.ofReal (p / (p - 1))) Gaussian.standardGaussianInfinitePi := by
      congr 1
      funext ω
      exact hfactor ω
    _ ≤ ENNReal.ofReal ((1 + Real.sqrt 15) ^ (2 / p) *
        ∫ ω, gaussianHilbertEnvelope c B v hA ω
          ∂Gaussian.standardGaussianInfinitePi) := hgaussian
    _ = _ := rfl

/-- On a cutoff sample, the physical OLD/fresh envelope uses the literal
OLD cutoff coefficient. -/
theorem physical_old_fresh_cutoff_envelope_eq
    (Q : TriadicCube 2) (a₀ b₀ c₀ d₀ : ℝ)
    (hab : a₀ < b₀) (hcd : c₀ < d₀)
    (hQ : openCubeSet Q ⊆ openRectangle a₀ b₀ c₀ d₀)
    (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ) (P : BlockVec 2) (e : Vec 2)
    (M : ABKModel 2) (ell m : ℤ)
    (hRect : closedRectangle a₀ b₀ c₀ d₀ ⊆ openCubeSet (originCube 2 ell))
    {b : ℕ} [NeZero b] (shellIndex : Fin b → ℤ)
    (ω : Cutoff.CutoffSample 2) :
    physicalOldFreshDefectEnvelope Q a₀ b₀ c₀ d₀ hab hcd hQ
        ν σ hν hσ P e
        (olderField (closedRectangle a₀ b₀ c₀ d₀) m ω,
          modelBand (closedRectangle a₀ b₀ c₀ d₀) shellIndex ω) =
      secondDefectEnvelopeFunction Q a₀ b₀ c₀ d₀ hab hcd hQ
        ν σ hν hσ (oldCutoffSkewCoefficient m Q ω) P e
        (modelBand (closedRectangle a₀ b₀ c₀ d₀) shellIndex ω) := by
  change secondDefectEnvelopeFunction Q a₀ b₀ c₀ d₀ hab hcd hQ
      ν σ hν hσ
      (freshResponseCoefficientCLM Q a₀ b₀ c₀ d₀ hab hcd hQ
        (olderField (closedRectangle a₀ b₀ c₀ d₀) m ω)) P e
      (modelBand (closedRectangle a₀ b₀ c₀ d₀) shellIndex ω) = _
  rw [oldField_responseCoefficient_eq_cutoff Q a₀ b₀ c₀ d₀
    hab hcd hQ M ell m hRect ω]

/-- The actual OLD/fresh quartic envelope has the product law of its OLD
marginal and a direct-sum Gaussian realization of the future shells.
This plugs the physical measurable envelope into the multi-shell OLD/fresh
law identity. -/
theorem physical_old_fresh_cutoff_eLpNorm_eq_ga_cm
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (ell m : ℤ) (Q : TriadicCube 2) (a₀ b₀ c₀ d₀ : ℝ)
    (hab : a₀ < b₀) (hcd : c₀ < d₀)
    (hQ : openCubeSet Q ⊆ openRectangle a₀ b₀ c₀ d₀)
    (hRect : closedRectangle a₀ b₀ c₀ d₀ ⊆ openCubeSet (originCube 2 ell))
    {b : ℕ} [NeZero b] (shellIndex : Fin b → ℤ)
    (hshell : Function.Injective shellIndex) (hfuture : ∀ i, m < shellIndex i)
    (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ) (P : BlockVec 2) (e : Vec 2)
    (p : ℝ≥0∞) :
    ∃ (T : BandHilbert b →L[ℝ]
        C(closedRectangle a₀ b₀ c₀ d₀, ℝ))
      (v : ℕ → BandHilbert b)
      (hA : Summable (fun j => ‖v j‖ ^ 2)),
      (Cutoff.cutoffSampleLaw M).toMeasure.map
          (modelBand (closedRectangle a₀ b₀ c₀ d₀) shellIndex) =
        Gaussian.standardGaussianInfinitePi.map (gaussianSeriesLimitE hA T) ∧
      eLpNorm
          (fun ω : Cutoff.CutoffSample 2 =>
            physicalOldFreshDefectEnvelope Q a₀ b₀ c₀ d₀ hab hcd hQ
              ν σ hν hσ P e
              (olderField (closedRectangle a₀ b₀ c₀ d₀) m ω,
                modelBand (closedRectangle a₀ b₀ c₀ d₀) shellIndex ω))
          p (Cutoff.cutoffSampleLaw M).toMeasure =
        eLpNorm
          (fun z : C(closedRectangle a₀ b₀ c₀ d₀, ℝ) × (ℕ → ℝ) =>
            physicalOldFreshDefectEnvelope Q a₀ b₀ c₀ d₀ hab hcd hQ
              ν σ hν hσ P e
              (z.1, gaussianSeriesLimitE hA T z.2))
          p (((Cutoff.cutoffSampleLaw M).toMeasure.map
              (olderField (closedRectangle a₀ b₀ c₀ d₀) m)).prod
            Gaussian.standardGaussianInfinitePi) := by
  let R := closedRectangle a₀ b₀ c₀ d₀
  let F : C(R, ℝ) × C(R, ℝ) → ℝ :=
    physicalOldFreshDefectEnvelope Q a₀ b₀ c₀ d₀ hab hcd hQ
      ν σ hν hσ P e
  have hF : Measurable F := by
    exact measurable_physical_old_fresh_defect_envelope
      Q a₀ b₀ c₀ d₀ hab hcd hQ ν σ hν hσ P e
  obtain ⟨T, v, hA, hEq⟩ :=
    joint_old_multishell_eLpNorm_eq_ga_cm M h hM ell m
      (K := R) hRect shellIndex hshell hfuture F hF p
  refine ⟨T, v, hA, ?_, ?_⟩
  · simpa [R] using hEq.1
  · simpa [R, F] using hEq.2

/-- For every fixed physical OLD field, the actual quartic envelope on
the fresh finite band obeys the conjugate-norm estimate against its
actual cutoff-law fiber mean. In the proof, the Gaussian Hilbert envelope is
pointwise the source envelope evaluated at `gaussianSeriesLimitE`: for the
proof's `F`, `c`, and `B`,
`F (gaussianSeriesLimitE hA T ω) = gaussianHilbertEnvelope c B v hA ω`.
The realization law transfers that mean to the cutoff fiber, so the
conclusion does not expose a choice of Gaussian realization. The OLD field
sets the response coefficient; the fresh field enters the actual shear and
local Dirichlet mode. -/
theorem physical_old_fresh_cutoff_fiber_conjugate_bound
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    {b : ℕ} [NeZero b] (shellIndex : Fin b → ℤ)
    (hshell : Function.Injective shellIndex)
    (Q : TriadicCube 2) (a₀ b₀ c₀ d₀ : ℝ)
    (hab : a₀ < b₀) (hcd : c₀ < d₀)
    (hQ : openCubeSet Q ⊆ openRectangle a₀ b₀ c₀ d₀)
    (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ) (P : BlockVec 2) (e : Vec 2)
    (old : C(closedRectangle a₀ b₀ c₀ d₀, ℝ))
    (p : ℝ) (hp : 2 ≤ p) :
    eLpNorm
        (fun ω : Cutoff.CutoffSample 2 =>
          physicalOldFreshDefectEnvelope Q a₀ b₀ c₀ d₀ hab hcd hQ
            ν σ hν hσ P e
            (old, modelBand (closedRectangle a₀ b₀ c₀ d₀) shellIndex ω))
        (ENNReal.ofReal (p / (p - 1))) (Cutoff.cutoffSampleLaw M).toMeasure ≤
      ENNReal.ofReal ((1 + Real.sqrt 15) ^ (2 / p) *
        ∫ ω, physicalOldFreshDefectEnvelope Q a₀ b₀ c₀ d₀ hab hcd hQ
          ν σ hν hσ P e
          (old, modelBand (closedRectangle a₀ b₀ c₀ d₀) shellIndex ω)
          ∂(Cutoff.cutoffSampleLaw M).toMeasure) := by
  let k := freshResponseCoefficientCLM Q a₀ b₀ c₀ d₀ hab hcd hQ old
  obtain ⟨T, v, hA, hresult⟩ :=
    defect_envelope_cutoff_conjugate_bound_of_multishell_ga_cm
      M h hM shellIndex hshell Q a₀ b₀ c₀ d₀ hab hcd hQ
      ν σ hν hσ k P e p hp
  rcases hresult with ⟨hlaw, hbound⟩
  let Bf := secondDefectFieldBilinear Q a₀ b₀ c₀ d₀ hab hcd hQ
    ν σ hν hσ k P e
  let B := composeDefectBilinear Bf T
  let c := gaussianBilinearTrace B v
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let X : Cutoff.CutoffSample 2 → C(closedRectangle a₀ b₀ c₀ d₀, ℝ) :=
    modelBand (closedRectangle a₀ b₀ c₀ d₀) shellIndex
  let G : (ℕ → ℝ) → C(closedRectangle a₀ b₀ c₀ d₀, ℝ) :=
    gaussianSeriesLimitE hA T
  let F : C(closedRectangle a₀ b₀ c₀ d₀, ℝ) → ℝ :=
    secondDefectEnvelopeFunction Q a₀ b₀ c₀ d₀ hab hcd hQ
      ν σ hν hσ k P e
  have hdiag : F = fun f => ‖Bf f f‖ ^ 2 := by
    funext f
    change ‖secondDefectSourceOfBandField Q a₀ b₀ c₀ d₀
      hab hcd hQ ν σ hν hσ k P e f‖ ^ 2 = ‖Bf f f‖ ^ 2
    rw [← second_defect_field_bilinear_diagonal Q a₀ b₀ c₀ d₀
      hab hcd hQ ν σ hν hσ k P e f]
  have hFcont : Continuous F := by
    rw [hdiag]
    fun_prop
  have hF : Measurable F := hFcont.measurable
  have hX : Measurable X := measurable_modelBand _ shellIndex
  have hG : StronglyMeasurable G := stronglyMeasurable_gaussianSeriesLimitE hA T
  have hfactor (ω : ℕ → ℝ) :
      F (G ω) = gaussianHilbertEnvelope c B v hA ω := by
    rw [hdiag]
    simp [gaussianHilbertEnvelope, gaussianBilinearChaos, B, c,
      composeDefectBilinear, gaussianSeriesLimitE,
      gaussianBilinearTrace, G, LinearMap.mkContinuous₂_apply]
  have hsource (ω : Cutoff.CutoffSample 2) :
      physicalOldFreshDefectEnvelope Q a₀ b₀ c₀ d₀ hab hcd hQ
        ν σ hν hσ P e (old, X ω) = F (X ω) := by
    rfl
  have hmean :
      ∫ ω, physicalOldFreshDefectEnvelope Q a₀ b₀ c₀ d₀ hab hcd hQ
        ν σ hν hσ P e (old, X ω) ∂μ =
      ∫ ω, gaussianHilbertEnvelope c B v hA ω
        ∂Gaussian.standardGaussianInfinitePi := by
    calc
      _ = ∫ ω, F (X ω) ∂μ := by
        apply integral_congr_ae
        filter_upwards [] with ω
        exact hsource ω
      _ = ∫ f, F f ∂(μ.map X) := by
        symm
        exact MeasureTheory.integral_map_of_stronglyMeasurable hX hF.stronglyMeasurable
      _ = ∫ f, F f ∂(Gaussian.standardGaussianInfinitePi.map G) := by
        rw [hlaw]
      _ = ∫ ω, F (G ω) ∂Gaussian.standardGaussianInfinitePi :=
        MeasureTheory.integral_map_of_stronglyMeasurable hG.measurable
          hF.stronglyMeasurable
      _ = ∫ ω, gaussianHilbertEnvelope c B v hA ω
          ∂Gaussian.standardGaussianInfinitePi := by
        apply integral_congr_ae
        filter_upwards [] with ω
        exact hfactor ω
  rw [← hmean] at hbound
  simpa [physicalOldFreshDefectEnvelope, k, X, μ] using hbound

end ASDExplicitGamma.Scalar
