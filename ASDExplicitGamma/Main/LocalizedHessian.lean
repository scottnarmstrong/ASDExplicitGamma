module

public import ASDExplicitGamma.Main.HessianTrial
public import ASDExplicitGamma.Main.InterpolantStability
public import ASDExplicitGamma.Variational.LocalizedShearBundle
public import ASDExplicitGamma.Variational.LemmaVLiftSource
public import Homogenization.Sobolev.PotentialSolenoidalL2

/-! The fixed-frame trial inequality with the source localized row split. -/

@[expose] public section
namespace ASDExplicitGamma.Main

open Homogenization MeasureTheory ASDExplicitGamma.Response ASDExplicitGamma.Triadic
  ASDExplicitGamma.Variational
open scoped ENNReal

local instance mainLocalizedHessianFiniteMeasure (Q : TriadicCube 2) :
    IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
  (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume

/-- The physical coefficient shear annihilates the pure-flux injection. -/
theorem main_response_shear_pure_flux_zero {U : Set (Vec 2)}
    [IsFiniteMeasure (volumeMeasureOn U)]
    (σ : ℝ) (hσ : 0 < σ) (H : ResponseCoefficient U)
    (Y : HilbertVectorL2 U) :
    responseShearL2Operator σ hσ H (hilbertPureSecondL2 U Y) = 0 := by
  apply (continuousLinearEquivBlockL2 (U := U)).symm.injective
  change hilbertBlockL2ToBlockL2
      (responseShearL2Operator σ hσ H (hilbertPureSecondL2 U Y)) = 0
  apply MeasureTheory.Lp.ext
  filter_upwards [responseShearL2Operator_toBlockL2_ae σ hσ H
      (hilbertPureSecondL2 U Y),
    coeFn_hilbertBlockL2ToBlockL2 (F := hilbertPureSecondL2 U Y),
    (ContinuousLinearMap.coeFn_compLpL (p := 2) (μ := volumeMeasureOn U)
      (L := hilbertPureSecond.toContinuousLinearMap) (f := Y)),
    MeasureTheory.Lp.coeFn_zero (E := BlockVec 2) 2 (volumeMeasureOn U)] with
      x hshear htransport hpure hzero
  rw [hshear, htransport, hilbertPureSecondL2, hpure, hzero]
  have hfirst : (hilbertPureSecond.toContinuousLinearMap (Y x)).toBlockVec.1 =
      (0 : Vec 2) := by
    change HilbertVec.toVec
      (PiLp.single (β := fun _ : Fin 2 => HilbertVec 2) 2 1 (Y x) 0) = 0
    funext i
    simp [HilbertVec.toVec]
  change responseShearCorrection σ (responseCoefficientExtension H x)
    (hilbertPureSecond.toContinuousLinearMap (Y x)).toBlockVec = 0
  rw [responseShearCorrection, hfirst]
  simp [matVecMul_zero]

/-- Every actual weak solenoidal zero-normal-trace flux is an admissible
pure-flux variation for the fixed response energy. -/
theorem main_pure_flux_variation_mem (Q : TriadicCube 2)
    (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (k : ResponseCoefficient (openCubeSet Q))
    (g : Vec 2 → Vec 2) (hg : MemVectorL2 (openCubeSet Q) g)
    (hsol : IsSolenoidalZeroNormalTraceOn (openCubeSet Q) g) :
    let D := responseFrameEnergyData (measurableSet_openCubeSet Q)
      (by rw [volume_openCubeSet_toReal]; exact cubeVolume_pos Q) ν σ hν hσ k
    responseEnergyUp D (hilbertPureSecondL2 (openCubeSet Q)
      (toHilbertVectorL2OfVecField hg)) ∈
      (responseFrameEnergyVariationSpace (measurableSet_openCubeSet Q)
        (by rw [volume_openCubeSet_toReal]; exact cubeVolume_pos Q)
        ν σ hν hσ k).toSubmodule := by
  let hzero : MemVectorL2 (openCubeSet Q) (0 : Vec 2 → Vec 2) := MeasureTheory.MemLp.zero
  let M := responseFrameMuOperatorSystemData (measurableSet_openCubeSet Q)
    (by rw [volume_openCubeSet_toReal]; exact cubeVolume_pos Q) ν σ hν hσ k
  let D := responseFrameEnergyData (measurableSet_openCubeSet Q)
    (by rw [volume_openCubeSet_toReal]; exact cubeVolume_pos Q) ν σ hν hσ k
  have hblock : hilbertBlockL2ToBlockL2 (U := openCubeSet Q)
      (hilbertPureSecondL2 (openCubeSet Q) (toHilbertVectorL2OfVecField hg)) =
      toBlockL2OfComponents hzero hg := by
    apply MeasureTheory.Lp.ext
    filter_upwards [coeFn_hilbertBlockL2ToBlockL2
        (F := hilbertPureSecondL2 (openCubeSet Q) (toHilbertVectorL2OfVecField hg)),
      (ContinuousLinearMap.coeFn_compLpL (p := 2) (μ := volumeMeasureOn (openCubeSet Q))
        (L := hilbertPureSecond.toContinuousLinearMap)
        (f := toHilbertVectorL2OfVecField hg)),
      coeFn_toHilbertVectorL2OfVecField hg,
      coeFn_toBlockL2OfComponents hzero hg] with x htransport hpure hvec hblockFn
    rw [htransport, hblockFn]
    have hpure' : hilbertPureSecondL2 (openCubeSet Q)
        (toHilbertVectorL2OfVecField hg) x =
        hilbertPureSecond.toContinuousLinearMap (hilbertifyVecField g x) := by
      simpa [hilbertPureSecondL2, hvec] using hpure
    rw [hpure']
    simp [hilbertPureSecond, blockField, HilbertBlockVec.toBlockVec,
      hilbertifyVecField]
  have hcorr := M.correctionSpace.mem_correctionSpace hzero hg
    isPotentialZeroTraceOn_zero hsol
  have heq : hilbertPureSecondL2 (openCubeSet Q)
      (toHilbertVectorL2OfVecField hg) = toHilbertBlockL2OfComponents hzero hg := by
    apply (continuousLinearEquivBlockL2 (U := openCubeSet Q)).symm.injective
    calc
      hilbertBlockL2ToBlockL2 (U := openCubeSet Q)
          (hilbertPureSecondL2 (openCubeSet Q) (toHilbertVectorL2OfVecField hg)) =
          toBlockL2OfComponents hzero hg := hblock
      _ = hilbertBlockL2ToBlockL2 (U := openCubeSet Q)
          (toHilbertBlockL2OfComponents hzero hg) := by
        symm
        exact Homogenization.PotentialSolenoidalL2Data.hilbertBlockL2ToBlockL2_toHilbertBlockL2OfComponents
          (U := openCubeSet Q) hzero hg
  change responseEnergyUp D (hilbertPureSecondL2 (openCubeSet Q)
      (toHilbertVectorL2OfVecField hg)) ∈
    responseEnergyCorrectionSpace M.toMuHilbertRealization D
  rw [responseEnergyCorrectionSpace_mem_iff]
  change hilbertPureSecondL2 (openCubeSet Q)
      (toHilbertVectorL2OfVecField hg) ∈ M.correctionSpace.correctionSpace
  rw [heq]
  exact hcorr

/-- The trial inequality with an actual solenoidal pure-flux correction.
The nilpotent shear and this correction remain separate in the trial vector;
the cross term vanishes because the shear kills every pure-flux field. -/
theorem main_response_hessian_pure_flux_trial_bound (Q : TriadicCube 2)
    (hU : MeasurableSet (openCubeSet Q))
    (hvol : 0 < (volume (openCubeSet Q)).toReal)
    (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (P : BlockVec 2) (k H : ResponseCoefficient (openCubeSet Q))
    (g : Vec 2 → Vec 2) (hg : MemVectorL2 (openCubeSet Q) g)
    (hsol : IsSolenoidalZeroNormalTraceOn (openCubeSet Q) g) :
    let D := responseFrameEnergyData hU hvol ν σ hν hσ k
    let C : ResponseCoefficient (openCubeSet Q) →L[ℝ]
        (EnergyCarrier D →L[ℝ] EnergyCarrier D) :=
      responseFrameEnergyShearFamily hU hvol ν σ hν hσ k
    let S : EnergyCarrier D := responseFrameEnergyBaseMinimizer hU hvol ν σ hν hσ k P
    (1 / 2 : ℝ) * fderiv ℝ (fun z => fderiv ℝ
      (responseFrameEnergyObservable hU hvol ν σ hν hσ P) z H) k H ≤
      ‖C H S + responseEnergyUp D
        (hilbertPureSecondL2 (openCubeSet Q) (toHilbertVectorL2OfVecField hg))‖ ^ 2 := by
  dsimp only
  let D := responseFrameEnergyData hU hvol ν σ hν hσ k
  let C : ResponseCoefficient (openCubeSet Q) →L[ℝ]
      (EnergyCarrier D →L[ℝ] EnergyCarrier D) :=
    responseFrameEnergyShearFamily hU hvol ν σ hν hσ k
  let S := responseFrameEnergyBaseMinimizer hU hvol ν σ hν hσ k P
  let Y : (responseFrameEnergyVariationSpace hU hvol ν σ hν hσ k).toSubmodule :=
    ⟨responseEnergyUp D
    (hilbertPureSecondL2 (openCubeSet Q) (toHilbertVectorL2OfVecField hg)),
      main_pure_flux_variation_mem Q ν σ hν hσ k g hg hsol⟩
  have htrial := main_response_hessian_trial_bound hU hvol ν σ hν hσ P k H
  dsimp only at htrial
  have hCY : C H (Y : EnergyCarrier D) = 0 := by
    change responseEnergyConjugateOperator D (responseShearL2Operator σ hσ H)
      (Y : EnergyCarrier D) = 0
    rw [responseEnergyConjugateOperator_apply]
    change responseEnergyUp D (responseShearL2Operator σ hσ H
      (hilbertPureSecondL2 (openCubeSet Q) (toHilbertVectorL2OfVecField hg))) = 0
    rw [main_response_shear_pure_flux_zero]
    rfl
  have h := htrial Y
  change (1 / 2 : ℝ) * fderiv ℝ (fun z => fderiv ℝ
      (responseFrameEnergyObservable hU hvol ν σ hν hσ P) z H) k H ≤
      ‖C H S + (Y : EnergyCarrier D)‖ ^ 2 +
        2 * inner ℝ S (C H (Y : EnergyCarrier D)) at h
  rw [hCY] at h
  simpa [Y, C] using h

/-- The actual localized row on an affine-potential gradient is the global
skew row plus the weak column-divergence lift of the interpolant residual.
The residual has the exact zero-trace and all-test pairing properties from
the source lift theorem. -/
theorem main_localized_row_decomposition_and_lift (Q : TriadicCube 2)
    (I : H1Function (openCubeSet Q) →ₗ[ℝ] H1Function (openCubeSet Q))
    (η v w : H1Function (openCubeSet Q))
    (hv : v ∈ affinePotentialSubmodule Q)
    (hres : MemH10 (openCubeSet Q) (v-I v).toFun)
    (hη : MemLp η.toFun (⊤ : ENNReal) (volume.restrict (openCubeSet Q)))
    (hDη : ∀ i, MemLp (fun x => η.grad x i) (⊤ : ENNReal)
      (volume.restrict (openCubeSet Q)))
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hI : ∀ u ∈ affinePotentialSubmodule Q,
      ‖(I u).gradToHilbertVectorL2‖ ≤ A*‖u.gradToHilbertVectorL2‖)
    (hR : ∀ u ∈ affinePotentialSubmodule Q,
      ‖(u-I u).toScalarL2‖ ≤ B*‖u.gradToHilbertVectorL2‖) :
    MemVectorL2 (openCubeSet Q)
      (localizedColumnProductDivergence η (v-I v)) ∧
    IsSolenoidalZeroNormalTraceOn (openCubeSet Q)
      (localizedColumnProductDivergence η (v-I v)) ∧
    (localizedRowOperator Q I η hη hDη hA hB hI hR
        (affineGradientRangeMap Q ⟨v, hv⟩) =ᵐ[volume.restrict (openCubeSet Q)]
      fun x => HilbertVec.ofVec
        (η.toFun x • matVecMul responsePlanarJ (v.grad x) +
          localizedColumnProductDivergence η (v-I v) x)) ∧
    volumeAverage (openCubeSet Q) (fun x => vecDot
      (η.toFun x • matVecMul responsePlanarJ (v.grad x)) (w.grad x)) =
    volumeAverage (openCubeSet Q) (fun x => vecDot
      (lemmaVPlanarRowField I η v x) (w.grad x)) := by
  have hlift := lemmaV_interpolant_lift_source
    (isOpenBoundedConvexDomain_openCubeSet Q) I v η w hres hη hDη
  refine ⟨hlift.1, hlift.2.1, ?_, hlift.2.2.2⟩
  calc
    localizedRowOperator Q I η hη hDη hA hB hI hR
        (affineGradientRangeMap Q ⟨v, hv⟩) =ᵐ[volume.restrict (openCubeSet Q)]
        fun x => HilbertVec.ofVec (lemmaVPlanarRowField I η v x) :=
      localizedRowOperator_apply_ae Q I η hη hDη hA hB hI hR ⟨v, hv⟩
    _ =ᵐ[volume.restrict (openCubeSet Q)] fun x => HilbertVec.ofVec
        (η.toFun x • matVecMul responsePlanarJ (v.grad x) +
          localizedColumnProductDivergence η (v-I v) x) := by
      filter_upwards with x
      exact congrArg HilbertVec.ofVec
        (congrFun (localizedColumnProductDivergence_row_identity I η v) x).symm

/-- The same localized row split with the actual source DIAG interpolant.
Its H¹-gradient and residual constants are the proved mesh-independent and
source-mesh bounds, so no stability premise is supplied by the caller. -/
theorem main_diag_localized_row_decomposition_and_lift (Q : TriadicCube 2) (j : ℕ)
    (p : Vec 2) (r : H10Function (openCubeSet Q))
    (η w : H1Function (openCubeSet Q))
    (hη : MemLp η.toFun (⊤ : ENNReal) (volume.restrict (openCubeSet Q)))
    (hDη : ∀ i, MemLp (fun x => η.grad x i) (⊤ : ENNReal)
      (volume.restrict (openCubeSet Q))) :
    let I := diagInterpolant Q j
    let v := lemmaVAffinePotential (isOpenBoundedConvexDomain_openCubeSet Q) p r
    let A : ℝ := 1
    let B : ℝ := diagMeshRadius Q j * (planarC0+1/2)
    let hA : 0 ≤ A := by norm_num [A]
    let hB : 0 ≤ B := by
      dsimp [B]
      exact mul_nonneg (diagMeshRadius_pos Q j).le
        (add_nonneg diagPlanarC0_pos.le (by norm_num))
    let hI : ∀ u ∈ affinePotentialSubmodule Q,
      ‖(I u).gradToHilbertVectorL2‖ ≤ A*‖u.gradToHilbertVectorL2‖ :=
        by simpa [A] using (main_diag_interpolant_stability Q j).1
    let hR : ∀ u ∈ affinePotentialSubmodule Q,
      ‖(u-I u).toScalarL2‖ ≤ B*‖u.gradToHilbertVectorL2‖ :=
        by simpa [B] using (main_diag_interpolant_stability Q j).2
    MemVectorL2 (openCubeSet Q) (localizedColumnProductDivergence η (v-I v)) ∧
    IsSolenoidalZeroNormalTraceOn (openCubeSet Q)
      (localizedColumnProductDivergence η (v-I v)) ∧
    (localizedRowOperator Q I η hη hDη hA hB hI hR
        (affineGradientRangeMap Q ⟨v, mem_affinePotentialSubmodule Q p r⟩) =ᵐ[
          volume.restrict (openCubeSet Q)]
      fun x => HilbertVec.ofVec
        (η.toFun x • matVecMul responsePlanarJ (v.grad x) +
          localizedColumnProductDivergence η (v-I v) x)) ∧
    volumeAverage (openCubeSet Q) (fun x => vecDot
      (η.toFun x • matVecMul responsePlanarJ (v.grad x)) (w.grad x)) =
    volumeAverage (openCubeSet Q) (fun x => vecDot
      (lemmaVPlanarRowField I η v x) (w.grad x)) := by
  exact main_localized_row_decomposition_and_lift Q (diagInterpolant Q j) η
    (lemmaVAffinePotential (isOpenBoundedConvexDomain_openCubeSet Q) p r) w
    (mem_affinePotentialSubmodule Q p r)
    (diagInterpolant_affine_residual_memH10 Q j p r) hη hDη
    (by norm_num) (by
      exact mul_nonneg (diagMeshRadius_pos Q j).le
        (add_nonneg diagPlanarC0_pos.le (by norm_num)))
    (by simpa using (main_diag_interpolant_stability Q j).1)
    (by simpa using (main_diag_interpolant_stability Q j).2)

/-- The actual DIAG localized correction is an admissible pure-flux Hessian
trial, with its L² and solenoidal zero-normal-trace certificates derived from
the interpolant adapter. -/
theorem main_diag_response_hessian_correction_trial_bound (Q : TriadicCube 2) (j : ℕ)
    (hU : MeasurableSet (openCubeSet Q))
    (hvol : 0 < (volume (openCubeSet Q)).toReal)
    (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (P : BlockVec 2) (k H : ResponseCoefficient (openCubeSet Q))
    (p : Vec 2) (r : H10Function (openCubeSet Q))
    (η : H1Function (openCubeSet Q))
    (hη : MemLp η.toFun (⊤ : ENNReal) (volume.restrict (openCubeSet Q)))
    (hDη : ∀ i, MemLp (fun x => η.grad x i) (⊤ : ENNReal)
      (volume.restrict (openCubeSet Q))) :
    let v := lemmaVAffinePotential (isOpenBoundedConvexDomain_openCubeSet Q) p r
    let g := localizedColumnProductDivergence η (v - diagInterpolant Q j v)
    ∃ hg : MemVectorL2 (openCubeSet Q) g,
      IsSolenoidalZeroNormalTraceOn (openCubeSet Q) g ∧
        let D := responseFrameEnergyData hU hvol ν σ hν hσ k
        let C : ResponseCoefficient (openCubeSet Q) →L[ℝ]
            (EnergyCarrier D →L[ℝ] EnergyCarrier D) :=
          responseFrameEnergyShearFamily hU hvol ν σ hν hσ k
        let S : EnergyCarrier D := responseFrameEnergyBaseMinimizer hU hvol ν σ hν hσ k P
        (1 / 2 : ℝ) * fderiv ℝ (fun z => fderiv ℝ
          (responseFrameEnergyObservable hU hvol ν σ hν hσ P) z H) k H ≤
          ‖C H S + responseEnergyUp D
            (hilbertPureSecondL2 (openCubeSet Q) (toHilbertVectorL2OfVecField hg))‖ ^ 2 := by
  let v := lemmaVAffinePotential (isOpenBoundedConvexDomain_openCubeSet Q) p r
  let g := localizedColumnProductDivergence η (v - diagInterpolant Q j v)
  have hsplit := main_diag_localized_row_decomposition_and_lift Q j p r η v hη hDη
  have hg : MemVectorL2 (openCubeSet Q) g := hsplit.1
  have hsol : IsSolenoidalZeroNormalTraceOn (openCubeSet Q) g := hsplit.2.1
  refine ⟨hg, hsol, ?_⟩
  simpa [g] using main_response_hessian_pure_flux_trial_bound Q hU hvol ν σ hν hσ P k H g hg hsol

end ASDExplicitGamma.Main
