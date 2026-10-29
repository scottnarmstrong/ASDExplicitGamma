module

public import ASDExplicitGamma.Main.ETermMixedCarrier
public import ASDExplicitGamma.Native.OldSignedAffineCorrector
public import ASDExplicitGamma.Scalar.CoefficientFlux
public import ASDExplicitGamma.Native.OldSignedAffineResidualSplit
public import ASDExplicitGamma.Native.OldSignedPureSecondInverseReciprocal
public import ASDExplicitGamma.Native.OldSignedResidualReciprocalEnergy
public import ASDExplicitGamma.Scalar.SmoothFeedbackResponse

/-! The affine/oscillatory split identifies its oscillatory receiver with
the OLD reciprocal response to the centered flat input. -/

@[expose] public section

namespace ASDExplicitGamma.Main

open Homogenization MeasureTheory ASDExplicitGamma.Native
  ASDExplicitGamma.Gaussian ASDExplicitGamma.Response ASDExplicitGamma.Scalar
  ASDExplicitGamma.Triadic

noncomputable section

/-- The top oscillatory receiver is the reciprocal defect of the centered
top flat input, almost everywhere on the source cell. -/
theorem main_e_top_oscillatory_receiver_eq_centered
    (Q U : TriadicCube 2) (depth : ℕ)
    (hU : U ∈ descendantsAtDepth Q depth)
    (nu sigma : ℝ) (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q))
    (b : ℝ) (L : {l : ℝ // 0 < l})
    (n : whiteBasisIndex) (i : Fin 2) :
    let hsub := openCubeSet_subset_of_mem_descendantsAtDepth hU
    let kU := oldSignedCellCoefficient Q U hsub k
    let a := responseFramePlanarCoefficientField nu sigma kU
    let F := oldSignedFlatInput Q b L true n i
    let hFparent := old_signed_flat_input_memL2 Q b L true n i
    let hF := hFparent.mono_measure (Measure.restrict_mono_set volume hsub)
    let A := oldSignedCellResidual Q U hsub nu sigma hnu hsigma k F
      hFparent
    let m := oldSignedBlockMean U F
    let G := fun x => F x - m
    let hG := hF.sub (memLp_const m)
    let ZG := scalarResidualField U nu sigma hnu hsigma kU
      (toHilbertBlockL2OfBlockField hG)
    mainECellTopOscillatoryReceiver U a A F
        (mainECellTopAffineOfFlatInput U a
          (responseFramePlanarCoefficientField_isElliptic
            (measurableSet_openCubeSet U) nu sigma hnu hsigma kU) F) =ᵐ[
      volumeMeasureOn (openCubeSet U)]
      (fun x => (scalarCoefficientFlux a ZG x).2 - (G x).2) := by
  classical
  intro hsub kU a F hFparent hF A m G hG ZG
  let HM := (scalarFrameRealization U nu sigma hnu hsigma kU).constantField m
  let ZM := scalarResidualField U nu sigma hnu hsigma kU HM
  let Z := scalarResidualField U nu sigma hnu hsigma kU
    (toHilbertBlockL2OfBlockField hF)
  let hEll := responseFramePlanarCoefficientField_isElliptic
    (measurableSet_openCubeSet U) nu sigma hnu hsigma kU
  have hmfirst : m.1 = 0 := by
    funext j
    simp [m, F, oldSignedFlatInput, oldSignedFlatPlusBlock,
      oldSignedBlockMean, cubeAverage_const]
  have hsplit := old_signed_residual_mean_split_ae U nu sigma hnu hsigma kU F hF
  have hsplit' : Z =ᵐ[volumeMeasureOn (openCubeSet U)]
      (fun x => ZM x + ZG x) := by
    simpa [Z, ZM, ZG, HM, G, hF, hG] using hsplit
  have hflux : (fun x => scalarCoefficientFlux a Z x) =ᵐ[
      volumeMeasureOn (openCubeSet U)]
      (fun x => scalarCoefficientFlux a ZM x + scalarCoefficientFlux a ZG x) := by
    filter_upwards [hsplit'] with x hx
    change blockMatVecMul (blockCoeffField a x) (Z x) =
      blockMatVecMul (blockCoeffField a x) (ZM x) +
        blockMatVecMul (blockCoeffField a x) (ZG x)
    rw [hx, blockMatVecMul_add]
  have hCeq : oldSignedCanonicalAffineField U a hEll (0, -m.2) = -ZM := by
    have hconst : (scalarFrameRealization U nu sigma hnu hsigma kU).constantField
        (0, -m.2) = -HM := by
      have hpair : (0, -m.2) = -m := by
        ext j <;> fin_cases j <;> simp [hmfirst]
      rw [hpair]
      simp [HM]
    have hres := old_signed_affine_residual_field U nu sigma hnu hsigma kU
      (0, -m.2)
    have hneg := smooth_feedback_scalar_residual_field_smul U nu sigma
      hnu hsigma kU (-1 : ℝ) HM
    have hneg' : scalarResidualField U nu sigma hnu hsigma kU (-HM) = -ZM := by
      rw [show (-HM : HilbertBlockL2 (openCubeSet U)) = (-1 : ℝ) • HM by simp,
        hneg]
      simp [ZM]
    calc
      oldSignedCanonicalAffineField U a hEll (0, -m.2) =
          scalarResidualField U nu sigma hnu hsigma kU
            ((scalarFrameRealization U nu sigma hnu hsigma kU).constantField
              (0, -m.2)) := hres.symm
      _ = scalarResidualField U nu sigma hnu hsigma kU (-HM) := by rw [hconst]
      _ = -ZM := hneg'
  have hC0 : oldSignedCanonicalAffineField U a hEll (0, -m.2) =ᵐ[
      volumeMeasureOn (openCubeSet U)] fun x => (-ZM) x :=
    Lp.ext_iff.mp hCeq
  have hC : oldSignedCanonicalAffineField U a hEll (0, -m.2) =ᵐ[
      volumeMeasureOn (openCubeSet U)] (fun x => -ZM x) :=
    hC0.trans (Lp.coeFn_neg ZM)
  have hCflux : scalarCoefficientFlux a
      (oldSignedCanonicalAffineField U a hEll (0, -m.2)) =ᵐ[
        volumeMeasureOn (openCubeSet U)] (fun x => -scalarCoefficientFlux a ZM x) := by
    filter_upwards [hC] with x hx
    change blockMatVecMul (blockCoeffField a x)
      (oldSignedCanonicalAffineField U a hEll (0, -m.2) x) =
      -blockMatVecMul (blockCoeffField a x) (ZM x)
    rw [hx]
    rw [show -(ZM x) = (-1 : ℝ) • ZM x by simp]
    rw [blockMatVecMul_smul]
    simp
  have heaff : mainECellTopAffineOfFlatInput U a hEll F =ᵐ[
      volumeMeasureOn (openCubeSet U)]
      (fun x => (scalarCoefficientFlux a ZM x).2 - m.2) := by
    filter_upwards [hCflux] with x hx
    change -((scalarCoefficientFlux a
        (oldSignedCanonicalAffineField U a hEll (0, -m.2)) x).2 - (-m.2)) = _
    rw [hx]
    simp
    ring
  have hAeq : A = Z := by
    simp [A, Z, oldSignedCellResidual, kU]
  have hfluxA : (fun x => scalarCoefficientFlux a A x) =ᵐ[
      volumeMeasureOn (openCubeSet U)]
      (fun x => scalarCoefficientFlux a ZM x + scalarCoefficientFlux a ZG x) := by
    simpa [hAeq] using hflux
  filter_upwards [hfluxA, heaff] with x hfluxx heaffx
  change (scalarCoefficientFlux a A x).2 - (F x).2 -
      mainECellTopAffineOfFlatInput U a hEll F x = _
  rw [hfluxx, heaffx]
  have hmPoint : F x = m + G x := by
    dsimp [G]
    abel
  rw [hmPoint]
  simp only [Prod.snd_add]
  abel

/-- The bottom oscillatory receiver is minus the reciprocal flux of the
centered bottom flat input, almost everywhere on the source cell. -/
theorem main_e_bottom_oscillatory_receiver_eq_centered
    (Q U : TriadicCube 2) (depth : ℕ)
    (hU : U ∈ descendantsAtDepth Q depth)
    (nu sigma : ℝ) (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q))
    (b : ℝ) (L : {l : ℝ // 0 < l})
    (n : whiteBasisIndex) (i : Fin 2) :
    let hsub := openCubeSet_subset_of_mem_descendantsAtDepth hU
    let kU := oldSignedCellCoefficient Q U hsub k
    let a := responseFramePlanarCoefficientField nu sigma kU
    let F := oldSignedFlatInput Q b L false n i
    let hFparent := old_signed_flat_input_memL2 Q b L false n i
    let hF := hFparent.mono_measure (Measure.restrict_mono_set volume hsub)
    let A := oldSignedCellResidual Q U hsub nu sigma hnu hsigma k F
      hFparent
    let m := oldSignedBlockMean U F
    let hG := hF.sub (memLp_const m)
    let ZG := scalarResidualField U nu sigma hnu hsigma kU
      (toHilbertBlockL2OfBlockField hG)
    mainECellBottomOscillatoryReceiver U a A F
        (mainECellBottomAffineOfFlatInput U a
          (responseFramePlanarCoefficientField_isElliptic
            (measurableSet_openCubeSet U) nu sigma hnu hsigma kU) F) =ᵐ[
      volumeMeasureOn (openCubeSet U)]
      (fun x => -(scalarCoefficientFlux a ZG x).2) := by
  classical
  intro hsub kU a F hFparent hF A m hG ZG
  let G := fun x => F x - m
  let HM := (scalarFrameRealization U nu sigma hnu hsigma kU).constantField m
  let ZM := scalarResidualField U nu sigma hnu hsigma kU HM
  let Z := scalarResidualField U nu sigma hnu hsigma kU
    (toHilbertBlockL2OfBlockField hF)
  let hEll := responseFramePlanarCoefficientField_isElliptic
    (measurableSet_openCubeSet U) nu sigma hnu hsigma kU
  have hmsecond : m.2 = 0 := by
    funext j
    simp [m, F, oldSignedFlatInput, oldSignedFlatMinusBlock,
      oldSignedBlockMean, cubeAverage_const]
  have hsplit := old_signed_residual_mean_split_ae U nu sigma hnu hsigma kU F hF
  have hsplit' : Z =ᵐ[volumeMeasureOn (openCubeSet U)]
      (fun x => ZM x + ZG x) := by
    simpa [Z, ZM, ZG, HM, G, hF, hG] using hsplit
  have hflux : (fun x => scalarCoefficientFlux a Z x) =ᵐ[
      volumeMeasureOn (openCubeSet U)]
      (fun x => scalarCoefficientFlux a ZM x + scalarCoefficientFlux a ZG x) := by
    filter_upwards [hsplit'] with x hx
    change blockMatVecMul (blockCoeffField a x) (Z x) =
      blockMatVecMul (blockCoeffField a x) (ZM x) +
        blockMatVecMul (blockCoeffField a x) (ZG x)
    rw [hx, blockMatVecMul_add]
  have hmeanPair : (m.1, 0) = m := by
    ext j <;> fin_cases j <;> simp [hmsecond]
  have hCeq : oldSignedCanonicalAffineField U a hEll (m.1, 0) = ZM := by
    have hres := old_signed_affine_residual_field U nu sigma hnu hsigma kU
      (m.1, 0)
    calc
      oldSignedCanonicalAffineField U a hEll (m.1, 0) =
          scalarResidualField U nu sigma hnu hsigma kU
            ((scalarFrameRealization U nu sigma hnu hsigma kU).constantField
              (m.1, 0)) := hres.symm
      _ = ZM := by rw [hmeanPair]
  have hC : oldSignedCanonicalAffineField U a hEll (m.1, 0) =ᵐ[
      volumeMeasureOn (openCubeSet U)] (fun x => ZM x) := Lp.ext_iff.mp hCeq
  have hCflux : scalarCoefficientFlux a
      (oldSignedCanonicalAffineField U a hEll (m.1, 0)) =ᵐ[
        volumeMeasureOn (openCubeSet U)] (fun x => scalarCoefficientFlux a ZM x) := by
    filter_upwards [hC] with x hx
    change blockMatVecMul (blockCoeffField a x)
      (oldSignedCanonicalAffineField U a hEll (m.1, 0) x) =
      blockMatVecMul (blockCoeffField a x) (ZM x)
    rw [hx]
  have heaff : mainECellBottomAffineOfFlatInput U a hEll F =ᵐ[
      volumeMeasureOn (openCubeSet U)]
      (fun x => -(scalarCoefficientFlux a ZM x).2) := by
    filter_upwards [hCflux] with x hx
    simp only [mainECellBottomAffineOfFlatInput,
      mainECellBottomAffineReceiver]
    change -(scalarCoefficientFlux a
        (oldSignedCanonicalAffineField U a hEll ((oldSignedBlockMean U F).1, 0)) x).2 = _
    rw [show (oldSignedBlockMean U F).1 = m.1 by rfl]
    rw [hx]
  have hAeq : A = Z := by
    simp [A, Z, oldSignedCellResidual, kU]
  have hfluxA : (fun x => scalarCoefficientFlux a A x) =ᵐ[
      volumeMeasureOn (openCubeSet U)]
      (fun x => scalarCoefficientFlux a ZM x + scalarCoefficientFlux a ZG x) := by
    simpa [hAeq] using hflux
  filter_upwards [hfluxA, heaff] with x hfluxx heaffx
  change -((scalarCoefficientFlux a A x).2 - (F x).2) -
      mainECellBottomAffineOfFlatInput U a hEll F x = _
  rw [hfluxx, heaffx]
  have hmPoint : F x = m + G x := by
    dsimp [G]
    abel
  rw [hmPoint]
  simp only [Prod.snd_add]
  have hGsecond : (G x).2 = 0 := by
    change (F x).2 - m.2 = 0
    rw [hmsecond]
    simp [F, oldSignedFlatInput, oldSignedFlatMinusBlock]
  simp only [hmsecond, hGsecond]
  abel

/-- Weak Haar size is invariant under a pointwise sign change. -/
theorem vectorWeakHaarNorm_neg (U : TriadicCube 2)
    (f : Vec 2 → Vec 2) :
    vectorWeakHaarNorm U (fun x => -f x) = vectorWeakHaarNorm U f := by
  unfold vectorWeakHaarNorm vectorWeakHaarEnergy
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  change dualEnergy U (Real.sqrt 3) (fun x => -(f x j)) =
    dualEnergy U (Real.sqrt 3) (fun x => f x j)
  unfold dualEnergy
  exact primalEnergy_neg U ((Real.sqrt 3)⁻¹) (fun x => f x j)

/-- The actual top oscillatory receiver has the pure-second inverse-history
cap after centering the actual top flat load on its source cell. -/
theorem main_e_top_oscillatory_receiver_weak_bound
    (Q U : TriadicCube 2) (depth : ℕ)
    (hU : U ∈ descendantsAtDepth Q depth)
    (nu sigma : ℝ) (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q))
    (b : ℝ) (L : {l : ℝ // 0 < l})
    (n : whiteBasisIndex) (i : Fin 2) :
    let hsub := openCubeSet_subset_of_mem_descendantsAtDepth hU
    let kU := oldSignedCellCoefficient Q U hsub k
    let a := responseFramePlanarCoefficientField nu sigma kU
    let F := oldSignedFlatInput Q b L true n i
    let hFparent := old_signed_flat_input_memL2 Q b L true n i
    let A := oldSignedCellResidual Q U hsub nu sigma hnu hsigma k F hFparent
    let m := oldSignedBlockMean U F
    let G := fun x => F x - m
    let hEll := responseFramePlanarCoefficientField_isElliptic
      (measurableSet_openCubeSet U) nu sigma hnu hsigma kU
    let eaff := mainECellTopAffineOfFlatInput U a hEll F
    vectorWeakHaarNorm U
      (mainECellTopOscillatoryReceiver U a A F eaff) ≤
      (oldSignedInverseHistory U a + 1) * oldSignedBlockPositiveNorm U G := by
  classical
  intro hsub kU a F hFparent A m G hEll eaff
  let hF := hFparent.mono_measure (Measure.restrict_mono_set volume hsub)
  let hG := hF.sub (memLp_const m)
  let ZG := scalarResidualField U nu sigma hnu hsigma kU
    (toHilbertBlockL2OfBlockField hG)
  have hmfirst : m.1 = 0 := by
    funext j
    simp [m, F, oldSignedFlatInput, oldSignedFlatPlusBlock,
      oldSignedBlockMean, cubeAverage_const]
  have hfirst : ∀ x, (G x).1 = 0 := by
    intro x
    change (F x).1 - m.1 = 0
    rw [hmfirst]
    simp [F, oldSignedFlatInput, oldSignedFlatPlusBlock]
  have hPfst : ∀ j : Fin 2, Summable (fun d : ℕ =>
      (Real.sqrt 3) ^ (d + 1) * energy U (cubeIncrement U (d + 1)
        (fun x => (G x).1 j))) := by
    intro j
    have h := old_signed_flat_input_cell_first_positive Q depth b L true n i
      U hU m.1 j
    simpa [G, F] using h
  have hPsnd : ∀ j : Fin 2, Summable (fun d : ℕ =>
      (Real.sqrt 3) ^ (d + 1) * energy U (cubeIncrement U (d + 1)
        (fun x => (G x).2 j))) := by
    intro j
    have h := old_signed_flat_input_cell_second_positive Q depth b L true n i
      U hU m.2 j
    simpa [G, F] using h
  have hrec := old_signed_pure_second_inverse_reciprocal_defect U nu sigma
    hnu hsigma kU G hG hfirst hPfst hPsnd
  have hEq := main_e_top_oscillatory_receiver_eq_centered Q U depth hU
    nu sigma hnu hsigma k b L n i
  rw [old_signed_vector_weak_congr U hEq]
  exact hrec

/-- The actual bottom oscillatory receiver has the centered reciprocal
inverse/response cap; the minus sign does not change its weak Haar norm. -/
theorem main_e_bottom_oscillatory_receiver_weak_bound
    (Q U : TriadicCube 2) (depth : ℕ)
    (hU : U ∈ descendantsAtDepth Q depth)
    (nu sigma : ℝ) (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q))
    (b : ℝ) (L : {l : ℝ // 0 < l})
    (n : whiteBasisIndex) (i : Fin 2) :
    let hsub := openCubeSet_subset_of_mem_descendantsAtDepth hU
    let kU := oldSignedCellCoefficient Q U hsub k
    let a := responseFramePlanarCoefficientField nu sigma kU
    let F := oldSignedFlatInput Q b L false n i
    let hFparent := old_signed_flat_input_memL2 Q b L false n i
    let A := oldSignedCellResidual Q U hsub nu sigma hnu hsigma k F hFparent
    let m := oldSignedBlockMean U F
    let G := fun x => F x - m
    let hEll := responseFramePlanarCoefficientField_isElliptic
      (measurableSet_openCubeSet U) nu sigma hnu hsigma kU
    let eaff := mainECellBottomAffineOfFlatInput U a hEll F
    vectorWeakHaarNorm U
      (mainECellBottomOscillatoryReceiver U a A F eaff) ≤
      Real.sqrt (oldSignedInverseHistory U a * oldSignedResponseHistory U a) *
        oldSignedBlockPositiveNorm U G := by
  classical
  intro hsub kU a F hFparent A m G hEll eaff
  let hF := hFparent.mono_measure (Measure.restrict_mono_set volume hsub)
  let hG := hF.sub (memLp_const m)
  let ZG := scalarResidualField U nu sigma hnu hsigma kU
    (toHilbertBlockL2OfBlockField hG)
  have hPfst : ∀ j : Fin 2, Summable (fun d : ℕ =>
      (Real.sqrt 3) ^ (d + 1) * energy U (cubeIncrement U (d + 1)
        (fun x => (G x).1 j))) := by
    intro j
    have h := old_signed_flat_input_cell_first_positive Q depth b L false n i
      U hU m.1 j
    simpa [G, F] using h
  have hPsnd : ∀ j : Fin 2, Summable (fun d : ℕ =>
      (Real.sqrt 3) ^ (d + 1) * energy U (cubeIncrement U (d + 1)
        (fun x => (G x).2 j))) := by
    intro j
    have h := old_signed_flat_input_cell_second_positive Q depth b L false n i
      U hU m.2 j
    simpa [G, F] using h
  have hrec := old_signed_centered_reciprocal_norm U nu sigma hnu hsigma
    kU G hG hPfst hPsnd
  have hEq := main_e_bottom_oscillatory_receiver_eq_centered Q U depth hU
    nu sigma hnu hsigma k b L n i
  rw [old_signed_vector_weak_congr U hEq]
  rw [vectorWeakHaarNorm_neg]
  exact hrec

end
end ASDExplicitGamma.Main
