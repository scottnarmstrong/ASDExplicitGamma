module

public import ASDExplicitGamma.Gaussian.SquareSource

/-! The exact physical feedback pairing on an arbitrary aligned tiling. -/

@[expose] public section
namespace ASDExplicitGamma.Gaussian
open Homogenization MeasureTheory ASDExplicitGamma.Inverse ASDExplicitGamma.Main
  ASDExplicitGamma.Model ASDExplicitGamma.Response ASDExplicitGamma.Triadic
  ASDExplicitGamma.Variational ASDExplicitGamma.Scalar
open scoped BigOperators
noncomputable section

local instance squarePairingFiniteMeasure (Q : TriadicCube 2) :
    IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
  (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume

/-- The actual shear feedback pairs the distinct source potential's DIAG row
with the same minimizer pair's conjugate gradient. -/
theorem square_q3_shear_pairing_eq_tiled_row
    (Q : TriadicCube 2) (ν σ b : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (L : {l : ℝ // 0 < l}) (l : whiteBasisIndex) (m : ℕ)
    (k : ResponseCoefficient (openCubeSet Q)) (P : BlockVec 2)
    (u : AHarmonicFunction (responseFramePlanarCoefficientField ν σ k)
      (openCubeSet Q))
    (w : AHarmonicFunction
      (adjointCoeffField (responseFramePlanarCoefficientField ν σ k))
      (openCubeSet Q))
    (hrep : hilbertBlockL2ToBlockL2
        ((responseFrameMuOperatorSystemData
          (isOpenBoundedConvexDomain_openCubeSet Q).isOpen.measurableSet
          (square_volume_pos Q)
          ν σ hν hσ k).toMuHilbertRealization.minimizerMap P) =ᵐ[
          volumeMeasureOn (openCubeSet Q)]
        (fun x => (blockResponsePairHalfState
          (responseFramePlanarCoefficientField ν σ k) u w).eval x))
    (z : H10Function (openCubeSet Q))
    (hfirst : (fun x => (hilbertBlockL2ToBlockL2
        (pureFluxResponseGeneratorY (measurableSet_openCubeSet Q)
          (square_volume_pos Q)
          ν σ hν hσ P k
          (squareQ3Directions Q b L
            (@Encodable.encode whiteBasisIndex
              (Encodable.ofCountable whiteBasisIndex) l))).down x).1) =ᵐ[
          volumeMeasureOn (openCubeSet Q)] z.toH1Function.grad) :
      let U := openCubeSet Q
    let H := squareQ3Directions Q b L
      (@Encodable.encode whiteBasisIndex (Encodable.ofCountable whiteBasisIndex) l)
    let η := squareQ3BasisMultiplier Q b σ L l
    let I := diagInterpolant Q m
    let S := responseFrameEnergyBaseMinimizer (measurableSet_openCubeSet Q)
      (square_volume_pos Q) ν σ hν hσ k P
    let C := responseFrameEnergyShearFamily (measurableSet_openCubeSet Q)
      (square_volume_pos Q) ν σ hν hσ k
    inner ℝ S (C H (pureFluxResponseGeneratorY
      (measurableSet_openCubeSet Q)
      (square_volume_pos Q)
      ν σ hν hσ P k H)) =
      volumeAverage U (fun x => vecDot
        (lemmaVPlanarRowField I η z.toH1Function x)
        ((1 / 2 : ℝ) • (w.toH1.grad x - u.toH1.grad x))) := by
  let U := openCubeSet Q
  let hU := isOpenBoundedConvexDomain_openCubeSet Q
  let hv := square_volume_pos Q
  let H := squareQ3Directions Q b L
    (@Encodable.encode whiteBasisIndex (Encodable.ofCountable whiteBasisIndex) l)
  let η := squareQ3BasisMultiplier Q b σ L l
  let I := diagInterpolant Q m
  let D := responseFrameEnergyData (measurableSet_openCubeSet Q) hv ν σ hν hσ k
  let M := responseFrameMuOperatorSystemData
    (measurableSet_openCubeSet Q) hv ν σ hν hσ k
  let X := M.toMuHilbertRealization.minimizerMap P
  let S := responseFrameEnergyBaseMinimizer (measurableSet_openCubeSet Q)
    hv ν σ hν hσ k P
  let C := responseFrameEnergyShearFamily (measurableSet_openCubeSet Q)
    hv ν σ hν hσ k
  let Y := pureFluxResponseGeneratorY (measurableSet_openCubeSet Q) hv
    ν σ hν hσ P k H
  let ηraw := mainQ3DirectionW2 Q b L (whiteBasis l)
  let g : H1Function U := (1 / 2 : ℝ) • (w.toH1 - u.toH1)
  have hS : S.down = X := rfl
  have hzero : lemmaVAffinePotential hU 0 z = z.toH1Function := by
    ext x
    · simp only [lemmaVAffinePotential, H1Function.add_toFun,
        H1Function.affineOnIsSobolevRegularDomain_apply]
      simp
    · simp only [lemmaVAffinePotential, H1Function.add_grad,
        H1Function.affineOnIsSobolevRegularDomain_grad]
      simp only [zero_add]
  have hrowRes : MemH10 U (z.toH1Function - I z.toH1Function).toFun := by
    simpa [I, hzero] using diagInterpolant_affine_residual_memH10 Q m 0 z
  have hηval (x : Vec 2) (hx : x ∈ U) : η.toFun x =
      responseCoefficientExtension H x / σ :=
    (squareQ3Directions_frameValue Q b σ L l hx).symm
  have hconj : (fun x => lemmaVConjugateGradient ν σ
      (responseCoefficientExtension k x) (hilbertBlockL2ToBlockL2 X x)) =ᵐ[
        volumeMeasureOn U] fun x => -g.grad x := by
    have hEll := responseFramePlanarCoefficientField_isElliptic
      (measurableSet_openCubeSet Q) ν σ hν hσ k
    have hlower := blockResponse_lowerImage_pair_half_ae_eq_gradDiff_of_isEllipticFieldOn
      (responseFramePlanarCoefficientField ν σ k) hEll u w
    filter_upwards [hrep, hlower] with x hx hl
    have hpair : hilbertBlockL2ToBlockL2 X x =
        (blockResponsePairHalfState
          (responseFramePlanarCoefficientField ν σ k) u w).eval x := hx
    have hmat := lemmaV_planar_lower_image ν σ
      (responseCoefficientExtension k x) hν hσ (hilbertBlockL2ToBlockL2 X x)
    have hmat' : (blockMatVecMul
        (blockCoeffField (responseFramePlanarCoefficientField ν σ k) x)
        (hilbertBlockL2ToBlockL2 X x)).2 =
        lemmaVConjugateGradient ν σ (responseCoefficientExtension k x)
          (hilbertBlockL2ToBlockL2 X x) := by
      simpa [responseFramePlanarCoefficientField, blockCoeffField] using hmat
    have hl' : (blockMatVecMul
        (blockCoeffField (responseFramePlanarCoefficientField ν σ k) x)
        (hilbertBlockL2ToBlockL2 X x)).2 =
        (1 / 2 : ℝ) • (u.toH1.grad x - w.toH1.grad x) := by
      have hl'' := hl
      rw [← hpair] at hl''
      exact hl''
    calc
      lemmaVConjugateGradient ν σ (responseCoefficientExtension k x)
          (hilbertBlockL2ToBlockL2 X x) =
        (blockMatVecMul
          (blockCoeffField (responseFramePlanarCoefficientField ν σ k) x)
          (hilbertBlockL2ToBlockL2 X x)).2 := hmat'.symm
      _ = (1 / 2 : ℝ) • (u.toH1.grad x - w.toH1.grad x) := hl'
      _ = -g.grad x := by
        simp only [g, H1Function.smul_grad, H1Function.sub_grad]
        ext i
        change (1 / 2 : ℝ) * (u.toH1.grad x i - w.toH1.grad x i) =
          -((1 / 2 : ℝ) * (w.toH1.grad x i - u.toH1.grad x i))
        ring
  have hdown : (C H Y).down = responseShearL2Operator σ hσ H Y.down := by
    simp [C, responseFrameEnergyShearFamily, responseEnergyShearFamilyLinear]
    rfl
  have hfirstY : (fun x =>
      (hilbertBlockL2ToBlockL2 Y.down x).1) =ᵐ[volumeMeasureOn U] z.grad := by
    simpa [Y, H] using hfirst
  have hbil := lemmaV_muSystem_bilinear_eq_volumeAverage
    M X (responseShearL2Operator σ hσ H Y.down)
  have hshear : (fun x => (hilbertBlockL2ToBlockL2
      (responseShearL2Operator σ hσ H Y.down) x).2) =ᵐ[volumeMeasureOn U]
      fun x => -((responseCoefficientExtension H x / σ) •
        matVecMul responsePlanarJ (z.toH1Function.grad x)) := by
    filter_upwards [responseShearL2Operator_toBlockL2_ae σ hσ H Y.down,
      hfirstY, ae_restrict_mem (measurableSet_openCubeSet Q)] with x hs hz hx
    have hsecond := congrArg Prod.snd hs
    change (hilbertBlockL2ToBlockL2
        (responseShearL2Operator σ hσ H Y.down) x).2 =
      (responseShearCorrection σ (responseCoefficientExtension H x)
        (hilbertBlockL2ToBlockL2 Y.down x)).2 at hsecond
    have hz' : (hilbertBlockL2ToBlockL2 Y.down x).1 =
        z.toH1Function.grad x := by simpa using hz
    calc
      (hilbertBlockL2ToBlockL2
        (responseShearL2Operator σ hσ H Y.down) x).2 =
          (responseShearCorrection σ (responseCoefficientExtension H x)
            (hilbertBlockL2ToBlockL2 Y.down x)).2 := hsecond
      _ = -((responseCoefficientExtension H x / σ) •
          matVecMul responsePlanarJ (z.toH1Function.grad x)) := by
        rw [responseShearCorrection, hz']
  have hshearFirst : (fun x => (hilbertBlockL2ToBlockL2
      (responseShearL2Operator σ hσ H Y.down) x).1) =ᵐ[volumeMeasureOn U]
      fun _ => (0 : Vec 2) := by
    filter_upwards [responseShearL2Operator_toBlockL2_ae σ hσ H Y.down] with x hs
    have hfirst := congrArg Prod.fst hs
    change (hilbertBlockL2ToBlockL2
        (responseShearL2Operator σ hσ H Y.down) x).1 =
      (responseShearCorrection σ (responseCoefficientExtension H x)
        (hilbertBlockL2ToBlockL2 Y.down x)).1 at hfirst
    rw [responseShearCorrection] at hfirst
    exact hfirst
  have hblock : (fun x => blockVecDot
      (hilbertBlockL2ToBlockL2
        (responseShearL2Operator σ hσ H Y.down) x)
      (blockMatVecMul (blockCoeffField (responseFramePlanarCoefficientField ν σ k) x)
        (hilbertBlockL2ToBlockL2 X x))) =ᵐ[volumeMeasureOn U]
      fun x => vecDot
        ((hilbertBlockL2ToBlockL2
          (responseShearL2Operator σ hσ H Y.down) x).2)
        (lemmaVConjugateGradient ν σ (responseCoefficientExtension k x)
          (hilbertBlockL2ToBlockL2 X x)) := by
    filter_upwards [hshearFirst, hshear, hconj] with x hsf hsh hco
    have hlow := lemmaV_planar_lower_image ν σ
      (responseCoefficientExtension k x) hν hσ (hilbertBlockL2ToBlockL2 X x)
    have hlow' : (blockMatVecMul
        (blockCoeffField (responseFramePlanarCoefficientField ν σ k) x)
        (hilbertBlockL2ToBlockL2 X x)).2 =
        lemmaVConjugateGradient ν σ (responseCoefficientExtension k x)
          (hilbertBlockL2ToBlockL2 X x) := by
      simpa [responseFramePlanarCoefficientField, blockCoeffField] using hlow
    simp only [blockVecDot]
    rw [hsf, hsh, hlow', hco]
    simp [vecDot]
  have hinner : inner ℝ S (C H Y) = volumeAverage U (fun x =>
      vecDot ((hilbertBlockL2ToBlockL2
        (responseShearL2Operator σ hσ H Y.down) x).2)
        (lemmaVConjugateGradient ν σ (responseCoefficientExtension k x)
          (hilbertBlockL2ToBlockL2 X x))) := by
    calc
      inner ℝ S (C H Y) = D.energy S.down (C H Y).down := rfl
      _ = D.energy X (responseShearL2Operator σ hσ H Y.down) := by rw [hS, hdown]
      _ = M.toMuHilbertRealization.energyBilin X
          (responseShearL2Operator σ hσ H Y.down) := rfl
      _ = volumeAverage U (fun x => blockVecDot
          (hilbertBlockL2ToBlockL2
            (responseShearL2Operator σ hσ H Y.down) x)
          (blockMatVecMul (blockCoeffField (responseFramePlanarCoefficientField ν σ k) x)
            (hilbertBlockL2ToBlockL2 X x))) := hbil
      _ = volumeAverage U (fun x => vecDot
          ((hilbertBlockL2ToBlockL2
            (responseShearL2Operator σ hσ H Y.down) x).2)
          (lemmaVConjugateGradient ν σ (responseCoefficientExtension k x)
            (hilbertBlockL2ToBlockL2 X x))) := by
          unfold volumeAverage
          congr 1
          exact integral_congr_ae hblock
  have hpoint : (fun x => vecDot
      ((hilbertBlockL2ToBlockL2
        (responseShearL2Operator σ hσ H Y.down) x).2)
      (lemmaVConjugateGradient ν σ (responseCoefficientExtension k x)
        (hilbertBlockL2ToBlockL2 X x))) =ᵐ[volumeMeasureOn U]
      fun x => vecDot (η.toFun x • matVecMul responsePlanarJ
        (z.toH1Function.grad x)) (g.grad x) := by
    filter_upwards [hshear, hconj, ae_restrict_mem (measurableSet_openCubeSet Q)]
      with x hsh hco hx
    rw [hsh, hco, hηval x hx]
    simp only [vecDot_neg_left, vecDot_neg_right, neg_neg]
  have hraw : volumeAverage U (fun x => vecDot
      (η.toFun x • matVecMul responsePlanarJ (z.toH1Function.grad x)) (g.grad x)) =
      volumeAverage U (fun x => vecDot
        (lemmaVPlanarRowField I η z.toH1Function x) (g.grad x)) := by
    have hη : MemLp η.toFun (⊤ : ENNReal) (volume.restrict U) := by
      dsimp [η, squareQ3BasisMultiplier]
      simpa only [H1Function.smul_toFun, smul_eq_mul, mul_comm] using
        (ηraw.value_memLp_top.const_mul (σ⁻¹))
    have hDη (i : Fin 2) : MemLp (fun x => η.grad x i) (⊤ : ENNReal)
        (volume.restrict U) := by
      have hcomponent : MemLp (fun x => ηraw.value.grad x i) (⊤ : ENNReal)
          (volume.restrict U) := ηraw.gradient_memLp_top_volume i
      dsimp [η, squareQ3BasisMultiplier]
      simpa only [H1Function.smul_grad, Pi.smul_apply, smul_eq_mul] using
        hcomponent.const_mul (σ⁻¹)
    exact lemmaV_pairing_lift_of_interpolant hU I z.toH1Function η g
      hrowRes hη hDη
  have hmain : inner ℝ S (C H Y) = volumeAverage U (fun x =>
      vecDot (lemmaVPlanarRowField I η z.toH1Function x) (g.grad x)) := by
    calc
      inner ℝ S (C H Y) = volumeAverage U (fun x => vecDot
          ((hilbertBlockL2ToBlockL2
            (responseShearL2Operator σ hσ H Y.down) x).2)
          (lemmaVConjugateGradient ν σ (responseCoefficientExtension k x)
            (hilbertBlockL2ToBlockL2 X x))) := hinner
      _ = volumeAverage U (fun x => vecDot
          (η.toFun x • matVecMul responsePlanarJ (z.toH1Function.grad x))
          (g.grad x)) := by
          unfold volumeAverage
          congr 1
          exact integral_congr_ae hpoint
      _ = volumeAverage U (fun x => vecDot
          (lemmaVPlanarRowField I η z.toH1Function x) (g.grad x)) := hraw
  simpa [Y, H, η, I, S, C, g] using hmain

end
end ASDExplicitGamma.Gaussian
