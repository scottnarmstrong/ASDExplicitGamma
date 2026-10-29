module

public import ASDExplicitGamma.Main.ObsLowerGeneratorY
public import ASDExplicitGamma.Main.ObsLowerRowBound
public import ASDExplicitGamma.Main.ObsLowerProjected
public import ASDExplicitGamma.Inverse.PureFluxGeneratorFeedback

/-! Observer-level (depth `m` source mesh) uncentered feedback pairing: the shear pairing of the
generator is the depth-`m` diagonal row pairing, and the finite feedback is bounded by the
column and row constants. -/

@[expose] public section

open Homogenization MeasureTheory ASDExplicitGamma.Gaussian ASDExplicitGamma.Main ASDExplicitGamma.Model
  ASDExplicitGamma.Response ASDExplicitGamma.Triadic ASDExplicitGamma.Variational
  ASDExplicitGamma.Scalar

namespace ASDExplicitGamma.Inverse

local instance obsFeedbackFiniteMeasure (n : ℤ) :
    IsFiniteMeasure (volumeMeasureOn (openCubeSet (originCube 2 n))) :=
  (isOpenBoundedConvexDomain_openCubeSet (originCube 2 n)).isFiniteMeasure_restrict_volume

/-- The physical shear pairing for the centered q3 direction is represented by
the centered DIAG row at every aligned source depth. -/
theorem obsGeneratorY_shear_pairing_eq_diagRow
    (n : ℤ) (ν σ b : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (L : {l : ℝ // 0 < l}) (l : whiteBasisIndex) (m : ℕ)
    (k : ResponseCoefficient (openCubeSet (originCube 2 n))) (P : BlockVec 2)
    (u : AHarmonicFunction (responseFramePlanarCoefficientField ν σ k)
      (openCubeSet (originCube 2 n)))
    (w : AHarmonicFunction
      (adjointCoeffField (responseFramePlanarCoefficientField ν σ k))
      (openCubeSet (originCube 2 n)))
    (hrep : hilbertBlockL2ToBlockL2
        ((responseFrameMuOperatorSystemData
          (isOpenBoundedConvexDomain_openCubeSet (originCube 2 n)).isOpen.measurableSet
          (volume_openCubeSet_originCube_toReal_pos (d := 2) n)
          ν σ hν hσ k).toMuHilbertRealization.minimizerMap P) =ᵐ[
          volumeMeasureOn (openCubeSet (originCube 2 n))]
        (fun x => (blockResponsePairHalfState
          (responseFramePlanarCoefficientField ν σ k) u w).eval x))
    (z : H10Function (openCubeSet (originCube 2 n)))
    (hfirst : (fun x => (hilbertBlockL2ToBlockL2
        (pureFluxResponseGeneratorY (measurableSet_openCubeSet (originCube 2 n))
          (volume_openCubeSet_originCube_toReal_pos (d := 2) n)
          ν σ hν hσ P k
          (pureFluxMainCubeQ3ResponseCoefficient n b L
            (@Encodable.encode whiteBasisIndex
              (Encodable.ofCountable whiteBasisIndex) l))).down x).1) =ᵐ[
          volumeMeasureOn (openCubeSet (originCube 2 n))] z.toH1Function.grad) :
    let Q := originCube 2 n
    let U := openCubeSet Q
    let H := pureFluxMainCubeQ3ResponseCoefficient n b L
      (@Encodable.encode whiteBasisIndex (Encodable.ofCountable whiteBasisIndex) l)
    let η := pureFluxMainQ3BasisFrameMultiplier n b σ L l
    let I := diagInterpolant Q m
    let S := responseFrameEnergyBaseMinimizer (measurableSet_openCubeSet Q)
      (volume_openCubeSet_originCube_toReal_pos (d := 2) n) ν σ hν hσ k P
    let C := responseFrameEnergyShearFamily (measurableSet_openCubeSet Q)
      (volume_openCubeSet_originCube_toReal_pos (d := 2) n) ν σ hν hσ k
    let Y := pureFluxResponseGeneratorY (measurableSet_openCubeSet Q)
      (volume_openCubeSet_originCube_toReal_pos (d := 2) n)
      ν σ hν hσ P k H
    inner ℝ S (C H Y) =
      volumeAverage U (fun x => vecDot
        (lemmaVPlanarRowField I η z.toH1Function x)
        ((1 / 2 : ℝ) • (w.toH1.grad x - u.toH1.grad x))) := by
  let Q := originCube 2 n
  let U := openCubeSet Q
  let hU := isOpenBoundedConvexDomain_openCubeSet Q
  let hv := volume_openCubeSet_originCube_toReal_pos (d := 2) n
  let H := pureFluxMainCubeQ3ResponseCoefficient n b L
    (@Encodable.encode whiteBasisIndex (Encodable.ofCountable whiteBasisIndex) l)
  let η := pureFluxMainQ3BasisFrameMultiplier n b σ L l
  let I := diagInterpolant Q m
  let D := responseFrameEnergyData (measurableSet_openCubeSet Q) hv ν σ hν hσ k
  let M := responseFrameMuOperatorSystemData (measurableSet_openCubeSet Q) hv ν σ hν hσ k
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
    simpa [I, Q, hzero] using diagInterpolant_affine_residual_memH10 Q m 0 z
  have hηval (x : Vec 2) (hx : x ∈ U) : η.toFun x =
      responseCoefficientExtension H x / σ := by
    simpa [η, H] using
      (obsCoefficientFrameValue n b σ L l hx).symm
  have hη : MemLp η.toFun (⊤ : ENNReal) (volume.restrict U) := by
    dsimp [η, pureFluxMainQ3BasisFrameMultiplier]
    simpa only [H1Function.smul_toFun, smul_eq_mul] using
      ηraw.value_memLp_top.const_mul (σ⁻¹)
  have hDη (i : Fin 2) : MemLp (fun x => η.grad x i) (⊤ : ENNReal)
      (volume.restrict U) := by
    have hcomponent : MemLp (fun x => ηraw.value.grad x i) (⊤ : ENNReal)
        (volume.restrict U) := ηraw.gradient_memLp_top_volume i
    dsimp [η, pureFluxMainQ3BasisFrameMultiplier]
    simpa only [H1Function.smul_grad, Pi.smul_apply, smul_eq_mul] using
      hcomponent.const_mul (σ⁻¹)
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
  have hfirstY : (fun x => (hilbertBlockL2ToBlockL2 Y.down x).1) =ᵐ[
      volumeMeasureOn U] z.toH1Function.grad := by
    simpa [Y, H] using hfirst
  have hbil := lemmaV_muSystem_bilinear_eq_volumeAverage M X
    (responseShearL2Operator σ hσ H Y.down)
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
      _ = volumeAverage U (fun x =>
          vecDot (lemmaVPlanarRowField I η z.toH1Function x) (g.grad x)) := hraw
  simpa [Y, H, η, I, S, C, g] using hmain

/-- Finite covariance feedback for one actual affine load. The source fields
and every shear pairing are generated from the same response minimizer; the
bound combines the source A-row, the distinct-potential feedback B-row, and
the actual tiled projected-source estimate. -/
theorem obsGeneratorY_cross_feedback_finite
    (n : ℤ) (m : ℕ) (ν σ b : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (L : {l : ℝ // 0 < l}) (s : Finset whiteBasisIndex)
    (k : ResponseCoefficient (openCubeSet (originCube 2 n))) (P : BlockVec 2)
    (r : H10Function (openCubeSet (originCube 2 n)))
    (u : AHarmonicFunction (responseFramePlanarCoefficientField ν σ k)
      (openCubeSet (originCube 2 n)))
    (w : AHarmonicFunction
      (adjointCoeffField (responseFramePlanarCoefficientField ν σ k))
      (openCubeSet (originCube 2 n)))
    (hrep : hilbertBlockL2ToBlockL2
        ((responseFrameMuOperatorSystemData
          (isOpenBoundedConvexDomain_openCubeSet (originCube 2 n)).isOpen.measurableSet
          (volume_openCubeSet_originCube_toReal_pos (d := 2) n)
          ν σ hν hσ k).toMuHilbertRealization.minimizerMap P) =ᵐ[
          volumeMeasureOn (openCubeSet (originCube 2 n))]
        (fun x => (blockResponsePairHalfState
          (responseFramePlanarCoefficientField ν σ k) u w).eval x))
    (hgrad : (lemmaVAffinePotential
        (isOpenBoundedConvexDomain_openCubeSet (originCube 2 n)) P.1 r).grad =ᵐ[
          volumeMeasureOn (openCubeSet (originCube 2 n))]
        (blockResponsePairHalfState
          (responseFramePlanarCoefficientField ν σ k) u w).potential)
    (B : ℝ) (hB : 0 ≤ B)
    (hhist : ∀ U ∈ descendantsAtDepth (originCube 2 n) m,
      lemmaVInverseHistory U (responseFramePlanarCoefficientField ν σ k)
        ((3 : ℝ)^(1/4:ℝ)) ≤ B) :
    let Q := originCube 2 n
    let v := lemmaVAffinePotential (isOpenBoundedConvexDomain_openCubeSet Q) P.1 r
    let g : H1Function (openCubeSet Q) := (1/2:ℝ) • (w.toH1-u.toH1)
    let S := responseFrameEnergyBaseMinimizer (measurableSet_openCubeSet Q)
      (volume_openCubeSet_originCube_toReal_pos (d := 2) n) ν σ hν hσ k P
    let C := responseFrameEnergyShearFamily (measurableSet_openCubeSet Q)
      (volume_openCubeSet_originCube_toReal_pos (d := 2) n) ν σ hν hσ k
    |(∑ l ∈ s,
      inner ℝ S (C (pureFluxMainCubeQ3ResponseCoefficient n b L
        (@Encodable.encode whiteBasisIndex (Encodable.ofCountable whiteBasisIndex) l))
        (pureFluxResponseGeneratorY (measurableSet_openCubeSet Q)
          (volume_openCubeSet_originCube_toReal_pos (d := 2) n)
          ν σ hν hσ P k (pureFluxMainCubeQ3ResponseCoefficient n b L
            (@Encodable.encode whiteBasisIndex
              (Encodable.ofCountable whiteBasisIndex) l)))))| ≤
      (63/50:ℝ)*B*|σ⁻¹|^2*obsColumnCoefficient Q m b L*
        mainQ3RowConstant (diagMeshRadius Q m) b L.1*
        Real.sqrt (lemmaVTiledWeakEnergy Q m v.grad) *
        Real.sqrt (lemmaVTiledWeakEnergy Q m g.grad) := by
  let Q := originCube 2 n
  let U := openCubeSet Q
  let hU := isOpenBoundedConvexDomain_openCubeSet Q
  let hv := volume_openCubeSet_originCube_toReal_pos (d := 2) n
  let v := lemmaVAffinePotential hU P.1 r
  let I := diagInterpolant Q m
  let g : H1Function U := (1/2:ℝ) • (w.toH1-u.toH1)
  let Smin := responseFrameEnergyBaseMinimizer (measurableSet_openCubeSet Q)
    hv ν σ hν hσ k P
  let C := responseFrameEnergyShearFamily (measurableSet_openCubeSet Q) hv ν σ hν hσ k
  let η (l : whiteBasisIndex) := pureFluxMainQ3BasisFrameMultiplier n b σ L l
  let H (l : whiteBasisIndex) := pureFluxMainCubeQ3ResponseCoefficient n b L
    (@Encodable.encode whiteBasisIndex (Encodable.ofCountable whiteBasisIndex) l)
  let Y (l : whiteBasisIndex) := pureFluxResponseGeneratorY
    (measurableSet_openCubeSet Q) hv ν σ hν hσ P k (H l)
  let sourcePositive (l : whiteBasisIndex) :=
    lemmaVTiledPositiveEnergy Q m (fun x => -(lemmaVPlanarRowField I (η l) v x))
  let sourceTrace := pureFluxMainQ3RowEnergy n b σ L m P.1 r
  let sourceCoeff := |σ⁻¹| * obsColumnCoefficient Q m b L
  let gWeak := lemmaVTiledWeakEnergy Q m g.grad
  have htrace := obs_row_trace_bound n m b σ L P.1 r
  have hsourceData (l : whiteBasisIndex) :
      ∃ z : H10Function U,
        (fun x => (hilbertBlockL2ToBlockL2 (Y l).down x).1) =ᵐ[
          volumeMeasureOn U] z.toH1Function.grad ∧
        Real.sqrt (lemmaVTiledWeakEnergy Q m z.toH1Function.grad) ≤
          (126/100)*B*Real.sqrt (sourcePositive l) := by
    obtain ⟨hF, hgen, z, hfirst, henergy, hfeedback⟩ :=
      obsGeneratorY_tiled_source_bound
        n ν σ b hν hσ L l m k P r u w hrep hgrad B hB hhist
    refine ⟨z, ?_, ?_⟩
    · have hgen' : Y l = responseEnergyUp
          (responseFrameEnergyData (measurableSet_openCubeSet Q) hv ν σ hν hσ k)
          (scalarProjectionResidual Q ν σ hν hσ k (projectedSourceLoad Q hF)) := by
        simpa [Y, H] using hgen
      rw [hgen']
      simpa [Y, H, responseEnergyUp_down, scalarProjectionResidual,
        scalarResidualField, projectedSourceField] using hfirst
    · simpa [sourcePositive, Q, v, I, η] using hfeedback
  choose z hfirst hfeedback using hsourceData
  have hRn (l : whiteBasisIndex) : 0 ≤ sourceTrace l := by
    unfold sourceTrace pureFluxMainQ3RowEnergy descendantsAverage
    exact mul_nonneg (by positivity) (Finset.sum_nonneg fun U _ =>
      vectorPositiveHaarEnergy_nonneg U _)
  have htraceTotal : (∑' l, sourceTrace l) ≤ sourceCoeff^2 *
      lemmaVTiledWeakEnergy Q m v.grad := by
    have hh := pow_le_pow_left₀ (Real.sqrt_nonneg _) htrace.2 2
    rw [Real.sq_sqrt (tsum_nonneg hRn), mul_pow,
      Real.sq_sqrt (lemmaVTiledWeakEnergy_nonneg Q m v.grad)] at hh
    exact hh
  have hsourcePositive_eq (l : whiteBasisIndex) :
      sourcePositive l = sourceTrace l := by
    dsimp [sourcePositive, sourceTrace, pureFluxMainQ3RowEnergy,
      lemmaVTiledPositiveEnergy, descendantsAverage, I, η, v]
    congr 1
    apply Finset.sum_congr rfl
    intro U hU'
    unfold vectorPositiveHaarEnergy
    apply Finset.sum_congr rfl
    intro j hj
    change primalEnergy U (Real.sqrt 3)
        (fun x => -(lemmaVPlanarRowField I (η l) v x j)) =
      primalEnergy U (Real.sqrt 3)
        (fun x => lemmaVPlanarRowField I (η l) v x j)
    exact primalEnergy_neg U (Real.sqrt 3) _
  have hPsum : (∑ l ∈ s, sourcePositive l) ≤ sourceCoeff^2 *
      lemmaVTiledWeakEnergy Q m v.grad := by
    calc
      _ = ∑ l ∈ s, sourceTrace l := by
        apply Finset.sum_congr rfl
        intro l hl
        exact hsourcePositive_eq l
      _ ≤ ∑' l, sourceTrace l := htrace.1.sum_le_tsum s (fun l hl => hRn l)
      _ ≤ _ := htraceTotal
  have hZsum : (∑ l ∈ s, lemmaVTiledWeakEnergy Q m (z l).toH1Function.grad) ≤
      ((126/100:ℝ)*B)^2 * (∑ l ∈ s, sourcePositive l) := by
    calc
      _ ≤ ∑ l ∈ s, ((126/100:ℝ)*B)^2 * sourcePositive l := by
        apply Finset.sum_le_sum
        intro l hl
        have hs := pow_le_pow_left₀
          (Real.sqrt_nonneg (lemmaVTiledWeakEnergy Q m (z l).toH1Function.grad))
          (hfeedback l) 2
        rw [Real.sq_sqrt (lemmaVTiledWeakEnergy_nonneg Q m
          (z l).toH1Function.grad)] at hs
        calc
          lemmaVTiledWeakEnergy Q m (z l).toH1Function.grad ≤
              ((126/100:ℝ)*B*Real.sqrt (sourcePositive l))^2 := hs
          _ = ((126/100:ℝ)*B)^2 * sourcePositive l := by
            rw [mul_pow, Real.sq_sqrt
              (lemmaVTiledPositiveEnergy_nonneg Q m
                (fun x => -(lemmaVPlanarRowField I (η l) v x)))]
      _ = _ := by rw [Finset.mul_sum]
  have hsourceCoeffNonneg : 0 ≤ sourceCoeff := by
    have hcoef : 0 ≤ obsColumnCoefficient Q m b L := by
      have hr : 0 ≤ diagMeshRadius Q m := (diagMeshRadius_pos Q m).le
      unfold obsColumnCoefficient
      positivity
    exact mul_nonneg (abs_nonneg _) hcoef
  have hhalfNonneg : 0 ≤ (126/100:ℝ)*B := mul_nonneg (by norm_num) hB
  have hWv := lemmaVTiledWeakEnergy_nonneg Q m v.grad
  have hZsqrt : Real.sqrt (∑ l ∈ s,
      lemmaVTiledWeakEnergy Q m (z l).toH1Function.grad) ≤
      (126/100:ℝ)*B*sourceCoeff*Real.sqrt (lemmaVTiledWeakEnergy Q m v.grad) := by
    apply (Real.sqrt_le_iff).2
    constructor
    · exact mul_nonneg (mul_nonneg hhalfNonneg hsourceCoeffNonneg)
        (Real.sqrt_nonneg _)
    · calc
        _ ≤ ((126/100:ℝ)*B)^2 * (∑ l ∈ s, sourcePositive l) := hZsum
        _ ≤ ((126/100:ℝ)*B)^2 *
            (sourceCoeff^2*lemmaVTiledWeakEnergy Q m v.grad) :=
          mul_le_mul_of_nonneg_left hPsum (sq_nonneg _)
        _ = ((126/100:ℝ)*B*sourceCoeff*
            Real.sqrt (lemmaVTiledWeakEnergy Q m v.grad))^2 := by
          calc
            _ = ((126/100:ℝ)*B)^2 * sourceCoeff^2 *
                lemmaVTiledWeakEnergy Q m v.grad := by ring
            _ = ((126/100:ℝ)*B)^2 * sourceCoeff^2 *
                (Real.sqrt (lemmaVTiledWeakEnergy Q m v.grad))^2 := by
              rw [Real.sq_sqrt hWv]
            _ = _ := by ring
  let Sraw := obsDistinctRow whiteBasis s b L Q m z
  let Sphys : Vec 2 → Vec 2 := fun x => ∑ l ∈ s,
    lemmaVPlanarRowField I (η l) (z l).toH1Function x
  have hSscale : Sphys = fun x => (σ⁻¹:ℝ) • Sraw x := by
    funext x
    dsimp [Sphys, Sraw, obsDistinctRow, η,
      pureFluxMainQ3BasisFrameMultiplier]
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro l hl
    exact congrFun (pureFluxPlanarRowField_smul I
      (mainQ3DirectionW2 Q b L (whiteBasis l)).value
      (z l).toH1Function (σ⁻¹)) x
  have hηraw (l : whiteBasisIndex) :
      MemLp ((mainQ3DirectionW2 Q b L (whiteBasis l)).value.toFun)
        (⊤ : ENNReal) (volume.restrict U) :=
    (mainQ3DirectionW2 Q b L (whiteBasis l)).value_memLp_top
  have hDηraw (l : whiteBasisIndex) (j : Fin 2) :
      MemLp (fun x => (mainQ3DirectionW2 Q b L
        (whiteBasis l)).value.grad x j) (⊤ : ENNReal) (volume.restrict U) :=
    (mainQ3DirectionW2 Q b L (whiteBasis l)).gradient_memLp_top_volume j
  have hSrawMem : MemVectorL2 U Sraw := by
    change MemLp (fun x => ∑ l ∈ s,
      lemmaVPlanarRowField I (mainQ3DirectionW2 Q b L
        (whiteBasis l)).value (z l).toH1Function x) 2 (volumeMeasureOn U)
    exact memLp_finsetSum s fun l hl =>
      lemmaVPlanarRowField_memL2 I
        (mainQ3DirectionW2 Q b L (whiteBasis l)).value
        (z l).toH1Function (hηraw l) (hDηraw l)
  have hSrawCoord (j : Fin 2) : MemLp (fun x => Sraw x j) 2
      (normalizedCubeMeasure Q) :=
    memL2On_openCubeSet_normalizedCubeMeasure (hSrawMem.eval j)
  have hgCoord (j : Fin 2) : MemLp (fun x => g.grad x j) 2
      (normalizedCubeMeasure Q) := g.grad_memL2_normalizedCubeMeasure j
  have hrow := obs_distinct_h10_row_bound whiteBasis s b L Q m z
  have hdual : |volumeAverage U (fun x => vecDot (Sraw x) (g.grad x))| ≤
      Real.sqrt (lemmaVTiledWeakEnergy Q m g.grad) *
        Real.sqrt (lemmaVTiledPositiveEnergy Q m Sraw) := by
    change |integralAverage U (fun x => vecDot (Sraw x) (g.grad x))| ≤ _
    rw [← cubeAverage_eq_integralAverage_openCubeSet]
    have hcomm : (fun x => vecDot (Sraw x) (g.grad x)) =
        fun x => vecDot (g.grad x) (Sraw x) := by
      funext x
      exact vecDot_comm _ _
    rw [hcomm]
    exact lemmaV_tiled_pairing_le Q m g.grad_memL2_normalizedCubeMeasure
      hSrawCoord hrow.1
  have hpairDir (l : whiteBasisIndex) (hl : l ∈ s) :
      inner ℝ Smin (C (H l) (Y l)) = volumeAverage U (fun x =>
        vecDot (lemmaVPlanarRowField I (η l) (z l).toH1Function x) (g.grad x)) := by
    have hp := obsGeneratorY_shear_pairing_eq_diagRow
      n ν σ b hν hσ L l m k P u w hrep (z l) (hfirst l)
    simpa [Q, U, I, η, H, Y, Smin, C, g] using hp
  have hsumPair : (∑ l ∈ s, inner ℝ Smin (C (H l) (Y l))) =
      volumeAverage U (fun x => vecDot (Sphys x) (g.grad x)) := by
    calc
      _ = ∑ l ∈ s, volumeAverage U (fun x =>
          vecDot (lemmaVPlanarRowField I (η l) (z l).toH1Function x) (g.grad x)) := by
        apply Finset.sum_congr rfl
        intro l hl
        exact hpairDir l hl
      _ = volumeAverage U (fun x => ∑ l ∈ s,
          vecDot (lemmaVPlanarRowField I (η l) (z l).toH1Function x) (g.grad x)) := by
        rw [volumeAverage_sum]
        · intro l hl
          have hrowMem : MemVectorL2 U
              (lemmaVPlanarRowField I (η l) (z l).toH1Function) := by
            have hη : MemLp (η l).toFun (⊤ : ENNReal) (volume.restrict U) := by
              dsimp [η, pureFluxMainQ3BasisFrameMultiplier]
              simpa only [H1Function.smul_toFun, smul_eq_mul] using
                (hηraw l).const_mul (σ⁻¹)
            have hDη (j : Fin 2) : MemLp (fun x => (η l).grad x j)
                (⊤ : ENNReal) (volume.restrict U) := by
              dsimp [η, pureFluxMainQ3BasisFrameMultiplier]
              simpa only [H1Function.smul_grad, Pi.smul_apply, smul_eq_mul] using
                (hDηraw l j).const_mul (σ⁻¹)
            exact lemmaVPlanarRowField_memL2 I (η l) (z l).toH1Function hη hDη
          exact integrableOn_vecDot_of_memVectorL2 hrowMem g.grad_memVectorL2
      _ = volumeAverage U (fun x => vecDot (Sphys x) (g.grad x)) := by
        congr 1
        funext x
        simp [Sphys, vecDot, Finset.sum_mul, Finset.sum_comm, mul_assoc]
  have hscaleAvg : volumeAverage U (fun x => vecDot (Sphys x) (g.grad x)) =
      (σ⁻¹:ℝ) * volumeAverage U (fun x => vecDot (Sraw x) (g.grad x)) := by
    calc
      _ = volumeAverage U (fun x => (σ⁻¹:ℝ) *
          vecDot (Sraw x) (g.grad x)) := by
        congr 1
        funext x
        rw [hSscale]
        simp [vecDot, Pi.smul_apply, Fin.sum_univ_two]
        ring
      _ = _ := volumeAverage_smul U (σ⁻¹)
        (fun x => vecDot (Sraw x) (g.grad x))
  have hrowBound := hrow.2
  have hcross : |(∑ l ∈ s, inner ℝ Smin (C (H l) (Y l)))| ≤
      (63/50:ℝ)*B*|σ⁻¹|^2*obsColumnCoefficient Q m b L*
        mainQ3RowConstant (diagMeshRadius Q m) b L.1*Real.sqrt (lemmaVTiledWeakEnergy Q m v.grad) *
          Real.sqrt gWeak := by
    rw [hsumPair, hscaleAvg, abs_mul]
    calc
      _ ≤ |σ⁻¹| *
          (Real.sqrt (lemmaVTiledWeakEnergy Q m g.grad) *
            Real.sqrt (lemmaVTiledPositiveEnergy Q m Sraw)) :=
        mul_le_mul_of_nonneg_left hdual (abs_nonneg (σ⁻¹))
      _ ≤ |σ⁻¹| *
          (Real.sqrt (lemmaVTiledWeakEnergy Q m g.grad) *
            (mainQ3RowConstant (diagMeshRadius Q m) b L.1 *
              Real.sqrt (∑ l ∈ s, lemmaVTiledWeakEnergy Q m (z l).toH1Function.grad))) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hrowBound
            (Real.sqrt_nonneg (lemmaVTiledWeakEnergy Q m g.grad)))
          (abs_nonneg (σ⁻¹))
      _ ≤ (63/50:ℝ)*B*|σ⁻¹|^2*obsColumnCoefficient Q m b L*
          mainQ3RowConstant (diagMeshRadius Q m) b L.1*Real.sqrt (lemmaVTiledWeakEnergy Q m v.grad) *
            Real.sqrt gWeak := by
        have hBcov : 0 ≤ mainQ3RowConstant (diagMeshRadius Q m) b L.1 :=
          obs_rowConstant_nonneg _ _ _ (diagMeshRadius_pos Q m).le
        have hfeedbackCoeff : (126/100:ℝ) = (63/50:ℝ) := by norm_num
        calc
          _ ≤ |σ⁻¹| * (Real.sqrt gWeak *
              (mainQ3RowConstant (diagMeshRadius Q m) b L.1 *
                ((126/100:ℝ)*B*sourceCoeff*
                  Real.sqrt (lemmaVTiledWeakEnergy Q m v.grad)))) := by
            apply mul_le_mul_of_nonneg_left
            · apply mul_le_mul_of_nonneg_left
              · exact mul_le_mul_of_nonneg_left hZsqrt
                  hBcov
              · exact Real.sqrt_nonneg gWeak
            · exact abs_nonneg _
          _ = (63/50:ℝ)*B*|σ⁻¹|^2*obsColumnCoefficient Q m b L*
                mainQ3RowConstant (diagMeshRadius Q m) b L.1*
                Real.sqrt (lemmaVTiledWeakEnergy Q m v.grad) * Real.sqrt gWeak := by
            rw [hfeedbackCoeff]
            dsimp [sourceCoeff]
            ring
  simpa [Q, v, g, Smin, C, H, Y, gWeak] using hcross



end ASDExplicitGamma.Inverse
