module

public import ASDExplicitGamma.Inverse.PureFluxGeneratorRowSource
public import ASDExplicitGamma.Inverse.PureFluxGeneratorCenteredSource
public import ASDExplicitGamma.Inverse.PureFluxGeneratorTiledProjected
public import ASDExplicitGamma.Inverse.PureFluxFeedbackCoefficient
public import ASDExplicitGamma.Gaussian.SquareDirections

/-! Actual uncentered q3 generator sources on an arbitrary aligned tiling. -/

@[expose] public section
namespace ASDExplicitGamma.Gaussian
open Homogenization MeasureTheory ASDExplicitGamma.Main ASDExplicitGamma.Model
  ASDExplicitGamma.Response ASDExplicitGamma.Triadic ASDExplicitGamma.Variational
  ASDExplicitGamma.Scalar ASDExplicitGamma.Inverse
open scoped BigOperators
noncomputable section

local instance squareSourceFiniteMeasure (Q : TriadicCube 2) :
    IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
  (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume

/-- Every uncentered physical q3 row has its positive Haar series on every tile. -/
theorem square_q3_row_positive_series
    (Q : TriadicCube 2) (b σ : ℝ) (L : {l : ℝ // 0 < l}) (m : ℕ)
    (p : Vec 2) (u : H10Function (openCubeSet Q))
    (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth Q m)
    (l : whiteBasisIndex) (i : Fin 2) :
    Summable (fun k => (Real.sqrt 3)^(k+1)*energy U
      (cubeIncrement U (k+1) (fun x => lemmaVPlanarRowField
        (diagInterpolant Q m)
        (squareQ3BasisMultiplier Q b σ L l)
        (lemmaVAffinePotential (isOpenBoundedConvexDomain_openCubeSet Q) p u) x i))) := by
  classical
  let v := lemmaVAffinePotential (isOpenBoundedConvexDomain_openCubeSet Q) p u
  let I := diagInterpolant Q m
  have hrow := (main_q3_row_product whiteBasis Q m b L p u
    {l} (fun _ => 1)).1 U hU i
  have hunit : Summable (fun k => (Real.sqrt 3)^(k+1)*energy U
      (cubeIncrement U (k+1) (fun x => lemmaVPlanarRowField I
        (mainQ3DirectionW2 Q b L (whiteBasis l)).value v x i))) := by
    simpa [lemmaVRowCombination, v, I] using hrow
  have heq : (fun x => lemmaVPlanarRowField I
      (squareQ3BasisMultiplier Q b σ L l) v x i) =
      fun x => σ⁻¹ * lemmaVPlanarRowField I
        (mainQ3DirectionW2 Q b L (whiteBasis l)).value v x i := by
    simp only [squareQ3BasisMultiplier, pureFluxPlanarRowField_smul]
    rfl
  change Summable (fun k => (Real.sqrt 3)^(k+1)*energy U
    (cubeIncrement U (k+1) (fun x => lemmaVPlanarRowField I
      (squareQ3BasisMultiplier Q b σ L l) v x i)))
  rw [heq]
  exact pureFlux_positive_series_smul U _ (σ⁻¹) hunit

private theorem squareNegativeShear_memLp
    {Q : TriadicCube 2} (η v : H1Function (openCubeSet Q))
    (hη : MemLp η.toFun (⊤ : ENNReal) (volume.restrict (openCubeSet Q))) :
    MemLp (fun x => -((η.toFun x) • matVecMul responsePlanarJ (v.grad x))) 2
      (normalizedCubeMeasure Q) := by
  have hvec : MemVectorL2 (openCubeSet Q)
      (fun x => -((η.toFun x) • matVecMul responsePlanarJ (v.grad x))) := by
    change MemLp (-(fun x => (η.toFun x) •
      matVecMul responsePlanarJ (v.grad x))) 2 (volumeMeasureOn (openCubeSet Q))
    exact (lemmaVPlanar_skewGradient_memL2 v hη).neg
  have hcoord (i : Fin 2) : MemLp
      (fun x => -((η.toFun x) • matVecMul responsePlanarJ (v.grad x)) i) 2
      (normalizedCubeMeasure Q) :=
    memLp_normalized_of_memL2On (memScalarL2_coord_of_memVectorL2 hvec i)
  exact memLp_pi_iff.mpr hcoord

/-- For one fixed affine minimizer pair, the response generator in a uncentered
q3 direction is the weighted projection residual of its uncentered DIAG row.
This is the bridge needed by arbitrary aligned source meshes. -/
theorem square_q3_generator_source_projection
    (Q : TriadicCube 2) (ν σ b : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (L : {l : ℝ // 0 < l}) (l : whiteBasisIndex) (m : ℕ)
    (k : ResponseCoefficient (openCubeSet Q)) (P : BlockVec 2)
    (r : H10Function (openCubeSet Q))
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
    (hgrad : (lemmaVAffinePotential
        (isOpenBoundedConvexDomain_openCubeSet Q) P.1 r).grad =ᵐ[
          volumeMeasureOn (openCubeSet Q)]
        (blockResponsePairHalfState
          (responseFramePlanarCoefficientField ν σ k) u w).potential) :
      let v := lemmaVAffinePotential (isOpenBoundedConvexDomain_openCubeSet Q) P.1 r
    let I := diagInterpolant Q m
    let η := squareQ3BasisMultiplier Q b σ L l
    ∃ hrow : MemLp (fun x => -(lemmaVPlanarRowField I η v x)) 2
        (normalizedCubeMeasure Q),
      pureFluxResponseGeneratorY (measurableSet_openCubeSet Q)
        (square_volume_pos Q)
        ν σ hν hσ P k
        (squareQ3Directions Q b L
          (@Encodable.encode whiteBasisIndex
            (Encodable.ofCountable whiteBasisIndex) l)) =
      responseEnergyUp
        (responseFrameEnergyData (measurableSet_openCubeSet Q)
          (square_volume_pos Q)
          ν σ hν hσ k)
        (scalarProjectionResidual Q ν σ hν hσ k
          (projectedSourceLoad Q hrow)) := by
  let U := openCubeSet Q
  let hU := isOpenBoundedConvexDomain_openCubeSet Q
  let hv := square_volume_pos Q
  let H := squareQ3Directions Q b L
    (@Encodable.encode whiteBasisIndex (Encodable.ofCountable whiteBasisIndex) l)
  let η := squareQ3BasisMultiplier Q b σ L l
  let ηraw := mainQ3DirectionW2 Q b L (whiteBasis l)
  let a := responseFramePlanarCoefficientField ν σ k
  let M := responseFrameMuOperatorSystemData hU.isOpen.measurableSet hv ν σ hν hσ k
  let X := M.toMuHilbertRealization.minimizerMap P
  let v := lemmaVAffinePotential hU P.1 r
  let I := diagInterpolant Q m
  have hfirst : (fun x => (hilbertBlockL2ToBlockL2 X x).1) =ᵐ[volumeMeasureOn U]
      v.grad := by
    filter_upwards [hrep, hgrad] with x hxrep hxgrad
    have hrepFirst := congrArg Prod.fst hxrep
    have hrepFirst' : (hilbertBlockL2ToBlockL2 X x).1 =
        (blockResponsePairHalfState a u w).potential x := by
      simpa [X, M, BlockState.eval] using hrepFirst
    exact hrepFirst'.trans hxgrad.symm
  let Factual := pureFluxResponseShearSourceField Q σ hσ H X
  have hFactual : MemLp Factual 2 (normalizedCubeMeasure Q) :=
    pureFluxResponseShearSourceField_memLp Q σ hσ H X
  have hactualRaw : Factual =ᵐ[volume.restrict U]
      (fun x => -((η.toFun x) • matVecMul responsePlanarJ (v.grad x))) := by
    filter_upwards [ae_restrict_mem (measurableSet_openCubeSet Q),
      responseShearL2Operator_toBlockL2_ae σ hσ H X, hfirst] with x hx hs hf
    have hcoef : responseCoefficientExtension H x / σ = η.toFun x :=
      squareQ3Directions_frameValue Q b σ L l hx
    change (hilbertBlockL2ToBlockL2 (responseShearL2Operator σ hσ H X) x).2 = _
    calc
      _ = (responseShearCorrection σ (responseCoefficientExtension H x)
          (hilbertBlockL2ToBlockL2 X x)).2 := by rw [hs]
      _ = -((responseCoefficientExtension H x / σ) •
          matVecMul responsePlanarJ ((hilbertBlockL2ToBlockL2 X x).1)) := rfl
      _ = -((η.toFun x) • matVecMul responsePlanarJ (v.grad x)) := by
          rw [← hcoef, hf]
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
  have hraw : MemLp
      (fun x => -((η.toFun x) • matVecMul responsePlanarJ (v.grad x))) 2
      (normalizedCubeMeasure Q) := squareNegativeShear_memLp η v hη
  have hzero : IsSolenoidalZeroNormalTraceOn U (fun x =>
      Factual x - -((η.toFun x) • matVecMul responsePlanarJ (v.grad x))) := by
    intro ψ
    have hdot : (fun x => vecDot
        (Factual x - -((η.toFun x) • matVecMul responsePlanarJ (v.grad x)))
        (ψ.grad x)) =ᵐ[volume.restrict U] 0 := by
      filter_upwards [hactualRaw] with x hx
      simp [hx, vecDot]
    rw [integral_congr_ae hdot]
    simp
  have hactualProjection : scalarProjectionResidual Q ν σ hν hσ k
      (projectedSourceLoad Q hFactual) = scalarProjectionResidual Q ν σ hν hσ k
      (projectedSourceLoad Q hraw) :=
    pureFlux_projectedSource_residual_eq_of_solenoidal_difference Q ν σ hν hσ k
      hFactual hraw hzero
  have hres : MemH10 U (v - I v).toFun :=
    diagInterpolant_affine_residual_memH10 Q m P.1 r
  have hrow : MemLp (fun x => -(lemmaVPlanarRowField I η v x)) 2
      (normalizedCubeMeasure Q) := by
    have hvec : MemVectorL2 U (lemmaVPlanarRowField I η v) :=
      lemmaVPlanarRowField_memL2 I η v hη hDη
    have hcoord (i : Fin 2) : MemLp
        (fun x => -(lemmaVPlanarRowField I η v x i)) 2
        (normalizedCubeMeasure Q) :=
      memLp_normalized_of_memL2On
        ((memScalarL2_coord_of_memVectorL2 hvec i).neg)
    exact memLp_pi_iff.mpr hcoord
  have hrowProjection : scalarProjectionResidual Q ν σ hν hσ k
      (projectedSourceLoad Q hraw) = scalarProjectionResidual Q ν σ hν hσ k
      (projectedSourceLoad Q hrow) :=
    pureFlux_projectedSource_residual_eq_of_lemmaV_lift Q ν σ hν hσ k
      I η v hres hη hDη hraw hrow
  refine ⟨hrow, ?_⟩
  rw [pureFluxResponseGeneratorY_eq_projectedSourceResidual Q ν σ hν hσ P k H hFactual,
    hactualProjection, hrowProjection]

/-- The actual uncentered q3 generator direction obeys the broken-mesh source
energy and first-potential estimates. Each tile uses its own physical inverse
history cap; the source field itself is the uncentered DIAG row of the affine
minimizer. -/
theorem square_q3_generator_tiled_source_bound
    (Q : TriadicCube 2) (ν σ b : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (L : {l : ℝ // 0 < l}) (l : whiteBasisIndex) (m : ℕ)
    (k : ResponseCoefficient (openCubeSet Q)) (P : BlockVec 2)
    (r : H10Function (openCubeSet Q))
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
    (hgrad : (lemmaVAffinePotential
        (isOpenBoundedConvexDomain_openCubeSet Q) P.1 r).grad =ᵐ[
          volumeMeasureOn (openCubeSet Q)]
        (blockResponsePairHalfState
          (responseFramePlanarCoefficientField ν σ k) u w).potential)
    (B : ℝ) (hB : 0 ≤ B)
    (hhist : ∀ U ∈ descendantsAtDepth Q m,
      lemmaVInverseHistory U (responseFramePlanarCoefficientField ν σ k)
        ((3 : ℝ)^(1/4:ℝ)) ≤ B) :
      let U := openCubeSet Q
    let v := lemmaVAffinePotential (isOpenBoundedConvexDomain_openCubeSet Q) P.1 r
    let I := diagInterpolant Q m
    let η := squareQ3BasisMultiplier Q b σ L l
    let F : Vec 2 → Vec 2 := fun x => -(lemmaVPlanarRowField I η v x)
    let Y := pureFluxResponseGeneratorY (measurableSet_openCubeSet Q)
      (square_volume_pos Q)
      ν σ hν hσ P k
      (squareQ3Directions Q b L
        (@Encodable.encode whiteBasisIndex
          (Encodable.ofCountable whiteBasisIndex) l))
    ∃ hF : MemLp F 2 (normalizedCubeMeasure Q),
      Y = responseEnergyUp (responseFrameEnergyData (measurableSet_openCubeSet Q)
        (square_volume_pos Q) ν σ hν hσ k)
        (scalarProjectionResidual Q ν σ hν hσ k (projectedSourceLoad Q hF)) ∧
      ∃ z : H10Function U,
        (fun x => (projectedSourceField Q ν σ hν hσ k hF x).1) =ᵐ[
          volumeMeasureOn U] z.toH1Function.grad ∧
        (scalarFrameRealization Q ν σ hν hσ k).energyBilin
          (scalarProjectionResidual Q ν σ hν hσ k (projectedSourceLoad Q hF))
          (scalarProjectionResidual Q ν σ hν hσ k (projectedSourceLoad Q hF)) ≤
            B * lemmaVTiledPositiveEnergy Q m F ∧
        Real.sqrt (lemmaVTiledWeakEnergy Q m z.toH1Function.grad) ≤
          (126/100)*B*Real.sqrt (lemmaVTiledPositiveEnergy Q m F) := by
  let U := openCubeSet Q
  let hU := isOpenBoundedConvexDomain_openCubeSet Q
  let hv := square_volume_pos Q
  let v := lemmaVAffinePotential hU P.1 r
  let I := diagInterpolant Q m
  let η := squareQ3BasisMultiplier Q b σ L l
  let H := squareQ3Directions Q b L
    (@Encodable.encode whiteBasisIndex (Encodable.ofCountable whiteBasisIndex) l)
  let F : Vec 2 → Vec 2 := fun x => -(lemmaVPlanarRowField I η v x)
  let Y := pureFluxResponseGeneratorY (measurableSet_openCubeSet Q) hv
      ν σ hν hσ P k H
  have hpos : ∀ U' ∈ descendantsAtDepth Q m, ∀ i : Fin 2,
      Summable (fun j : ℕ => (Real.sqrt 3)^(j+1) *
        energy U' (cubeIncrement U' (j+1) (fun x => F x i))) := by
    intro U' hU' i
    have hrow : Summable (fun j : ℕ => (Real.sqrt 3)^(j+1) *
        energy U' (cubeIncrement U' (j+1) (fun x =>
          lemmaVPlanarRowField I η v x i))) := by
      simpa [v, I, η] using
        square_q3_row_positive_series Q b σ L m P.1 r U' hU' l i
    change Summable (fun j : ℕ => (Real.sqrt 3)^(j+1) *
      energy U' (cubeIncrement U' (j+1) (fun x =>
        -(lemmaVPlanarRowField I η v x i))))
    simpa only [cubeIncrement_neg, energy_neg] using hrow
  obtain ⟨hrow, hgenerator⟩ :=
    square_q3_generator_source_projection
      Q ν σ b hν hσ L l m k P r u w hrep hgrad
  have hF : MemLp F 2 (normalizedCubeMeasure Q) := by
    simpa [F, v, I, η] using hrow
  have hgenerator' : Y = responseEnergyUp
      (responseFrameEnergyData (measurableSet_openCubeSet Q) hv ν σ hν hσ k)
      (scalarProjectionResidual Q ν σ hν hσ k (projectedSourceLoad Q hF)) := by
    simpa [Y, hv, H] using hgenerator
  obtain ⟨z, hz⟩ := projectedSource_firstPotential_exists Q ν σ hν hσ k hF
  have hfirst : (fun x => (projectedSourceField Q ν σ hν hσ k hF x).1) =ᵐ[
      volumeMeasureOn U] z.toH1Function.grad := by
    simpa using hz
  have htile := pureFlux_projectedSource_tiled_bound Q m ν σ hν hσ k hF hpos
    z hfirst B hB hhist
  have hnorm : ‖Y‖ ^ 2 = (scalarFrameRealization Q ν σ hν hσ k).energyBilin
      (scalarProjectionResidual Q ν σ hν hσ k (projectedSourceLoad Q hF))
      (scalarProjectionResidual Q ν σ hν hσ k (projectedSourceLoad Q hF)) := by
    rw [hgenerator', energyCarrier_norm_sq]
    simp [responseEnergyUp_down, responseFrameEnergyData,
      responseEnergyHilbertData, scalarFrameRealization]
  have henergy : (scalarFrameRealization Q ν σ hν hσ k).energyBilin
      (scalarProjectionResidual Q ν σ hν hσ k (projectedSourceLoad Q hF))
      (scalarProjectionResidual Q ν σ hν hσ k (projectedSourceLoad Q hF)) ≤
        B * lemmaVTiledPositiveEnergy Q m F := by
    simpa [hnorm] using htile.1
  have hcap : (1/2:ℝ)+(3:ℝ)^(-(1/4:ℝ)) ≤ 126/100 := by
    have hh := pureFlux_half_gain_cap
    norm_num at hh ⊢
    exact le_of_lt hh
  have hfeedback : Real.sqrt (lemmaVTiledWeakEnergy Q m z.toH1Function.grad) ≤
      (126/100)*B*Real.sqrt (lemmaVTiledPositiveEnergy Q m F) := by
    calc
      _ ≤ (1/2+(3:ℝ)^(-(1/4:ℝ)))*B*
          Real.sqrt (lemmaVTiledPositiveEnergy Q m F) := htile.2
      _ ≤ (126/100)*B*Real.sqrt (lemmaVTiledPositiveEnergy Q m F) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hcap hB) (Real.sqrt_nonneg _)
  exact ⟨hF, hgenerator', z, hfirst, henergy, hfeedback⟩

end
end ASDExplicitGamma.Gaussian
