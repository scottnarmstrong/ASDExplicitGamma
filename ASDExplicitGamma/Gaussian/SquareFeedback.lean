module

public import ASDExplicitGamma.Gaussian.SquarePairing
public import ASDExplicitGamma.Gaussian.SquareEnergy

/-! Finite full-shell feedback contractions for the actual minimizer pair. -/

@[expose] public section
namespace ASDExplicitGamma.Gaussian
open Homogenization MeasureTheory ASDExplicitGamma.Inverse ASDExplicitGamma.Main
  ASDExplicitGamma.Model ASDExplicitGamma.Response ASDExplicitGamma.Triadic
  ASDExplicitGamma.Variational ASDExplicitGamma.Scalar ASDExplicitGamma.Numerics
open scoped BigOperators
noncomputable section

local instance squareFeedbackFiniteMeasure (Q : TriadicCube 2) :
    IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
  (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume

/-- The actual uncentered source column and distinct-potential row give the
physical finite feedback contraction with the same common minimizer pair. -/
theorem square_q3_cross_feedback_finite
    (Q : TriadicCube 2) (m : ℕ) (ν σ b : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (L : {l : ℝ // 0 < l}) (s : Finset whiteBasisIndex)
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
      let v := lemmaVAffinePotential (isOpenBoundedConvexDomain_openCubeSet Q) P.1 r
    let g : H1Function (openCubeSet Q) := (1/2:ℝ) • (w.toH1-u.toH1)
    let S := responseFrameEnergyBaseMinimizer (measurableSet_openCubeSet Q)
      (square_volume_pos Q) ν σ hν hσ k P
    let C := responseFrameEnergyShearFamily (measurableSet_openCubeSet Q)
      (square_volume_pos Q) ν σ hν hσ k
    |(∑ l ∈ s,
      inner ℝ S (C (squareQ3Directions Q b L
        (@Encodable.encode whiteBasisIndex (Encodable.ofCountable whiteBasisIndex) l))
        (pureFluxResponseGeneratorY (measurableSet_openCubeSet Q)
          (square_volume_pos Q)
          ν σ hν hσ P k (squareQ3Directions Q b L
            (@Encodable.encode whiteBasisIndex
              (Encodable.ofCountable whiteBasisIndex) l)))))| ≤
      (63/50:ℝ)*B*(|σ⁻¹| * |b|)^2*generatorKA (diagMeshRadius Q m/L.1)*
        generatorKB (diagMeshRadius Q m/L.1)*
        Real.sqrt (lemmaVTiledWeakEnergy Q m v.grad) *
        Real.sqrt (lemmaVTiledWeakEnergy Q m g.grad) := by
  let U := openCubeSet Q
  let hU := isOpenBoundedConvexDomain_openCubeSet Q
  let hv := square_volume_pos Q
  let v := lemmaVAffinePotential hU P.1 r
  let I := diagInterpolant Q m
  let g : H1Function U := (1/2:ℝ) • (w.toH1-u.toH1)
  let Smin := responseFrameEnergyBaseMinimizer (measurableSet_openCubeSet Q)
    hv ν σ hν hσ k P
  let C := responseFrameEnergyShearFamily (measurableSet_openCubeSet Q) hv ν σ hν hσ k
  let η (l : whiteBasisIndex) := squareQ3BasisMultiplier Q b σ L l
  let H (l : whiteBasisIndex) := squareQ3Directions Q b L
    (@Encodable.encode whiteBasisIndex (Encodable.ofCountable whiteBasisIndex) l)
  let Y (l : whiteBasisIndex) := pureFluxResponseGeneratorY
    (measurableSet_openCubeSet Q) hv ν σ hν hσ P k (H l)
  let sourcePositive (l : whiteBasisIndex) :=
    lemmaVTiledPositiveEnergy Q m (fun x => -(lemmaVPlanarRowField I (η l) v x))
  let sourceTrace := squareQ3RowEnergy Q b σ L m P.1 r
  let sourceCoeff := |σ⁻¹| * |b| * generatorKA (diagMeshRadius Q m/L.1)
  let gWeak := lemmaVTiledWeakEnergy Q m g.grad
  have htrace := square_q3_row_source_trace_bound Q b σ L m P.1 r
  have hsourceData (l : whiteBasisIndex) :
      ∃ z : H10Function U,
        (fun x => (hilbertBlockL2ToBlockL2 (Y l).down x).1) =ᵐ[
          volumeMeasureOn U] z.toH1Function.grad ∧
        Real.sqrt (lemmaVTiledWeakEnergy Q m z.toH1Function.grad) ≤
          (126/100)*B*Real.sqrt (sourcePositive l) := by
    obtain ⟨hF, hgen, z, hfirst, henergy, hfeedback⟩ :=
      square_q3_generator_tiled_source_bound
        Q ν σ b hν hσ L l m k P r u w hrep hgrad B hB hhist
    refine ⟨z, ?_, ?_⟩
    · have hgen' : Y l = responseEnergyUp
          (responseFrameEnergyData (measurableSet_openCubeSet Q) hv ν σ hν hσ k)
          (scalarProjectionResidual Q ν σ hν hσ k (projectedSourceLoad Q hF)) := by
        simpa [Y, H] using hgen
      rw [hgen']
      simpa [Y, H, responseEnergyUp_down, scalarProjectionResidual,
        scalarResidualField, projectedSourceField] using hfirst
    · simpa [sourcePositive, v, I, η] using hfeedback
  choose z hfirst hfeedback using hsourceData
  have hRn (l : whiteBasisIndex) : 0 ≤ sourceTrace l := by
    unfold sourceTrace squareQ3RowEnergy descendantsAverage
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
    dsimp [sourcePositive, sourceTrace, squareQ3RowEnergy,
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
  have hδ0 : 0 ≤ diagMeshRadius Q m/L.1 :=
    div_nonneg (diagMeshRadius_pos Q m).le L.2.le
  have hsourceCoeffNonneg : 0 ≤ sourceCoeff := by
    have hA : 0 ≤ generatorKA (diagMeshRadius Q m/L.1) := by
      unfold generatorKA
      positivity
    exact mul_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _)) hA
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
  let Sraw := q3DistinctRow whiteBasis s b L Q m z
  let Sphys : Vec 2 → Vec 2 := fun x => ∑ l ∈ s,
    lemmaVPlanarRowField I (η l) (z l).toH1Function x
  have hSscale : Sphys = fun x => (σ⁻¹:ℝ) • Sraw x := by
    funext x
    dsimp [Sphys, Sraw, q3DistinctRow, η,
      squareQ3BasisMultiplier]
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
  have hrow := q3_distinct_h10_row_generatorKB whiteBasis s b L Q m z
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
    have hp := square_q3_shear_pairing_eq_tiled_row
      Q ν σ b hν hσ L l m k P u w hrep (z l) (hfirst l)
    simpa [U, I, η, H, Y, Smin, C, g] using hp
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
              dsimp [η, squareQ3BasisMultiplier]
              simpa only [H1Function.smul_toFun, smul_eq_mul] using
                (hηraw l).const_mul (σ⁻¹)
            have hDη (j : Fin 2) : MemLp (fun x => (η l).grad x j)
                (⊤ : ENNReal) (volume.restrict U) := by
              dsimp [η, squareQ3BasisMultiplier]
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
  have hrowBound : Real.sqrt (lemmaVTiledPositiveEnergy Q m Sraw) ≤
      |b| * generatorKB (diagMeshRadius Q m/L.1) *
        Real.sqrt (∑ l ∈ s, lemmaVTiledWeakEnergy Q m (z l).toH1Function.grad) := by
    simpa only [mul_comm, mul_left_comm, mul_assoc] using hrow.2
  have hcross : |(∑ l ∈ s, inner ℝ Smin (C (H l) (Y l)))| ≤
      (63/50:ℝ)*B*(|σ⁻¹| * |b|)^2*generatorKA (diagMeshRadius Q m/L.1)*
        generatorKB (diagMeshRadius Q m/L.1)*Real.sqrt (lemmaVTiledWeakEnergy Q m v.grad) *
          Real.sqrt gWeak := by
    rw [hsumPair, hscaleAvg, abs_mul]
    calc
      _ ≤ |σ⁻¹| *
          (Real.sqrt (lemmaVTiledWeakEnergy Q m g.grad) *
            Real.sqrt (lemmaVTiledPositiveEnergy Q m Sraw)) :=
        mul_le_mul_of_nonneg_left hdual (abs_nonneg (σ⁻¹))
      _ ≤ |σ⁻¹| *
          (Real.sqrt (lemmaVTiledWeakEnergy Q m g.grad) *
            (|b| * generatorKB (diagMeshRadius Q m/L.1)*
              Real.sqrt (∑ l ∈ s, lemmaVTiledWeakEnergy Q m (z l).toH1Function.grad))) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hrowBound
            (Real.sqrt_nonneg (lemmaVTiledWeakEnergy Q m g.grad)))
          (abs_nonneg (σ⁻¹))
      _ ≤ (63/50:ℝ)*B*(|σ⁻¹| * |b|)^2*generatorKA (diagMeshRadius Q m/L.1)*
          generatorKB (diagMeshRadius Q m/L.1)*Real.sqrt (lemmaVTiledWeakEnergy Q m v.grad) *
            Real.sqrt gWeak := by
        have hA : 0 ≤ generatorKA (diagMeshRadius Q m/L.1) := by
          unfold generatorKA
          positivity
        have hBcov : 0 ≤ generatorKB (diagMeshRadius Q m/L.1) := by
          unfold generatorKB
          positivity
        have hc : 0 ≤ |σ⁻¹| * |b| := mul_nonneg (abs_nonneg _) (abs_nonneg _)
        have hfeedbackCoeff : (126/100:ℝ) = (63/50:ℝ) := by norm_num
        calc
          _ ≤ |σ⁻¹| * (Real.sqrt gWeak *
              (|b| * generatorKB (diagMeshRadius Q m/L.1) *
                ((126/100:ℝ)*B*sourceCoeff*
                  Real.sqrt (lemmaVTiledWeakEnergy Q m v.grad)))) := by
            apply mul_le_mul_of_nonneg_left
            · apply mul_le_mul_of_nonneg_left
              · exact mul_le_mul_of_nonneg_left hZsqrt
                  (mul_nonneg (abs_nonneg _) hBcov)
              · exact Real.sqrt_nonneg gWeak
            · exact abs_nonneg _
          _ = (63/50:ℝ)*B*(|σ⁻¹| * |b|)^2*generatorKA (diagMeshRadius Q m/L.1)*
                generatorKB (diagMeshRadius Q m/L.1)*
                Real.sqrt (lemmaVTiledWeakEnergy Q m v.grad) * Real.sqrt gWeak := by
            rw [hfeedbackCoeff]
            dsimp [sourceCoeff]
            ring
  simpa [v, g, Smin, C, H, Y, gWeak] using hcross


end
end ASDExplicitGamma.Gaussian
