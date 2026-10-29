module

public import ASDExplicitGamma.Native.ParentBoundaryCommonGeneratorTiled
public import ASDExplicitGamma.Native.ParentBoundaryCommonGeneratorPairing
public import ASDExplicitGamma.Native.ParentBoundaryCommonCenterHilbertBound
public import ASDExplicitGamma.Native.ParentBoundaryCommonDistinctRow
public import ASDExplicitGamma.Triadic.PlanarDirectionScalar

/-! Full common-center feedback from the actual direction-dependent source potentials. -/

@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Gaussian Main Model Response Triadic Variational Scalar Inverse
open scoped ENNReal BigOperators
noncomputable section

local instance parentCommonFeedbackFiniteMeasure (Q : TriadicCube 2) :
    IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
  (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume

/-- Actual finite covariance feedback. Every first corrector is constructed
from the corresponding projected source, and the common original center is
retained throughout the sum. -/
theorem parent_boundary_common_generator_cross_feedback
    (P0 Q : TriadicCube 2) (hQP : cubeSet Q ⊆ cubeSet P0)
    (ν σ b : ℝ) (hν : 0 < ν) (hσ : 0 < σ) (L : {l : ℝ // 0 < l}) (m : ℕ)
    (s : Finset whiteBasisIndex)
    (P : BlockVec 2) (k : ResponseCoefficient (openCubeSet Q))
    (H : whiteBasisIndex → ResponseCoefficient (openCubeSet Q))
    (r : H10Function (openCubeSet Q))
    (hlink : ∀ l,(parentBoundaryCommonBasisMultiplier P0 Q b σ L l).toFun =ᵐ[
      volume.restrict (openCubeSet Q)] fun x => responseCoefficientExtension (H l) x / σ)
    (hbase : (fun x => (hilbertBlockL2ToBlockL2
      ((responseFrameMuOperatorSystemData (measurableSet_openCubeSet Q)
        (by rw [volume_openCubeSet_toReal]; exact cubeVolume_pos Q) ν σ hν hσ k).toMuHilbertRealization.minimizerMap P) x).1) =ᵐ[
      volumeMeasureOn (openCubeSet Q)]
        (lemmaVAffinePotential (isOpenBoundedConvexDomain_openCubeSet Q) P.1 r).grad)
    (u : AHarmonicFunction (responseFramePlanarCoefficientField ν σ k) (openCubeSet Q))
    (w : AHarmonicFunction (adjointCoeffField (responseFramePlanarCoefficientField ν σ k))
      (openCubeSet Q))
    (hrep : hilbertBlockL2ToBlockL2
      ((responseFrameMuOperatorSystemData (measurableSet_openCubeSet Q)
        (by rw [volume_openCubeSet_toReal]; exact cubeVolume_pos Q) ν σ hν hσ k).toMuHilbertRealization.minimizerMap P) =ᵐ[
          volumeMeasureOn (openCubeSet Q)]
      (fun x => (blockResponsePairHalfState (responseFramePlanarCoefficientField ν σ k) u w).eval x))
    (B : ℝ) (hB : 0 ≤ B)
    (hhist : ∀ U ∈ descendantsAtDepth Q m,lemmaVInverseHistory U
      (responseFramePlanarCoefficientField ν σ k) ((3:ℝ)^(1/4:ℝ)) ≤ B) :
    let v := lemmaVAffinePotential (isOpenBoundedConvexDomain_openCubeSet Q) P.1 r
    let g : H1Function (openCubeSet Q) := (1/2:ℝ) • (w.toH1-u.toH1)
    let S := responseFrameEnergyBaseMinimizer (measurableSet_openCubeSet Q)
      (by rw [volume_openCubeSet_toReal]; exact cubeVolume_pos Q) ν σ hν hσ k P
    let C := responseFrameEnergyShearFamily (measurableSet_openCubeSet Q)
      (by rw [volume_openCubeSet_toReal]; exact cubeVolume_pos Q) ν σ hν hσ k
    |(∑ l ∈ s,inner ℝ S (C (H l) (pureFluxResponseGeneratorY (measurableSet_openCubeSet Q)
        (by rw [volume_openCubeSet_toReal]; exact cubeVolume_pos Q) ν σ hν hσ P k (H l))))| ≤
      (63/50:ℝ)*B*|σ⁻¹|^2*parentBoundaryCommonRowCoefficient P0 Q b L m*
        parentBoundaryCommonFeedbackCoefficient P0 Q b L m*
        Real.sqrt (lemmaVTiledWeakEnergy Q m v.grad)*Real.sqrt (lemmaVTiledWeakEnergy Q m g.grad) := by
  let U := openCubeSet Q
  let hU := isOpenBoundedConvexDomain_openCubeSet Q
  let hv : 0 < (volume U).toReal := by rw [volume_openCubeSet_toReal]; exact cubeVolume_pos Q
  let v := lemmaVAffinePotential hU P.1 r
  let I := diagInterpolant Q m
  let g : H1Function U := (1/2:ℝ) • (w.toH1-u.toH1)
  let Smin := responseFrameEnergyBaseMinimizer (measurableSet_openCubeSet Q)
    hv ν σ hν hσ k P
  let C := responseFrameEnergyShearFamily (measurableSet_openCubeSet Q) hv ν σ hν hσ k
  let η (l : whiteBasisIndex) := parentBoundaryCommonBasisMultiplier P0 Q b σ L l
  let Y (l : whiteBasisIndex) := pureFluxResponseGeneratorY
    (measurableSet_openCubeSet Q) hv ν σ hν hσ P k (H l)
  let sourcePositive (l : whiteBasisIndex) :=
    lemmaVTiledPositiveEnergy Q m (fun x => -(lemmaVPlanarRowField I (η l) v x))
  let sourceTrace := parentBoundaryCommonRowEnergy P0 Q b σ L m P.1 r
  let sourceCoeff := |σ⁻¹| * parentBoundaryCommonRowCoefficient P0 Q b L m
  let gWeak := lemmaVTiledWeakEnergy Q m g.grad
  have htrace := parent_boundary_common_row_trace_bound P0 Q hQP b σ L m P.1 r
  have hsourceData (l : whiteBasisIndex) :
      ∃ z : H10Function U,
        (fun x => (hilbertBlockL2ToBlockL2 (Y l).down x).1) =ᵐ[
          volumeMeasureOn U] z.toH1Function.grad ∧
        Real.sqrt (lemmaVTiledWeakEnergy Q m z.toH1Function.grad) ≤
          (126/100)*B*Real.sqrt (sourcePositive l) := by
    obtain ⟨hF, hgen, z, hfirst, henergy, hfeedback⟩ :=
      parent_boundary_common_generator_tiled_source
        P0 Q hQP ν σ b hν hσ L m P k l (H l) r (hlink l) hbase B hB hhist
    refine ⟨z, ?_, ?_⟩
    · have hgen' : Y l = responseEnergyUp
          (responseFrameEnergyData (measurableSet_openCubeSet Q) hv ν σ hν hσ k)
          (scalarProjectionResidual Q ν σ hν hσ k (projectedSourceLoad Q hF)) := by
        simpa [Y] using hgen
      rw [hgen']
      simpa [Y,responseEnergyUp_down, scalarProjectionResidual,
        scalarResidualField, projectedSourceField] using hfirst
    · simpa [sourcePositive,v,I,η] using hfeedback
  choose z hfirst hfeedback using hsourceData
  have hRn (l : whiteBasisIndex) : 0 ≤ sourceTrace l := by
    unfold sourceTrace parentBoundaryCommonRowEnergy descendantsAverage
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
    dsimp [sourcePositive, sourceTrace, parentBoundaryCommonRowEnergy,
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
    have hm := (diagMeshRadius_pos Q m).le
    dsimp [sourceCoeff,parentBoundaryCommonRowCoefficient]
    positivity
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
  let Sraw := parentBoundaryCommonDistinctRow whiteBasis s b L P0 Q m z
  let Sphys : Vec 2 → Vec 2 := fun x => ∑ l ∈ s,
    lemmaVPlanarRowField I (η l) (z l).toH1Function x
  have hSscale : Sphys = fun x => (σ⁻¹:ℝ) • Sraw x := by
    funext x
    dsimp [Sphys, Sraw, parentBoundaryCommonDistinctRow, η,
      parentBoundaryCommonBasisMultiplier]
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro l hl
    exact congrFun (pureFluxPlanarRowField_smul I
      (parentBoundaryCommonQ3Direction P0 Q b L (whiteBasis l)).value
      (z l).toH1Function (σ⁻¹)) x
  have hηraw (l : whiteBasisIndex) :
      MemLp ((parentBoundaryCommonQ3Direction P0 Q b L (whiteBasis l)).value.toFun)
        (⊤ : ENNReal) (volume.restrict U) :=
    (parentBoundaryCommonQ3Direction P0 Q b L (whiteBasis l)).value_memLp_top
  have hDηraw (l : whiteBasisIndex) (j : Fin 2) :
      MemLp (fun x => (parentBoundaryCommonQ3Direction P0 Q b L
        (whiteBasis l)).value.grad x j) (⊤ : ENNReal) (volume.restrict U) :=
    (parentBoundaryCommonQ3Direction P0 Q b L (whiteBasis l)).gradient_memLp_top_volume j
  have hSrawMem : MemVectorL2 U Sraw := by
    change MemLp (fun x => ∑ l ∈ s,
      lemmaVPlanarRowField I (parentBoundaryCommonQ3Direction P0 Q b L
        (whiteBasis l)).value (z l).toH1Function x) 2 (volumeMeasureOn U)
    exact memLp_finsetSum s fun l hl =>
      lemmaVPlanarRowField_memL2 I
        (parentBoundaryCommonQ3Direction P0 Q b L (whiteBasis l)).value
        (z l).toH1Function (hηraw l) (hDηraw l)
  have hSrawCoord (j : Fin 2) : MemLp (fun x => Sraw x j) 2
      (normalizedCubeMeasure Q) :=
    memL2On_openCubeSet_normalizedCubeMeasure (hSrawMem.eval j)
  have hgCoord (j : Fin 2) : MemLp (fun x => g.grad x j) 2
      (normalizedCubeMeasure Q) := g.grad_memL2_normalizedCubeMeasure j
  have hrow := parent_boundary_common_distinct_h10_row_bound
    whiteBasis s b L P0 Q m hQP z
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
    have hp := parent_boundary_common_generator_shear_pairing Q ν σ hν hσ m k (H l) P
      ((parentBoundaryCommonQ3Direction P0 Q b L (whiteBasis l)).smul σ⁻¹)
      (hlink l) u w hrep (z l) (hfirst l)
    have hηvalue : ((parentBoundaryCommonQ3Direction P0 Q b L (whiteBasis l)).smul σ⁻¹).value = η l := rfl
    rw [hηvalue] at hp
    simpa only [U,I,Y,Smin,C,g,H1Function.smul_grad,H1Function.sub_grad,Pi.smul_apply,Pi.sub_apply] using hp
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
              dsimp [η, parentBoundaryCommonBasisMultiplier]
              simpa only [H1Function.smul_toFun, smul_eq_mul] using
                (hηraw l).const_mul (σ⁻¹)
            have hDη (j : Fin 2) : MemLp (fun x => (η l).grad x j)
                (⊤ : ENNReal) (volume.restrict U) := by
              dsimp [η, parentBoundaryCommonBasisMultiplier]
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
      parentBoundaryCommonFeedbackCoefficient P0 Q b L m *
        Real.sqrt (∑ l ∈ s,lemmaVTiledWeakEnergy Q m (z l).toH1Function.grad) := hrow.2
  have hcross : |(∑ l ∈ s, inner ℝ Smin (C (H l) (Y l)))| ≤
      (63/50:ℝ)*B*|σ⁻¹|^2*parentBoundaryCommonRowCoefficient P0 Q b L m*
        parentBoundaryCommonFeedbackCoefficient P0 Q b L m*Real.sqrt (lemmaVTiledWeakEnergy Q m v.grad) *
          Real.sqrt gWeak := by
    rw [hsumPair, hscaleAvg, abs_mul]
    calc
      _ ≤ |σ⁻¹| *
          (Real.sqrt (lemmaVTiledWeakEnergy Q m g.grad) *
            Real.sqrt (lemmaVTiledPositiveEnergy Q m Sraw)) :=
        mul_le_mul_of_nonneg_left hdual (abs_nonneg (σ⁻¹))
      _ ≤ |σ⁻¹| *
          (Real.sqrt (lemmaVTiledWeakEnergy Q m g.grad) *
            (parentBoundaryCommonFeedbackCoefficient P0 Q b L m*
              Real.sqrt (∑ l ∈ s, lemmaVTiledWeakEnergy Q m (z l).toH1Function.grad))) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hrowBound
            (Real.sqrt_nonneg (lemmaVTiledWeakEnergy Q m g.grad)))
          (abs_nonneg (σ⁻¹))
      _ ≤ (63/50:ℝ)*B*|σ⁻¹|^2*parentBoundaryCommonRowCoefficient P0 Q b L m*
          parentBoundaryCommonFeedbackCoefficient P0 Q b L m*Real.sqrt (lemmaVTiledWeakEnergy Q m v.grad) *
            Real.sqrt gWeak := by
        have hBcov : 0 ≤ parentBoundaryCommonFeedbackCoefficient P0 Q b L m := by
          have hm := (diagMeshRadius_pos Q m).le
          unfold parentBoundaryCommonFeedbackCoefficient
          positivity
        have hfeedbackCoeff : (126/100:ℝ) = (63/50:ℝ) := by norm_num
        calc
          _ ≤ |σ⁻¹| * (Real.sqrt gWeak *
              (parentBoundaryCommonFeedbackCoefficient P0 Q b L m *
                ((126/100:ℝ)*B*sourceCoeff*
                  Real.sqrt (lemmaVTiledWeakEnergy Q m v.grad)))) := by
            apply mul_le_mul_of_nonneg_left
            · apply mul_le_mul_of_nonneg_left
              · exact mul_le_mul_of_nonneg_left hZsqrt
                  hBcov
              · exact Real.sqrt_nonneg gWeak
            · exact abs_nonneg _
          _ = (63/50:ℝ)*B*|σ⁻¹|^2*parentBoundaryCommonRowCoefficient P0 Q b L m*
                parentBoundaryCommonFeedbackCoefficient P0 Q b L m*
                Real.sqrt (lemmaVTiledWeakEnergy Q m v.grad) * Real.sqrt gWeak := by
            rw [hfeedbackCoeff]
            dsimp [sourceCoeff]
            ring
  simpa [v,g,Smin,C,Y,gWeak] using hcross

end
end ASDExplicitGamma.Native
