module

public import ASDExplicitGamma.Main.InverseLowerCenteredProjectionTrace
public import ASDExplicitGamma.Inverse.PureFluxGeneratorCenteredYTrace
public import ASDExplicitGamma.Inverse.PureFluxGeneratorDirectionBridge
public import ASDExplicitGamma.Inverse.PureFluxGeneratorTraceLimit

/-! Summability of the actual centered q3 signed feedback coefficients. -/

@[expose] public section

open Homogenization MeasureTheory ASDExplicitGamma.Gaussian ASDExplicitGamma.Inverse
  ASDExplicitGamma.Response ASDExplicitGamma.Triadic ASDExplicitGamma.Variational

namespace ASDExplicitGamma.Main

/-- The signed centered q3 shear-pairing coefficients are summable. This
follows from the exact source decomposition and summability of its two square
terms and its Hessian trace. -/
theorem main_q3_centered_feedback_pairing_summable
    (n : ℤ) (q i m : ℕ) (ν σ b B : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (L : {l : ℝ // 0 < l})
    (hρ : cubeScaleFactor (originCube 2 n)/L.1 = pureFluxCovarianceRho q i)
    (hδ : diagMeshRadius (originCube 2 n) m/L.1 = pureFluxCovarianceDelta q i)
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
    (hB : 0 ≤ B)
    (hhist : ∀ U ∈ descendantsAtDepth (originCube 2 n) m,
      lemmaVInverseHistory U (responseFramePlanarCoefficientField ν σ k)
        ((3 : ℝ)^(1/4:ℝ)) ≤ B) :
    let Q := originCube 2 n
    let H (l : whiteBasisIndex) := pureFluxMainCubeQ3CenteredResponseCoefficient n b L
      (@Encodable.encode whiteBasisIndex
        (Encodable.ofCountable whiteBasisIndex) l)
    let S := responseFrameEnergyBaseMinimizer
      (measurableSet_openCubeSet Q)
      (volume_openCubeSet_originCube_toReal_pos (d := 2) n) ν σ hν hσ k P
    let C := responseFrameEnergyShearFamily
      (measurableSet_openCubeSet Q)
      (volume_openCubeSet_originCube_toReal_pos (d := 2) n) ν σ hν hσ k
    let Y (l : whiteBasisIndex) := pureFluxResponseGeneratorY
      (measurableSet_openCubeSet Q)
      (volume_openCubeSet_originCube_toReal_pos (d := 2) n)
      ν σ hν hσ P k (H l)
    Summable (fun l => inner ℝ S (C (H l) (Y l))) := by
  classical
  intro Q H S C Y
  let hU := measurableSet_openCubeSet Q
  let hv := volume_openCubeSet_originCube_toReal_pos (d := 2) n
  let Hnat (j : ℕ) := pureFluxMainCubeQ3CenteredResponseCoefficient n b L j
  let Z (l : whiteBasisIndex) :=
    pureFluxResponseGeneratorZ hU hv ν σ hν hσ P k (H l)
  let G (l : whiteBasisIndex) :=
    pureFluxResponseHessianDiagonal hU hv ν σ hν hσ P k (H l)
  let F (l : whiteBasisIndex) := inner ℝ S (C (H l) (Y l))
  let Ysq (l : whiteBasisIndex) := ‖Y l‖^2
  let Zsq (l : whiteBasisIndex) := ‖Z l‖^2
  let E := responseFrameEnergyObservable hU hv ν σ hν hσ P
  have hYsum := pureFluxMainQ3CenteredGeneratorY_covariance_trace_bound
    n q i m ν σ b hν hσ L k P r u w hrep hgrad hρ hδ B hB hhist
  have hZsum := main_q3_centered_projected_adjoint_source_trace_bound
    n q i m ν σ b hν hσ L hρ hδ k P u w hrep
  have hEd : ContDiff ℝ 2 E :=
    responseFrameEnergyObservable_contDiff _ _ ν σ hν hσ P
  have hdirs := pureFluxMainCubeQ3CenteredResponseCoefficient_summable n b L
  have hsecond (j : ℕ) : secondDirectionalDerivative E k (Hnat j) =
      pureFluxResponseHessianDiagonal hU hv ν σ hν hσ P k (Hnat j) := by
    unfold secondDirectionalDerivative pureFluxResponseHessianDiagonal
    exact responseFrameEnergyObservable_hessian _ _ ν σ hν hσ P k _ _
  have hsecondSum := pureFlux_secondDirectionalDerivative_summable E hEd Hnat hdirs k
  have hGSNat : Summable (fun j => pureFluxResponseHessianDiagonal
      hU hv ν σ hν hσ P k (Hnat j)) := by
    simpa only [Hnat, hsecond] using hsecondSum
  have hGsum : Summable G := by
    have hcomp := hGSNat.comp_injective
      (@Encodable.encode_injective whiteBasisIndex
        (Encodable.ofCountable whiteBasisIndex))
    simpa only [G, H, Hnat, Function.comp_def] using hcomp
  have hYsq : Summable Ysq := by
    simpa only [Ysq, Y] using hYsum.1
  have hZsq : Summable Zsq := by
    simpa only [Zsq, Z] using hZsum.1
  have hidentity (l : whiteBasisIndex) :
      (1 / 2 : ℝ) * G l = Ysq l + 2 * F l - Zsq l := by
    simpa only [G, Ysq, Zsq, F, Y, Z, H] using
      pureFluxResponseHessianDiagonal_source_identity hU hv ν σ hν hσ P k (H l)
  have hterm (l : whiteBasisIndex) :
      F l = (1 / 4 : ℝ) * G l - (1 / 2 : ℝ) * Ysq l +
        (1 / 2 : ℝ) * Zsq l := by
    linarith [hidentity l]
  have hcombined : Summable (fun l : whiteBasisIndex =>
      (1 / 4 : ℝ) * G l - (1 / 2 : ℝ) * Ysq l +
        (1 / 2 : ℝ) * Zsq l) := by
    exact (hGsum.mul_left (1 / 4 : ℝ)).sub
      (hYsq.mul_left (1 / 2 : ℝ)) |>.add (hZsq.mul_left (1 / 2 : ℝ))
  change Summable F
  rw [show F = fun l : whiteBasisIndex =>
      (1 / 4 : ℝ) * G l - (1 / 2 : ℝ) * Ysq l +
        (1 / 2 : ℝ) * Zsq l by
    funext l
    exact hterm l]
  exact hcombined

/-- The finite centered feedback estimate passes to the full encoded
covariance trace with its exact source-row coefficient. -/
theorem main_q3_centered_feedback_pairing_tsum_bound
    (n : ℤ) (q i m : ℕ) (ν σ b B : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (L : {l : ℝ // 0 < l})
    (hρ : cubeScaleFactor (originCube 2 n)/L.1 = pureFluxCovarianceRho q i)
    (hδ : diagMeshRadius (originCube 2 n) m/L.1 = pureFluxCovarianceDelta q i)
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
    (hB : 0 ≤ B)
    (hhist : ∀ U ∈ descendantsAtDepth (originCube 2 n) m,
      lemmaVInverseHistory U (responseFramePlanarCoefficientField ν σ k)
        ((3 : ℝ)^(1/4:ℝ)) ≤ B) :
    let Q := originCube 2 n
    let H (l : whiteBasisIndex) := pureFluxMainCubeQ3CenteredResponseCoefficient n b L
      (@Encodable.encode whiteBasisIndex
        (Encodable.ofCountable whiteBasisIndex) l)
    let S := responseFrameEnergyBaseMinimizer
      (measurableSet_openCubeSet Q)
      (volume_openCubeSet_originCube_toReal_pos (d := 2) n) ν σ hν hσ k P
    let C := responseFrameEnergyShearFamily
      (measurableSet_openCubeSet Q)
      (volume_openCubeSet_originCube_toReal_pos (d := 2) n) ν σ hν hσ k
    let Y (l : whiteBasisIndex) := pureFluxResponseGeneratorY
      (measurableSet_openCubeSet Q)
      (volume_openCubeSet_originCube_toReal_pos (d := 2) n)
      ν σ hν hσ P k (H l)
    |∑' l : whiteBasisIndex, inner ℝ S (C (H l) (Y l))| ≤
      (63/50:ℝ)*B*(abs σ⁻¹*abs b)^2*pureFluxCovarianceA q i*
        pureFluxCovarianceB q i*
        Real.sqrt (lemmaVTiledWeakEnergy Q m
          (lemmaVAffinePotential (isOpenBoundedConvexDomain_openCubeSet Q) P.1 r).grad)*
        Real.sqrt (lemmaVTiledWeakEnergy Q m
          ((1/2:ℝ) • (w.toH1-u.toH1)).grad) := by
  classical
  intro Q H S C Y
  let F (l : whiteBasisIndex) := inner ℝ S (C (H l) (Y l))
  let v := lemmaVAffinePotential (isOpenBoundedConvexDomain_openCubeSet Q) P.1 r
  let g : H1Function (openCubeSet Q) := (1/2:ℝ) • (w.toH1-u.toH1)
  let Wv := lemmaVTiledWeakEnergy Q m v.grad
  let Wg := lemmaVTiledWeakEnergy Q m g.grad
  let K := (63/50:ℝ)*B*(abs σ⁻¹*abs b)^2*pureFluxCovarianceA q i*
    pureFluxCovarianceB q i*Real.sqrt Wv*Real.sqrt Wg
  have hFsum : Summable F := by
    simpa only [F, Q, H, S, C, Y] using
      main_q3_centered_feedback_pairing_summable
        n q i m ν σ b B hν hσ L hρ hδ k P r u w hrep hgrad hB hhist
  have hcoef : 0 ≤ (63/50:ℝ)*B*(abs σ⁻¹*abs b)^2*
      pureFluxCovarianceA q i*pureFluxCovarianceB q i := by
    have hrows := pureFlux_covariance_rows_order q i
    have hA : 0 ≤ pureFluxCovarianceA q i := hrows.1.trans hrows.2
    have hBcov : 0 ≤ pureFluxCovarianceB q i := hrows.1
    have hbase : 0 ≤ (63/50:ℝ) * B := mul_nonneg (by norm_num) hB
    have hsquare : 0 ≤ (abs σ⁻¹ * abs b)^2 := sq_nonneg _
    exact mul_nonneg (mul_nonneg (mul_nonneg hbase hsquare) hA) hBcov
  have hK : 0 ≤ K := by
    dsimp [K]
    exact mul_nonneg (mul_nonneg hcoef (Real.sqrt_nonneg _))
      (Real.sqrt_nonneg _)
  have hfinite (s : Finset whiteBasisIndex) : |∑ l ∈ s, F l| ≤ K := by
    have h := pureFluxMainQ3CenteredGeneratorY_cross_feedback_finite
      n q i m ν σ b hν hσ L s k P r u w hrep hgrad hρ hδ B hB hhist
    simpa only [F, Q, H, S, C, Y, v, g, Wv, Wg, K] using h
  have hupperFinite (s : Finset whiteBasisIndex) :
      ∑ l ∈ s, F l ≤ K := (le_abs_self _).trans (hfinite s)
  have hupper := hFsum.tsum_le_of_sum_le hupperFinite
  have hnegativeFinite (s : Finset whiteBasisIndex) :
      ∑ l ∈ s, -F l ≤ K := by
    calc
      _ = -(∑ l ∈ s, F l) := by rw [Finset.sum_neg_distrib]
      _ ≤ |∑ l ∈ s, F l| := neg_le_abs _
      _ ≤ K := hfinite s
  have hnegative := hFsum.neg.tsum_le_of_sum_le hnegativeFinite
  have hlower : -(∑' l : whiteBasisIndex, F l) ≤ K := by
    simpa only [tsum_neg] using hnegative
  change |∑' l : whiteBasisIndex, F l| ≤ K
  exact abs_le.mpr ⟨by linarith [hlower], hupper⟩

end ASDExplicitGamma.Main

end
