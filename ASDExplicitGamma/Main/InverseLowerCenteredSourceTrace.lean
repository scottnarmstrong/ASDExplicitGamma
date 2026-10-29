module

public import ASDExplicitGamma.Main.InverseLowerCenteredFeedbackTrace
public import ASDExplicitGamma.Inverse.PureFluxGeneratorCenteredYTrace

/-! A single actual centered q3 covariance row has the expected source lower bound. -/

@[expose] public section

open Homogenization MeasureTheory ASDExplicitGamma.Gaussian ASDExplicitGamma.Inverse
  ASDExplicitGamma.Response ASDExplicitGamma.Triadic ASDExplicitGamma.Variational
open scoped BigOperators

namespace ASDExplicitGamma.Main

/-- The actual centered q3 source-component series is bounded below by its
projected-adjoint square loss and signed feedback row. The positive generator
square is retained as a nonnegative term. -/
theorem main_q3_centered_source_components_tsum_lower
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
    let Z (l : whiteBasisIndex) := pureFluxResponseGeneratorZ
      (measurableSet_openCubeSet Q)
      (volume_openCubeSet_originCube_toReal_pos (d := 2) n)
      ν σ hν hσ P k (H l)
    let F (l : whiteBasisIndex) := inner ℝ S (C (H l) (Y l))
    let v := lemmaVAffinePotential (isOpenBoundedConvexDomain_openCubeSet Q) P.1 r
    let g : H1Function (openCubeSet Q) := (1/2:ℝ) • (w.toH1-u.toH1)
    let Kf := (63/50:ℝ)*B*(abs σ⁻¹*abs b)^2*pureFluxCovarianceA q i*
      pureFluxCovarianceB q i*
      Real.sqrt (lemmaVTiledWeakEnergy Q m v.grad)*
      Real.sqrt (lemmaVTiledWeakEnergy Q m g.grad)
    let Kz := abs σ⁻¹*abs b*pureFluxCovarianceB q i*
      Real.sqrt (σ/ν)*Real.sqrt (lemmaVTiledWeakEnergy Q m g.grad)
    (∑' l : whiteBasisIndex, (‖Y l‖^2 + 2*F l - ‖Z l‖^2)) ≥
      -2*Kf-Kz^2 := by
  classical
  intro Q H S C Y Z F v g Kf Kz
  let Ysq (l : whiteBasisIndex) := ‖Y l‖^2
  let Zsq (l : whiteBasisIndex) := ‖Z l‖^2
  let T (l : whiteBasisIndex) := Ysq l + 2*F l - Zsq l
  have hYsum : Summable Ysq := by
    simpa only [Ysq, Q, Y, H] using
      (pureFluxMainQ3CenteredGeneratorY_covariance_trace_bound
        n q i m ν σ b hν hσ L k P r u w hrep hgrad hρ hδ B hB hhist).1
  have hZresult := main_q3_centered_projected_adjoint_source_trace_bound
    n q i m ν σ b hν hσ L hρ hδ k P u w hrep
  have hZsum : Summable Zsq := by
    simpa only [Zsq, Q, Z, H] using hZresult.1
  have hFsum : Summable F := by
    simpa only [Q, H, S, C, Y, F] using
      main_q3_centered_feedback_pairing_summable
        n q i m ν σ b B hν hσ L hρ hδ k P r u w hrep hgrad hB hhist
  have hTsum : Summable T := by
    dsimp [T]
    exact (hYsum.add (hFsum.mul_left 2)).sub hZsum
  have hYnonneg : ∀ l, 0 ≤ Ysq l := fun l => sq_nonneg _
  have hYtsum : 0 ≤ ∑' l, Ysq l := tsum_nonneg hYnonneg
  have hFbound : |∑' l, F l| ≤ Kf := by
    simpa only [Q, H, S, C, Y, F, v, g, Kf] using
      main_q3_centered_feedback_pairing_tsum_bound
        n q i m ν σ b B hν hσ L hρ hδ k P r u w hrep hgrad hB hhist
  have hZbound : (∑' l, Zsq l) ≤ Kz^2 := by
    simpa only [Q, H, Z, g, Kz] using hZresult.2
  have hTidentity : (∑' l, T l) =
      (∑' l, Ysq l) + 2*(∑' l, F l) - (∑' l, Zsq l) := by
    dsimp only [T]
    rw [(hYsum.add (hFsum.mul_left 2)).tsum_sub hZsum,
      hYsum.tsum_add (hFsum.mul_left 2), tsum_mul_left]
  have hFlower : -Kf ≤ ∑' l, F l := by
    have h := (abs_le.mp hFbound).1
    linarith
  calc
    (∑' l, T l) = (∑' l, Ysq l) + 2*(∑' l, F l) - (∑' l, Zsq l) := hTidentity
    _ ≥ -2*Kf-Kz^2 := by linarith

/-- The per-row source-component estimate is an estimate for the actual
fixed-frame response covariance Hessian trace. -/
theorem main_q3_centered_response_covariance_trace_lower
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
    let H (j : ℕ) := pureFluxMainCubeQ3CenteredResponseCoefficient n b L j
    let hU := measurableSet_openCubeSet Q
    let hvol := volume_openCubeSet_originCube_toReal_pos (d := 2) n
    let E := responseFrameEnergyObservable hU hvol ν σ hν hσ P
    let v := lemmaVAffinePotential (isOpenBoundedConvexDomain_openCubeSet Q) P.1 r
    let g : H1Function (openCubeSet Q) := (1/2:ℝ) • (w.toH1-u.toH1)
    let Wv := lemmaVTiledWeakEnergy Q m v.grad
    let Wg := lemmaVTiledWeakEnergy Q m g.grad
    (1/2:ℝ) * modelCovarianceTrace E H k ≥
      -2*((63/50:ℝ)*B*(abs σ⁻¹*abs b)^2*pureFluxCovarianceA q i*
        pureFluxCovarianceB q i*Real.sqrt Wv*Real.sqrt Wg) -
      (abs σ⁻¹*abs b*pureFluxCovarianceB q i*Real.sqrt (σ/ν)*Real.sqrt Wg)^2 := by
  classical
  intro Q H hU hvol E v g Wv Wg
  let Hnat (j : ℕ) := pureFluxMainCubeQ3CenteredResponseCoefficient n b L j
  let Henc (l : whiteBasisIndex) := Hnat
    (@Encodable.encode whiteBasisIndex
      (Encodable.ofCountable whiteBasisIndex) l)
  let Y (l : whiteBasisIndex) := pureFluxResponseGeneratorY hU hvol ν σ hν hσ P k (Henc l)
  let Z (l : whiteBasisIndex) := pureFluxResponseGeneratorZ hU hvol ν σ hν hσ P k (Henc l)
  let S := responseFrameEnergyBaseMinimizer hU hvol ν σ hν hσ k P
  let C := responseFrameEnergyShearFamily hU hvol ν σ hν hσ k
  let F (l : whiteBasisIndex) := inner ℝ S (C (Henc l) (Y l))
  have hsource := main_q3_centered_source_components_tsum_lower
    n q i m ν σ b B hν hσ L hρ hδ k P r u w hrep hgrad hB hhist
  have hsecond (j : ℕ) : secondDirectionalDerivative E
      k (Hnat j) = pureFluxResponseHessianDiagonal hU hvol ν σ hν hσ P
        k (Hnat j) := by
    unfold secondDirectionalDerivative pureFluxResponseHessianDiagonal
    exact responseFrameEnergyObservable_hessian hU hvol ν σ hν hσ P k (Hnat j) (Hnat j)
  have hdiagZero : pureFluxResponseHessianDiagonal hU hvol ν σ hν hσ P
      k 0 = 0 := by
    have hzero : secondDirectionalDerivative E k 0 =
        pureFluxResponseHessianDiagonal hU hvol ν σ hν hσ P k 0 := by
      unfold secondDirectionalDerivative pureFluxResponseHessianDiagonal
      exact responseFrameEnergyObservable_hessian hU hvol ν σ hν hσ P k 0 0
    rw [← hzero]
    simp [secondDirectionalDerivative]
  have htrace : modelCovarianceTrace E Hnat k =
      ∑' l : whiteBasisIndex,
        pureFluxResponseHessianDiagonal hU hvol ν σ hν hσ P k (Henc l) := by
    have hnat : modelCovarianceTrace E Hnat k =
        ∑' j : ℕ, pureFluxResponseHessianDiagonal hU hvol ν σ hν hσ P
          k (Hnat j) := by
      unfold modelCovarianceTrace
      apply tsum_congr
      intro j
      exact hsecond j
    rw [hnat]
    exact pureFlux_centered_directions_tsum_apply n b L
      (fun V => pureFluxResponseHessianDiagonal hU hvol ν σ hν hσ P k V)
      hdiagZero
  have hidentity (l : whiteBasisIndex) :
      (1/2:ℝ) * pureFluxResponseHessianDiagonal hU hvol ν σ hν hσ P
          k (Henc l) = ‖Y l‖^2 + 2*F l - ‖Z l‖^2 := by
    simpa only [Henc, Y, Z, S, C, F] using
      pureFluxResponseHessianDiagonal_source_identity hU hvol ν σ hν hσ P
        k (Henc l)
  have htraceSource : (1/2:ℝ) * modelCovarianceTrace E Hnat k =
      ∑' l : whiteBasisIndex, (‖Y l‖^2 + 2*F l - ‖Z l‖^2) := by
    rw [htrace, ← tsum_mul_left]
    apply tsum_congr
    intro l
    exact hidentity l
  dsimp only [Hnat, H, E, v, g, Wv, Wg] at hsource ⊢
  rw [htraceSource]
  exact hsource

end ASDExplicitGamma.Main

end
