module

public import ASDExplicitGamma.Native.ParentBoundaryInverseSourceTrace
public import ASDExplicitGamma.Inverse.PureFluxGeneratorMinimizerEnergy

/-! The sharp inverse-history lower generator for a genuine affine load.
The reciprocal covariance row is the diagonal channel of the negative bill. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Gaussian Main Triadic Variational Inverse
noncomputable section

/-- The actual centered generator lower bound, with no molecular ratio
loss and no assumed response-minimizer estimate. -/
theorem parent_boundary_affine_inverse_generator_lower
    (n : ℤ) (q i depth : ℕ) (nu sigma b B : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (L : {l : ℝ // 0<l})
    (hrho : cubeScaleFactor (originCube 2 n)/L.1=pureFluxCovarianceRho q i)
    (hdelta : diagMeshRadius (originCube 2 n) depth/L.1=pureFluxCovarianceDelta q i)
    (k : ResponseCoefficient (openCubeSet (originCube 2 n))) (P : BlockVec 2)
    (hB : 0≤B)
    (hhist : ∀ U∈descendantsAtDepth (originCube 2 n) depth,
      lemmaVInverseHistory U (responseFramePlanarCoefficientField nu sigma k)
        ((3:ℝ)^(1/4:ℝ))≤B) :
    (1/2:ℝ)*modelCovarianceTrace
      (responseFrameEnergyObservable (measurableSet_openCubeSet (originCube 2 n))
        (volume_openCubeSet_originCube_toReal_pos (d := 2) n) nu sigma hnu hsigma P)
      (pureFluxMainCubeQ3CenteredResponseCoefficient n b L) k ≥
      -(b^2/sigma^2*pureFluxCovarianceMu (pureFluxCovarianceB q i) (pureFluxCovarianceA q i)*B^2*
        responseFrameEnergyObservable (measurableSet_openCubeSet (originCube 2 n))
          (volume_openCubeSet_originCube_toReal_pos (d := 2) n) nu sigma hnu hsigma P k) := by
  let Q := originCube 2 n
  let hU := isOpenBoundedConvexDomain_openCubeSet Q
  let hv := volume_openCubeSet_originCube_toReal_pos (d := 2) n
  let a := responseFramePlanarCoefficientField nu sigma k
  let E := responseFrameEnergyObservable (measurableSet_openCubeSet Q) hv nu sigma hnu hsigma P
  let c := abs sigma⁻¹*abs b
  have hEll := responseFramePlanarCoefficientField_isElliptic
    (measurableSet_openCubeSet Q) nu sigma hnu hsigma k
  obtain ⟨r,u,w,hrep,hgrad,hEv,hEu⟩ := lemmaV_minimizer_pair n hEll P
  rw [lemmaV_responseSystem_eq_canonical hU.isOpen.measurableSet hv nu sigma hnu hsigma k]
    at hrep hEv hEu
  have hE : E k=2*(responseFrameMuOperatorSystemData hU.isOpen.measurableSet hv
      nu sigma hnu hsigma k).toMuHilbertRealization.muCandidate P :=
    lemmaV_observable_eq_twice_muCandidate hU.isOpen.measurableSet hv nu sigma hnu hsigma P k
  rw [←hE] at hEv hEu
  let v := lemmaVAffinePotential hU P.1 r
  let g : H1Function (openCubeSet Q) := (1/2:ℝ) • (w.toH1-u.toH1)
  let x := Real.sqrt (lemmaVTiledWeakEnergy Q depth v.grad)
  let y := Real.sqrt (lemmaVTiledWeakEnergy Q depth g.grad)
  have hx : x^2=lemmaVTiledWeakEnergy Q depth v.grad := Real.sq_sqrt (lemmaVTiledWeakEnergy_nonneg Q depth _)
  have hy : y^2=lemmaVTiledWeakEnergy Q depth g.grad := Real.sq_sqrt (lemmaVTiledWeakEnergy_nonneg Q depth _)
  have hgg : g.grad=fun z => (1/2:ℝ) • (w.toH1.grad z-u.toH1.grad z) := by
    funext z j
    simp only [g,H1Function.smul_grad,H1Function.sub_grad,Pi.smul_apply,Pi.sub_apply,smul_eq_mul]
  have hbudget : x^2+y^2≤B*E k := by
    rw [hx,hy,hgg]
    exact pureFlux_minimizer_pair_tiled_energy_bound n depth nu sigma hnu hsigma k P
      r u w hgrad hEv hEu B hhist
  have hs := parent_boundary_centered_response_trace_lower n q i depth nu sigma b B
    hnu hsigma L hrho hdelta k P r u w hrep hgrad hB hhist
  have hsq : (c*pureFluxCovarianceB q i*Real.sqrt B*y)^2=
      B*c^2*(pureFluxCovarianceB q i)^2*y^2 := by
    have ht := Real.sq_sqrt hB
    calc
      _ = c^2*(pureFluxCovarianceB q i)^2*(Real.sqrt B)^2*y^2 := by ring
      _ = _ := by rw [ht]; ring
  change _≥-2*((63/50:ℝ)*B*c^2*pureFluxCovarianceA q i*pureFluxCovarianceB q i*x*y)-
    (c*pureFluxCovarianceB q i*Real.sqrt B*y)^2 at hs
  rw [hsq] at hs
  have hquad := mul_le_mul_of_nonneg_left
    (pureFlux_covariance_quadratic_bound (pureFluxCovarianceB q i) (pureFluxCovarianceA q i) y x)
    (mul_nonneg hB (sq_nonneg c))
  have htotal := mul_le_mul_of_nonneg_left hbudget
    (mul_nonneg (mul_nonneg hB (sq_nonneg c))
      (pureFlux_covariance_mu_lower (pureFluxCovarianceB q i) (pureFluxCovarianceA q i)).1)
  have hc : c^2=b^2/sigma^2 := by
    dsimp [c]
    rw [mul_pow,sq_abs,sq_abs,inv_pow,div_eq_mul_inv]
    ring
  rw [hc] at hs hquad htotal
  dsimp only [E,Q,hv] at hs htotal ⊢
  nlinarith only [hs,hquad,htotal]

end
end ASDExplicitGamma.Native
