module

public import ASDExplicitGamma.Main.InverseLowerCenteredSourceTrace

/-! Aggregate the actual centered q3 covariance estimate over both affine
response loads in the fixed OLD frame. -/

@[expose] public section

open Homogenization MeasureTheory ASDExplicitGamma.Gaussian ASDExplicitGamma.Inverse
  ASDExplicitGamma.Response ASDExplicitGamma.Triadic ASDExplicitGamma.Variational
open scoped BigOperators

namespace ASDExplicitGamma.Main

private theorem main_pairTrace_fderiv_fderiv_add
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : E → ℝ} (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (x : E) :
    fderiv ℝ (fderiv ℝ (fun y => f y + g y)) x =
      fderiv ℝ (fderiv ℝ f) x + fderiv ℝ (fderiv ℝ g) x := by
  have hfdF : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hfdG : Differentiable ℝ g := hg.differentiable (by norm_num)
  have hfirst : (fun y => fderiv ℝ (fun z => f z + g z) y) =
      fun y => fderiv ℝ f y + fderiv ℝ g y := by
    funext y
    exact fderiv_fun_add (hfdF y) (hfdG y)
  have hsecondF : Differentiable ℝ (fun y => fderiv ℝ f y) :=
    (hf.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).differentiable_one
  have hsecondG : Differentiable ℝ (fun y => fderiv ℝ g y) :=
    (hg.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).differentiable_one
  change fderiv ℝ (fun y => fderiv ℝ (fun z => f z + g z) y) x = _
  rw [hfirst, fderiv_fun_add (hsecondF x) (hsecondG x)]

private theorem main_pairTrace_add
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (H : ℕ → E) (hH : Summable (fun j => ‖H j‖ ^ 2))
    {f g : E → ℝ} (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (x : E) :
    modelCovarianceTrace (fun y => f y + g y) H x =
      modelCovarianceTrace f H x + modelCovarianceTrace g H x := by
  rw [modelCovarianceTrace_eq_bilinearTraceMap H hH (hf.add hg) x,
    modelCovarianceTrace_eq_bilinearTraceMap H hH hf x,
    modelCovarianceTrace_eq_bilinearTraceMap H hH hg x,
    main_pairTrace_fderiv_fderiv_add hf hg x]
  exact (bilinearTraceMap H hH).map_add _ _

/-- The fixed-frame centered q3 covariance trace lower bound for the two
actual affine loads. Each summand is the per-load source estimate, with its
own response minimizer energy and gradient energy. -/
theorem main_twoLoad_q3_centered_response_covariance_trace_lower
    (n : ℤ) (q i m : ℕ) (ν σ b B : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (L : {l : ℝ // 0 < l})
    (hρ : cubeScaleFactor (originCube 2 n) / L.1 = pureFluxCovarianceRho q i)
    (hδ : diagMeshRadius (originCube 2 n) m / L.1 = pureFluxCovarianceDelta q i)
    (k : ResponseCoefficient (openCubeSet (originCube 2 n)))
    (P : Fin 2 → BlockVec 2)
    (r : Fin 2 → H10Function (openCubeSet (originCube 2 n)))
    (u : Fin 2 → AHarmonicFunction (responseFramePlanarCoefficientField ν σ k)
      (openCubeSet (originCube 2 n)))
    (w : Fin 2 → AHarmonicFunction
      (adjointCoeffField (responseFramePlanarCoefficientField ν σ k))
      (openCubeSet (originCube 2 n)))
    (hrep : ∀ a, hilbertBlockL2ToBlockL2
        ((responseFrameMuOperatorSystemData
          (isOpenBoundedConvexDomain_openCubeSet (originCube 2 n)).isOpen.measurableSet
          (volume_openCubeSet_originCube_toReal_pos (d := 2) n)
          ν σ hν hσ k).toMuHilbertRealization.minimizerMap (P a)) =ᵐ[
          volumeMeasureOn (openCubeSet (originCube 2 n))]
        (fun x => (blockResponsePairHalfState
          (responseFramePlanarCoefficientField ν σ k) (u a) (w a)).eval x))
    (hgrad : ∀ a, (lemmaVAffinePotential
        (isOpenBoundedConvexDomain_openCubeSet (originCube 2 n)) (P a).1 (r a)).grad =ᵐ[
          volumeMeasureOn (openCubeSet (originCube 2 n))]
        (blockResponsePairHalfState
          (responseFramePlanarCoefficientField ν σ k) (u a) (w a)).potential)
    (hB : 0 ≤ B)
    (hhist : ∀ (U : TriadicCube 2),
      U ∈ descendantsAtDepth (originCube 2 n) m →
      lemmaVInverseHistory U (responseFramePlanarCoefficientField ν σ k)
        ((3 : ℝ)^(1/4:ℝ)) ≤ B) :
    let Q := originCube 2 n
    let H (j : ℕ) := pureFluxMainCubeQ3CenteredResponseCoefficient n b L j
    let hU := measurableSet_openCubeSet Q
    let hvol := volume_openCubeSet_originCube_toReal_pos (d := 2) n
    let E (a : Fin 2) := responseFrameEnergyObservable hU hvol ν σ hν hσ (P a)
    let Eall := fun k' => ∑ a : Fin 2, E a k'
    let Wv (a : Fin 2) := lemmaVTiledWeakEnergy Q m
      (lemmaVAffinePotential (isOpenBoundedConvexDomain_openCubeSet Q) (P a).1 (r a)).grad
    let Wg (a : Fin 2) := lemmaVTiledWeakEnergy Q m
      ((1/2:ℝ) • ((w a).toH1-(u a).toH1)).grad
    let Kf (a : Fin 2) := (63/50:ℝ)*B*(abs σ⁻¹*abs b)^2*
      pureFluxCovarianceA q i*pureFluxCovarianceB q i*
      Real.sqrt (Wv a)*Real.sqrt (Wg a)
    let Kz (a : Fin 2) := abs σ⁻¹*abs b*pureFluxCovarianceB q i*
      Real.sqrt (σ/ν)*Real.sqrt (Wg a)
    (1/2:ℝ) * modelCovarianceTrace Eall H k ≥
      ∑ a : Fin 2, (-2*Kf a-(Kz a)^2) := by
  classical
  intro Q H hU hvol E Eall Wv Wg Kf Kz
  let Hnat (j : ℕ) := pureFluxMainCubeQ3CenteredResponseCoefficient n b L j
  have hH : Summable (fun j => ‖Hnat j‖ ^ 2) :=
    pureFluxMainCubeQ3CenteredResponseCoefficient_summable n b L
  have hEd (a : Fin 2) : ContDiff ℝ 2 (E a) := by
    exact responseFrameEnergyObservable_contDiff hU hvol ν σ hν hσ (P a)
  have hEall : Eall = fun k' => E 0 k' + E 1 k' := by
    funext k'
    simp [Eall, Fin.sum_univ_two]
  have htrace : modelCovarianceTrace Eall Hnat k =
      ∑ a : Fin 2, modelCovarianceTrace (E a) Hnat k := by
    rw [hEall]
    rw [main_pairTrace_add Hnat hH (hEd 0) (hEd 1) k]
    simp only [Fin.sum_univ_two]
  have hrow (a : Fin 2) :
      (1/2:ℝ) * modelCovarianceTrace (E a) Hnat k ≥
        -2*Kf a-(Kz a)^2 := by
    simpa only [Q, Hnat, H, hU, hvol, E, Wv, Wg, Kf, Kz] using
      main_q3_centered_response_covariance_trace_lower
        n q i m ν σ b B hν hσ L hρ hδ k (P a) (r a) (u a) (w a)
        (hrep a) (hgrad a) hB hhist
  rw [htrace]
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum (fun a _ => hrow a)

end ASDExplicitGamma.Main

end
