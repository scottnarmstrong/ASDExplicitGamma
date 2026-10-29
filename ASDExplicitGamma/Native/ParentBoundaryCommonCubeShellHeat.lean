module

public import ASDExplicitGamma.Native.ParentBoundaryCommonGaussianLaw
public import ASDExplicitGamma.Native.ParentBoundaryCommonTraceTests
public import ASDExplicitGamma.Native.GenericSourceBandHeat
public import ASDExplicitGamma.Inverse.SourceGaussianBandTrace

/-! Actual complete shell-sum heat derivative on common-centered descendants. -/

@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Variational Gaussian Inverse Main Model Triadic Algsuperdiff.Section3
noncomputable section

local instance parentCommonShellHeatCompact (P : TriadicCube 2) : CompactSpace (closure (cubeSet P)) :=
  isCompact_iff_compactSpace.mp (isBounded_cubeSet P).isCompact_closure
local instance parentCommonShellHeatOpenCompact (Q : TriadicCube 2) : CompactSpace (closure (openCubeSet Q)) :=
  isCompact_iff_compactSpace.mp (isBounded_openCubeSet Q).isCompact_closure
local instance parentCommonShellHeatMeasurable (Q : TriadicCube 2) :
    MeasurableSpace (ResponseCoefficient (openCubeSet Q)) := borel _
local instance parentCommonShellHeatBorel (Q : TriadicCube 2) :
    BorelSpace (ResponseCoefficient (openCubeSet Q)) := ⟨rfl⟩
local instance parentCommonShellHeatSecondCountable (Q : TriadicCube 2) :
    SecondCountableTopology (ResponseCoefficient (openCubeSet Q)) := by
  let e : ResponseCoefficient (openCubeSet Q) → C(closure (openCubeSet Q),ℝ) := fun f => f.toContinuousMap
  have he : Isometry e := by
    intro f g
    rw [edist_dist,edist_dist]
    simp [e,BoundedContinuousFunction.dist_eq_iSup,ContinuousMap.dist_eq_iSup]
  exact he.isEmbedding.secondCountableTopology

/-- The actual whole-band derivative is the COMPLETE sum of the physical
shell contractions on the observed descendant, with one original center. -/
theorem parent_boundary_common_cube_average_shell_heat
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    {P Q : TriadicCube 2} {d : ℕ} (hQ : Q ∈ descendantsAtDepth P d)
    (n : ℤ) (height : ℕ) (hheight : 1 ≤ height)
    (Φ : ResponseCoefficient (openCubeSet Q) → ℝ) (hΦ : HasPolynomiallyBoundedC2Derivatives Φ) :
    ContinuousOn (parentBoundaryCommonCubeAverage M hQ n height Φ) (Set.Ici 0) ∧
    ∀ t ∈ Set.Ioi (0:ℝ),HasDerivAt (parentBoundaryCommonCubeAverage M hQ n height Φ)
      ((1/2:ℝ)*∫ ω : Cutoff.CutoffSample 2,∑ i : Fin height,
        modelCovarianceTrace Φ (parentBoundaryCommonResponseDirections P Q
          (q3ModelAmplitude M h (n+((i.val+1:ℕ):ℤ)))
          (q3ModelLength (n+((i.val+1:ℕ):ℤ))))
          (parentBoundaryCommonCubeObserved hQ n height t ω)
        ∂(Cutoff.cutoffSampleLaw M).toMeasure) t := by
  let parentCommonShellHeightNonzero : NeZero height := ⟨by omega⟩
  let K := closure (cubeSet P)
  let k := nativeSourceBandIndex n height
  have hk : Function.Injective k := by
    intro i j hij
    apply Fin.ext
    dsimp [k,nativeSourceBandIndex] at hij
    omega
  have hk0 (i : Fin height) : n < k i := by dsimp [k,nativeSourceBandIndex]; omega
  have hex (i : Fin height) := freshShell_map_scalarRestriction_eq_gaussianSeries M h hM (k i-1) (K := K)
  choose T v hv hlaw using hex
  simp only [sub_add_cancel] at hlaw
  let A0 := parentBoundaryCommonOpenCellCoefficient hQ
  let B := parentBoundaryCommonObservedMap hQ
  let A := bandFactor T
  let w := bandDirections v
  have hw : Summable (fun j => ‖w j‖^2) := bandDirections_summable v hv
  have hband := modelBand_law_of_factors (fun _ : Fin height => GaussianFactorL2 ℕ) K M k hk T v hv hlaw
  have hCov (x : ResponseCoefficient (openCubeSet Q)) : modelCovarianceTrace Φ (fun j => B (A (w j))) x =
      ∑ i : Fin height,modelCovarianceTrace Φ (parentBoundaryCommonResponseDirections P Q
        (q3ModelAmplitude M h (n+((i.val+1:ℕ):ℤ)))
        (q3ModelLength (n+((i.val+1:ℕ):ℤ)))) x := by
    have he : (fun j => B (A (w j))) =
        fun j => bandFactor (fun i => B.comp (T i)) (bandDirections v j) := by
      funext j
      simp only [A,w,bandDirections,bandFactor_single,ContinuousLinearMap.comp_apply]
    rw [he,source_gaussian_band_covariance_trace_sum v hv (fun i => B.comp (T i)) Φ hΦ.1 x]
    apply Finset.sum_congr rfl
    intro i _
    have hklabel : k i=n+((i.val+1:ℕ):ℤ) := by dsimp [k,nativeSourceBandIndex]; omega
    have hlawi : (Cutoff.cutoffSampleLaw M).toMeasure.map
        (fun ω : Cutoff.CutoffSample 2 => shellFieldScalarRestriction K (ω.1 (n+((i.val+1:ℕ):ℤ)))) =
        standardGaussianInfinitePi.map (gaussianSeriesLimitE (hv i) (T i)) := by
      simpa only [hklabel] using hlaw i
    exact parent_boundary_common_observed_shell_covariance M h hM hQ
      (n+((i.val+1:ℕ):ℤ)) (T i) (v i) (hv i) hlawi Φ hΦ x
  obtain ⟨ell,hK⟩ := exists_originCube_containing_compact K (isBounded_cubeSet P).isCompact_closure
  have hheat := c1On_bandModelAverage K M ell n hK k hk0 hw A hband A0 B Φ hΦ
  have hmean : bandModelAverage K M n k A0 B Φ=parentBoundaryCommonCubeAverage M hQ n height Φ := rfl
  rw [hmean] at hheat
  refine ⟨hheat.1,?_⟩
  intro t ht
  have hh := hheat.2.2.1 t ht
  have hvalue : bandModelAverage K M n k A0 B
      (modelCovarianceTrace Φ (fun j => B (A (w j)))) t =
      ∫ ω : Cutoff.CutoffSample 2,∑ i : Fin height,
        modelCovarianceTrace Φ (parentBoundaryCommonResponseDirections P Q
          (q3ModelAmplitude M h (n+((i.val+1:ℕ):ℤ)))
          (q3ModelLength (n+((i.val+1:ℕ):ℤ))))
          (parentBoundaryCommonCubeObserved hQ n height t ω) ∂(Cutoff.cutoffSampleLaw M).toMeasure := by
    apply integral_congr_ae
    filter_upwards [] with ω
    exact hCov _
  rw [hvalue] at hh
  exact hh

/-- Exact p20 moment derivative on the actual common-centered descendant.
Every shell generator is the already-proved physical source generator. -/
theorem parent_boundary_common_cube_p20_shell_heat
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    {P Q : TriadicCube 2} {d : ℕ} (hQ : Q ∈ descendantsAtDepth P d)
    (n : ℤ) (height : ℕ) (hheight : 1 ≤ height) :
    let Φ := squareTrace Q M.nu (Annealed.sigmaBar M n)
    ContinuousOn (parentBoundaryCommonCubeAverage M hQ n height (fun x => Φ x^(20:ℝ))) (Set.Ici 0) ∧
    ∀ t ∈ Set.Ioi (0:ℝ),HasDerivAt (parentBoundaryCommonCubeAverage M hQ n height (fun x => Φ x^(20:ℝ)))
      (∫ ω : Cutoff.CutoffSample 2,∑ i : Fin height,
        modelPowerHeatGenerator Φ (parentBoundaryCommonResponseDirections P Q
          (q3ModelAmplitude M h (n+((i.val+1:ℕ):ℤ)))
          (q3ModelLength (n+((i.val+1:ℕ):ℤ)))) 20
          (parentBoundaryCommonCubeObserved hQ n height t ω) ∂(Cutoff.cutoffSampleLaw M).toMeasure) t := by
  intro Φ
  have hσ := (Annealed.sigmaBar_characterization M n).1
  have hΦ := parent_boundary_common_square_trace_polynomial Q M.nu (Annealed.sigmaBar M n) M.nu_pos hσ
  have hΦ0 := parent_boundary_common_square_trace_nonneg Q M.nu (Annealed.sigmaBar M n) M.nu_pos hσ
  have hh := parent_boundary_common_cube_average_shell_heat M h hM hQ n height hheight
    (fun x => Φ x^(20:ℝ)) (hasPolynomiallyBoundedC2Derivatives_rpow hΦ hΦ0 (by norm_num : (2:ℝ) ≤ 20))
  refine ⟨hh.1,?_⟩
  intro t ht
  have hd := hh.2 t ht
  have he : (1/2:ℝ)*(∫ ω : Cutoff.CutoffSample 2,∑ i : Fin height,
      modelCovarianceTrace (fun x => Φ x^(20:ℝ)) (parentBoundaryCommonResponseDirections P Q
        (q3ModelAmplitude M h (n+((i.val+1:ℕ):ℤ))) (q3ModelLength (n+((i.val+1:ℕ):ℤ))))
        (parentBoundaryCommonCubeObserved hQ n height t ω) ∂(Cutoff.cutoffSampleLaw M).toMeasure) =
      ∫ ω : Cutoff.CutoffSample 2,∑ i : Fin height,
        modelPowerHeatGenerator Φ (parentBoundaryCommonResponseDirections P Q
          (q3ModelAmplitude M h (n+((i.val+1:ℕ):ℤ)))
          (q3ModelLength (n+((i.val+1:ℕ):ℤ)))) 20
          (parentBoundaryCommonCubeObserved hQ n height t ω) ∂(Cutoff.cutoffSampleLaw M).toMeasure := by
    rw [←integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with ω
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact parent_boundary_common_response_power_identity hQ M.nu (Annealed.sigmaBar M n)
      (q3ModelAmplitude M h (n+((i.val+1:ℕ):ℤ))) M.nu_pos hσ
      (q3ModelLength (n+((i.val+1:ℕ):ℤ))) _
  rw [he] at hd
  exact hd

end
end ASDExplicitGamma.Native
