module

public import ASDExplicitGamma.Native.ParentBoundaryCommonDirectionRepresentation
public import ASDExplicitGamma.Native.ParentBoundaryCommonTraceGenerator
public import ASDExplicitGamma.Native.ParentBoundaryCommonSingletonBank
public import ASDExplicitGamma.Gaussian.ModelHeatPower

/-! The actual common-center p20 generator in a protected singleton bank frame. -/

@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Variational Gaussian Inverse Main Model Triadic Algsuperdiff.Section3
noncomputable section

/-- Actual per-shell p20 generator on every source-square descendant.
The original source center, full trace, actual common inverse bank and true
frame ratio are retained. No generator, history, moment or source cap is a premise. -/
theorem parent_boundary_common_protected_power_generator
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (hg : M.gamma ≤ gammaZero)
    {P Q : TriadicCube 2} {d : ℕ} (hQ : Q ∈ descendantsAtDepth P d)
    (m n : ℤ) (hQm : Q.scale ≤ m) (hgap : m-Q.scale ≤ 5) (hmn : m ≤ n) (height : ℕ)
    (hpast : ∀ k<n,nativeInductionState M h k) (t : ℝ) (ht : t ≤ 1) (i : Fin height) :
    let J := n+((i.val+1:ℕ):ℤ)
    let σ : ℝ := Annealed.sigmaBar M n
    let b := q3ModelAmplitude M h J
    let L := q3ModelLength J
    let A := parentBoundaryCommonRowCoefficient P Q b L 0
    let κ := lemmaVH2Bn (cubeScaleFactor P/L.val) (diagMeshRadius Q 0/L.val)
    let R := σ/(Annealed.sigmaBar M m:ℝ)
    let Φ := squareTrace Q M.nu σ
    let H := parentBoundaryCommonResponseDirections P Q b L
    ∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      let X := parentBoundaryCommonCubeObserved hQ n height t ω
      modelPowerHeatGenerator Φ H 20 X ≤
        20*(Φ X)^19*(σ⁻¹^2*R^2*((232/125:ℝ)*A^2+38*b^2*κ^2)*
          (parentBoundaryCommonSingletonHistory M Q m n height t ω)^2*(Φ X+4)) := by
  intro J σ b L A κ R Φ H
  have hσ : 0 < σ := (Annealed.sigmaBar_characterization M n).1
  have hν := M.nu_pos
  have hQP := cubeSet_subset_of_mem_descendantsAtDepth hQ
  filter_upwards [parent_boundary_common_singleton_centered_source M h hM hg hQ m n hQm hgap hmn
    height hpast t ht] with ω hB
  dsimp only at hB ⊢
  let X := parentBoundaryCommonCubeObserved hQ n height t ω
  let T := Φ X
  let Z := parentBoundaryCommonSingletonHistory M Q m n height t ω
  let c := σ⁻¹^2
  let af := responseFramePlanarCoefficientField M.nu σ X
  let B := pureFluxSourceTileHistory Q 0 af
  let B' := lemmaVTileHistory Q 0 af
  let LL := (1/2:ℝ)*modelCovarianceTrace Φ H X
  let Γ := modelGradientSquareTrace Φ H X
  have hT : 0 ≤ T := traceDefect_nonneg_of_ellipticFieldOn_triCube (div_pos hν hσ)
    (lemmaV_frameCoefficient_isEllipticOn (measurableSet_cubeSet Q) M.nu σ hν hσ X) (by norm_num)
  have hB0 : 0 ≤ B := pureFlux_source_tile_history_nonneg Q 0 af
  have hB'0 : 0 ≤ B' := lemmaVTileHistory_nonneg Q 0 af
  have hBP : B ≤ R*Z := (le_max_right _ _).trans hB
  have hB'P : B' ≤ R*Z := (le_max_left _ _).trans hB
  have hBsq : B^2 ≤ R^2*Z^2 := by simpa only [mul_pow] using pow_le_pow_left₀ hB0 hBP 2
  have hB'sq : B'^2 ≤ R^2*Z^2 := by simpa only [mul_pow] using pow_le_pow_left₀ hB'0 hB'P 2
  have hl := parent_boundary_common_trace_generator P Q hQP M.nu σ b hν hσ L 0 X
  have hμ := parent_boundary_common_covariance_mu P Q b L 0
  have hL : LL ≤ c*((232/125:ℝ)*A^2)*(R^2*Z^2)*(T+4) := by
    have hl' : LL ≤ c*pureFluxCovarianceMu A (parentBoundaryCommonFeedbackCoefficient P Q b L 0)*B^2*(T+4) := by
      simpa only [sq_abs] using hl
    calc
      LL ≤ c*pureFluxCovarianceMu A (parentBoundaryCommonFeedbackCoefficient P Q b L 0)*B^2*(T+4) := hl'
      _ = pureFluxCovarianceMu A (parentBoundaryCommonFeedbackCoefficient P Q b L 0)*(c*B^2*(T+4)) := by ring
      _ ≤ ((232/125:ℝ)*A^2)*(c*B^2*(T+4)) := mul_le_mul_of_nonneg_right hμ (by dsimp [c]; positivity)
      _ = c*((232/125:ℝ)*A^2)*B^2*(T+4) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hBsq (by dsimp [c]; positivity)) (by positivity)
  have hγ := (parent_boundary_common_response_trace_bracket P Q hQP 0 M.nu σ b hν hσ L X).2
  have hframe : (b/σ)^2=c*b^2 := by dsimp [c]; rw [div_pow,div_eq_mul_inv,inv_pow]; ring
  have hΓ : Γ ≤ 4*c*b^2*κ^2*(R^2*Z^2)*T*(T+4) := by
    have hγ' : Γ ≤ 4*(Real.sqrt ((b/σ)^2)*κ)^2*B'^2*T*(T+4) := hγ
    rw [mul_pow,Real.sq_sqrt (sq_nonneg _),hframe] at hγ'
    calc
      Γ ≤ 4*(c*b^2*κ^2)*B'^2*T*(T+4) := hγ'
      _ = (4*c*b^2*κ^2)*B'^2*T*(T+4) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hB'sq (by dsimp [c]; positivity)) hT) (by positivity)
  have hleft := mul_le_mul_of_nonneg_left hL (by positivity : 0 ≤ 20*T^19)
  have hright := mul_le_mul_of_nonneg_left hΓ (by positivity : 0 ≤ 190*T^18)
  have he : modelPowerHeatGenerator Φ H 20 X=20*T^19*LL+190*T^18*Γ := by
    norm_num [modelPowerHeatGenerator,T,LL,Γ,Real.rpow_ofNat]
  rw [he]
  exact (add_le_add hleft hright).trans_eq (by dsimp only [c]; ring)

end
end ASDExplicitGamma.Native
