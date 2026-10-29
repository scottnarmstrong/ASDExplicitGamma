module

public import ASDExplicitGamma.Native.ParentBoundaryCommonCubeGauge
public import ASDExplicitGamma.Native.ParentBoundaryObserverBandBank
public import ASDExplicitGamma.Native.ParentBoundaryBandRegular
public import ASDExplicitGamma.Native.ParentBoundaryCommonCubeFrame
public import ASDExplicitGamma.Inverse.PureFluxGeneratorRowSource
public import ASDExplicitGamma.Inverse.PureFluxGeneratorCenteredSource
public import ASDExplicitGamma.Inverse.PureFluxGeneratorTiledProjected
public import ASDExplicitGamma.Inverse.PureFluxFeedbackCoefficient
public import ASDExplicitGamma.Gaussian.CovarianceRow
public import ASDExplicitGamma.Native.ParentBoundaryPopulationBankL256

/-! Protected-gap singleton inverse banks in the exact source history frame. -/

@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Variational Gaussian Inverse Main Triadic Algsuperdiff.Section3
open scoped ENNReal
noncomputable section

/-- The original singleton observer bank in any protected completed label
m. Intervening old shells through n retain unit weight. -/
def parentBoundaryCommonSingletonHistory (M : ABKModel 2) (Q : TriadicCube 2)
    (m n : ℤ) (height : ℕ) (t : ℝ) (ω : Cutoff.CutoffSample 2) : ℝ :=
  (bankFiniteRootHistoryMax ({Q}:Finset (TriadicCube 2)) M m (n+(height:ℤ))
    (parentBoundaryObserverBandWeights n t) ω).toReal

/-- The actual singleton source bank at every protected observer label,
with all causal inputs discharged. -/
theorem parent_boundary_common_singleton_bank
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (hg : M.gamma ≤ gammaZero)
    (Q : TriadicCube 2) (m n : ℤ) (hQm : Q.scale ≤ m) (hgap : m-Q.scale ≤ 5) (hmn : m ≤ n)
    (height : ℕ) (hpast : ∀ k<n,nativeInductionState M h k) (t : ℝ) (ht : t ≤ 1) :
    InverseBankConclusion M .localInverse ({Q}:Finset (TriadicCube 2)) m (n+(height:ℤ))
      (parentBoundaryObserverBandWeights n t) := by
  classical
  have hp : ∀ k<m,nativeInductionState M h k := fun k hk => hpast k (lt_of_lt_of_le hk hmn)
  exact local_inverse_bank M h hM hg _ m (n+(height:ℤ)) (by omega) _
    (parent_boundary_observer_band_weights_bounds m n height t ht)
    (fun R hR => by simpa only [Finset.mem_singleton.mp hR] using And.intro hQm hgap)
    (by norm_num) hp (bank_inverse_mean_inputs_of_states M h hM hg m hp).2

/-- The real singleton history retains the original actual L128 cap. -/
theorem parent_boundary_common_singleton_history_L128
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (hg : M.gamma ≤ gammaZero)
    (Q : TriadicCube 2) (m n : ℤ) (hQm : Q.scale ≤ m) (hgap : m-Q.scale ≤ 5) (hmn : m ≤ n)
    (height : ℕ) (hpast : ∀ k<n,nativeInductionState M h k) (t : ℝ) (ht : t ≤ 1) :
    eLpNorm (parentBoundaryCommonSingletonHistory M Q m n height t) 128 (Cutoff.cutoffSampleLaw M).toMeasure ≤
      ENNReal.ofReal (3683/2500:ℝ) := by
  have hb := parent_boundary_common_singleton_bank M h hM hg Q m n hQm hgap hmn height hpast t ht
  have he := eLpNorm_congr_ae (p := 128) (ofReal_toReal_ae_eq hb.history_finite)
  have hr : eLpNorm (parentBoundaryCommonSingletonHistory M Q m n height t) 128
      (Cutoff.cutoffSampleLaw M).toMeasure =
      eLpNorm (bankFiniteRootHistoryMax ({Q}:Finset (TriadicCube 2)) M m (n+(height:ℤ))
        (parentBoundaryObserverBandWeights n t)) 128 (Cutoff.cutoffSampleLaw M).toMeasure := by
    calc
      _ = eLpNorm (fun ω => ENNReal.ofReal (parentBoundaryCommonSingletonHistory M Q m n height t ω))
          128 (Cutoff.cutoffSampleLaw M).toMeasure :=
        (eLpNorm_ofReal _ (Filter.Eventually.of_forall fun _ => ENNReal.toReal_nonneg)).symm
      _ = _ := he
  exact hr.trans_le (by simpa only [inverseBankCap,Rat.cast_div,Rat.cast_ofNat] using hb.total_L128)

/-- The actual protected-label singleton history has the original L256
cap. The pretruncation affine majorant is estimated directly in extended
Lp before the actual finite history is converted to real values. -/
theorem parent_boundary_common_singleton_history_L256
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (hg : M.gamma ≤ gammaZero)
    (Q : TriadicCube 2) (m n : ℤ) (hQm : Q.scale ≤ m) (hgap : m-Q.scale ≤ 5) (hmn : m ≤ n)
    (height : ℕ) (hpast : ∀ k<n,nativeInductionState M h k) (t : ℝ) (ht : t ≤ 1) :
    eLpNorm (parentBoundaryCommonSingletonHistory M Q m n height t) 256 (Cutoff.cutoffSampleLaw M).toMeasure ≤
      ENNReal.ofReal (3683/2500:ℝ) := by
  classical
  exact parent_boundary_population_bank_L256 M h hM hg ({Q}:Finset (TriadicCube 2))
    m (n+(height:ℤ)) (by omega) (parentBoundaryObserverBandWeights n t)
    (parent_boundary_observer_band_weights_bounds m n height t ht)
    (fun S hS => by simpa only [Finset.mem_singleton.mp hS] using And.intro hQm hgap)
    (by norm_num) (fun k hk => hpast k (lt_of_lt_of_le hk hmn))

/-- Actual mesh-zero source histories are paid in the protected label m,
so descendants at depth j can use m=n-j without the fixed offset-r loss. -/
theorem parent_boundary_common_singleton_physical_source
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (hg : M.gamma ≤ gammaZero)
    (Q : TriadicCube 2) (m n : ℤ) (hQm : Q.scale ≤ m) (hgap : m-Q.scale ≤ 5) (hmn : m ≤ n)
    (height : ℕ) (hpast : ∀ k<n,nativeInductionState M h k) (t : ℝ) (ht : t ≤ 1) :
    ∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      let a := responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M n)
        (parentBoundaryCommonOpenCubeCoefficient Q (parentBoundaryCommonCubeBand Q n height t ω))
      max (lemmaVTileHistory Q 0 a) (pureFluxSourceTileHistory Q 0 a) ≤
        ((Annealed.sigmaBar M n:ℝ)/(Annealed.sigmaBar M m:ℝ))*
          parentBoundaryCommonSingletonHistory M Q m n height t ω := by
  have hb := parent_boundary_common_singleton_bank M h hM hg Q m n hQm hgap hmn height hpast t ht
  filter_upwards [hb.history_finite] with ω hfinite
  let sigma : ℝ := Annealed.sigmaBar M n
  let sigmaM : ℝ := Annealed.sigmaBar M m
  let weights := parentBoundaryObserverBandWeights n t
  let a := attenuatedCoefficient M n (n+(height:ℤ)) (fun _ => Real.sqrt t) ω
  let k := parentBoundaryCommonOpenCubeCoefficient Q (parentBoundaryCommonCubeBand Q n height t ω)
  let af := responseFramePlanarCoefficientField M.nu sigma k
  let q : ℝ := (3:ℝ)^((1:ℝ)/4)
  have hsigma : 0 < sigma := (Annealed.sigmaBar_characterization M n).1
  have hsigmaM : 0 < sigmaM := (Annealed.sigmaBar_characterization M m).1
  have hq : 1 < q := Real.one_lt_rpow (by norm_num) (by norm_num)
  have hpromote : attenuatedCoefficient M m (n+(height:ℤ)) weights ω=a :=
    full_response_coefficient_promote M m n (n+(height:ℤ)) hmn (by omega) _ ω
  obtain ⟨Lam,_hLam,hEllCube⟩ := parent_boundary_band_elliptic_cube M n (n+(height:ℤ))
    (fun _ => Real.sqrt t) ω Q
  have hEll := hEllCube.mono (measurableSet_openCubeSet Q) (openCubeSet_subset_cubeSet Q)
  have hEllFrame := responseFramePlanarCoefficientField_isElliptic (measurableSet_openCubeSet Q)
    M.nu sigma M.nu_pos hsigma k
  have hframe : lemmaVInverseHistory Q af q=sigma*lemmaVInverseHistory Q a q :=
    parent_boundary_common_inverse_history_frame Q a af hEll hEllFrame hsigma (fun R j hR =>
      parent_boundary_common_cube_band_coarse_frame M Q n height t ω sigma hsigma hR)
  have hroot := bank_root_history_physical Q M m (n+(height:ℤ)) weights ω a hpromote hEll
  have hnonneg := lemmaVInverseHistory_nonneg Q a hq
  have heq : lemmaVInverseHistory Q af q=(sigma/sigmaM)*
      (bankRootInverseHistory Q M m (n+(height:ℤ)) weights ω).toReal := by
    rw [hframe,hroot,ENNReal.toReal_ofReal (mul_nonneg hsigmaM.le hnonneg)]
    field_simp [hsigmaM.ne']
  have hmax := bank_member_history_le M ({Q}:Finset (TriadicCube 2)) Q (by simp) m (n+(height:ℤ)) weights ω
  have hmaxReal := ENNReal.toReal_mono hfinite.ne hmax
  have hsource : lemmaVInverseHistory Q af q ≤ (sigma/sigmaM)*parentBoundaryCommonSingletonHistory M Q m n height t ω := by
    rw [heq]
    exact mul_le_mul_of_nonneg_left hmaxReal (div_nonneg hsigma.le hsigmaM.le)
  have hp : pureFluxSourceTileHistory Q 0 af ≤ (sigma/sigmaM)*parentBoundaryCommonSingletonHistory M Q m n height t ω := by
    apply pureFlux_source_tile_history_le
    intro R hR
    have heR : R=Q := by simpa only [descendantsAtDepth_zero,Finset.mem_singleton] using hR
    subst R
    exact hsource
  have hm := tile_history_le_source_history Q 0 M.nu sigma M.nu_pos hsigma k
  exact max_le (hm.trans hp) hp

/-- The exact same protected singleton bank pays the common-centered
observation: the whole reciprocal history is gauge invariant pathwise. -/
theorem parent_boundary_common_singleton_centered_source
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (hg : M.gamma ≤ gammaZero)
    {P Q : TriadicCube 2} {d : ℕ} (hQ : Q ∈ descendantsAtDepth P d)
    (m n : ℤ) (hQm : Q.scale ≤ m) (hgap : m-Q.scale ≤ 5) (hmn : m ≤ n)
    (height : ℕ) (hpast : ∀ k<n,nativeInductionState M h k) (t : ℝ) (ht : t ≤ 1) :
    ∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      let a := responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M n)
        (parentBoundaryCommonCubeObserved hQ n height t ω)
      max (lemmaVTileHistory Q 0 a) (pureFluxSourceTileHistory Q 0 a) ≤
        ((Annealed.sigmaBar M n:ℝ)/(Annealed.sigmaBar M m:ℝ))*
          parentBoundaryCommonSingletonHistory M Q m n height t ω := by
  filter_upwards [parent_boundary_common_singleton_physical_source M h hM hg Q m n
    hQm hgap hmn height hpast t ht] with ω hω
  have he := parent_boundary_common_cube_actual_histories_gauge hQ M.nu (Annealed.sigmaBar M n)
    M.nu_pos (Annealed.sigmaBar_characterization M n).1 n height t ω 0
  dsimp only at he hω ⊢
  rw [parent_boundary_common_cube_band_observed_eq M hQ] at he
  rw [←he.1,←he.2]
  exact hω

end
end ASDExplicitGamma.Native
