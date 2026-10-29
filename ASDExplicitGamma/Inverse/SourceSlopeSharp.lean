module

public import ASDExplicitGamma.Inverse.BankObservers
public import ASDExplicitGamma.Model.Cutoff
public import ASDExplicitGamma.Inverse.SourceInterfaceTransport
public import ASDExplicitGamma.Inverse.FullResponseCoefficientTransport
public import ASDExplicitGamma.Native.ParentBoundaryMeanProtectedExpectation
public import ASDExplicitGamma.Native.ParentBoundaryMeanGeometry
public import ASDExplicitGamma.Native.ParentBoundaryCommonHistoryRawProfile
public import ASDExplicitGamma.Native.ParentBoundaryObserverBandCoefficient

/-! The exact protected one-shell source row for the translated OLD slope. -/

@[expose] public section

namespace ASDExplicitGamma.Inverse

open MeasureTheory Set Filter Homogenization Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Main ASDExplicitGamma.Native
  ASDExplicitGamma.Model ASDExplicitGamma.Scalar ASDExplicitGamma.Triadic
  ASDExplicitGamma.Variational ASDExplicitGamma.Response
open scoped ENNReal

noncomputable section

private theorem in_source_rate_eq_parent_shell_generator
    (M : ABKModel 2) (h : ℝ) (m : ℤ) (r : ℕ) (t : ℝ) :
    inSourceMeanRateActual M h m r t =
      ∫ ω, parentBoundaryMeanShellGenerator M h
        (m - (r : ℤ)) m 1 t (0 : Fin 1) ω
          ∂(Cutoff.cutoffSampleLaw M).toMeasure := by
  let q : ℤ := m - (r : ℤ)
  let K := closure (cubeSet (originCube 2 q))
  let Φ := modelTraceObservable q M.nu (Annealed.sigmaBar M m)
  let H := pureFluxMainCubeQ3Directions q (q3ModelAmplitude M h (m + 1))
    (q3ModelLength (m + 1))
  obtain ⟨ell, hK⟩ := exists_originCube_containing_compact K
    (isBounded_cubeSet (originCube 2 q)).isCompact_closure
  have hcoeff' (ω : Cutoff.CutoffSample 2) :
      attenuatedCoefficient M m (m + 1) (fun _ => Real.sqrt t) ω =
        fun x => Cutoff.coefficientCutoff M.nu m ω x +
          Real.sqrt t • (ω.val (m + 1)).forgetShell x := by
    simpa only [show m + 1 - 1 = m by omega] using
      (full_response_coefficient_partial M (m + 1) t ω)
  have hcoeff (ω : Cutoff.CutoffSample 2) :
      attenuatedCoefficient M m (m + 1) (fun _ => Real.sqrt t) ω =
        (Model.partialInsertedCoefficient M m t ω).toFun := by
    funext x
    have hh := congrArg (fun f => f x) (hcoeff' ω)
    simpa [Model.partialInsertedCoefficient] using hh
  have hX (ω : Cutoff.CutoffSample 2) :
      modelInsertedScalar K m t ω = parentBoundaryObserverBandScalar q m 1 t ω := by
    ext x
    rw [Gaussian.modelInsertedScalar_apply K M ell m hK t ω x]
    rw [parent_boundary_observer_band_scalar_apply M q m 1 t ω x]
    exact congrArg (fun c => c x.1 1 0) (hcoeff ω).symm
  change (1 / 2 : ℝ) * modelHeatTraceAverage K M m Φ H t = _
  unfold modelHeatTraceAverage modelHeatAverage
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with ω
  dsimp only [parentBoundaryMeanShellGenerator, q, Φ, H]
  rw [hX ω]
  simp only [Nat.zero_add, Fin.val_zero]
  rfl

private def inSourceProtectedSlopeRow
    (M : ABKModel 2) (h : ℝ) (m : ℤ) (j : ℕ) : ℝ :=
  let sigma : ℝ := Annealed.sigmaBar M m
  let v := (q3ModelAmplitude M h (m + 1) / sigma) ^ 2
  let q : ℤ := m - ((5 + j : ℕ) : ℤ)
  let rho := cubeScaleFactor (originCube 2 q) /
    (q3ModelLength (m + 1)).val
  let kappa := lemmaVH2kn rho rho
  let mu := pureFluxCovarianceMu (pureFluxCovarianceA 0 (5 + j))
    (pureFluxCovarianceB 0 (5 + j))
  let E := (3 : ℝ) ^ (2 * M.gamma * (j : ℝ))
  let F := parentBoundaryBandTraceCap M 1 (5 + j)
  2 * v * E * (3683 / 2500 : ℝ) +
    2 * v * kappa * E * ((3683 / 2500 : ℝ) * F) +
    v * mu * E ^ 2 * ((3683 / 2500 : ℝ) ^ 2 * F)

private theorem in_source_lemmaVH2kn_self_nonneg (rho : ℝ) :
    0 ≤ lemmaVH2kn rho rho := by
  rw [parent_boundary_mean_kn_shape]
  have hsqrt0 : 0 ≤ Real.sqrt (2 : ℝ) := Real.sqrt_nonneg _
  have hdiv : 0 ≤ (36 / 25 : ℝ) / Real.sqrt 2 :=
    div_nonneg (by norm_num) hsqrt0
  have hmul : 0 ≤ (57 / 200 : ℝ) * Real.sqrt 2 :=
    mul_nonneg (by norm_num) hsqrt0
  have hcoef : 0 ≤ (1 / 4 : ℝ) + (36 / 25 : ℝ) / Real.sqrt 2 +
      (57 / 200 : ℝ) * Real.sqrt 2 :=
    add_nonneg (add_nonneg (by norm_num) hdiv) hmul
  exact mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg rho)) hcoef

private theorem in_source_rate_le_protected_row
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero) (N : ℤ)
    (hpast : ∀ l < N, nativeInductionState M h l)
    (m : ℤ) (hm : m < N) (j : ℕ) (t : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    inSourceMeanRateActual M h m (5 + j) t ≤
      inSourceProtectedSlopeRow M h m j := by
  let sigma : ℝ := Annealed.sigmaBar M m
  let v := (q3ModelAmplitude M h (m + 1) / sigma) ^ 2
  let q : ℤ := m - ((5 + j : ℕ) : ℤ)
  let rho := cubeScaleFactor (originCube 2 q) /
    (q3ModelLength (m + 1)).val
  let kappa := lemmaVH2kn rho rho
  let mu := pureFluxCovarianceMu (pureFluxCovarianceA 0 (5 + j))
    (pureFluxCovarianceB 0 (5 + j))
  let R := sigma / (Annealed.sigmaBar M (m - (j : ℤ)) : ℝ)
  let F := parentBoundaryBandTraceCap M 1 (5 + j)
  let E := (3 : ℝ) ^ (2 * M.gamma * (j : ℝ))
  have hpastM : ∀ l < m, nativeInductionState M h l :=
    fun l hl => hpast l (hl.trans hm)
  have hqCast : q = m - ((5 + j : ℕ) : ℤ) := rfl
  have hrate := in_source_rate_eq_parent_shell_generator M h m (5 + j) t
  have hrow := parent_boundary_mean_protected_expectation
    M h hM hγ q m j hqCast 1 (by norm_num) hpastM t ht.2 (0 : Fin 1)
  have hratio :
      (q3ModelAmplitude M h (m + 1)) ^ 2 /
        (Annealed.sigmaBar M m : ℝ) ^ 2 = v := by
    dsimp [v, sigma]
    rw [← div_pow]
  simp only [Nat.zero_add, Nat.cast_one, Fin.val_zero,
    Nat.add_sub_cancel_right] at hrow
  rw [hratio] at hrow
  have hrow' :
      (∫ ω, parentBoundaryMeanShellGenerator M h q m 1 t (0 : Fin 1) ω
        ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
        2 * v * R * (3683 / 2500 : ℝ) +
          2 * v * kappa * R * ((3683 / 2500 : ℝ) * F) +
          v * mu * R ^ 2 * ((3683 / 2500 : ℝ) ^ 2 * F) := by
    simpa [sigma, v, rho, kappa, mu, R, F] using hrow
  have hR := parent_boundary_common_protected_frame_depth M m j
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have hR0 : 0 ≤ R := by
    dsimp [R, sigma]
    exact div_nonneg (Annealed.sigmaBar_characterization M m).1.le
      (Annealed.sigmaBar_characterization M (m - (j : ℤ))).1.le
  have hE : 0 ≤ E := by positivity
  have hF : 0 ≤ F := parent_boundary_band_trace_cap_nonneg M 1 (5 + j)
  have hkappa : 0 ≤ kappa := by
    change 0 ≤ lemmaVH2kn rho rho
    exact in_source_lemmaVH2kn_self_nonneg rho
  have hmu : 0 ≤ mu := (pureFlux_covariance_mu_lower _ _).1
  have hRle : R ≤ E := by
    simpa [R, E, sigma] using hR.2
  have hratecap :
      inSourceMeanRateActual M h m (5 + j) t ≤
        2 * v * R * (3683 / 2500 : ℝ) +
          2 * v * kappa * R * ((3683 / 2500 : ℝ) * F) +
          v * mu * R ^ 2 * ((3683 / 2500 : ℝ) ^ 2 * F) := by
    rw [hrate]
    exact hrow'
  unfold inSourceProtectedSlopeRow
  dsimp only [sigma, v, q, rho, kappa, mu, R, F, E]
  calc
    _ ≤ 2 * v * R * (3683 / 2500 : ℝ) +
        2 * v * kappa * R * ((3683 / 2500 : ℝ) * F) +
        v * mu * R ^ 2 * ((3683 / 2500 : ℝ) ^ 2 * F) := hratecap
    _ ≤ 2 * v * ((3 : ℝ) ^ (2 * M.gamma * (j : ℝ))) *
          (3683 / 2500 : ℝ) +
        2 * v * kappa * ((3 : ℝ) ^ (2 * M.gamma * (j : ℝ))) *
          ((3683 / 2500 : ℝ) * F) +
        v * mu * ((3 : ℝ) ^ (2 * M.gamma * (j : ℝ))) ^ 2 *
          ((3683 / 2500 : ℝ) ^ 2 * F) := by
      apply add_le_add
      · apply add_le_add
        · calc
            2 * v * R * (3683 / 2500 : ℝ) =
                (2 * v) * R * (3683 / 2500 : ℝ) := by ring
            _ ≤ (2 * v) * E * (3683 / 2500 : ℝ) := by
              exact mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left hRle (by positivity)) (by norm_num)
            _ = 2 * v * E * (3683 / 2500 : ℝ) := by ring
        · calc
            2 * v * kappa * R * ((3683 / 2500 : ℝ) * F) =
                (2 * v * kappa) * R * ((3683 / 2500 : ℝ) * F) := by ring
            _ ≤ (2 * v * kappa) * E * ((3683 / 2500 : ℝ) * F) := by
              exact mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left hRle (by positivity)) (by positivity)
            _ = 2 * v * kappa * E * ((3683 / 2500 : ℝ) * F) := by ring
      · calc
          v * mu * R ^ 2 * ((3683 / 2500 : ℝ) ^ 2 * F) =
              (v * mu) * R ^ 2 * ((3683 / 2500 : ℝ) ^ 2 * F) := by ring
          _ ≤ (v * mu) * E ^ 2 * ((3683 / 2500 : ℝ) ^ 2 * F) := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hR0 hRle 2)
                (by positivity)) (by positivity)
          _ = v * mu * E ^ 2 * ((3683 / 2500 : ℝ) ^ 2 * F) := by ring
    _ = _ := by ring

/-- The actual one-shell OLD-frame source slope at depth `5+j` is bounded by
the protected generator row. The only model assumptions are the Gaussian,
gamma, and strict-past source inputs; the frame transport `R ≤ E` is proved
internally and no coarse `inSourceOldEnergyCap` cap is used. -/
theorem inSourceMeanSlopeActual_le_protectedRow
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero) (N : ℤ)
    (hpast : ∀ l < N, nativeInductionState M h l)
    (m : ℤ) (hm : m < N) (j : ℕ) :
    let sigma : ℝ := Annealed.sigmaBar M m
    let v := (q3ModelAmplitude M h (m + 1) / sigma) ^ 2
    let q : ℤ := m - ((5 + j : ℕ) : ℤ)
    let rho := cubeScaleFactor (originCube 2 q) /
      (q3ModelLength (m + 1)).val
    let kappa := lemmaVH2kn rho rho
    let mu := pureFluxCovarianceMu (pureFluxCovarianceA 0 (5 + j))
      (pureFluxCovarianceB 0 (5 + j))
    let E := (3 : ℝ) ^ (2 * M.gamma * (j : ℝ))
    let F := parentBoundaryBandTraceCap M 1 (5 + j)
    inSourceMeanSlopeActual M h m (5 + j) ≤
      2 * v * E * (3683 / 2500 : ℝ) +
        2 * v * kappa * E * ((3683 / 2500 : ℝ) * F) +
        v * mu * E ^ 2 * ((3683 / 2500 : ℝ) ^ 2 * F) := by
  let sigma : ℝ := Annealed.sigmaBar M m
  let v := (q3ModelAmplitude M h (m + 1) / sigma) ^ 2
  let q : ℤ := m - ((5 + j : ℕ) : ℤ)
  let rho := cubeScaleFactor (originCube 2 q) /
    (q3ModelLength (m + 1)).val
  let kappa := lemmaVH2kn rho rho
  let mu := pureFluxCovarianceMu (pureFluxCovarianceA 0 (5 + j))
    (pureFluxCovarianceB 0 (5 + j))
  let E := (3 : ℝ) ^ (2 * M.gamma * (j : ℝ))
  let F := parentBoundaryBandTraceCap M 1 (5 + j)
  have hcap0 : 0 ≤ inSourceProtectedSlopeRow M h m j := by
    unfold inSourceProtectedSlopeRow
    have hv : 0 ≤ (q3ModelAmplitude M h (m + 1) /
        Annealed.sigmaBar M m) ^ 2 := sq_nonneg _
    have hE : 0 ≤ (3 : ℝ) ^ (2 * M.gamma * (j : ℝ)) := by positivity
    have hF : 0 ≤ parentBoundaryBandTraceCap M 1 (5 + j) :=
      parent_boundary_band_trace_cap_nonneg M 1 (5 + j)
    have hrho : 0 ≤ cubeScaleFactor (originCube 2
        (m - ((5 + j : ℕ) : ℤ))) /
          (q3ModelLength (m + 1)).val :=
      div_nonneg (Triadic.cubeScaleFactor_pos' _).le
        (q3ModelLength (m + 1)).property.le
    have hkappa : 0 ≤ lemmaVH2kn
        (cubeScaleFactor (originCube 2
          (m - ((5 + j : ℕ) : ℤ))) /
            (q3ModelLength (m + 1)).val)
        (cubeScaleFactor (originCube 2
          (m - ((5 + j : ℕ) : ℤ))) /
            (q3ModelLength (m + 1)).val) := by
      exact in_source_lemmaVH2kn_self_nonneg _
    have hmu : 0 ≤ pureFluxCovarianceMu
        (pureFluxCovarianceA 0 (5 + j))
        (pureFluxCovarianceB 0 (5 + j)) :=
      (pureFlux_covariance_mu_lower _ _).1
    positivity
  have hrate := in_source_rate_le_protected_row
    M h hM hγ N hpast m hm j
  change inSourceMeanSlopeActual M h m (5 + j) ≤
      inSourceProtectedSlopeRow M h m j
  let S := inSourceMeanRateActual M h m (5 + j) '' Set.Icc (0 : ℝ) 1
  have hnonempty : S.Nonempty := by
    refine ⟨inSourceMeanRateActual M h m (5 + j) 0, ?_⟩
    exact ⟨0, ⟨le_rfl, by norm_num⟩, rfl⟩
  have hsup : sSup S ≤ inSourceProtectedSlopeRow M h m j := by
    apply csSup_le hnonempty
    rintro x ⟨t, ht, rfl⟩
    exact hrate t ht
  unfold inSourceMeanSlopeActual
  exact max_le hcap0 hsup

end
end ASDExplicitGamma.Inverse
