module

public import ASDExplicitGamma.Native.HeatVHEATRefinedDriftAssembly
public import ASDExplicitGamma.Native.HeatVHEATSourceCarrierGen
public import ASDExplicitGamma.Native.HeatVHEATRefinedShellLawGen
public import ASDExplicitGamma.Native.HeatVHEATDriftSourceClocksGen
public import ASDExplicitGamma.Native.HeatVHEATRefinedSourceProfilesGen
public import ASDExplicitGamma.Native.HeatVHEATRefinedSourceTransportGen
public import ASDExplicitGamma.Native.HeatVHEATDriftSourceGeometryGen
public import ASDExplicitGamma.Native.HeatVHEATDriftSourceBankGen
public import ASDExplicitGamma.Native.HeatVHEATDriftBankIdentityGen
public import ASDExplicitGamma.Native.HeatVHEATDriftBankMeasurableGen
public import ASDExplicitGamma.Native.HeatVHEATDriftSourceIntegrandGen
public import ASDExplicitGamma.Native.HeatVHEATDriftSourceNormsGen
public import ASDExplicitGamma.Native.HeatVHEATDriftSourceExpectationGen
public import ASDExplicitGamma.Native.HeatVHEATRefinedCoefficientsGen
public import ASDExplicitGamma.Native.HeatVHEATDriftConfiguredCoefficientsGen
public import ASDExplicitGamma.Native.HeatVHEATDriftConfiguredExpectationGen
public import ASDExplicitGamma.Native.HeatVHEATDriftRefinedProfileGen
public import ASDExplicitGamma.Native.HeatVHEATDriftRefinedExpectationGen
public import ASDExplicitGamma.Native.HeatVHEATDriftRefinedPhysicalGen
public import ASDExplicitGamma.Native.HeatVHEATDriftRefinedBindingGen
public import ASDExplicitGamma.Native.HeatVHEATRefinedSourceObserverGen
public import ASDExplicitGamma.Native.HeatVHEATDriftRefinedActualGen
public import ASDExplicitGamma.Native.HeatVHEATRefinedAssemblyGen
public import ASDExplicitGamma.Native.HeatVHEATRefinedRowGen
public import ASDExplicitGamma.Native.Q3GridOverlapGen
public import ASDExplicitGamma.Native.HeatVHEATBracketRefinedSupportGeometryGen
public import ASDExplicitGamma.Native.HeatVHEATBracketRefinedGeometryGen
public import ASDExplicitGamma.Native.HeatVHEATBracketRefinedObservationGen
public import ASDExplicitGamma.Native.HeatVHEATBracketRefinedParentLawGen
public import ASDExplicitGamma.Native.HeatVHEATBracketRefinedSourceMapGen
public import ASDExplicitGamma.Native.HeatVHEATBracketRefinedMeanVarianceGen
public import ASDExplicitGamma.Native.HeatVHEATBracketRefinedRemainderGen
public import ASDExplicitGamma.Native.HeatVHEATBracketRefinedMeanChildBoundGen
public import ASDExplicitGamma.Native.HeatVHEATBracketMeanRieszSupportGen
public import ASDExplicitGamma.Native.HeatVHEATBracketParentRieszGen
public import ASDExplicitGamma.Native.HeatVHEATBracketMeanDerivativeGen
public import ASDExplicitGamma.Native.HeatVHEATBracketMeanDerivativeCLMGen
public import ASDExplicitGamma.Native.HeatVHEATBracketMeanRieszIdentityGen
public import ASDExplicitGamma.Native.HeatVHEATBracketRefinedMeanRieszIdentityGen
public import ASDExplicitGamma.Native.HeatVHEATBracketRefinedMeanAverageProfilesGen
public import ASDExplicitGamma.Native.HeatVHEATBracketRefinedMeanBracketGen
public import ASDExplicitGamma.Native.HeatVHEATBracketSourceCarrierGen

/-! The `ns`-shell generalization of `HeatVHEATRefinedDriftAssembly`. -/

@[expose] public section


namespace ASDExplicitGamma.Native

open MeasureTheory Homogenization Gaussian Algsuperdiff.Section3 Numerics.Native
open ASDExplicitGamma.Inverse ASDExplicitGamma.Response ASDExplicitGamma.Variational
open ASDExplicitGamma.Triadic ASDExplicitGamma.Main
open scoped ENNReal NNReal
open scoped RealInnerProductSpace
noncomputable section

variable (ns : ℕ) [NeZero ns]

local instance heatVHEATRefinedDriftAssemblyIndexNeZeroGenRefinedDriftAssembly :
    NeZero (3 ^ 10 * 3 ^ 10) := ⟨by norm_num⟩

local instance heatVHEATRefinedDriftAssemblyChildFiniteGenRefinedDriftAssembly (m : ℤ)
    (i : nativeHeatQ3RefinedCarrierIndex) :
    IsFiniteMeasure (volumeMeasureOn (cubeSet (nativeHeatQ3RefinedCarrierChild m i))) :=
  ((isBounded_cubeSet (nativeHeatQ3RefinedCarrierChild m i)).isBoundedDomain).isFiniteMeasure_restrict_volume

local instance heatVHEATRefinedDriftAssemblyChildCompactGenRefinedDriftAssembly (m : ℤ)
    (i : nativeHeatQ3RefinedCarrierIndex) :
    CompactSpace (closure (cubeSet (nativeHeatQ3RefinedCarrierChild m i))) :=
  isCompact_iff_compactSpace.mp
    (isBounded_cubeSet (nativeHeatQ3RefinedCarrierChild m i)).isCompact_closure

/-- The actual old field plus the physical refined band, before the
independent auxiliary child-center shift. -/
noncomputable def nativeHeatQ3RefinedCarrierPhysicalBaseChildrenGen
    (m : ℤ) (t : ℝ) (ω : Cutoff.CutoffSample 2) :
    ∀ i : nativeHeatQ3RefinedCarrierIndex,
      C(closure (cubeSet (nativeHeatQ3RefinedCarrierChild m i)), ℝ) :=
  nativeHeatQ3RefinedCarrierOldMap m
    (olderField (nativeHeatQ3RefinedCarrierDomain m) (m + 1) ω +
      Real.sqrt t • modelBand (nativeHeatQ3RefinedCarrierDomain m)
        (nativeHeatQ3RefinedCarrierPhysicalShellsGen m ns) ω)

theorem nativeHeatQ3RefinedCarrierPhysicalAverage_eq_childMeanTrace_Gen
    (M : ABKModel 2) (m : ℤ) (t : ℝ)
    (g : nativeHeatQ3RefinedCarrierIndex → (ℕ → ℝ) → ℝ)
    (z : Cutoff.CutoffSample 2 × (ℕ → ℝ)) :
    (heatVHEATDriftRefinedPhysicalAverageGen ns) M m t g z =
      childMeanTrace
        (fun i : nativeHeatQ3RefinedCarrierIndex =>
          cubeSet (nativeHeatQ3RefinedCarrierChild m i))
        (fun i => measurableSet_cubeSet (nativeHeatQ3RefinedCarrierChild m i))
        (fun i => volume_cubeSet_toReal_pos (nativeHeatQ3RefinedCarrierChild m i))
        M.nu (Annealed.sigmaBar M (m + 1)) M.nu_pos
        (Annealed.sigmaBar_characterization M (m + 1)).1
        (fun i => (heatVHEATDriftRefinedChildFieldGen ns) m t g z i) := by
  classical
  have hw : (((3 ^ 10 * 3 ^ 10 : ℕ) : ℝ)⁻¹) =
      heatVHEATDriftRefinedWeight := by
    norm_num [heatVHEATDriftRefinedWeight]
  unfold heatVHEATDriftRefinedPhysicalAverageGen
  unfold childMeanTrace
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← hw]
  rfl

/-- The off-diagonal first-order term as it appears in the actual
`cancelledGenerator` estimate, before its child sum is distributed. -/
def nativeHeatQ3RefinedCarrierOffDiagonalGeneratorRowGen
    (M : ABKModel 2) (h : ℝ) (m : ℤ) (t : ℝ) (k : ℕ)
    (g : nativeHeatQ3RefinedCarrierIndex → (ℕ → ℝ) → ℝ)
    (z : Cutoff.CutoffSample 2 × (ℕ → ℝ)) : ℝ :=
  (k : ℝ) * Real.rpow
      (childMeanTrace
        (fun i : nativeHeatQ3RefinedCarrierIndex =>
          cubeSet (nativeHeatQ3RefinedCarrierChild m i))
        (fun i => measurableSet_cubeSet (nativeHeatQ3RefinedCarrierChild m i))
        (fun i => volume_cubeSet_toReal_pos (nativeHeatQ3RefinedCarrierChild m i))
        M.nu (Annealed.sigmaBar M (m + 1)) M.nu_pos
        (Annealed.sigmaBar_characterization M (m + 1)).1
        (fun i => (heatVHEATDriftRefinedChildFieldGen ns) m t g z i))
      ((k : ℝ) - 1) *
      (((3 ^ 10 * 3 ^ 10 : ℕ) : ℝ)⁻¹ *
        ∑ i : nativeHeatQ3RefinedCarrierIndex, ∑ d : Fin ns,
          (nativeHeatQ3RefinedCarrierChildSignedOffDiagonalProfileGen ns) M h m i d
            (Annealed.sigmaBar M (m + 1))
            ((heatVHEATDriftRefinedChildFieldGen ns) m t g z i))

/-- The normalized off-diagonal first-order row on the actual physical
refined child fields. The coefficient is the generator's `9^10` child
average, with all nine physical shells retained. -/
def nativeHeatQ3RefinedCarrierOffDiagonalFirstOrderRowGen
    (M : ABKModel 2) (h : ℝ) (m : ℤ) (t : ℝ) (k : ℕ)
    (g : nativeHeatQ3RefinedCarrierIndex → (ℕ → ℝ) → ℝ)
    (z : Cutoff.CutoffSample 2 × (ℕ → ℝ)) : ℝ :=
  ∑ i : nativeHeatQ3RefinedCarrierIndex,
    (((3 ^ 10 * 3 ^ 10 : ℕ) : ℝ)⁻¹) *
      ((k : ℝ) * ((heatVHEATDriftRefinedPhysicalAverageGen ns) M m t g z) ^ (k - 1) *
        ∑ d : Fin ns,
          (nativeHeatQ3RefinedCarrierChildSignedOffDiagonalProfileGen ns) M h m i d
            (Annealed.sigmaBar M (m + 1))
            ((heatVHEATDriftRefinedChildFieldGen ns) m t g z i))

/-- The generator's normalized off-diagonal row is exactly the physical
drift integrand, including the `9^10` normalization. -/
theorem nativeHeatQ3RefinedCarrierOffDiagonalFirstOrderRow_eq_Gen
    (M : ABKModel 2) (h : ℝ) (m : ℤ) (t : ℝ) (k : ℕ)
    (g : nativeHeatQ3RefinedCarrierIndex → (ℕ → ℝ) → ℝ)
    (z : Cutoff.CutoffSample 2 × (ℕ → ℝ)) :
    (nativeHeatQ3RefinedCarrierOffDiagonalFirstOrderRowGen ns) M h m t k g z =
      (heatVHEATDriftRefinedPhysicalDriftGen ns) M h m t k g z := by
  classical
  have hw : (((3 ^ 10 * 3 ^ 10 : ℕ) : ℝ)⁻¹) =
      heatVHEATDriftRefinedWeight := by
    norm_num [heatVHEATDriftRefinedWeight]
  rw [nativeHeatQ3RefinedCarrierOffDiagonalFirstOrderRowGen]
  unfold heatVHEATDriftRefinedPhysicalDriftGen
  apply Finset.sum_congr rfl
  intro i hi
  rw [hw]

/-- Distributing the moment derivative factor over the actual `9^10`
normalized child sum gives the row above. This is the precise first-order
off-diagonal term displayed by the refined generator estimate. -/
theorem nativeHeatQ3RefinedCarrierOffDiagonalFirstOrderRow_eq_generatorForm_Gen
    (M : ABKModel 2) (h : ℝ) (m : ℤ) (t : ℝ) (k : ℕ)
    (g : nativeHeatQ3RefinedCarrierIndex → (ℕ → ℝ) → ℝ)
    (z : Cutoff.CutoffSample 2 × (ℕ → ℝ)) :
    (k : ℝ) * ((heatVHEATDriftRefinedPhysicalAverageGen ns) M m t g z) ^ (k - 1) *
        (((3 ^ 10 * 3 ^ 10 : ℕ) : ℝ)⁻¹ *
          ∑ i : nativeHeatQ3RefinedCarrierIndex, ∑ d : Fin ns,
            (nativeHeatQ3RefinedCarrierChildSignedOffDiagonalProfileGen ns) M h m i d
              (Annealed.sigmaBar M (m + 1))
              ((heatVHEATDriftRefinedChildFieldGen ns) m t g z i)) =
      (nativeHeatQ3RefinedCarrierOffDiagonalFirstOrderRowGen ns) M h m t k g z := by
  classical
  unfold nativeHeatQ3RefinedCarrierOffDiagonalFirstOrderRowGen
  let a : ℝ := (k : ℝ) *
    ((heatVHEATDriftRefinedPhysicalAverageGen ns) M m t g z) ^ (k - 1)
  calc
    a * (((3 ^ 10 * 3 ^ 10 : ℕ) : ℝ)⁻¹ *
        ∑ i : nativeHeatQ3RefinedCarrierIndex, ∑ d : Fin ns,
          (nativeHeatQ3RefinedCarrierChildSignedOffDiagonalProfileGen ns) M h m i d
            (Annealed.sigmaBar M (m + 1))
            ((heatVHEATDriftRefinedChildFieldGen ns) m t g z i)) =
      (((3 ^ 10 * 3 ^ 10 : ℕ) : ℝ)⁻¹) *
        (a * ∑ i : nativeHeatQ3RefinedCarrierIndex, ∑ d : Fin ns,
          (nativeHeatQ3RefinedCarrierChildSignedOffDiagonalProfileGen ns) M h m i d
            (Annealed.sigmaBar M (m + 1))
            ((heatVHEATDriftRefinedChildFieldGen ns) m t g z i)) := by ring
    _ = (((3 ^ 10 * 3 ^ 10 : ℕ) : ℝ)⁻¹) *
        ∑ i : nativeHeatQ3RefinedCarrierIndex,
          a * ∑ d : Fin ns,
            (nativeHeatQ3RefinedCarrierChildSignedOffDiagonalProfileGen ns) M h m i d
              (Annealed.sigmaBar M (m + 1))
              ((heatVHEATDriftRefinedChildFieldGen ns) m t g z i) := by
        rw [Finset.mul_sum]
    _ = ∑ i : nativeHeatQ3RefinedCarrierIndex,
        (((3 ^ 10 * 3 ^ 10 : ℕ) : ℝ)⁻¹) *
          (a * ∑ d : Fin ns,
            (nativeHeatQ3RefinedCarrierChildSignedOffDiagonalProfileGen ns) M h m i d
              (Annealed.sigmaBar M (m + 1))
              ((heatVHEATDriftRefinedChildFieldGen ns) m t g z i)) := by
        calc
          _ = (((3 ^ 10 * 3 ^ 10 : ℕ) : ℝ)⁻¹) *
              ∑ i : nativeHeatQ3RefinedCarrierIndex,
                a * ∑ d : Fin ns,
                  (nativeHeatQ3RefinedCarrierChildSignedOffDiagonalProfileGen ns) M h m i d
                    (Annealed.sigmaBar M (m + 1))
                    ((heatVHEATDriftRefinedChildFieldGen ns) m t g z i) := by
              rw [Finset.mul_sum]
          _ = _ := by rw [Finset.mul_sum]

/-- The same identity with the actual `childMeanTrace` and real power
exponent used by `cancelledGenerator`. -/
theorem nativeHeatQ3RefinedCarrierOffDiagonalFirstOrderRow_eq_actualGeneratorForm_Gen
    (M : ABKModel 2) (h : ℝ) (m : ℤ) (t : ℝ) (k : ℕ) (hk : 1 ≤ k)
    (g : nativeHeatQ3RefinedCarrierIndex → (ℕ → ℝ) → ℝ)
    (z : Cutoff.CutoffSample 2 × (ℕ → ℝ)) :
    (k : ℝ) * Real.rpow
        (childMeanTrace
          (fun i : nativeHeatQ3RefinedCarrierIndex =>
            cubeSet (nativeHeatQ3RefinedCarrierChild m i))
          (fun i => measurableSet_cubeSet (nativeHeatQ3RefinedCarrierChild m i))
          (fun i => volume_cubeSet_toReal_pos (nativeHeatQ3RefinedCarrierChild m i))
          M.nu (Annealed.sigmaBar M (m + 1)) M.nu_pos
          (Annealed.sigmaBar_characterization M (m + 1)).1
          (fun i => (heatVHEATDriftRefinedChildFieldGen ns) m t g z i))
        ((k : ℝ) - 1) *
        (((3 ^ 10 * 3 ^ 10 : ℕ) : ℝ)⁻¹ *
          ∑ i : nativeHeatQ3RefinedCarrierIndex, ∑ d : Fin ns,
            (nativeHeatQ3RefinedCarrierChildSignedOffDiagonalProfileGen ns) M h m i d
              (Annealed.sigmaBar M (m + 1))
              ((heatVHEATDriftRefinedChildFieldGen ns) m t g z i)) =
      (nativeHeatQ3RefinedCarrierOffDiagonalFirstOrderRowGen ns) M h m t k g z := by
  have hmean := (nativeHeatQ3RefinedCarrierPhysicalAverage_eq_childMeanTrace_Gen ns) M m t g z
  have hpow : Real.rpow
      (childMeanTrace
        (fun i : nativeHeatQ3RefinedCarrierIndex =>
          cubeSet (nativeHeatQ3RefinedCarrierChild m i))
        (fun i => measurableSet_cubeSet (nativeHeatQ3RefinedCarrierChild m i))
        (fun i => volume_cubeSet_toReal_pos (nativeHeatQ3RefinedCarrierChild m i))
        M.nu (Annealed.sigmaBar M (m + 1)) M.nu_pos
        (Annealed.sigmaBar_characterization M (m + 1)).1
        (fun i => (heatVHEATDriftRefinedChildFieldGen ns) m t g z i))
      ((k : ℝ) - 1) =
      (childMeanTrace
        (fun i : nativeHeatQ3RefinedCarrierIndex =>
          cubeSet (nativeHeatQ3RefinedCarrierChild m i))
        (fun i => measurableSet_cubeSet (nativeHeatQ3RefinedCarrierChild m i))
        (fun i => volume_cubeSet_toReal_pos (nativeHeatQ3RefinedCarrierChild m i))
        M.nu (Annealed.sigmaBar M (m + 1)) M.nu_pos
        (Annealed.sigmaBar_characterization M (m + 1)).1
        (fun i => (heatVHEATDriftRefinedChildFieldGen ns) m t g z i)) ^ (k - 1) := by
    rw [show (k : ℝ) - 1 = ((k - 1 : ℕ) : ℝ) by
      rw [Nat.cast_sub hk]
      norm_num]
    exact Real.rpow_natCast _ _
  calc
    _ = (k : ℝ) *
        ((heatVHEATDriftRefinedPhysicalAverageGen ns) M m t g z) ^ (k - 1) *
          (((3 ^ 10 * 3 ^ 10 : ℕ) : ℝ)⁻¹ *
            ∑ i : nativeHeatQ3RefinedCarrierIndex, ∑ d : Fin ns,
              (nativeHeatQ3RefinedCarrierChildSignedOffDiagonalProfileGen ns) M h m i d
                (Annealed.sigmaBar M (m + 1))
                ((heatVHEATDriftRefinedChildFieldGen ns) m t g z i)) := by
          rw [hmean, hpow]
    _ = _ := (nativeHeatQ3RefinedCarrierOffDiagonalFirstOrderRow_eq_generatorForm_Gen ns)
      M h m t k g z

/-- The actual real-power generator row agrees pointwise with the physical
drift integrand after replacing the generator mean by its physical average. -/
theorem nativeHeatQ3RefinedCarrierOffDiagonalGeneratorRow_eq_Gen
    (M : ABKModel 2) (h : ℝ) (m : ℤ) (t : ℝ) (k : ℕ) (hk : 1 ≤ k)
    (g : nativeHeatQ3RefinedCarrierIndex → (ℕ → ℝ) → ℝ)
    (z : Cutoff.CutoffSample 2 × (ℕ → ℝ)) :
    (nativeHeatQ3RefinedCarrierOffDiagonalGeneratorRowGen ns) M h m t k g z =
      (heatVHEATDriftRefinedPhysicalDriftGen ns) M h m t k g z := by
  unfold nativeHeatQ3RefinedCarrierOffDiagonalGeneratorRowGen
  rw [(nativeHeatQ3RefinedCarrierOffDiagonalFirstOrderRow_eq_actualGeneratorForm_Gen ns)
    M h m t k hk g z,
    (nativeHeatQ3RefinedCarrierOffDiagonalFirstOrderRow_eq_Gen ns) M h m t k g z]

/-- A common refined-shell center direction has exactly the diagonal source
profile recorded for that child and shell. This identifies the positive center
covariance before it is canceled from the physical generator. -/
theorem nativeHeatQ3RefinedCarrierChildCenterCovariance_eq_profile_shell_Gen
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (m : ℤ)
    (Ffam : NativeHeatQ3RefinedCarrierFreshShellFamilyGen M m ns) (i : nativeHeatQ3RefinedCarrierIndex) (d : Fin ns)
    (σ : ℝ) (hσ : 0 < σ)
    (x : C(closure (cubeSet (nativeHeatQ3RefinedCarrierChild m i)), ℝ)) :
    let Q := nativeHeatQ3RefinedCarrierChild m i
    (1 / 2 : ℝ) * modelCovarianceTrace
      (childTraceObservable (measurableSet_cubeSet Q)
        (volume_cubeSet_toReal_pos Q) M.nu σ M.nu_pos hσ)
      (fun j => ContinuousMap.const (closure (cubeSet Q))
        ((Ffam.factor d (Ffam.direction d j))
          (nativeHeatQ3RefinedCarrierCenter m i))) x =
      (nativeHeatQ3RefinedCarrierChildCenterDriftProfileGen ns) M h m i d σ x := by
  classical
  let Q := nativeHeatQ3RefinedCarrierChild m i
  let K := closure (cubeSet Q)
  let K₀ := closure (cubeSet (originCube 2 Q.scale))
  let A := nativeHeat_translateTriadicFieldToOrigin Q
  let Φ := modelTraceObservable Q.scale M.nu σ
  let center := pureFluxParentCenter Q.scale
  let S : ℕ → ℝ := fun j =>
    (Ffam.factor d (Ffam.direction d j)) (nativeHeatQ3RefinedCarrierCenter m i)
  let H : ℕ → C(K, ℝ) := fun j => ContinuousMap.const K (S j)
  have hH : Summable (fun j => ‖H j‖ ^ 2) := by
    let J : C(nativeHeatQ3RefinedCarrierDomain m, ℝ) →L[ℝ] C(K, ℝ) :=
      (ContinuousMap.evalCLM ℝ (nativeHeatQ3RefinedCarrierCenter m i)).smulRight
        (1 : C(K, ℝ))
    have hJ (j : ℕ) : H j = J (Ffam.factor d (Ffam.direction d j)) := by
      ext y
      change S j =
        (((Ffam.factor d (Ffam.direction d j))
          (nativeHeatQ3RefinedCarrierCenter m i)) • (1 : C(K, ℝ))) y
      simp [S]
    have hsum := summable_sq_bounded_image _ (Ffam.squareSummable d)
      (J.comp (Ffam.factor d))
    exact hsum.congr (fun j => by
      simp only [ContinuousLinearMap.comp_apply]
      rw [hJ j])
  have hΦ : HasPolynomiallyBoundedC2Derivatives Φ :=
    modelTraceObservable_hasPolynomiallyBoundedC2Derivatives
      Q.scale M.nu σ M.nu_pos hσ
  have hfun :
      childTraceObservable (measurableSet_cubeSet Q)
        (volume_cubeSet_toReal_pos Q) M.nu σ M.nu_pos hσ = Φ ∘ A := by
    funext y
    exact nativeHeatQ3RefinedCarrierChildTraceObservable_toOrigin
      Q M.nu σ M.nu_pos hσ y
  have htrace := nativeHeat_modelCovarianceTrace_comp_continuousLinearMap
    A H hH Φ hΦ.1 x
  have hconstA (a : ℝ) :
      A (ContinuousMap.const K a) = ContinuousMap.const K₀ a := by
    ext y
    rfl
  have hdirs : (fun j => A (H j)) =
      (fun j => ContinuousMap.const K₀ (S j)) := by
    funext j
    simpa only [H] using hconstA (S j)
  have htrace' : modelCovarianceTrace
      (childTraceObservable (measurableSet_cubeSet Q)
        (volume_cubeSet_toReal_pos Q) M.nu σ M.nu_pos hσ)
      H x = modelCovarianceTrace Φ
        (fun j => ContinuousMap.const K₀ (S j)) (A x) := by
    calc
      _ = modelCovarianceTrace (Φ ∘ A) H x := by rw [hfun]
      _ = modelCovarianceTrace Φ (fun j => A (H j)) (A x) := htrace
      _ = _ := by rw [hdirs]
  let p := finProdFinEquiv.symm i
  let amp := q3ModelAmplitude M h
    (nativeHeatQ3RefinedCarrierPhysicalShellsGen m ns d)
  let len := q3ModelLength
    (nativeHeatQ3RefinedCarrierPhysicalShellsGen m ns d)
  let qSection : Gaussian.WhiteNoise :=
    q3Section amp (q3GridKernelScale 10 (d.val + 2)) h3Zero
      (q3GridRectangleCenter 10 p)
  let pts : Unit → nativeHeatQ3RefinedCarrierDomain m :=
    fun _ => nativeHeatQ3RefinedCarrierCenter m i
  let ptsVec : Unit → Vec 2 := fun _ => cubeCenter Q
  let weights : Unit → ℝ := fun _ => 1
  let sections : Unit → Gaussian.WhiteNoise := fun _ => qSection
  have hpts (u : Unit) : (pts u : Vec 2) = ptsVec u := by rfl
  have hkernel : q3ShellCovariance M h
      (nativeHeatQ3RefinedCarrierPhysicalShellsGen m ns d) (cubeCenter Q) (cubeCenter Q) =
      ‖qSection‖ ^ 2 := by
    have hidx : finProdFinEquiv p = i := by
      exact Equiv.apply_symm_apply finProdFinEquiv i
    have hcenter : cubeCenter Q =
        cubeCenter (nativeHeatQ3RefinedCarrierChild m (finProdFinEquiv p)) := by
      simp only [Q, nativeHeatQ3RefinedCarrierChild]
      rw [hidx]
    have hker := (nativeHeatQ3RefinedCarrierShellKernel_eq_Gen ns) M h m d p p
    rw [← hcenter] at hker
    have hpcenter : (q3GridRectangleCenter 10 p : Vec 2) =
        q3GridCenterVector 10 p := rfl
    rw [← hpcenter] at hker
    have hker' : q3ShellCovariance M h
        (nativeHeatQ3RefinedCarrierPhysicalShellsGen m ns d) (cubeCenter Q) (cubeCenter Q) =
        ⟪qSection, qSection⟫ := by
      simpa [qSection, p, amp, nativeHeatQ3RefinedCarrierPhysicalShellsGen] using hker
    exact hker'.trans (real_inner_self_eq_norm_sq qSection)
  have hkernelInner : q3ShellCovariance M h
      (nativeHeatQ3RefinedCarrierPhysicalShellsGen m ns d) (cubeCenter Q) (cubeCenter Q) =
      ⟪qSection, qSection⟫ := by
    rw [hkernel, real_inner_self_eq_norm_sq]
  have hvariance := nativeHeatQ3RefinedCarrierShellObservationVariance_of_kernel_Gen (ns := ns)
    (I := Unit) M h hM m d Ffam pts ptsVec hpts weights sections
    (by intro u v; simpa only [ptsVec, sections] using hkernelInner)
  have hvarActual : ∑' j, (S j) ^ 2 = amp ^ 2 := by
    have hobs : ∑' j, (S j) ^ 2 = ‖qSection‖ ^ 2 := by
      simpa [S, pts, weights, sections,
        nativeHeatQ3FiniteCenterObservation_apply,
        nativeHeatQ3FiniteSectionSum] using hvariance
    calc
      _ = ‖qSection‖ ^ 2 := hobs
      _ = amp ^ 2 := by
        rw [← hkernel, q3ShellCovariance_diagonal, q3ModelAmplitude_sq]
  let Hq := pureFluxMainCubeQ3Directions Q.scale
    (q3ModelAmplitude M h
      (Q.scale + ((d.val + 2 : ℕ) : ℤ)))
    (q3ModelLength (Q.scale + ((d.val + 2 : ℕ) : ℤ)))
  have hvarCanon : ∑' j, (Hq j center) ^ 2 =
      (q3ModelAmplitude M h
        (Q.scale + ((d.val + 2 : ℕ) : ℤ))) ^ 2 :=
    pureFluxMainCubeQ3_parentCenter_variance Q.scale
      (q3ModelAmplitude M h
        (Q.scale + ((d.val + 2 : ℕ) : ℤ)))
      (q3ModelLength (Q.scale + ((d.val + 2 : ℕ) : ℤ)))
  have hscale : Q.scale = m := by
    simpa [Q] using nativeHeatQ3RefinedCarrierChild_scale m i
  have hvar : (∑' j, (S j) ^ 2) = ∑' j, (Hq j center) ^ 2 := by
    rw [hvarActual, hvarCanon]
    simp [amp, hscale, nativeHeatQ3RefinedCarrierPhysicalShellsGen_offset]
  have hscalar (s : ℕ → ℝ) :
      modelCovarianceTrace Φ
        (fun j => ContinuousMap.const K₀ (s j)) (A x) =
      (∑' j, (s j) ^ 2) *
        secondDirectionalDerivative Φ (A x) (1 : C(K₀, ℝ)) := by
    unfold modelCovarianceTrace
    have hterm (j : ℕ) :
        secondDirectionalDerivative Φ (A x)
          (ContinuousMap.const K₀ (s j)) =
        (s j) ^ 2 * secondDirectionalDerivative Φ (A x) (1 : C(K₀, ℝ)) := by
      have hc : ContinuousMap.const K₀ (s j) =
          (s j) • (1 : C(K₀, ℝ)) := by
        ext y
        simp
      have hFd : ContDiffAt ℝ 1 (fderiv ℝ Φ) (A x) :=
        hΦ.1.contDiffAt.fderiv_right
          (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)
      have hDirectional : ContDiffAt ℝ 1
          (fun y => fderiv ℝ Φ y (1 : C(K₀, ℝ))) (A x) :=
        hFd.clm_apply contDiffAt_const
      have hdiff := hDirectional.differentiableAt (by norm_num)
      rw [hc]
      unfold secondDirectionalDerivative
      have hfun : (fun y => fderiv ℝ Φ y
          ((s j) • (1 : C(K₀, ℝ)))) =
          fun y => (s j) * fderiv ℝ Φ y (1 : C(K₀, ℝ)) := by
        funext y
        simp [smul_eq_mul]
      rw [hfun, fderiv_const_mul hdiff (s j)]
      simp [smul_eq_mul]
      ring
    calc
      _ = ∑' j, (s j) ^ 2 *
          secondDirectionalDerivative Φ (A x) (1 : C(K₀, ℝ)) :=
            tsum_congr hterm
      _ = _ := tsum_mul_right
  let Cq : C(K₀, ℝ) →L[ℝ] (Fin 1 → ℝ) :=
    ContinuousLinearMap.pi fun _ => ContinuousMap.evalCLM ℝ center
  let Iq : (Fin 1 → ℝ) →L[ℝ] C(K₀, ℝ) :=
    (ContinuousLinearMap.proj (0 : Fin 1)).smulRight (1 : C(K₀, ℝ))
  let B := fderiv ℝ (fderiv ℝ Φ) (A x)
  have hHq : Summable (fun j => ‖Hq j‖ ^ 2) := by
    exact @summable_sq_bounded_image ℕ
      (MainCubeH3 Q.scale
        (q3ModelAmplitude M h
          (Q.scale + ((d.val + 2 : ℕ) : ℤ)))
        (q3ModelLength (Q.scale + ((d.val + 2 : ℕ) : ℤ))))
      C(K₀, ℝ) inferInstance
      (mainCubeH3InnerProductSpace Q.scale
        (q3ModelAmplitude M h
          (Q.scale + ((d.val + 2 : ℕ) : ℤ)))
        (q3ModelLength (Q.scale + ((d.val + 2 : ℕ) : ℤ)))).toNormedSpace
      inferInstance inferInstance
      (mainCubeQ3Directions Q.scale
        (q3ModelAmplitude M h
          (Q.scale + ((d.val + 2 : ℕ) : ℤ)))
        (q3ModelLength (Q.scale + ((d.val + 2 : ℕ) : ℤ))))
      (mainCubeQ3Directions_summable Q.scale
        (q3ModelAmplitude M h
          (Q.scale + ((d.val + 2 : ℕ) : ℤ)))
        (q3ModelLength (Q.scale + ((d.val + 2 : ℕ) : ℤ))))
      (mainCubeH3Value Q.scale
        (q3ModelAmplitude M h
          (Q.scale + ((d.val + 2 : ℕ) : ℤ)))
        (q3ModelLength (Q.scale + ((d.val + 2 : ℕ) : ℤ))))
  have hcanonCov :
      (1 / 2 : ℝ) * modelCovarianceTrace Φ
        (fun j => ContinuousMap.const K₀ (Hq j center)) (A x) =
      centerGenerator Hq Cq Iq B := by
    have hdir (j : ℕ) : Iq (Cq (Hq j)) =
        ContinuousMap.const K₀ (Hq j center) := by
      ext y
      simp [Iq, Cq, ContinuousMap.const_apply]
    have hterm (j : ℕ) :
        secondDirectionalDerivative Φ (A x)
          (ContinuousMap.const K₀ (Hq j center)) =
        B (Iq (Cq (Hq j))) (Iq (Cq (Hq j))) := by
      rw [← hdir j]
      exact second_fderiv_eq hΦ.1 (A x)
        (Iq (Cq (Hq j))) (Iq (Cq (Hq j)))
    calc
      _ = (1 / 2 : ℝ) * ∑' j,
          B (Iq (Cq (Hq j))) (Iq (Cq (Hq j))) := by
            unfold modelCovarianceTrace
            congr 1
            exact tsum_congr hterm
      _ = _ := center_generator_eq hHq Cq Iq B
  have hcenterGenerator := raw_trace_model_q3_center_shear_row
    Q.scale M.nu σ
    (q3ModelAmplitude M h
      (Q.scale + ((d.val + 2 : ℕ) : ℤ)))
    M.nu_pos hσ
    (q3ModelLength (Q.scale + ((d.val + 2 : ℕ) : ℤ))) (A x)
  have hprofile :
      (1 / 2 : ℝ) * modelCovarianceTrace Φ
        (fun j => ContinuousMap.const K₀ (S j)) (A x) =
      (nativeHeatQ3RefinedCarrierChildCenterDriftProfileGen ns) M h m i d σ x := by
    calc
      _ = (1 / 2 : ℝ) * modelCovarianceTrace Φ
          (fun j => ContinuousMap.const K₀ (Hq j center)) (A x) := by
            rw [hscalar, hvar, ← hscalar]
      _ = centerGenerator Hq Cq Iq B := hcanonCov
      _ = _ := by
        rw [hcenterGenerator]
        simp [nativeHeatQ3RefinedCarrierChildCenterDriftProfileGen,
          Q, A, Hq, Cq, Iq, B, center, K₀]
        ring
  calc
    _ = (1 / 2 : ℝ) * modelCovarianceTrace Φ
        (fun j => ContinuousMap.const K₀ (S j)) (A x) := by
          rw [htrace']
    _ = _ := hprofile

/-- The common center part of the mean-trace covariance is exactly the
normalized sum of the nine child center profiles. This keeps the first-order
cancellation available before applying the off-diagonal aggregation. -/
theorem nativeHeatQ3RefinedCarrierMeanCenterCovariance_eq_profileRows_Gen
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (m : ℤ)
    (Ffam : NativeHeatQ3RefinedCarrierFreshShellFamilyGen M m ns) (σ : ℝ) (hσ : 0 < σ)
    (x : ∀ i : nativeHeatQ3RefinedCarrierIndex,
      C(closure (cubeSet (nativeHeatQ3RefinedCarrierChild m i)), ℝ)) :
    let Q : nativeHeatQ3RefinedCarrierIndex → TriadicCube 2 :=
      fun i => nativeHeatQ3RefinedCarrierChild m i
    let U : nativeHeatQ3RefinedCarrierIndex → Set (Vec 2) := fun i => cubeSet (Q i)
    let hU : ∀ i, MeasurableSet (U i) := fun i => measurableSet_cubeSet (Q i)
    let hvol : ∀ i, 0 < (volume (U i)).toReal := fun i => volume_cubeSet_toReal_pos (Q i)
    let V : nativeHeatQ3RefinedCarrierIndex → Set (Vec 2) := fun i => closure (U i)
    let μ := childMeanTrace U hU hvol M.nu σ M.nu_pos hσ
    let I := childConstantMap V
    let C₀ := childCenterMap (nativeHeatQ3RefinedCarrierCenter m)
    (1 / 2 : ℝ) * modelCovarianceTrace μ
        (fun j => I (C₀ (nativeHeatQ3RefinedCarrierFreshShellSeriesFactorGen Ffam
          (nativeHeatQ3RefinedCarrierFreshShellSeriesDirectionsGen Ffam j)))) x =
      ((Fintype.card nativeHeatQ3RefinedCarrierIndex : ℝ)⁻¹ *
        ∑ i : nativeHeatQ3RefinedCarrierIndex, ∑ d : Fin ns,
          (nativeHeatQ3RefinedCarrierChildCenterDriftProfileGen ns) M h m i d σ (x i)) := by
  classical
  intro Q U hU hvol V μ I C₀
  let H := nativeHeatQ3RefinedCarrierFreshShellSeriesFactorGen Ffam
  let w := nativeHeatQ3RefinedCarrierFreshShellSeriesDirectionsGen Ffam
  let Cmap : C(nativeHeatQ3RefinedCarrierDomain m, ℝ) →L[ℝ]
      (∀ i : nativeHeatQ3RefinedCarrierIndex,
        C(closure (cubeSet (nativeHeatQ3RefinedCarrierChild m i)), ℝ)) := I.comp C₀
  have hA : Summable (fun j => ‖w j‖ ^ 2) :=
    nativeHeatQ3RefinedCarrierFreshShellSeriesSummableGen Ffam
  have hcard : (Fintype.card nativeHeatQ3RefinedCarrierIndex : ℝ) =
      ((3 ^ 10 * 3 ^ 10 : ℕ) : ℝ) := by
    norm_num [nativeHeatQ3RefinedCarrierIndex]
  have hlaw := nativeHeatQ3RefinedCarrierFreshShellSeriesLawGen Ffam
  have hμpoly : HasPolynomiallyBoundedC2Derivatives μ := by
    simpa [μ] using childMeanTrace_polynomial U hU hvol M.nu σ M.nu_pos hσ
  have hsplit := (nativeHeatQ3RefinedCarrierCovariance_eq_sum_actualShellRows_of_law_Gen ns)
    M h hM m Ffam hA hlaw Cmap hμpoly x
  have hchild (d : Fin ns) :
      (1 / 2 : ℝ) * modelCovarianceTrace μ
        (fun j => Cmap (Ffam.factor d (Ffam.direction d j))) x =
      (Fintype.card nativeHeatQ3RefinedCarrierIndex : ℝ)⁻¹ *
        ∑ i : nativeHeatQ3RefinedCarrierIndex,
          (nativeHeatQ3RefinedCarrierChildCenterDriftProfileGen ns) M h m i d σ (x i) := by
    have hmean := nativeHeat_childMeanTrace_covarianceTrace
      Q M.nu σ M.nu_pos hσ (Ffam.squareSummable d)
      (Cmap.comp (Ffam.factor d)) x
    simp only [ContinuousLinearMap.comp_apply] at hmean
    have hdir (i : nativeHeatQ3RefinedCarrierIndex) (j : ℕ) :
        (Cmap (Ffam.factor d (Ffam.direction d j))) i =
          ContinuousMap.const (V i)
            ((Ffam.factor d (Ffam.direction d j))
              (nativeHeatQ3RefinedCarrierCenter m i)) := by
      ext y
      simp [Cmap, I, C₀, childConstantMap, childCenterMap]
      rw [ContinuousMap.const_apply]
    rw [hmean]
    calc
      _ = (((3 ^ 10 * 3 ^ 10 : ℕ) : ℝ)⁻¹) *
          ((1 / 2 : ℝ) * ∑ i : nativeHeatQ3RefinedCarrierIndex,
            modelCovarianceTrace
              (childTraceObservable (hU i) (hvol i) M.nu σ M.nu_pos hσ)
              (fun j => (Cmap (Ffam.factor d (Ffam.direction d j))) i) (x i)) := by ring
      _ = (((3 ^ 10 * 3 ^ 10 : ℕ) : ℝ)⁻¹) *
          ∑ i : nativeHeatQ3RefinedCarrierIndex,
            ((1 / 2 : ℝ) * modelCovarianceTrace
              (childTraceObservable (hU i) (hvol i) M.nu σ M.nu_pos hσ)
              (fun j => (Cmap (Ffam.factor d (Ffam.direction d j))) i) (x i)) := by
            rw [Finset.mul_sum]
      _ = (Fintype.card nativeHeatQ3RefinedCarrierIndex : ℝ)⁻¹ *
          ∑ i : nativeHeatQ3RefinedCarrierIndex,
            (nativeHeatQ3RefinedCarrierChildCenterDriftProfileGen ns) M h m i d σ (x i) := by
            rw [← hcard]
            apply congrArg (fun z : ℝ =>
              (Fintype.card nativeHeatQ3RefinedCarrierIndex : ℝ)⁻¹ * z)
            apply Finset.sum_congr rfl
            intro i hi
            have hrewrite : (fun j => (Cmap (Ffam.factor d (Ffam.direction d j))) i) =
                (fun j => ContinuousMap.const (V i)
                  ((Ffam.factor d (Ffam.direction d j))
                    (nativeHeatQ3RefinedCarrierCenter m i))) := by
              funext j
              exact hdir i j
            rw [hrewrite]
            simpa [V] using
              (nativeHeatQ3RefinedCarrierChildCenterCovariance_eq_profile_shell_Gen ns)
                M h hM m Ffam i d σ hσ (x i)
  have hfinal :
      modelCovarianceTrace μ
        (fun j => Cmap (H (w j))) x =
      ∑ d : Fin ns, modelCovarianceTrace μ
        (fun j => Cmap (Ffam.factor d (Ffam.direction d j))) x := by
    simpa [Cmap, H, w] using hsplit
  have hmap : (fun j => I (C₀
      (nativeHeatQ3RefinedCarrierFreshShellSeriesFactorGen Ffam
        (nativeHeatQ3RefinedCarrierFreshShellSeriesDirectionsGen Ffam j)))) =
      (fun j => Cmap (H (w j))) := by
    rfl
  rw [hmap, hfinal]
  calc
    (1 / 2 : ℝ) *
        ∑ d : Fin ns, modelCovarianceTrace μ
          (fun j => Cmap (Ffam.factor d (Ffam.direction d j))) x =
      ∑ d : Fin ns, (1 / 2 : ℝ) * modelCovarianceTrace μ
          (fun j => Cmap (Ffam.factor d (Ffam.direction d j))) x := by
            rw [Finset.mul_sum]
    _ = ∑ d : Fin ns,
        ((Fintype.card nativeHeatQ3RefinedCarrierIndex : ℝ)⁻¹ *
          ∑ i : nativeHeatQ3RefinedCarrierIndex,
            (nativeHeatQ3RefinedCarrierChildCenterDriftProfileGen ns) M h m i d σ (x i)) := by
            apply Finset.sum_congr rfl
            intro d hd
            exact hchild d
    _ = (Fintype.card nativeHeatQ3RefinedCarrierIndex : ℝ)⁻¹ *
        ∑ d : Fin ns, ∑ i : nativeHeatQ3RefinedCarrierIndex,
          (nativeHeatQ3RefinedCarrierChildCenterDriftProfileGen ns) M h m i d σ (x i) := by
            rw [Finset.mul_sum]
    _ = (Fintype.card nativeHeatQ3RefinedCarrierIndex : ℝ)⁻¹ *
        ∑ i : nativeHeatQ3RefinedCarrierIndex, ∑ d : Fin ns,
          (nativeHeatQ3RefinedCarrierChildCenterDriftProfileGen ns) M h m i d σ (x i) := by
            rw [Finset.sum_comm]

theorem nativeHeatQ3RefinedCarrierCenteredMeanGradientSquare_eq_sum_shellRows_Gen
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (m : ℤ)
    (Ffam : NativeHeatQ3RefinedCarrierFreshShellFamilyGen M m ns)
    (σ : ℝ) (hσ : 0 < σ)
    (x : ∀ i : nativeHeatQ3RefinedCarrierIndex,
      C(closure (cubeSet (nativeHeatQ3RefinedCarrierChild m i)), ℝ)) :
    let Q : nativeHeatQ3RefinedCarrierIndex → TriadicCube 2 :=
      fun i => nativeHeatQ3RefinedCarrierChild m i
    let U : nativeHeatQ3RefinedCarrierIndex → Set (Vec 2) := fun i => cubeSet (Q i)
    let hU : ∀ i, MeasurableSet (U i) := fun i => measurableSet_cubeSet (Q i)
    let hvol : ∀ i, 0 < (volume (U i)).toReal := fun i => volume_cubeSet_toReal_pos (Q i)
    let V : nativeHeatQ3RefinedCarrierIndex → Set (Vec 2) := fun i => closure (U i)
    let hV : ∀ i, V i ⊆ nativeHeatQ3RefinedCarrierDomain m :=
      nativeHeatQ3RefinedCarrierChild_closure_subset m
    let μ := childMeanTrace U hU hvol M.nu σ M.nu_pos hσ
    let R₀ := childRemainderMap V hV (nativeHeatQ3RefinedCarrierCenter m)
    modelGradientSquareTrace μ
        (fun j => R₀ (nativeHeatQ3RefinedCarrierFreshShellSeriesFactorGen Ffam
          (nativeHeatQ3RefinedCarrierFreshShellSeriesDirectionsGen Ffam j))) x =
      ∑ d : Fin ns, modelGradientSquareTrace μ
        (fun j => R₀ (Ffam.factor d (Ffam.direction d j))) x := by
  classical
  dsimp only
  let V : Fin ns → Type := fun _ => GaussianFactorL2 ℕ
  let A : C(nativeHeatQ3RefinedCarrierDomain m, ℝ) →L[ℝ]
      (∀ i : nativeHeatQ3RefinedCarrierIndex,
        C(closure (cubeSet (nativeHeatQ3RefinedCarrierChild m i)), ℝ)) :=
    childRemainderMap
      (fun i : nativeHeatQ3RefinedCarrierIndex =>
        closure (cubeSet (nativeHeatQ3RefinedCarrierChild m i)))
      (nativeHeatQ3RefinedCarrierChild_closure_subset m)
      (nativeHeatQ3RefinedCarrierCenter m)
  let D := fderiv ℝ (childMeanTrace
      (fun i : nativeHeatQ3RefinedCarrierIndex =>
        cubeSet (nativeHeatQ3RefinedCarrierChild m i))
      (fun i => measurableSet_cubeSet (nativeHeatQ3RefinedCarrierChild m i))
      (fun i => volume_cubeSet_toReal_pos (nativeHeatQ3RefinedCarrierChild m i))
      M.nu σ M.nu_pos hσ) x
  have hbil := finiteFactor_bilinearTrace_eq_sum_refined Ffam.direction
    Ffam.squareSummable (fun d => A.comp (Ffam.factor d)) (D.smulRight D)
  have hcomp : A.comp (finiteFactor V Ffam.factor) =
      finiteFactor V (fun d => A.comp (Ffam.factor d)) := by
    ext z
    simp [finiteFactor]
  have hmap : (fun j => A (finiteFactor V Ffam.factor
      (finiteDirections V Ffam.direction j))) =
      (fun j => finiteFactor V (fun d => A.comp (Ffam.factor d))
        (finiteDirections V Ffam.direction j)) := by
    funext j
    have hh := congrArg (fun L => L (finiteDirections V Ffam.direction j)) hcomp
    simpa only [ContinuousLinearMap.comp_apply] using hh
  have hmap_point j := congrFun hmap j
  change ∑' j, (D (A (finiteFactor V Ffam.factor
      (finiteDirections V Ffam.direction j)))) ^ 2 =
    ∑ d : Fin ns, ∑' j,
      (D (A (Ffam.factor d (Ffam.direction d j)))) ^ 2
  simp_rw [hmap_point]
  simpa [D, A, V, ContinuousLinearMap.smulRight_apply, smul_eq_mul,
    ContinuousLinearMap.comp_apply, pow_two] using hbil

/-- The exact shellwise global-mean remainder bracket on the actual refined
carrier. This proposition is the in-node premise used by the final VHEAT assembly. -/
def nativeHeatQ3RefinedCarrierShellBracketGen
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (m : ℤ)
    (Ffam : NativeHeatQ3RefinedCarrierFreshShellFamilyGen M m ns) (d : Fin ns) (σ : ℝ) (hσ : 0 < σ)
    (x : ∀ i : nativeHeatQ3RefinedCarrierIndex,
      C(closure (cubeSet (nativeHeatQ3RefinedCarrierChild m i)), ℝ)) : Prop :=
  let Q : nativeHeatQ3RefinedCarrierIndex → TriadicCube 2 :=
    fun i => nativeHeatQ3RefinedCarrierChild m i
  let U : nativeHeatQ3RefinedCarrierIndex → Set (Vec 2) := fun i => cubeSet (Q i)
  let hU : ∀ i, MeasurableSet (U i) := fun i => measurableSet_cubeSet (Q i)
  let hvol : ∀ i, 0 < (volume (U i)).toReal := fun i => volume_cubeSet_toReal_pos (Q i)
  let V : nativeHeatQ3RefinedCarrierIndex → Set (Vec 2) := fun i => closure (U i)
  let hV : ∀ i, V i ⊆ nativeHeatQ3RefinedCarrierDomain m :=
    nativeHeatQ3RefinedCarrierChild_closure_subset m
  let μ := childMeanTrace U hU hvol M.nu σ M.nu_pos hσ
  let R₀ := childRemainderMap V hV (nativeHeatQ3RefinedCarrierCenter m)
  let s : ℕ := d.val + 2
  let L := q3ModelLength (m + (s : ℤ))
  let profile : nativeHeatQ3RefinedCarrierIndex → ℝ := fun i =>
    let Q := nativeHeatQ3RefinedCarrierChild m i
    let A := nativeHeat_translateTriadicFieldToOrigin Q
    let k := pureFluxOpenResponseRestriction Q.scale (A (x i))
    let B := lemmaVTileHistory (originCube 2 Q.scale) (pureFluxBankSourceDepth s)
      (responseFramePlanarCoefficientField M.nu σ k)
    let T := modelTraceObservable Q.scale M.nu σ (A (x i))
    B ^ 2 * T * (T + 4)
  modelGradientSquareTrace μ
      (fun j => R₀ (Ffam.factor d (Ffam.direction d j))) x ≤
      4 * (q3ModelAmplitude M h (m + (s : ℤ)) / σ) ^ 2 *
      q3GridOverlapFactor 10 s *
      (lemmaVH2Bn
        (cubeScaleFactor (originCube 2 m) / L.1)
        (diagMeshRadius (originCube 2 m) (pureFluxBankSourceDepth s) / L.1)) ^ 2 *
      ((Fintype.card nativeHeatQ3RefinedCarrierIndex : ℝ)⁻¹ * ∑ i, profile i)

/-- Sum the exact shellwise global-mean remainder bracket over the actual
refined shell realization, applying each bound to the same child field vector. -/
theorem nativeHeatQ3RefinedCarrierMeanRemainderBracket_sum_Gen
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (m : ℤ)
    (Ffam : NativeHeatQ3RefinedCarrierFreshShellFamilyGen M m ns) (σ : ℝ) (hσ : 0 < σ)
    (x : ∀ i : nativeHeatQ3RefinedCarrierIndex,
      C(closure (cubeSet (nativeHeatQ3RefinedCarrierChild m i)), ℝ)) :
    let Q : nativeHeatQ3RefinedCarrierIndex → TriadicCube 2 :=
      fun i => nativeHeatQ3RefinedCarrierChild m i
    let U : nativeHeatQ3RefinedCarrierIndex → Set (Vec 2) := fun i => cubeSet (Q i)
    let hU : ∀ i, MeasurableSet (U i) := fun i => measurableSet_cubeSet (Q i)
    let hvol : ∀ i, 0 < (volume (U i)).toReal := fun i => volume_cubeSet_toReal_pos (Q i)
    let V : nativeHeatQ3RefinedCarrierIndex → Set (Vec 2) := fun i => closure (U i)
    let hV : ∀ i, V i ⊆ nativeHeatQ3RefinedCarrierDomain m :=
      nativeHeatQ3RefinedCarrierChild_closure_subset m
    let μ := childMeanTrace U hU hvol M.nu σ M.nu_pos hσ
    let R₀ := childRemainderMap V hV (nativeHeatQ3RefinedCarrierCenter m)
    modelGradientSquareTrace μ
        (fun j => R₀ (nativeHeatQ3RefinedCarrierFreshShellSeriesFactorGen Ffam
          (nativeHeatQ3RefinedCarrierFreshShellSeriesDirectionsGen Ffam j))) x ≤
      ∑ d : Fin ns,
        4 * (q3ModelAmplitude M h (m + ((d.val + 2 : ℕ) : ℤ)) ^ 2 / σ ^ 2) *
          q3GridOverlapFactor 10 (d.val + 2) *
          (lemmaVH2Bn
            (cubeScaleFactor (originCube 2 m) /
              (q3ModelLength (m + ((d.val + 2 : ℕ) : ℤ))).1)
            (diagMeshRadius (originCube 2 m)
              (pureFluxBankSourceDepth (d.val + 2)) /
              (q3ModelLength (m + ((d.val + 2 : ℕ) : ℤ))).1)) ^ 2 *
          ((Fintype.card nativeHeatQ3RefinedCarrierIndex : ℝ)⁻¹ *
            ∑ i : nativeHeatQ3RefinedCarrierIndex,
              let Q := nativeHeatQ3RefinedCarrierChild m i
              let A := nativeHeat_translateTriadicFieldToOrigin Q
              let k := pureFluxOpenResponseRestriction Q.scale (A (x i))
              let B := lemmaVTileHistory (originCube 2 Q.scale)
                (pureFluxBankSourceDepth (d.val + 2))
                (responseFramePlanarCoefficientField M.nu σ k)
              let T := modelTraceObservable Q.scale M.nu σ (A (x i))
              B ^ 2 * T * (T + 4)) := by
  classical
  dsimp only
  rw [(nativeHeatQ3RefinedCarrierCenteredMeanGradientSquare_eq_sum_shellRows_Gen ns)
    M h hM m Ffam σ hσ x]
  apply Finset.sum_le_sum
  intro d hd
  have hRemainderBracket := (nativeHeatQ3RefinedCarrierMeanRemainderBracket_le_Gen ns)
    M h hM m Ffam d σ hσ x
  simpa only [nativeHeatQ3RefinedCarrierShellBracketGen,
    div_pow] using hRemainderBracket

/-- The exact shellwise bracket payment also bounds the weighted
second-order power bracket, with its full `1 + θ⁻¹` coefficient retained. -/
theorem nativeHeatQ3RefinedCarrierPowerCenteredBracket_le_profileRows_Gen
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (m : ℤ)
    (Ffam : NativeHeatQ3RefinedCarrierFreshShellFamilyGen M m ns) (σ : ℝ) (hσ : 0 < σ)
    (x : ∀ i : nativeHeatQ3RefinedCarrierIndex,
      C(closure (cubeSet (nativeHeatQ3RefinedCarrierChild m i)), ℝ))
    (r : ℕ) (hr : 2 ≤ r) (θ : ℝ) (hθ : 0 < θ)
    (hrow :
      let Q : nativeHeatQ3RefinedCarrierIndex → TriadicCube 2 :=
        fun i => nativeHeatQ3RefinedCarrierChild m i
      let U : nativeHeatQ3RefinedCarrierIndex → Set (Vec 2) :=
        fun i => cubeSet (Q i)
      let hU : ∀ i, MeasurableSet (U i) := fun i => measurableSet_cubeSet (Q i)
      let hvol : ∀ i, 0 < (volume (U i)).toReal :=
        fun i => volume_cubeSet_toReal_pos (Q i)
      let V : nativeHeatQ3RefinedCarrierIndex → Set (Vec 2) :=
        fun i => closure (U i)
      let hV : ∀ i, V i ⊆ nativeHeatQ3RefinedCarrierDomain m :=
        nativeHeatQ3RefinedCarrierChild_closure_subset m
      let μ := childMeanTrace U hU hvol M.nu σ M.nu_pos hσ
      let R₀ := childRemainderMap V hV (nativeHeatQ3RefinedCarrierCenter m)
      modelGradientSquareTrace μ
          (fun j => R₀ (nativeHeatQ3RefinedCarrierFreshShellSeriesFactorGen Ffam
            (nativeHeatQ3RefinedCarrierFreshShellSeriesDirectionsGen Ffam j))) x ≤
        ∑ d : Fin ns,
          4 * (q3ModelAmplitude M h (m + ((d.val + 2 : ℕ) : ℤ)) ^ 2 / σ ^ 2) *
            q3GridOverlapFactor 10 (d.val + 2) *
            (lemmaVH2Bn
              (cubeScaleFactor (originCube 2 m) /
                (q3ModelLength (m + ((d.val + 2 : ℕ) : ℤ))).1)
              (diagMeshRadius (originCube 2 m)
                (pureFluxBankSourceDepth (d.val + 2)) /
                (q3ModelLength (m + ((d.val + 2 : ℕ) : ℤ))).1)) ^ 2 *
            ((Fintype.card nativeHeatQ3RefinedCarrierIndex : ℝ)⁻¹ *
              ∑ i : nativeHeatQ3RefinedCarrierIndex,
                let Q := nativeHeatQ3RefinedCarrierChild m i
                let A := nativeHeat_translateTriadicFieldToOrigin Q
                let k := pureFluxOpenResponseRestriction Q.scale (A (x i))
                let B := lemmaVTileHistory (originCube 2 Q.scale)
                  (pureFluxBankSourceDepth (d.val + 2))
                  (responseFramePlanarCoefficientField M.nu σ k)
                let T := modelTraceObservable Q.scale M.nu σ (A (x i))
                B ^ 2 * T * (T + 4))) :
    let Q : nativeHeatQ3RefinedCarrierIndex → TriadicCube 2 :=
      fun i => nativeHeatQ3RefinedCarrierChild m i
    let U : nativeHeatQ3RefinedCarrierIndex → Set (Vec 2) := fun i => cubeSet (Q i)
    let hU : ∀ i, MeasurableSet (U i) := fun i => measurableSet_cubeSet (Q i)
    let hvol : ∀ i, 0 < (volume (U i)).toReal := fun i => volume_cubeSet_toReal_pos (Q i)
    let V : nativeHeatQ3RefinedCarrierIndex → Set (Vec 2) := fun i => closure (U i)
    let hV : ∀ i, V i ⊆ nativeHeatQ3RefinedCarrierDomain m :=
      nativeHeatQ3RefinedCarrierChild_closure_subset m
    let μ := childMeanTrace U hU hvol M.nu σ M.nu_pos hσ
    let R₀ := childRemainderMap V hV (nativeHeatQ3RefinedCarrierCenter m)
    (((r : ℝ) * ((r : ℝ) - 1) / 2) * (1 + θ⁻¹) *
        Real.rpow (μ x) ((r : ℝ) - 2)) *
        modelGradientSquareTrace μ
          (fun j => R₀ (nativeHeatQ3RefinedCarrierFreshShellSeriesFactorGen Ffam
            (nativeHeatQ3RefinedCarrierFreshShellSeriesDirectionsGen Ffam j))) x ≤
      (((r : ℝ) * ((r : ℝ) - 1) / 2) * (1 + θ⁻¹) *
        Real.rpow (μ x) ((r : ℝ) - 2)) *
        ∑ d : Fin ns,
          4 * (q3ModelAmplitude M h (m + ((d.val + 2 : ℕ) : ℤ)) ^ 2 / σ ^ 2) *
            q3GridOverlapFactor 10 (d.val + 2) *
            (lemmaVH2Bn
              (cubeScaleFactor (originCube 2 m) /
                (q3ModelLength (m + ((d.val + 2 : ℕ) : ℤ))).1)
              (diagMeshRadius (originCube 2 m)
                (pureFluxBankSourceDepth (d.val + 2)) /
                (q3ModelLength (m + ((d.val + 2 : ℕ) : ℤ))).1)) ^ 2 *
            ((Fintype.card nativeHeatQ3RefinedCarrierIndex : ℝ)⁻¹ *
              ∑ i : nativeHeatQ3RefinedCarrierIndex,
                let Q := nativeHeatQ3RefinedCarrierChild m i
                let A := nativeHeat_translateTriadicFieldToOrigin Q
                let k := pureFluxOpenResponseRestriction Q.scale (A (x i))
                let B := lemmaVTileHistory (originCube 2 Q.scale)
                  (pureFluxBankSourceDepth (d.val + 2))
                  (responseFramePlanarCoefficientField M.nu σ k)
                let T := modelTraceObservable Q.scale M.nu σ (A (x i))
                B ^ 2 * T * (T + 4)) := by
  classical
  have hμ : 0 ≤ childMeanTrace
      (fun i : nativeHeatQ3RefinedCarrierIndex =>
        cubeSet (nativeHeatQ3RefinedCarrierChild m i))
      (fun i => measurableSet_cubeSet (nativeHeatQ3RefinedCarrierChild m i))
      (fun i => volume_cubeSet_toReal_pos (nativeHeatQ3RefinedCarrierChild m i))
      M.nu σ M.nu_pos hσ x :=
    nativeHeat_childMeanTrace_nonneg (nativeHeatQ3RefinedCarrierChild m)
      M.nu σ M.nu_pos hσ x
  have hcoef : 0 ≤ (((r : ℝ) * ((r : ℝ) - 1) / 2) *
      (1 + θ⁻¹) * Real.rpow
        (childMeanTrace
          (fun i : nativeHeatQ3RefinedCarrierIndex =>
            cubeSet (nativeHeatQ3RefinedCarrierChild m i))
          (fun i => measurableSet_cubeSet (nativeHeatQ3RefinedCarrierChild m i))
          (fun i => volume_cubeSet_toReal_pos (nativeHeatQ3RefinedCarrierChild m i))
          M.nu σ M.nu_pos hσ x) ((r : ℝ) - 2)) := by
    apply mul_nonneg
    · apply mul_nonneg
      · apply div_nonneg
        · apply mul_nonneg
          · exact Nat.cast_nonneg r
          · have hrR : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
            linarith
        · norm_num
      · exact add_nonneg (by norm_num) (inv_nonneg.mpr hθ.le)
    · exact Real.rpow_nonneg hμ _
  dsimp only at hrow ⊢
  exact mul_le_mul_of_nonneg_left hrow hcoef

