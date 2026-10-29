module

public import ASDExplicitGamma.Native.HeatVHEATSourceFinalAssembly
public import ASDExplicitGamma.Native.HeatVHEATSourceAuxiliary

/-! The `n`-shell generalization of the VHEAT source carrier.  The heat step
inserts `n` shells simultaneously, at the physical levels `m+2, ..., m+n+1`,
on the same depth-ten cells, with the old field at cutoff `m+1`, the frame
`Annealed.sigmaBar M (m+1)`, the unscaled center map and the auxiliary
covariance `(1+θ)(1-t)`.  The Gaussian-series realization of the shells is a
parameter `F`; every statement holds for every realization, and the chosen
realization is `nativeHeatQ3RefinedCarrierFreshShellFamilyChosenGen`. -/

@[expose] public section

namespace ASDExplicitGamma.Native

open MeasureTheory Homogenization Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Model
open ProbabilityTheory
open scoped ENNReal NNReal Topology

/-- The `n` physical shells of the refined carrier: levels `m+2, ..., m+n+1`. -/
def nativeHeatQ3RefinedCarrierPhysicalShellsGen (m : ℤ) (n : ℕ) : Fin n → ℤ :=
  fun d => m + (d.val : ℤ) + 2

theorem nativeHeatQ3RefinedCarrierPhysicalShellsGen_injective (m : ℤ) {n : ℕ} :
    Function.Injective (nativeHeatQ3RefinedCarrierPhysicalShellsGen m n) := by
  intro i j hij
  apply Fin.ext
  simp only [nativeHeatQ3RefinedCarrierPhysicalShellsGen] at hij
  omega

theorem nativeHeatQ3RefinedCarrierPhysicalShellsGen_gt (m : ℤ) {n : ℕ} (d : Fin n) :
    m + 1 < nativeHeatQ3RefinedCarrierPhysicalShellsGen m n d := by
  simp only [nativeHeatQ3RefinedCarrierPhysicalShellsGen]; omega

theorem nativeHeatQ3RefinedCarrierPhysicalShellsGen_offset (m : ℤ) {n : ℕ} (d : Fin n) :
    nativeHeatQ3RefinedCarrierPhysicalShellsGen m n d =
      m + ((d.val + 2 : ℕ) : ℤ) := by
  simp only [nativeHeatQ3RefinedCarrierPhysicalShellsGen, Nat.cast_add, Nat.cast_ofNat]
  ring

theorem nativeHeatQ3RefinedCarrierPhysicalShellsGen_mem (m : ℤ) {n : ℕ} (d : Fin n) :
    nativeHeatQ3RefinedCarrierPhysicalShellsGen m n d ∈ Set.Icc (m + 2) (m + n + 1) := by
  have := d.isLt
  simp only [Set.mem_Icc, nativeHeatQ3RefinedCarrierPhysicalShellsGen]
  constructor <;> omega

/-- A Gaussian-series realization of the `n` physical shells on the carrier. -/
structure NativeHeatQ3RefinedCarrierFreshShellFamilyGen
    (M : ABKModel 2) (m : ℤ) (n : ℕ) where
  factor : Fin n → GaussianFactorL2 ℕ →L[ℝ] C(nativeHeatQ3RefinedCarrierDomain m, ℝ)
  direction : Fin n → ℕ → GaussianFactorL2 ℕ
  squareSummable : ∀ i, Summable (fun j => ‖direction i j‖ ^ 2)
  law : ∀ i, (Cutoff.cutoffSampleLaw M).toMeasure.map
      (fun ω : Cutoff.CutoffSample 2 =>
        shellFieldScalarRestriction (nativeHeatQ3RefinedCarrierDomain m)
          (ω.1 (nativeHeatQ3RefinedCarrierPhysicalShellsGen m n i))) =
    standardGaussianInfinitePi.map
      (gaussianSeriesLimitE (squareSummable i) (factor i))

/-- The nine-shell family, as an `n = 9` realization. -/
noncomputable def nativeHeatQ3RefinedCarrierFreshShellFamilyGen_of
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (m : ℤ) :
    NativeHeatQ3RefinedCarrierFreshShellFamilyGen M m 9 :=
  let F := nativeHeatQ3RefinedCarrierFreshShellFamily M h hM m
  ⟨F.factor, F.direction, F.squareSummable, F.law⟩

/-- A chosen realization of the `n` shells. -/
noncomputable def nativeHeatQ3RefinedCarrierFreshShellFamilyChosenGen
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (m : ℤ) (n : ℕ) :
    NativeHeatQ3RefinedCarrierFreshShellFamilyGen M m n := by
  classical
  have hshell (i : Fin n) :=
    freshShell_map_scalarRestriction_eq_gaussianSeries M h hM
      (nativeHeatQ3RefinedCarrierPhysicalShellsGen m n i - 1)
      (K := nativeHeatQ3RefinedCarrierDomain m)
  choose factor direction squareSummable law using hshell
  refine ⟨factor, direction, squareSummable, ?_⟩
  intro i
  simpa only [Int.sub_add_cancel] using law i

variable {M : ABKModel 2} {m : ℤ} {n : ℕ}

/-- The direct-sum factor of the `n` shell factors. -/
noncomputable def nativeHeatQ3RefinedCarrierFreshShellSeriesFactorGen
    (F : NativeHeatQ3RefinedCarrierFreshShellFamilyGen M m n) :
    BandHilbert n →L[ℝ] C(nativeHeatQ3RefinedCarrierDomain m, ℝ) :=
  finiteFactor (fun _ : Fin n => GaussianFactorL2 ℕ) (fun i => F.factor i)

/-- The direct-sum directions of the `n` shell families. -/
noncomputable def nativeHeatQ3RefinedCarrierFreshShellSeriesDirectionsGen
    [NeZero n] (F : NativeHeatQ3RefinedCarrierFreshShellFamilyGen M m n) :
    ℕ → BandHilbert n :=
  finiteDirections (fun _ : Fin n => GaussianFactorL2 ℕ) (fun i => F.direction i)

theorem nativeHeatQ3RefinedCarrierFreshShellSeriesSummableGen [NeZero n]
    (F : NativeHeatQ3RefinedCarrierFreshShellFamilyGen M m n) :
    Summable (fun j =>
      ‖nativeHeatQ3RefinedCarrierFreshShellSeriesDirectionsGen F j‖ ^ 2) :=
  finiteDirections_summable (fun _ : Fin n => GaussianFactorL2 ℕ)
    (fun i => F.direction i) F.squareSummable

/-- The band has the Gaussian-series law of the direct-sum realization. -/
theorem nativeHeatQ3RefinedCarrierFreshShellSeriesLawGen [NeZero n]
    (F : NativeHeatQ3RefinedCarrierFreshShellFamilyGen M m n) :
    (Cutoff.cutoffSampleLaw M).toMeasure.map
        (modelBand (nativeHeatQ3RefinedCarrierDomain m)
          (nativeHeatQ3RefinedCarrierPhysicalShellsGen m n)) =
      standardGaussianInfinitePi.map
        (gaussianSeriesLimitE
          (nativeHeatQ3RefinedCarrierFreshShellSeriesSummableGen F)
          (nativeHeatQ3RefinedCarrierFreshShellSeriesFactorGen F)) := by
  classical
  simpa [nativeHeatQ3RefinedCarrierFreshShellSeriesFactorGen,
    nativeHeatQ3RefinedCarrierFreshShellSeriesDirectionsGen,
    nativeHeatQ3RefinedCarrierFreshShellSeriesSummableGen] using
    (modelBand_law_of_factors
      (fun _ : Fin n => GaussianFactorL2 ℕ) (nativeHeatQ3RefinedCarrierDomain m) M
      (nativeHeatQ3RefinedCarrierPhysicalShellsGen m n)
      (nativeHeatQ3RefinedCarrierPhysicalShellsGen_injective m)
      F.factor F.direction F.squareSummable F.law)

/-- The source center map: the actual, unscaled child-center vector. -/
noncomputable abbrev nativeHeatQ3RefinedCarrierSourceCenterMapGen (m : ℤ) :=
  nativeHeatQ3RefinedCarrierSourceCenterMap m

local instance nativeHeatQ3RefinedCarrierGenChildFinite (m : ℤ)
    (i : nativeHeatQ3RefinedCarrierIndex) :
    IsFiniteMeasure
      (volumeMeasureOn (cubeSet (nativeHeatQ3RefinedCarrierChild m i))) :=
  ((isBounded_cubeSet (nativeHeatQ3RefinedCarrierChild m i)).isBoundedDomain).isFiniteMeasure_restrict_volume

/-- The source-normalized `n`-shell moment. -/
noncomputable def nativeHeatQ3RefinedCarrierSourceMomentGen
    (M : ABKModel 2) (m : ℤ) (n : ℕ) [NeZero n]
    (F : NativeHeatQ3RefinedCarrierFreshShellFamilyGen M m n)
    (k : ℕ) (θ t : ℝ) : ℝ :=
  nativeHeatChildBandMoment
    (fun i : nativeHeatQ3RefinedCarrierIndex =>
      cubeSet (nativeHeatQ3RefinedCarrierChild m i))
    (fun i => measurableSet_cubeSet (nativeHeatQ3RefinedCarrierChild m i))
    (fun i => volume_cubeSet_toReal_pos (nativeHeatQ3RefinedCarrierChild m i))
    M.nu (Annealed.sigmaBar M (m + 1) : ℝ) M.nu_pos
    (Annealed.sigmaBar_characterization M (m + 1)).1
    (nativeHeatQ3RefinedCarrierDomain m) M (m + 1)
    (nativeHeatQ3RefinedCarrierPhysicalShellsGen m n)
    (nativeHeatQ3RefinedCarrierOldMap m)
    (nativeHeatQ3RefinedCarrierSourceCenterMapGen m)
    (nativeHeatQ3RefinedCarrierFreshShellSeriesSummableGen F)
    (nativeHeatQ3RefinedCarrierFreshShellSeriesFactorGen F)
    k θ t

/-- The exact canceled generator of the source-normalized `n`-shell moment. -/
noncomputable def nativeHeatQ3RefinedCarrierSourceMomentGeneratorGen
    (M : ABKModel 2) (m : ℤ) (n : ℕ) [NeZero n]
    (F : NativeHeatQ3RefinedCarrierFreshShellFamilyGen M m n)
    (k : ℕ) (θ t : ℝ) : ℝ :=
  nativeHeatChildBandMomentGenerator
    (fun i : nativeHeatQ3RefinedCarrierIndex =>
      cubeSet (nativeHeatQ3RefinedCarrierChild m i))
    (fun i => measurableSet_cubeSet (nativeHeatQ3RefinedCarrierChild m i))
    (fun i => volume_cubeSet_toReal_pos (nativeHeatQ3RefinedCarrierChild m i))
    M.nu (Annealed.sigmaBar M (m + 1) : ℝ) M.nu_pos
    (Annealed.sigmaBar_characterization M (m + 1)).1
    (nativeHeatQ3RefinedCarrierDomain m) M (m + 1)
    (nativeHeatQ3RefinedCarrierPhysicalShellsGen m n)
    (nativeHeatQ3RefinedCarrierOldMap m)
    (nativeHeatQ3RefinedCarrierSourceCenterMapGen m)
    (nativeHeatQ3RefinedCarrierFreshShellSeriesSummableGen F)
    (nativeHeatQ3RefinedCarrierFreshShellSeriesFactorGen F)
    k θ t

/-- Scalar observation of the center value with the source inflated variance. -/
noncomputable abbrev nativeHeatQ3RefinedCarrierSourceAuxCenterObservationGen
    (M : ABKModel 2) (m : ℤ) (θ t : ℝ) (i : nativeHeatQ3RefinedCarrierIndex) :=
  nativeHeatQ3RefinedCarrierSourceAuxCenterObservation M m θ t i

/-- Exact scalar variance of the auxiliary center coordinate. -/
noncomputable def nativeHeatQ3RefinedCarrierSourceAuxCenterVarianceGen
    (M : ABKModel 2) (m : ℤ) (n : ℕ) [NeZero n]
    (F : NativeHeatQ3RefinedCarrierFreshShellFamilyGen M m n)
    (θ t : ℝ) (i : nativeHeatQ3RefinedCarrierIndex) : ℝ≥0 :=
  Real.toNNReal (∑' j,
    (nativeHeatQ3RefinedCarrierSourceAuxCenterObservationGen M m θ t i
      (nativeHeatQ3RefinedCarrierFreshShellSeriesFactorGen F
        (nativeHeatQ3RefinedCarrierFreshShellSeriesDirectionsGen F j))) ^ 2)

/-- The auxiliary scalar coordinate, in physical coefficient units. -/
noncomputable def nativeHeatQ3RefinedCarrierSourceAuxCenterGaussianGen
    (M : ABKModel 2) (m : ℤ) (n : ℕ) [NeZero n]
    (F : NativeHeatQ3RefinedCarrierFreshShellFamilyGen M m n)
    (θ t : ℝ) (i : nativeHeatQ3RefinedCarrierIndex) (ξ : ℕ → ℝ) : ℝ :=
  (Annealed.sigmaBar M (m + 1) : ℝ) *
    nativeHeatQ3RefinedCarrierSourceAuxCenterObservationGen M m θ t i
      (gaussianSeriesLimitE
        (nativeHeatQ3RefinedCarrierFreshShellSeriesSummableGen F)
        (nativeHeatQ3RefinedCarrierFreshShellSeriesFactorGen F) ξ)

theorem nativeHeatQ3RefinedCarrierSourceAuxCenterGaussianGen_eq_backwardCenterInput
    (M : ABKModel 2) (m : ℤ) (n : ℕ) [NeZero n]
    (F : NativeHeatQ3RefinedCarrierFreshShellFamilyGen M m n)
    (θ t : ℝ) (i : nativeHeatQ3RefinedCarrierIndex) (ξ : ℕ → ℝ) :
    nativeHeatQ3RefinedCarrierSourceAuxCenterGaussianGen M m n F θ t i ξ =
      Real.sqrt ((1 + θ) * (1 - t)) *
        nativeHeatQ3RefinedCarrierSourceCenterMapGen m
          (gaussianSeriesLimitE
            (nativeHeatQ3RefinedCarrierFreshShellSeriesSummableGen F)
            (nativeHeatQ3RefinedCarrierFreshShellSeriesFactorGen F) ξ) i := by
  have hσ : (Annealed.sigmaBar M (m + 1) : ℝ) ≠ 0 :=
    ne_of_gt (Annealed.sigmaBar_characterization M (m + 1)).1
  change (Annealed.sigmaBar M (m + 1) : ℝ) *
      ((Real.sqrt ((1 + θ) * (1 - t)) /
        (Annealed.sigmaBar M (m + 1) : ℝ)) * _ ) = _
  field_simp [hσ]
  rfl

theorem nativeHeatQ3RefinedCarrierSourceAuxCenterGaussianGen_measurable
    (M : ABKModel 2) (m : ℤ) (n : ℕ) [NeZero n]
    (F : NativeHeatQ3RefinedCarrierFreshShellFamilyGen M m n)
    (θ t : ℝ) (i : nativeHeatQ3RefinedCarrierIndex) :
    Measurable (nativeHeatQ3RefinedCarrierSourceAuxCenterGaussianGen M m n F θ t i) := by
  let hA := nativeHeatQ3RefinedCarrierFreshShellSeriesSummableGen F
  let T := nativeHeatQ3RefinedCarrierFreshShellSeriesFactorGen F
  let A := nativeHeatQ3RefinedCarrierSourceAuxCenterObservationGen M m θ t i
  have hZ : StronglyMeasurable (gaussianSeriesLimitE hA T) :=
    stronglyMeasurable_gaussianSeriesLimitE hA T
  change Measurable (fun ξ =>
    (Annealed.sigmaBar M (m + 1) : ℝ) * A (gaussianSeriesLimitE hA T ξ))
  exact measurable_const.mul (A.continuous.measurable.comp hZ.measurable)

theorem nativeHeatQ3RefinedCarrierSourceAuxCenterGaussianGen_law
    (M : ABKModel 2) (m : ℤ) (n : ℕ) [NeZero n]
    (F : NativeHeatQ3RefinedCarrierFreshShellFamilyGen M m n)
    (θ t : ℝ) (i : nativeHeatQ3RefinedCarrierIndex) :
    standardGaussianInfinitePi.map
      (fun ξ => nativeHeatQ3RefinedCarrierSourceAuxCenterGaussianGen
          M m n F θ t i ξ / (Annealed.sigmaBar M (m + 1) : ℝ)) =
      gaussianReal 0
        (nativeHeatQ3RefinedCarrierSourceAuxCenterVarianceGen M m n F θ t i) := by
  let hA := nativeHeatQ3RefinedCarrierFreshShellSeriesSummableGen F
  let T := nativeHeatQ3RefinedCarrierFreshShellSeriesFactorGen F
  let A := nativeHeatQ3RefinedCarrierSourceAuxCenterObservationGen M m θ t i
  have hσ : (Annealed.sigmaBar M (m + 1) : ℝ) ≠ 0 :=
    ne_of_gt (Annealed.sigmaBar_characterization M (m + 1)).1
  have hpoint :
      (fun ξ => nativeHeatQ3RefinedCarrierSourceAuxCenterGaussianGen
          M m n F θ t i ξ / (Annealed.sigmaBar M (m + 1) : ℝ)) =
      fun ξ => A (gaussianSeriesLimitE hA T ξ) := by
    funext ξ
    change ((Annealed.sigmaBar M (m + 1) : ℝ) *
        A (gaussianSeriesLimitE hA T ξ)) /
        (Annealed.sigmaBar M (m + 1) : ℝ) = _
    field_simp [hσ]
  rw [hpoint]
  simpa [nativeHeatQ3RefinedCarrierSourceAuxCenterVarianceGen, A, hA, T] using
    (map_gaussianSeriesLimitE_linear hA T A)

/-! ### The `n = 9` instance is the carrier. -/

section Nine
variable (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (m : ℤ)

end Nine

end ASDExplicitGamma.Native
