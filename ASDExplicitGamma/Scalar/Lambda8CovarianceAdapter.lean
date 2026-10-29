module

public import ASDExplicitGamma.Scalar.Lambda8LocalProjection
public import ASDExplicitGamma.Gaussian.BilinearCovariance
public import ASDExplicitGamma.Gaussian.Q3ModelH3Realization
public import ASDExplicitGamma.Gaussian.Q3SeriesCovariance
public import ASDExplicitGamma.Response.FrameAlgebra
public import ASDExplicitGamma.Model.CutoffAction
public import ASDExplicitGamma.Model.CutoffStationaryEnergy
public import ASDExplicitGamma.Model.StationaryPhysicalProjection
public import Algsuperdiff.Section3.Provider.Diffusivity.Corrector.CorrectorMeasurableForcing

/-! # The q3 covariance directions after local Dirichlet projection -/

@[expose] public section

open MeasureTheory ProbabilityTheory Homogenization Set
open Algsuperdiff.Probability.Stationary
open Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3
open Algsuperdiff.Section3.Provider.Corrector
open Algsuperdiff.Section3.Provider.Diffusivity.Corrector
open scoped Topology

namespace ASDExplicitGamma.Scalar

def lambda8CovarianceClampReal (a b x : ℝ) : ℝ :=
  max a (min x b)

private theorem lambda8CovarianceClampReal_mem (a b x : ℝ) (hab : a < b) :
    lambda8CovarianceClampReal a b x ∈ Icc a b := by
  constructor
  · exact le_max_left _ _
  · exact max_le_iff.mpr ⟨hab.le, min_le_right _ _⟩

def lambda8CovarianceClamp (a b c d : ℝ)
    (hab : a < b) (hcd : c < d) (x : Vec 2) :
    Gaussian.closedRectangle a b c d :=
  ⟨fun i => if i = 0 then lambda8CovarianceClampReal a b (x i)
      else lambda8CovarianceClampReal c d (x i),
    by
      change lambda8CovarianceClampReal a b (x 0) ∈ Icc a b ∧
        lambda8CovarianceClampReal c d (x 1) ∈ Icc c d
      exact ⟨lambda8CovarianceClampReal_mem a b (x 0) hab,
        lambda8CovarianceClampReal_mem c d (x 1) hcd⟩⟩

private theorem lambda8CovarianceClamp_continuous (a b c d : ℝ)
    (hab : a < b) (hcd : c < d) :
    Continuous (lambda8CovarianceClamp a b c d hab hcd) :=
  Continuous.subtype_mk (by
    change Continuous (fun x : Vec 2 => fun i =>
      if i = 0 then max a (min (x i) b) else max c (min (x i) d))
    exact continuous_pi fun i => by
      fin_cases i
      · simpa using continuous_const.max ((continuous_apply 0).min continuous_const)
      · simpa using continuous_const.max ((continuous_apply 1).min continuous_const))
    (fun x => by
      change lambda8CovarianceClampReal a b (x 0) ∈ Icc a b ∧
        lambda8CovarianceClampReal c d (x 1) ∈ Icc c d
      exact ⟨lambda8CovarianceClampReal_mem a b (x 0) hab,
        lambda8CovarianceClampReal_mem c d (x 1) hcd⟩)

theorem lambda8CovarianceClamp_eq_of_mem (a b c d : ℝ)
    (hab : a < b) (hcd : c < d) {x : Vec 2}
    (hx : x ∈ Gaussian.openRectangle a b c d) :
    lambda8CovarianceClamp a b c d hab hcd x = ⟨x, by
      exact ⟨Ioo_subset_Icc_self hx.1, Ioo_subset_Icc_self hx.2⟩⟩ := by
  apply Subtype.ext
  ext i
  fin_cases i
  · simp only [lambda8CovarianceClamp, lambda8CovarianceClampReal]
    change max a (min (x 0) b) = x 0
    rw [min_eq_left hx.1.2.le, max_eq_right hx.1.1.le]
  · simp only [lambda8CovarianceClamp, lambda8CovarianceClampReal]
    change max c (min (x 1) d) = x 1
    rw [min_eq_left hx.2.2.le, max_eq_right hx.2.1.le]

def lambda8Q3LoadField (a b c d : ℝ) (hab : a < b) (hcd : c < d)
    (e : Vec 2) (f : C(Gaussian.closedRectangle a b c d, ℝ)) : Vec 2 → Vec 2 :=
  fun x => f (lambda8CovarianceClamp a b c d hab hcd x) •
    matVecMul ASDExplicitGamma.Response.responsePlanarJ e

/-- On a source rectangle, the clamped continuous extension is exactly the
actual one-shell vector load `ψ J e`. -/
theorem lambda8Q3LoadField_eq_actualShell
    {U : Set (Vec 2)} {a b c d : ℝ} (hUK : U ⊆ Gaussian.openRectangle a b c d)
    (hab : a < b) (hcd : c < d) (e : Vec 2)
    (ω : Cutoff.CutoffSample 2) (k : ℤ) {x : Vec 2} (hx : x ∈ U) :
    lambda8Q3LoadField a b c d hab hcd e
      (Gaussian.shellFieldScalarRestriction (Gaussian.closedRectangle a b c d)
        (ω.1 k)) x = (ω.1 k x 1 0) •
          matVecMul ASDExplicitGamma.Response.responsePlanarJ e := by
  unfold lambda8Q3LoadField
  rw [lambda8CovarianceClamp_eq_of_mem a b c d hab hcd (hUK hx)]
  simp only [Gaussian.shellFieldScalarRestriction, Gaussian.planarShellScalarStream,
    Gaussian.planarShellMatrixEntry,
    ContinuousMap.comp_apply, ContinuousMap.restrict_apply]
  rfl

theorem lambda8Q3ShellMatVec_eq_scalarJ (j : ShellField 2) (x e : Vec 2) :
    matVecMul (j x) e = j x 1 0 •
      matVecMul ASDExplicitGamma.Response.responsePlanarJ e := by
  have h00 : j x 0 0 = 0 := by
    have h := ShellField.skew_entry j x 0 0
    linarith
  have h11 : j x 1 1 = 0 := by
    have h := ShellField.skew_entry j x 1 1
    linarith
  have h01 : j x 0 1 = -j x 1 0 := ShellField.skew_entry j x 0 1
  ext i
  fin_cases i
  · simp [matVecMul, ASDExplicitGamma.Response.responsePlanarJ,
      Fin.sum_univ_two, h00, h01]
  · simp [matVecMul, ASDExplicitGamma.Response.responsePlanarJ,
      Fin.sum_univ_two, h11]

/-- The literal one-shell forcing on the actual cutoff-sample carrier. -/
def lambda8Q3CutoffShellForcing (e : Vec 2) (k : ℤ)
    (ω : Cutoff.CutoffSample 2) : HilbertVec 2 :=
  layerForcing e k (seqValuePath ω.1)

theorem lambda8Q3CutoffShellForcing_memLp (M : ABKModel 2) (e : Vec 2) (k : ℤ) :
    MemLp (lambda8Q3CutoffShellForcing e k) 2 (Cutoff.cutoffSampleLaw M).toMeasure := by
  exact (memLp_two_layerForcing M e k).comp_measurePreserving
    (Model.measurePreserving_cutoffSeqPath M)

theorem lambda8Q3CutoffShellForcing_stronglyMeasurable (e : Vec 2) (k : ℤ) :
    StronglyMeasurable (lambda8Q3CutoffShellForcing e k) := by
  have hcont : Continuous (fun F : ℤ → C(Vec 2, Mat 2) => layerForcing e k F) := by
    change Continuous (fun F : ℤ → C(Vec 2, Mat 2) => valuePathForcing e (F k))
    exact (continuous_valuePathForcing e).comp (continuous_apply k)
  exact (hcont.measurable.comp
    (measurable_seqValuePath.comp measurable_subtype_coe)).stronglyMeasurable

theorem lambda8Q3CutoffShellForcing_realize (e : Vec 2) (k : ℤ)
    (ω : Cutoff.CutoffSample 2) (x : Vec 2) :
    (realize (lambda8Q3CutoffShellForcing e k) ω x).toVec =
      matVecMul ((ω.1 k) x) e := by
  change (layerForcing e k (seqValuePath (x +ᵥ ω).1)).toVec = _
  rw [Model.cutoffSeqPath_vadd]
  simp [layerForcing, valuePathForcing, HilbertVec.toVec_ofVec,
    seqValuePath, ShellField.vadd_apply, ShellField.valuePath, zero_add]

noncomputable def lambda8Q3CutoffShellForcingL2 (M : ABKModel 2)
    (e : Vec 2) (k : ℤ) :=
  carrierTransport (HilbertVec 2) (Model.measurePreserving_cutoffSeqPath M)
    (layerForcingL2 M e k)

theorem lambda8Q3CutoffShellForcing_toLp_eq (M : ABKModel 2) (e : Vec 2) (k : ℤ) :
    (lambda8Q3CutoffShellForcing_memLp M e k).toLp
      (lambda8Q3CutoffShellForcing e k) = lambda8Q3CutoffShellForcingL2 M e k := by
  apply Lp.ext
  let hΦ := Model.measurePreserving_cutoffSeqPath M
  have hF := (lambda8Q3CutoffShellForcing_memLp M e k).coeFn_toLp
  have hT := coeFn_carrierTransport hΦ (layerForcingL2 M e k)
  have hL := hΦ.quasiMeasurePreserving.ae
    (memLp_two_layerForcing M e k).coeFn_toLp
  filter_upwards [hF, hT, hL] with ω hFω hTω hLω
  change (lambda8Q3CutoffShellForcing_memLp M e k).toLp
      (lambda8Q3CutoffShellForcing e k) ω = _ at hFω
  change carrierTransport (HilbertVec 2) hΦ (layerForcingL2 M e k) ω = _ at hTω
  change layerForcingL2 M e k (seqValuePath ω.1) = _ at hLω
  calc
    ((lambda8Q3CutoffShellForcing_memLp M e k).toLp
        (lambda8Q3CutoffShellForcing e k)) ω =
        lambda8Q3CutoffShellForcing e k ω := hFω
    _ = layerForcing e k (seqValuePath ω.1) := rfl
    _ = layerForcingL2 M e k (seqValuePath ω.1) := hLω.symm
    _ = carrierTransport (HilbertVec 2) hΦ (layerForcingL2 M e k) ω := hTω.symm

/-- The actual one-shell forcing has the exact stationary q3 projected energy
`vₖ/2`, with `vₖ` its actual shell variance. -/
theorem lambda8Q3CutoffShellForcing_projection_energy (M : ABKModel 2)
    (h : ℝ) (hM : PlanarQ3Gaussian M h) {e : Vec 2}
    (he : Book.Ch02.vecNorm e = 1) (k : ℤ) :
    ‖stationaryPotentialProjection
      ((lambda8Q3CutoffShellForcing_memLp M e k).toLp
        (lambda8Q3CutoffShellForcing e k))‖ ^ 2 =
      (h ^ 2 * (3 : ℝ) ^ (2 * M.gamma * (k : ℝ))) / 2 := by
  rw [lambda8Q3CutoffShellForcing_toLp_eq,
    lambda8Q3CutoffShellForcingL2,
    stationaryPotentialProjection_carrierTransport
      (Model.measurePreserving_cutoffSeqPath M) Model.cutoffSeqPath_vadd
      (layerForcingL2 M e k)]
  rw [norm_carrierTransport,
    norm_sq_stationaryPotentialProjection_layerForcingL2 M e k,
    norm_sq_stationaryPotentialProjection_layerForcingL2_zero M he,
    ASDExplicitGamma.Model.q3_cstar_exact M h hM]
  have hl : Real.log (3 : ℝ) ≠ 0 :=
    ne_of_gt (Real.log_pos (by norm_num))
  field_simp [hl]

private theorem lambda8Q3LoadField_continuous (a b c d : ℝ)
    (hab : a < b) (hcd : c < d) (e : Vec 2)
    (f : C(Gaussian.closedRectangle a b c d, ℝ)) :
    ∀ i : Fin 2, Continuous (fun x : Vec 2 => lambda8Q3LoadField a b c d hab hcd e f x i) := by
  intro i
  change Continuous (fun x =>
    f (lambda8CovarianceClamp a b c d hab hcd x) *
      matVecMul ASDExplicitGamma.Response.responsePlanarJ e i)
  exact (f.continuous.comp (lambda8CovarianceClamp_continuous a b c d hab hcd)).mul
    continuous_const

theorem lambda8Q3LoadField_memVectorL2
    {U : Set (Vec 2)} [IsFiniteMeasure (volumeMeasureOn U)]
    (_hU : MeasurableSet U) (a b c d : ℝ) (hab : a < b) (hcd : c < d)
    (e : Vec 2) (f : C(Gaussian.closedRectangle a b c d, ℝ)) :
    MemVectorL2 U (lambda8Q3LoadField a b c d hab hcd e f) := by
  rw [Homogenization.MemVectorL2, Homogenization.volumeMeasureOn, memLp_pi_iff]
  intro i
  apply MemLp.of_bound
    (lambda8Q3LoadField_continuous a b c d hab hcd e f i).aestronglyMeasurable
    (‖f‖ * ‖e‖)
  filter_upwards with x
  change ‖lambda8Q3LoadField a b c d hab hcd e f x i‖ ≤ ‖f‖ * ‖e‖
  simp only [lambda8Q3LoadField, Pi.smul_apply, smul_eq_mul]
  rw [Real.norm_eq_abs, abs_mul]
  apply mul_le_mul
  · simpa only [Real.norm_eq_abs] using
      ContinuousMap.norm_coe_le_norm f (lambda8CovarianceClamp a b c d hab hcd x)
  · have he : |matVecMul ASDExplicitGamma.Response.responsePlanarJ e i| ≤ ‖e‖ := by
      fin_cases i
      · simpa [ASDExplicitGamma.Response.responsePlanarJ, matVecMul,
          Fin.sum_univ_two] using norm_le_pi_norm e 1
      · simpa [ASDExplicitGamma.Response.responsePlanarJ, matVecMul,
          Fin.sum_univ_two] using norm_le_pi_norm e 0
    exact he
  · exact abs_nonneg _
  · exact norm_nonneg _

noncomputable def lambda8Q3LoadClassLinear
    {U : Set (Vec 2)} [IsFiniteMeasure (volumeMeasureOn U)]
    (hU : MeasurableSet U) (a b c d : ℝ) (hab : a < b) (hcd : c < d)
    (e : Vec 2) :
    C(Gaussian.closedRectangle a b c d, ℝ) →ₗ[ℝ] HilbertVectorL2 U where
  toFun f := toHilbertVectorL2OfVecField
    (lambda8Q3LoadField_memVectorL2 hU a b c d hab hcd e f)
  map_add' f g := by
    have hfield : lambda8Q3LoadField a b c d hab hcd e (f + g) =
        lambda8Q3LoadField a b c d hab hcd e f +
          lambda8Q3LoadField a b c d hab hcd e g := by
      funext x
      ext i
      simp only [lambda8Q3LoadField, ContinuousMap.add_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul]
      ring
    calc
      _ = toHilbertVectorL2OfVecField
          ((lambda8Q3LoadField_memVectorL2 hU a b c d hab hcd e f).add
            (lambda8Q3LoadField_memVectorL2 hU a b c d hab hcd e g)) :=
          toHilbertVectorL2OfVecField_congr _ _ hfield
      _ = _ := toHilbertVectorL2OfVecField_add _ _
  map_smul' r f := by
    have hfield : lambda8Q3LoadField a b c d hab hcd e (r • f) =
        r • lambda8Q3LoadField a b c d hab hcd e f := by
      funext x
      ext i
      simp only [lambda8Q3LoadField, ContinuousMap.smul_apply,
        Pi.smul_apply, smul_eq_mul]
      ring
    calc
      _ = toHilbertVectorL2OfVecField
          ((lambda8Q3LoadField_memVectorL2 hU a b c d hab hcd e f).const_smul r) :=
          toHilbertVectorL2OfVecField_congr _ _ hfield
      _ = r • toHilbertVectorL2OfVecField
          (lambda8Q3LoadField_memVectorL2 hU a b c d hab hcd e f) := by
          change toHilbertVectorL2
            (memHilbertVectorL2_hilbertifyVecField
              ((lambda8Q3LoadField_memVectorL2 hU a b c d hab hcd e f).const_smul r)) = _
          exact MeasureTheory.MemLp.toLp_const_smul r
            (memHilbertVectorL2_hilbertifyVecField
              (lambda8Q3LoadField_memVectorL2 hU a b c d hab hcd e f))

/-- The actual local vector load map induced by the q3 scalar covariance field. -/
noncomputable def lambda8Q3LoadClass
    {U : Set (Vec 2)} [IsFiniteMeasure (volumeMeasureOn U)]
    (hU : MeasurableSet U) (a b c d : ℝ) (hab : a < b) (hcd : c < d)
    (e : Vec 2) :
    C(Gaussian.closedRectangle a b c d, ℝ) →L[ℝ] HilbertVectorL2 U := by
  let T := lambda8Q3LoadClassLinear hU a b c d hab hcd e
  let C : ℝ := 4 * ((volumeMeasureOn U Set.univ).toReal) ^ ((2 : ℝ)⁻¹) * ‖e‖
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine T.mkContinuous C ?_
  intro f
  have hbound : ∀ x ∈ U,
      ‖lambda8Q3LoadField a b c d hab hcd e f x‖ ≤ ‖f‖ * ‖e‖ := by
    intro x hx
    apply (pi_norm_le_iff_of_nonneg (mul_nonneg (norm_nonneg f) (norm_nonneg e))).2
    intro i
    change ‖f (lambda8CovarianceClamp a b c d hab hcd x) *
        matVecMul ASDExplicitGamma.Response.responsePlanarJ e i‖ ≤ ‖f‖ * ‖e‖
    rw [Real.norm_eq_abs, abs_mul]
    apply mul_le_mul
    · simpa only [Real.norm_eq_abs] using
        ContinuousMap.norm_coe_le_norm f (lambda8CovarianceClamp a b c d hab hcd x)
    · have he : |matVecMul ASDExplicitGamma.Response.responsePlanarJ e i| ≤ ‖e‖ := by
        fin_cases i
        · simpa [ASDExplicitGamma.Response.responsePlanarJ, matVecMul,
            Fin.sum_univ_two] using norm_le_pi_norm e 1
        · simpa [ASDExplicitGamma.Response.responsePlanarJ, matVecMul,
            Fin.sum_univ_two] using norm_le_pi_norm e 0
      exact he
    · exact abs_nonneg _
    · exact norm_nonneg _
  have hnorm := norm_toHilbertVectorL2OfVecField_le_of_bound_on hU
    (lambda8Q3LoadField_memVectorL2 hU a b c d hab hcd e f)
    (mul_nonneg (norm_nonneg f) (norm_nonneg e)) hbound
  change ‖T f‖ ≤ _ at hnorm
  calc
    ‖T f‖ ≤ (volumeMeasureOn U Set.univ).toReal ^ ((2 : ℝ)⁻¹) *
        (2 * (‖f‖ * ‖e‖)) := hnorm
    _ ≤ C * ‖f‖ := by
      dsimp [C]
      have hv : 0 ≤ (volumeMeasureOn U Set.univ).toReal ^ ((2 : ℝ)⁻¹) := by positivity
      have hp := mul_nonneg hv (mul_nonneg (norm_nonneg f) (norm_nonneg e))
      nlinarith

/-- Applying the local Dirichlet projection to the q3 load covariance factor. -/
noncomputable def lambda8Q3ProjectedLoadClass
    {U : Set (Vec 2)} [IsFiniteMeasure (volumeMeasureOn U)]
    (hU : IsOpenBoundedConvexDomain U) (a b c d : ℝ)
    (hab : a < b) (hcd : c < d) (e : Vec 2) :
    C(Gaussian.closedRectangle a b c d, ℝ) →L[ℝ] HilbertVectorL2 U :=
  ((lambda8H10GradientRange hU).toSubmodule.starProjection).comp
    (lambda8Q3LoadClass hU.1.measurableSet a b c d hab hcd e)

/-- Applying the local Dirichlet projection to the q3 load covariance factor. -/
noncomputable def lambda8Q3ProjectedLoad
    {U : Set (Vec 2)} [IsFiniteMeasure (volumeMeasureOn U)]
    (hU : IsOpenBoundedConvexDomain U) (a b c d : ℝ)
    (hab : a < b) (hcd : c < d) (e : Vec 2)
    (β : ℝ) (L : {l : ℝ // 0 < l}) :
    Gaussian.Q3H3Range a b c d β L →L[ℝ] HilbertVectorL2 U :=
  ((lambda8H10GradientRange hU).toSubmodule.starProjection).comp
    ((lambda8Q3LoadClass hU.1.measurableSet a b c d hab hcd e).comp
      (Gaussian.q3H3RangeValue a b c d β L))

/-- The actual q3 shell's expected local projected energy is exactly the
energy of its source-faithful H³/C¹ Cameron--Martin series. -/
theorem lambda8Q3ProjectedLoad_actualShellLaw
    {U : Set (Vec 2)} [IsFiniteMeasure (volumeMeasureOn U)]
    (hU : IsOpenBoundedConvexDomain U) (a b c d : ℝ)
    (hab : a < b) (hcd : c < d) (e : Vec 2)
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (k : ℤ) :
    (∫ ω, ‖lambda8Q3ProjectedLoadClass hU a b c d hab hcd e
      (Gaussian.shellFieldScalarRestriction (Gaussian.closedRectangle a b c d)
        (ω.1 k))‖ ^ 2 ∂(Cutoff.cutoffSampleLaw M).toMeasure) =
      ∫ ω, ‖lambda8Q3ProjectedLoadClass hU a b c d hab hcd e
        (Gaussian.q3C1Series a b c d
          (Gaussian.q3ModelAmplitude M h k) (Gaussian.q3ModelLength k)
          Gaussian.whiteBasis ω 0)‖ ^ 2
        ∂Gaussian.standardGaussianInfinitePi := by
  let K := Gaussian.closedRectangle a b c d
  let T := lambda8Q3ProjectedLoadClass hU a b c d hab hcd e
  let Q : C(K, ℝ) → ℝ := fun f => ‖T f‖ ^ 2
  have hQ : Continuous Q := by
    change Continuous (fun f => ‖T f‖ ^ 2)
    exact (T.continuous.norm).pow 2
  have hactual : Measurable (fun ω : Cutoff.CutoffSample 2 =>
      Gaussian.shellFieldScalarRestriction K (ω.1 k)) :=
    (Gaussian.measurable_shellFieldScalarRestriction K).comp
      ((measurable_pi_apply k).comp measurable_subtype_coe)
  have hseries : Measurable (fun ω : ℕ → ℝ => Gaussian.q3C1Series a b c d
      (Gaussian.q3ModelAmplitude M h k) (Gaussian.q3ModelLength k)
      Gaussian.whiteBasis ω 0) := by
    exact ((ContinuousLinearMap.proj (R := ℝ)
      (φ := fun _ : Fin 3 => C(K, ℝ)) 0).continuous.comp_stronglyMeasurable
      (Gaussian.stronglyMeasurable_q3C1Series a b c d
        (Gaussian.q3ModelAmplitude M h k) (Gaussian.q3ModelLength k)
        Gaussian.whiteBasis)).measurable
  have hlaw := Gaussian.actualShellLaw_eq_h3Series a b c d hab hcd M h hM k
  change (∫ ω, Q (Gaussian.shellFieldScalarRestriction K (ω.1 k))
      ∂(Cutoff.cutoffSampleLaw M).toMeasure) = _
  rw [← integral_map hactual.aemeasurable hQ.aestronglyMeasurable,
    hlaw, integral_map hseries.aemeasurable hQ.aestronglyMeasurable]

/-- The actual local Dirichlet projection of one q3 shell has annealed energy
at most `|U| vₖ/2`. The comparison uses the physical solenoidal residual of
the stationary projection, while the source equality on `U` identifies the
local continuous covariance load with the actual shell forcing. -/
theorem lambda8Q3ProjectedLoadClass_local_energy_le
    {U : Set (Vec 2)} [IsFiniteMeasure (volumeMeasureOn U)]
    (hU : IsOpenBoundedConvexDomain U) {a b c d : ℝ}
    (hUK : U ⊆ Gaussian.openRectangle a b c d)
    (hab : a < b) (hcd : c < d) (e : Vec 2)
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (he : Book.Ch02.vecNorm e = 1) (k : ℤ) :
    (∫ ω, ‖lambda8Q3ProjectedLoadClass hU a b c d hab hcd e
      (Gaussian.shellFieldScalarRestriction (Gaussian.closedRectangle a b c d)
        (ω.1 k))‖ ^ 2 ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
      (volume U).toReal *
        ((h ^ 2 * (3 : ℝ) ^ (2 * M.gamma * (k : ℝ))) / 2) := by
  let F := lambda8Q3CutoffShellForcing e k
  let hF := lambda8Q3CutoffShellForcing_memLp M e k
  let H := Model.stationaryProjectionRepr hF
  let hHm := Model.stronglyMeasurable_stationaryProjectionRepr hF
  let hH := Model.memLp_stationaryProjectionRepr hF
  let T := lambda8Q3ProjectedLoadClass hU a b c d hab hcd e
  let φ := fun ω : Cutoff.CutoffSample 2 =>
    Gaussian.shellFieldScalarRestriction (Gaussian.closedRectangle a b c d)
      (ω.1 k)
  let Y := fun ω : Cutoff.CutoffSample 2 => ‖T (φ ω)‖ ^ 2
  have hφm : Measurable φ :=
    (Gaussian.measurable_shellFieldScalarRestriction
      (Gaussian.closedRectangle a b c d)).comp
      ((measurable_pi_apply k).comp measurable_subtype_coe)
  have hYm : Measurable Y := by
    change Measurable (fun ω => ‖T (φ ω)‖ ^ 2)
    exact ((T.continuous.norm).pow 2).measurable.comp hφm
  have hfm : StronglyMeasurable F :=
    lambda8Q3CutoffShellForcing_stronglyMeasurable e k
  have hres := Model.stationaryProjectionRepr_physical_residual
    (μ := (Cutoff.cutoffSampleLaw M).toMeasure) hU.isOpen
    (ne_of_lt hU.volume_lt_top) hfm hF
  have hsourceAE := ae_memLp_two_realize (μ := (Cutoff.cutoffSampleLaw M).toMeasure)
    (ne_of_lt hU.volume_lt_top) hfm hF
  have hstationAE := ae_memLp_two_realize (μ := (Cutoff.cutoffSampleLaw M).toMeasure)
    (ne_of_lt hU.volume_lt_top) hHm hH
  have hrightInt := integrable_setIntegral_normSq_realize
    (μ := (Cutoff.cutoffSampleLaw M).toMeasure) (S := U)
    (ne_of_lt hU.volume_lt_top) hHm hH
  have hqle : ∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      Y ω ≤ ∫ x in U, ‖realize H ω x‖ ^ 2 := by
    filter_upwards [hres, hsourceAE, hstationAE] with ω hresω hsourceω hstationω
    have hsourceVec : MemVectorL2 U (fun x => (realize F ω x).toVec) :=
      (HilbertVec.continuousLinearEquivVec 2).toContinuousLinearMap.comp_memLp'
        hsourceω
    have hstationVec : MemVectorL2 U (fun x => (realize H ω x).toVec) :=
      (HilbertVec.continuousLinearEquivVec 2).toContinuousLinearMap.comp_memLp'
        hstationω
    have hload := lambda8Q3LoadField_memVectorL2 hU.isOpen.measurableSet
      a b c d hab hcd e (φ ω)
    have hloadEq :
        toHilbertVectorL2OfVecField hload =
          toHilbertVectorL2OfVecField hsourceVec := by
      apply Lp.ext
      filter_upwards [coeFn_toHilbertVectorL2OfVecField hload,
        coeFn_toHilbertVectorL2OfVecField hsourceVec,
        ae_restrict_mem hU.isOpen.measurableSet] with x hloadx hsourcex hx
      rw [hloadx, hsourcex]
      simp only [hilbertifyVecField]
      congr 1
      calc
        lambda8Q3LoadField a b c d hab hcd e (φ ω) x =
            (ω.1 k x 1 0) •
              matVecMul ASDExplicitGamma.Response.responsePlanarJ e :=
          lambda8Q3LoadField_eq_actualShell hUK hab hcd e ω k hx
        _ = matVecMul ((ω.1 k) x) e :=
          (lambda8Q3ShellMatVec_eq_scalarJ (ω.1 k) x e).symm
        _ = (realize F ω x).toVec :=
          (lambda8Q3CutoffShellForcing_realize e k ω x).symm
    have hprojection : T (φ ω) =
        lambda8DirichletProjection hU (toHilbertVectorL2OfVecField hsourceVec) := by
      change ((lambda8H10GradientRange hU).toSubmodule.starProjection)
        (toHilbertVectorL2OfVecField hload) = _
      rw [hloadEq]
      rfl
    have hnormle := lambda8DirichletProjection_norm_le_of_solenoidalResidual
      hU hsourceVec hstationVec hresω.2
    have hpoint : ‖T (φ ω)‖ ^ 2 ≤
        ‖toHilbertVectorL2OfVecField hstationVec‖ ^ 2 := by
      rw [hprojection]
      nlinarith [norm_nonneg (lambda8DirichletProjection hU
          (toHilbertVectorL2OfVecField hsourceVec)),
        norm_nonneg (toHilbertVectorL2OfVecField hstationVec)]
    have henergy : ‖toHilbertVectorL2OfVecField hstationVec‖ ^ 2 =
        ∫ x in U, ‖realize H ω x‖ ^ 2 := by
      rw [← real_inner_self_eq_norm_sq,
        inner_toHilbertVectorL2OfVecField_eq_integral hstationVec hstationVec]
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem hU.isOpen.measurableSet] with x hx
      exact (HilbertVec.inner_def _ _).symm.trans (real_inner_self_eq_norm_sq _)
    exact hpoint.trans_eq henergy
  have hYint : Integrable Y (Cutoff.cutoffSampleLaw M).toMeasure :=
    hrightInt.mono' hYm.aestronglyMeasurable (by
      filter_upwards [hqle] with ω hω
      change ‖‖T (φ ω)‖ ^ 2‖ ≤ _
      rw [Real.norm_of_nonneg (sq_nonneg (‖T (φ ω)‖))]
      simpa [H] using hω)
  calc
    _ = ∫ ω, Y ω ∂(Cutoff.cutoffSampleLaw M).toMeasure := by rfl
    _ ≤ ∫ ω, (∫ x in U, ‖realize H ω x‖ ^ 2)
        ∂(Cutoff.cutoffSampleLaw M).toMeasure :=
      integral_mono_ae hYint hrightInt hqle
    _ = (volume U).toReal * ∫ ω, ‖H ω‖ ^ 2
        ∂(Cutoff.cutoffSampleLaw M).toMeasure :=
      integral_setIntegral_normSq_realize (μ := (Cutoff.cutoffSampleLaw M).toMeasure)
        (S := U) (ne_of_lt hU.volume_lt_top) hHm hH
    _ = (volume U).toReal *
        ‖stationaryPotentialProjection (hF.toLp F)‖ ^ 2 := by
      rw [integral_normSq_eq_norm_sq_toLp hH]
      change (volume U).toReal *
          ‖(Model.memLp_stationaryProjectionRepr hF).toLp
            (Model.stationaryProjectionRepr hF)‖ ^ 2 = _
      rw [Model.toLp_stationaryProjectionRepr]
    _ = _ := by
      rw [lambda8Q3CutoffShellForcing_projection_energy M h hM he k]

/-- The normalized one-load energy is at most half of its actual shell
variance. -/
theorem lambda8Q3ProjectedLoadClass_volumeNormalized_energy_le
    {U : Set (Vec 2)} [IsFiniteMeasure (volumeMeasureOn U)]
    (hU : IsOpenBoundedConvexDomain U)
    (hvol : (volume U).toReal ≠ 0) {a b c d : ℝ}
    (hUK : U ⊆ Gaussian.openRectangle a b c d)
    (hab : a < b) (hcd : c < d) (e : Vec 2)
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (he : Book.Ch02.vecNorm e = 1) (k : ℤ) :
    (volume U).toReal⁻¹ *
      (∫ ω, ‖lambda8Q3ProjectedLoadClass hU a b c d hab hcd e
        (Gaussian.shellFieldScalarRestriction (Gaussian.closedRectangle a b c d)
          (ω.1 k))‖ ^ 2 ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
      (h ^ 2 * (3 : ℝ) ^ (2 * M.gamma * (k : ℝ))) / 2 := by
  have hraw := lambda8Q3ProjectedLoadClass_local_energy_le hU hUK hab hcd e M h hM he k
  calc
    _ ≤ (volume U).toReal⁻¹ * ((volume U).toReal *
        ((h ^ 2 * (3 : ℝ) ^ (2 * M.gamma * (k : ℝ))) / 2)) :=
      mul_le_mul_of_nonneg_left hraw (inv_nonneg.mpr ENNReal.toReal_nonneg)
    _ = _ := by rw [← mul_assoc, inv_mul_cancel₀ hvol, one_mul]

end ASDExplicitGamma.Scalar
