module

public import ASDExplicitGamma.Scalar.UpperCellEnergyResetWeakGradient
public import ASDExplicitGamma.Scalar.UpperCellEnergyResetStationaryAverage
public import ASDExplicitGamma.Scalar.UpperCellEnergyResetFrame
public import ASDExplicitGamma.Scalar.UpperCellEnergyResetHistory
public import ASDExplicitGamma.Scalar.UpperCellEnergyResetLoad
public import ASDExplicitGamma.Scalar.UpperCellEnergyResetOrbitGaussian
public import ASDExplicitGamma.Scalar.UpperCellEnergyResetPoincare
public import ASDExplicitGamma.Scalar.UpperCellEnergyResetBottomResidual
public import ASDExplicitGamma.Scalar.UpperCellEnergyTrial
public import ASDExplicitGamma.Scalar.UpperCellEnergyEndpointMonotone
public import ASDExplicitGamma.Gaussian.SupMeanFirstCovariance
public import ASDExplicitGamma.Gaussian.DerivativeLawMoments
public import ASDExplicitGamma.Triadic.PoincareCell
public import Homogenization.Book.Ch02.Theorems.MatrixOperatorNorm

/-! The actual correlated first moment of the physical RESET residual. -/

@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory ProbabilityTheory Gaussian
open Algsuperdiff.Probability.Stationary Algsuperdiff.Section3
open Algsuperdiff.Section3.Provider.Corrector Algsuperdiff.Frozen.Assumptions
open ASDExplicitGamma.Model Annealed Response Triadic
open scoped ENNReal BigOperators
noncomputable section

private theorem upper_cell_reset_weak_gradient_sub_const
    {d : ℕ} (U : Set (Vec d)) [IsFiniteMeasure (volume.restrict U)]
    (u : Vec d → ℝ) (G : Vec d → Vec d)
    (hu : MemLp u 2 (volume.restrict U)) (a : ℝ)
    (hw : HasWeakGradientOn U u G) :
    HasWeakGradientOn U (fun x => u x-a) G := by
  intro i φ hφ hcompact hsub
  let Dφ := fun x : Vec d => (fderiv ℝ φ x) (basisVec i)
  have hDcont : Continuous Dφ := by
    dsimp [Dφ]
    exact (hφ.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hDcompact : HasCompactSupport Dφ := by
    simpa [Dφ] using hcompact.fderiv_apply (𝕜 := ℝ) (basisVec i)
  have hD : MemLp Dφ 2 (volume.restrict U) :=
    hDcont.memLp_of_hasCompactSupport hDcompact
  have huD : Integrable (fun x => u x*Dφ x) (volume.restrict U) := hu.integrable_mul hD
  have hcD : Integrable (fun x => a*Dφ x) (volume.restrict U) :=
    (memLp_const (μ := volume.restrict U) (p := (2:ℝ≥0∞)) a).integrable_mul hD
  have hconst := HasWeakGradientOn.of_contDiff (U := U)
    (contDiff_const : ContDiff ℝ 1 (fun _ : Vec d => a))
  have hz : (∫ x in U, a*Dφ x ∂volume)=0 := by
    have hh := hconst i φ hφ hcompact hsub
    simpa [Dφ] using hh
  have hsubint : (∫ x in U, (u x-a)*Dφ x ∂volume) =
      (∫ x in U, u x*Dφ x ∂volume) - ∫ x in U, a*Dφ x ∂volume := by
    calc
      _ = ∫ x in U, (u x*Dφ x-a*Dφ x) ∂volume := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun x => by dsimp [Dφ]; ring)
      _ = _ := integral_sub huD hcD
  calc
    _ = ∫ x in U, u x*Dφ x ∂volume := by simpa [Dφ, hz] using hsubint
    _ = _ := by simpa [Dφ] using hw i φ hφ hcompact hsub

private theorem upper_cell_reset_scalarLp_norm_sq
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (f : ScalarL2 μ) :
    ‖f‖ ^ 2 = ∫ ω, (f ω) ^ 2 ∂μ := by
  calc
    ‖f‖ ^ 2 = inner ℝ f f := (real_inner_self_eq_norm_sq f).symm
    _ = ∫ ω, inner ℝ (f ω) (f ω) ∂μ := rfl
    _ = ∫ ω, (f ω) ^ 2 ∂μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun ω => by simp)

private noncomputable def upperCellResetPhysicalDerivative
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (n : ℤ) (height : ℕ) (c : ℝ) (e : Vec 2) :
    Fin 2 → VectorL2 2 (Cutoff.cutoffSampleLaw M).toMeasure := by
  let k := upperCellPhysicalBandLabel n height
  let w : Fin height → ℝ := fun _ => c
  let hGaussian := upper_cell_reset_band_jets_gaussian M h hM n height c
  exact fun j => upperCellResetScalarVectorMap
    (Cutoff.cutoffSampleLaw M).toMeasure (matVecMul Response.responsePlanarJ e)
    (upperCellResetBandJetClass M k w hGaussian (.first 0 (basisVec j)))

private def upperCellResetPhysicalGradientCoordinate
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (n : ℤ) (height : ℕ) (c : ℝ) (e : Vec 2) (i j : Fin 2) :
    Cutoff.CutoffSample 2 → ℝ :=
  fun ω => (upperCellResetDerivativeRowRepr
    (upperCellResetPhysicalDerivative M h hM n height c e) i ω).toVec j

private theorem upper_cell_reset_physical_gradient_coordinate_gaussian
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (n : ℤ) (height : ℕ) (c : ℝ) (e : Vec 2)
    (i j : Fin 2) :
    ∃ variance : NNReal, (Cutoff.cutoffSampleLaw M).toMeasure.map
      (upperCellResetPhysicalGradientCoordinate
        M h hM n height c e i j) = gaussianReal 0 variance := by
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let k := upperCellPhysicalBandLabel n height
  let w : Fin height → ℝ := fun _ => c
  let hGaussian := upper_cell_reset_band_jets_gaussian M h hM n height c
  let v := upperCellResetBandJetClass M k w hGaussian (.value 0)
  let T := upperCellResetScalarVectorMap μ (matVecMul Response.responsePlanarJ e)
  let F := upperCellResetBandForcing M n (n+(height:ℤ)) c e
  let D := upperCellResetPhysicalDerivative M h hM n height c e
  have hvOrbit : v ∈ upperCellResetOrbit v := by
    unfold upperCellResetOrbit ASDExplicitGamma.Model.KoopmanOrbitSubspace
    exact Submodule.le_topologicalClosure _
      (Submodule.subset_span ⟨0, by simp [koopman_zero]⟩)
  have hFcoord (a : Fin 2) : vectorL2Coord a F =
      matVecMul Response.responsePlanarJ e a • v := by
    exact upper_cell_reset_band_forcing_coord M h hM n height c e a
  have hF_eq : T v = F := by
    apply upper_cell_reset_vector_ext μ
    intro a
    rw [upper_cell_reset_scalar_vector_map_coord, hFcoord]
  have hFOrbit : ∀ a : Fin 2, vectorL2Coord a F ∈ upperCellResetOrbit v := by
    intro a
    rw [hFcoord a]
    exact (upperCellResetOrbit v).smul_mem _ hvOrbit
  have hvGaussian := upper_cell_reset_band_orbit_gaussian M k w hGaussian
  have hD (b : Fin 2) : HasDerivAt
      (fun t : ℝ => koopman (t • basisVec b) F) (D b) 0 := by
    have hs := upper_cell_reset_band_horizontal_derivative M k w hGaussian (basisVec b)
    have hm := T.hasFDerivAt.comp_hasDerivAt 0 hs
    have heq : (fun t : ℝ => T (koopman (t • basisVec b) v)) =
        (fun t : ℝ => koopman (t • basisVec b) F) := by
      funext t
      rw [upper_cell_reset_scalar_vector_map_translate, hF_eq]
    rw [← heq]
    exact hm
  obtain ⟨variance, hmap⟩ := upper_cell_reset_flux_derivative_gaussian
    v hvGaussian (basisVec j) F (D j) hFOrbit (hD j) i
  let Z := vectorL2Coord j (upperCellResetDerivativeRow D i)
  have hrowCoord : vectorL2Coord j (upperCellResetDerivativeRow D i) =
      vectorL2Coord i (upperCellResetStationaryFlux (D j)) :=
    upper_cell_reset_derivative_row_coord D i j
  have hmapZ : μ.map Z = gaussianReal 0 variance := by
    dsimp only [Z]
    rw [hrowCoord]
    exact hmap
  have hrowMem := upper_cell_reset_derivative_row_memLp D i
  have hrowMeas := upper_cell_reset_derivative_row_measurable D i
  have hrowToLp := upper_cell_reset_derivative_row_toLp D i
  have hcoordAE : Z =ᵐ[μ] upperCellResetPhysicalGradientCoordinate
      M h hM n height c e i j := by
    change vectorL2Coord j (upperCellResetDerivativeRow D i) =ᵐ[μ]
      fun ω => (upperCellResetDerivativeRowRepr D i ω).toVec j
    rw [← hrowToLp]
    have hcoord := Lp.ext_iff.mp (vectorL2Coord_toLp hrowMeas hrowMem j)
    have hfield := (memLp_coordField hrowMeas hrowMem j).coeFn_toLp
    filter_upwards [hcoord, hfield] with ω hω hfieldω
    exact hω.trans hfieldω
  exact ⟨variance, (Measure.map_congr hcoordAE).symm.trans hmapZ⟩

private theorem upper_cell_reset_physical_gradient_coordinate_l2_ae
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (n : ℤ) (height : ℕ) (c : ℝ) (e : Vec 2) (i j : Fin 2) :
    upperCellResetPhysicalGradientCoordinate M h hM n height c e i j =ᵐ[
      (Cutoff.cutoffSampleLaw M).toMeasure]
      (vectorL2Coord i (upperCellResetStationaryFlux
        (upperCellResetPhysicalDerivative M h hM n height c e j)) :
          Cutoff.CutoffSample 2 → ℝ) := by
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let D := upperCellResetPhysicalDerivative M h hM n height c e
  let row := upperCellResetDerivativeRow D i
  let repr := upperCellResetDerivativeRowRepr D i
  have hrowMem := upper_cell_reset_derivative_row_memLp D i
  have hrowMeas := upper_cell_reset_derivative_row_measurable D i
  have hrowToLp := upper_cell_reset_derivative_row_toLp D i
  have hrepr : (vectorL2Coord j row : Cutoff.CutoffSample 2 → ℝ) =ᵐ[μ]
      fun ω => (repr ω).toVec j := by
    change vectorL2Coord j (upperCellResetDerivativeRow D i) =ᵐ[μ]
      fun ω => (upperCellResetDerivativeRowRepr D i ω).toVec j
    rw [← hrowToLp]
    have hcoord := Lp.ext_iff.mp (vectorL2Coord_toLp hrowMeas hrowMem j)
    have hfield := (memLp_coordField hrowMeas hrowMem j).coeFn_toLp
    filter_upwards [hcoord, hfield] with ω hω hfieldω
    exact hω.trans hfieldω
  have hrowCoord : vectorL2Coord j row =
      vectorL2Coord i (upperCellResetStationaryFlux (D j)) := by
    exact upper_cell_reset_derivative_row_coord D i j
  have hcoord := Lp.ext_iff.mp hrowCoord
  change (fun ω => (repr ω).toVec j) =ᵐ[μ]
      (vectorL2Coord i (upperCellResetStationaryFlux (D j)) :
        Cutoff.CutoffSample 2 → ℝ)
  exact hrepr.symm.trans hcoord

private theorem upper_cell_reset_band_jet_second_moment
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (n : ℤ) (height : ℕ) (c : ℝ) (j : Fin 2) :
    ∫ ω : Cutoff.CutoffSample 2,
      (upperCellResetBandJet (upperCellPhysicalBandLabel n height)
        (fun _ => c) (.first 0 (basisVec j)) ω) ^ 2
        ∂(Cutoff.cutoffSampleLaw M).toMeasure =
      (78/5:ℝ)*upperCellBandVariance M h
        (upperCellPhysicalBandLabel n height) (fun _ => c) 1 := by
  let k := upperCellPhysicalBandLabel n height
  let w : Fin height → ℝ := fun _ => c
  let o := ShellDerivativeObservation.first 0 (basisVec j)
  have hcov := upper_cell_band_jet_covariance M h hM k
    (upper_cell_physical_band_label_injective n height) w o o
  have hsecond :
      ∫ ω : Cutoff.CutoffSample 2,
        (upperCellResetBandJet k w o ω) ^ 2
          ∂(Cutoff.cutoffSampleLaw M).toMeasure =
        ∑ a : Fin height, w a ^ 2 * q3ShellDerivativeCovariance M h (k a) o o := by
    change ∫ ω, (upperCellBandJet k w o ω) ^ 2 ∂_ = _
    convert hcov using 1 <;> congr 1 <;> funext ω <;> ring
  have hdiag (a : Fin height) :
      q3ShellDerivativeCovariance M h (k a) o o =
        (78/5:ℝ)*(h^2*(3:ℝ)^(2*M.gamma*((k a:ℤ):ℝ))/((3:ℝ)^(k a))^2) := by
    have hraw := q3Shell_stored_derivative_covariance M h hM (k a) o o
    have hsup := supMean_shell_first_covariance_diagonal M h hM (k a) 0
      (basisVec j) (basisVec j)
    have hh := hraw.symm.trans hsup
    have hbasis :
        basisVec j 0 * basisVec j 0 + basisVec j 1 * basisVec j 1 = 1 := by
      fin_cases j <;> simp [basisVec]
    calc
      _ = h ^ 2 * (3:ℝ) ^ (2*M.gamma*((k a:ℤ):ℝ)) *
          ((3:ℝ)^(k a))⁻¹^2 * (78/5:ℝ) *
            (basisVec j 0*basisVec j 0 + basisVec j 1*basisVec j 1) := by
          simpa [o] using hh
      _ = _ := by rw [hbasis]; ring
  rw [hsecond]
  simp_rw [hdiag]
  unfold upperCellBandVariance
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  ring

private theorem upper_cell_reset_physical_gradient_second_moment_sum
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (n : ℤ) (height : ℕ) (c : ℝ) (e : Vec 2)
    (he : Book.Ch02.vecNorm e = 1) :
    (∑ i : Fin 2, ∑ j : Fin 2,
      ∫ ω : Cutoff.CutoffSample 2,
        (upperCellResetPhysicalGradientCoordinate
          M h hM n height c e i j ω) ^ 2
          ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
      (156/5:ℝ)*upperCellBandVariance M h
        (upperCellPhysicalBandLabel n height) (fun _ => c) 1 := by
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let k := upperCellPhysicalBandLabel n height
  let w : Fin height → ℝ := fun _ => c
  let hGaussian := upper_cell_reset_band_jets_gaussian M h hM n height c
  let D := upperCellResetPhysicalDerivative M h hM n height c e
  let b := matVecMul Response.responsePlanarJ e
  have heSq : vecNormSq e = 1 := by
    rw [← Book.Ch02.vecNorm_sq_eq_vecNormSq, he]
    norm_num
  have hbSq : vecNormSq b = 1 := by
    calc
      vecNormSq b = vecNormSq e := by dsimp [b]; exact responsePlanarJ_vecNormSq e
      _ = 1 := heSq
  have hvecNorm (F : VectorL2 2 μ) :
      ‖F‖ ^ 2 = ∑ i : Fin 2, ‖vectorL2Coord i F‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, upper_cell_reset_vector_inner μ]
    simp only [real_inner_self_eq_norm_sq]
  have hjet (j : Fin 2) :
      ‖upperCellResetBandJetClass M k w hGaussian
        (.first 0 (basisVec j))‖ ^ 2 =
        (78/5:ℝ)*upperCellBandVariance M h k w 1 := by
    rw [upper_cell_reset_scalarLp_norm_sq]
    have hrep := (upper_cell_reset_band_jet_memLp M k w hGaussian
      (.first 0 (basisVec j))).coeFn_toLp
    have hrep' :
        (upperCellResetBandJetClass M k w hGaussian
          (.first 0 (basisVec j)) : ScalarL2 μ) =ᵐ[μ]
          upperCellResetBandJet k w (.first 0 (basisVec j)) := by
      simpa [upperCellResetBandJetClass] using hrep
    have hmoment := upper_cell_reset_band_jet_second_moment M h hM n height c j
    calc
      _ = ∫ ω : Cutoff.CutoffSample 2,
          (upperCellResetBandJet k w (.first 0 (basisVec j)) ω) ^ 2 ∂μ := by
            apply integral_congr_ae
            filter_upwards [hrep'] with ω hω
            rw [hω]
      _ = _ := hmoment
  have hD (j : Fin 2) : ‖D j‖ ^ 2 =
      ‖upperCellResetBandJetClass M k w hGaussian
        (.first 0 (basisVec j))‖ ^ 2 := by
    calc
      ‖D j‖ ^ 2 = ∑ a : Fin 2, ‖vectorL2Coord a (D j)‖ ^ 2 := hvecNorm (D j)
      _ = ∑ a : Fin 2,
          (b a) ^ 2 * ‖upperCellResetBandJetClass M k w hGaussian
            (.first 0 (basisVec j))‖ ^ 2 := by
          apply Finset.sum_congr rfl
          intro a ha
          dsimp only [D, upperCellResetPhysicalDerivative]
          rw [upper_cell_reset_scalar_vector_map_coord]
          rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
      _ = vecNormSq b * ‖upperCellResetBandJetClass M k w hGaussian
          (.first 0 (basisVec j))‖ ^ 2 := by
          rw [← Finset.sum_mul]
          simp [vecNormSq, vecDot, pow_two]
      _ = _ := by rw [hbSq]; norm_num
  have hcoordMoment (i j : Fin 2) :
      ∫ ω : Cutoff.CutoffSample 2,
        (upperCellResetPhysicalGradientCoordinate
          M h hM n height c e i j ω) ^ 2 ∂μ =
        ‖vectorL2Coord i (upperCellResetStationaryFlux (D j))‖ ^ 2 := by
    have hae := upper_cell_reset_physical_gradient_coordinate_l2_ae
      M h hM n height c e i j
    calc
      _ = ∫ ω : Cutoff.CutoffSample 2,
          ((vectorL2Coord i (upperCellResetStationaryFlux (D j)) :
            Cutoff.CutoffSample 2 → ℝ) ω) ^ 2 ∂μ := by
            apply integral_congr_ae
            filter_upwards [hae] with ω hω
            rw [hω]
      _ = _ := (upper_cell_reset_scalarLp_norm_sq μ
        (vectorL2Coord i (upperCellResetStationaryFlux (D j)))).symm
  calc
    _ = ∑ j : Fin 2, ∑ i : Fin 2,
        ‖vectorL2Coord i (upperCellResetStationaryFlux (D j))‖ ^ 2 := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro j hj
          apply Finset.sum_congr rfl
          intro i hi
          exact hcoordMoment i j
    _ = ∑ j : Fin 2, ‖upperCellResetStationaryFlux (D j)‖ ^ 2 := by
          apply Finset.sum_congr rfl
          intro j hj
          exact (hvecNorm (upperCellResetStationaryFlux (D j))).symm
    _ ≤ ∑ j : Fin 2, ‖D j‖ ^ 2 := by
          apply Finset.sum_le_sum
          intro j hj
          have hn := upper_cell_reset_stationary_flux_norm (D j)
          nlinarith [norm_nonneg (upperCellResetStationaryFlux (D j)), norm_nonneg (D j)]
    _ = (156/5:ℝ)*upperCellBandVariance M h k w 1 := by
          simp_rw [hD, hjet]
          simp [Finset.sum_const, Finset.card_fin]
          ring

private theorem upper_cell_reset_physical_gradient_spatial_square_L2
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (n : ℤ) (height : ℕ) (c : ℝ) (e : Vec 2) (Q : TriadicCube 2)
    (he : Book.Ch02.vecNorm e = 1) :
    MemLp (fun ω : Cutoff.CutoffSample 2 =>
      ∑ i : Fin 2, ∑ j : Fin 2,
        cubeAverage Q (fun x =>
          (realize (upperCellResetDerivativeRowRepr
            (upperCellResetPhysicalDerivative M h hM n height c e) i) ω x).toVec j ^ 2))
      2 (Cutoff.cutoffSampleLaw M).toMeasure ∧
    lpNorm (fun ω : Cutoff.CutoffSample 2 =>
      ∑ i : Fin 2, ∑ j : Fin 2,
        cubeAverage Q (fun x =>
          (realize (upperCellResetDerivativeRowRepr
            (upperCellResetPhysicalDerivative M h hM n height c e) i) ω x).toVec j ^ 2))
      2 (Cutoff.cutoffSampleLaw M).toMeasure ≤
      Real.sqrt 3 * (156/5:ℝ) *
        upperCellBandVariance M h (upperCellPhysicalBandLabel n height)
          (fun _ => c) 1 := by
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let D := upperCellResetPhysicalDerivative M h hM n height c e
  let X : Fin 2 × Fin 2 → Cutoff.CutoffSample 2 → ℝ := fun ij ω =>
    (upperCellResetDerivativeRowRepr D ij.1 ω).toVec ij.2
  let G : Cutoff.CutoffSample 2 → ℝ := fun ω =>
    ∑ ij : Fin 2 × Fin 2, cubeAverage Q (fun x => (realize (X ij) ω x)^2)
  have hXm (ij : Fin 2 × Fin 2) : StronglyMeasurable (X ij) := by
    dsimp [X]
    exact ((ContinuousLinearMap.proj ij.2 : Vec 2 →L[ℝ] ℝ).continuous.comp
      (HilbertVec.continuousLinearEquivVec 2).continuous).comp_stronglyMeasurable
        (upper_cell_reset_derivative_row_measurable D ij.1)
  have hmap (ij : Fin 2 × Fin 2) :
      ∃ v : NNReal, μ.map (X ij) = gaussianReal 0 v := by
    exact upper_cell_reset_physical_gradient_coordinate_gaussian
      M h hM n height c e ij.1 ij.2
  have hX (ij : Fin 2 × Fin 2) : HasGaussianLaw (X ij) μ := by
    obtain ⟨v,hv⟩ := hmap ij
    exact ⟨(hXm ij).aemeasurable, by rw [hv]; infer_instance⟩
  have hm (ij : Fin 2 × Fin 2) : ∫ ω, X ij ω ∂μ = 0 := by
    have hi := integral_map (μ := μ) (hXm ij).aemeasurable
      measurable_id.aestronglyMeasurable
    obtain ⟨v,hv⟩ := hmap ij
    calc
      (∫ ω, X ij ω ∂μ) = ∫ x, x ∂μ.map (X ij) := hi.symm
      _ = 0 := by rw [hv]; exact integral_id_gaussianReal
  have hspace := upper_cell_reset_gaussian_spatial_vector_L2 Q X hXm hX hm
  have hmoment := upper_cell_reset_physical_gradient_second_moment_sum
    M h hM n height c e he
  have hmoment' :
      ∑ ij : Fin 2 × Fin 2, ∫ ω, (X ij ω)^2 ∂μ ≤
        (156/5:ℝ)*upperCellBandVariance M h
          (upperCellPhysicalBandLabel n height) (fun _ => c) 1 := by
    rw [Fintype.sum_prod_type]
    simpa [X, upperCellResetPhysicalGradientCoordinate] using hmoment
  have hG : MemLp G 2 μ ∧
      lpNorm G 2 μ ≤ Real.sqrt 3 * (156/5:ℝ) *
        upperCellBandVariance M h (upperCellPhysicalBandLabel n height)
          (fun _ => c) 1 := by
    refine ⟨hspace.1, ?_⟩
    calc
      _ ≤ Real.sqrt 3 * ∑ ij : Fin 2 × Fin 2, ∫ ω, (X ij ω)^2 ∂μ := hspace.2
      _ ≤ Real.sqrt 3 * ((156/5:ℝ) *
          upperCellBandVariance M h (upperCellPhysicalBandLabel n height)
            (fun _ => c) 1) := by
          exact mul_le_mul_of_nonneg_left hmoment' (Real.sqrt_nonneg 3)
      _ = _ := by ring
  have hG_eq : G = fun ω =>
      ∑ i : Fin 2, ∑ j : Fin 2,
        cubeAverage Q (fun x =>
          (realize (upperCellResetDerivativeRowRepr D i) ω x).toVec j ^ 2) := by
    funext ω
    dsimp [G]
    rw [Fintype.sum_prod_type]
    simp [X, realize]
  rw [← hG_eq]
  exact hG

private theorem upper_cell_reset_holder_product
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (H G : Ω → ℝ) (hH0 : ∀ ω, 0 ≤ H ω) (hG0 : ∀ ω, 0 ≤ G ω)
    (hG : MemLp G 2 μ)
    (hBound : ℝ) (hBound0 : 0 ≤ hBound)
    (hHcap : eLpNorm H (ENNReal.ofReal (64:ℝ)) μ ≤ ENNReal.ofReal hBound)
    (gBound : ℝ)
    (hGcap : lpNorm G 2 μ ≤ gBound) :
    Integrable (fun ω => H ω * G ω) μ ∧
      (∫ ω, H ω * G ω ∂μ) ≤ hBound*gBound := by
  have hHmem : MemLp H (ENNReal.ofReal (64:ℝ)) μ := by
    rw [memLp_iff]
    exact lt_of_le_of_lt hHcap ENNReal.ofReal_lt_top
  have hGmem : MemLp G (ENNReal.ofReal (64/63:ℝ)) μ :=
    hG.mono_exponent (by norm_num : ENNReal.ofReal (64/63:ℝ) ≤ 2)
  have hconj : (64:ℝ).HolderConjugate (64/63:ℝ) := by
    rw [Real.holderConjugate_iff_eq_conjExponent (by norm_num : (1:ℝ)<64)]
    norm_num [Real.conjExponent]
  letI : ENNReal.HolderTriple (ENNReal.ofReal (64:ℝ))
      (ENNReal.ofReal (64/63:ℝ)) 1 := hconj.ennrealOfReal
  have hprodMem : MemLp (fun ω => H ω * G ω) 1 μ := hHmem.mul hGmem
  have hprod : Integrable (fun ω => H ω * G ω) μ :=
    memLp_one_iff_integrable.mp hprodMem
  have hHolder := integral_mul_le_Lp_mul_Lq_of_nonneg hconj
    (Filter.Eventually.of_forall fun ω => hH0 ω)
    (Filter.Eventually.of_forall fun ω => hG0 ω) hHmem hGmem
  have hHnorm : lpNorm H (ENNReal.ofReal (64:ℝ)) μ ≤ hBound := by
    calc
      lpNorm H (ENNReal.ofReal (64:ℝ)) μ =
          (eLpNorm H (ENNReal.ofReal (64:ℝ)) μ).toReal := rfl
      _ ≤ (ENNReal.ofReal hBound).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hHcap
      _ = hBound := ENNReal.toReal_ofReal hBound0
  have hGnorm : lpNorm G (ENNReal.ofReal (64/63:ℝ)) μ ≤ gBound := by
    calc
      lpNorm G (ENNReal.ofReal (64/63:ℝ)) μ =
          (eLpNorm G (ENNReal.ofReal (64/63:ℝ)) μ).toReal := rfl
      _ ≤ (eLpNorm G 2 μ).toReal := ENNReal.toReal_mono hG.eLpNorm_ne_top
        (eLpNorm_le_eLpNorm_of_exponent_le (by norm_num))
      _ = lpNorm G 2 μ := rfl
      _ ≤ gBound := hGcap
  have hpow (f : Ω → ℝ) (p : ℝ) (hp : 0 < p) (hf : MemLp f (ENNReal.ofReal p) μ)
      (hfn : ∀ ω, 0 ≤ f ω) :
      (∫ ω, f ω ^ p ∂μ) ^ (1/p) = lpNorm f (ENNReal.ofReal p) μ := by
    rw [lpNorm_eq_integral_norm_rpow_toReal (by positivity) (by simp) hf.aestronglyMeasurable]
    have hp' : (ENNReal.ofReal p).toReal = p := ENNReal.toReal_ofReal hp.le
    rw [hp']
    congr 1
    apply integral_congr_ae
    filter_upwards [] with ω
    rw [Real.norm_of_nonneg (hfn ω)]
    rw [one_div]
  rw [hpow H 64 (by norm_num) hHmem hH0,
    hpow G (64/63) (by norm_num) hGmem hG0] at hHolder
  refine ⟨hprod, ?_⟩
  have hGnorm_nonneg : 0 ≤ lpNorm G (ENNReal.ofReal (64/63:ℝ)) μ :=
    lpNorm_nonneg
  have hnormProduct :
      lpNorm H (ENNReal.ofReal (64:ℝ)) μ *
        lpNorm G (ENNReal.ofReal (64/63:ℝ)) μ ≤ hBound*gBound :=
    mul_le_mul hHnorm hGnorm hGnorm_nonneg hBound0
  have hbound : ∫ ω, H ω * G ω ∂μ ≤ hBound*gBound :=
    hHolder.trans hnormProduct
  simpa using hbound

/-- The first moment of the literal physical RESET residual is paid by the
complete terminal history and the correlated spatial gradient-square load.
The history and source are evaluated on the same cutoff sample throughout. -/
theorem upper_cell_reset_physical_residual_first_moment
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero) (N : ℤ)
    (hpast : ∀ k < N, nativeInductionState M h k)
    (n : ℤ) (hn : n < N) (e : Vec 2) (he : Book.Ch02.vecNorm e = 1)
    (F : Cutoff.CutoffSample 2 → HilbertBlockL2
      (openCubeSet (originCube 2 (n-14))))
    (hFmeas : Measurable F)
    (hF : ∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      ∃ hω : MemBlockL2 (openCubeSet (originCube 2 (n-14)))
        (bandLoad M n (n + ((Nat.floor ((17/50:ℝ)/M.gamma)):ℤ))
          (Annealed.sigmaBar M n : ℝ) e ω),
        F ω = toHilbertBlockL2OfBlockField hω) :
    let height : ℕ := Nat.floor ((17/50:ℝ)/M.gamma)
    let Q := originCube 2 (n-14)
    let σ : ℝ := (Annealed.sigmaBar M n : ℝ)
    let μ := (Cutoff.cutoffSampleLaw M).toMeasure
    let Y : Cutoff.CutoffSample 2 → HilbertBlockL2 (openCubeSet Q) :=
      fun ω => scalarProjectionResidual Q M.nu σ M.nu_pos (Annealed.sigmaBar M n).property
        (oldCutoffSkewCoefficient (n+(height:ℤ)) Q ω)
        (F ω-upperCellResetMeanField Q (F ω))
    let E : Cutoff.CutoffSample 2 → ℝ := fun ω =>
      (scalarFrameRealization Q M.nu σ M.nu_pos (Annealed.sigmaBar M n).property
        (oldCutoffSkewCoefficient (n+(height:ℤ)) Q ω)).energyBilin (Y ω) (Y ω)
    Integrable E μ ∧
      (∫ ω, E ω ∂μ) ≤
        upperCellResidualProfile M.gamma (M.gamma*(height:ℝ)) := by
  let height : ℕ := Nat.floor ((17/50:ℝ)/M.gamma)
  let terminal : ℤ := n+(height:ℤ)
  let Q : TriadicCube 2 := originCube 2 (n-14)
  let σ : ℝ := (Annealed.sigmaBar M n : ℝ)
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let c : ℝ := σ⁻¹
  let H : Cutoff.CutoffSample 2 → ℝ≥0∞ := fun ω =>
    completeFullResponseHistory Q
      (responseFramePlanarCoefficientField M.nu σ
        (oldCutoffSkewCoefficient terminal Q ω))
  let D : Fin 2 → VectorL2 2 μ :=
    upperCellResetPhysicalDerivative M h hM n height c e
  let G : Cutoff.CutoffSample 2 → ℝ := fun ω =>
    ∑ i : Fin 2, ∑ j : Fin 2,
      cubeAverage Q (fun x =>
        (realize (upperCellResetDerivativeRowRepr D i) ω x).toVec j ^ 2)
  let Fcenter : Cutoff.CutoffSample 2 → HilbertBlockL2 (openCubeSet Q) :=
    fun ω => F ω-upperCellResetMeanField Q (F ω)
  let Y : Cutoff.CutoffSample 2 → HilbertBlockL2 (openCubeSet Q) := fun ω =>
      scalarProjectionResidual Q M.nu σ M.nu_pos (Annealed.sigmaBar M n).property
      (oldCutoffSkewCoefficient terminal Q ω) (Fcenter ω)
  let E : Cutoff.CutoffSample 2 → ℝ := fun ω =>
    (scalarFrameRealization Q M.nu σ M.nu_pos (Annealed.sigmaBar M n).property
      (oldCutoffSkewCoefficient terminal Q ω)).energyBilin (Y ω) (Y ω)
  let Hreal : Cutoff.CutoffSample 2 → ℝ := fun ω => (H ω).toReal
  let histCap : ℝ := upperCellHistoryProfile M.gamma (M.gamma*(height:ℝ))
  let gCap : ℝ := Real.sqrt 3*(156/5:ℝ)*
    upperCellBandVariance M h (upperCellPhysicalBandLabel n height)
      (fun _ => c) 1
  let B : ℝ := upperCellResetPoincareConstant*cubeScaleFactor Q^2

  have hgamma : 0 < M.gamma := M.shellPrefix.gamma_pos
  have hsigma : 0 < σ := (Annealed.sigmaBar M n).property
  have hfloor : (height:ℝ) ≤ (17/50:ℝ)/M.gamma := by
    dsimp [height]
    exact Nat.floor_le (by positivity)
  have hb : M.gamma*(height:ℝ) ≤ 17/50 := by
    calc
      M.gamma*(height:ℝ) ≤ M.gamma*((17/50:ℝ)/M.gamma) :=
        mul_le_mul_of_nonneg_left hfloor hgamma.le
      _ = 17/50 := by field_simp
  have hpastN : ∀ k < n, nativeInductionState M h k := by
    intro k hk
    exact hpast k (hk.trans hn)

  have hhist := upper_cell_reset_terminal_history_L64 M h hM hγ n
    hpastN height hb
  have hHistCap : eLpNorm Hreal (ENNReal.ofReal (64:ℝ)) μ ≤ ENNReal.ofReal histCap := by
    simpa [Hreal, H, histCap, Q, terminal] using hhist.1
  have hHistFinite : ∀ᵐ ω ∂μ, H ω < ⊤ := by
    simpa [H, Q, terminal] using hhist.2
  have hHistNonneg : ∀ ω, 0 ≤ Hreal ω := by
    intro ω
    exact ENNReal.toReal_nonneg
  have hHistCapNonneg : 0 ≤ histCap := by
    have hh := upper_cell_history_profile_bounds M.gamma
      (M.gamma*(height:ℝ)) hgamma.le hγ (mul_nonneg hgamma.le (Nat.cast_nonneg _)) hb
    simpa [histCap] using hh.1

  have hvariance := upper_cell_physical_band_variance_le M h n hγ
    (hpast n hn) 1 height (by norm_num)
  have hscale : cubeScaleFactor Q^2 =
      (3:ℝ)^(2*((1:ℕ):ℝ)*((n:ℝ)-14)) := by
    calc
      cubeScaleFactor Q^2 = ((3:ℝ)^(n-14))^2 := by
        simp [Q, cubeScaleFactor_originCube]
      _ = ((3:ℝ)^(n-14))^(2*1) := by norm_num
      _ = (3:ℝ)^(2*((1:ℕ):ℝ)*((n-14:ℤ):ℝ)) :=
        upper_cell_physical_scale_power (n-14) 1
      _ = (3:ℝ)^(2*((1:ℕ):ℝ)*((n:ℝ)-14)) := by
        congr 1
        push_cast
        ring
  have hvariance' := hvariance
  rw [← hscale] at hvariance'
  have hexp : -28*((1:ℕ):ℝ) = -(28:ℝ) := by norm_num
  rw [hexp, Real.rpow_neg (by norm_num : (0:ℝ)≤3)] at hvariance'
  have hscaledVariance : cubeScaleFactor Q^2 *
      upperCellBandVariance M h (upperCellPhysicalBandLabel n height)
        (fun _ => c) 1 ≤ M.gamma/(3:ℝ)^28 := by
    simpa [c, σ, div_eq_mul_inv] using hvariance'
  have hVnonneg : 0 ≤ upperCellBandVariance M h
      (upperCellPhysicalBandLabel n height) (fun _ => c) 1 :=
    upper_cell_band_variance_nonneg M h
      (upperCellPhysicalBandLabel n height) (fun _ => c) 1
  have hgCapNonneg : 0 ≤ gCap := by
    dsimp [gCap]
    exact mul_nonneg (mul_nonneg (Real.sqrt_nonneg 3) (by norm_num)) hVnonneg
  have hGdata := upper_cell_reset_physical_gradient_spatial_square_L2
    M h hM n height c e Q he

  have hMeanMeas : Measurable (fun ω => upperCellResetMeanField Q (F ω)) :=
    upper_cell_reset_mean_field_measurable Q F hFmeas
  have hFcenterMeas : Measurable Fcenter := by
    dsimp [Fcenter]
    exact ((continuous_id.sub (upperCellResetMeanField Q).continuous).measurable.comp
      hFmeas)
  have hYmeas : Measurable Y := by
    dsimp [Y]
    exact upper_cell_random_projection_measurable terminal Q M.nu σ
      M.nu_pos hsigma Fcenter hFcenterMeas
  have hEmeas : Measurable E := by
    dsimp [E]
    exact upper_cell_random_energy_measurable M terminal σ hsigma Q Y hYmeas
  have hEnonneg : ∀ ω, 0 ≤ E ω := by
    intro ω
    change 0 ≤ (scalarFrameRealization Q M.nu σ M.nu_pos hsigma
      (oldCutoffSkewCoefficient terminal Q ω)).energyBilin (Y ω) (Y ω)
    rw [upper_cell_cutoff_hilbert_energy M terminal σ hsigma Q ω (Y ω)]
    apply volumeAverage_nonneg_of_nonneg_on (measurableSet_openCubeSet Q)
    intro x hx
    unfold responseFrameEnergyDensity
    exact add_nonneg
      (mul_nonneg (div_nonneg M.nu_pos.le (le_of_lt hsigma)) (vecNormSq_nonneg _))
      (mul_nonneg (div_nonneg hsigma.le M.nu_pos.le) (vecNormSq_nonneg _))

  have hCenteredAE := upper_cell_reset_actual_band_centered
    M n terminal σ e Q F hF
  have hWeakAE := upper_cell_reset_band_physical_weak_gradient
    M h hM n height c e Q
  have hRowsMemAE : ∀ᵐ ω ∂μ, ∀ i : Fin 2,
      MemLp (fun x => realize (upperCellResetDerivativeRowRepr D i) ω x)
        2 (volume.restrict (openCubeSet Q)) := by
    apply ae_all_iff.mpr
    intro i
    exact ae_memLp_two_realize (μ := μ) (volume_openCubeSet_lt_top Q).ne
      (upper_cell_reset_derivative_row_measurable D i)
      (upper_cell_reset_derivative_row_memLp D i)

  have hEnergyBoundAE : ∀ᵐ ω ∂μ,
      E ω ≤ B*(Hreal ω*G ω) := by
    filter_upwards [hF, hCenteredAE, hWeakAE, hRowsMemAE, hHistFinite] with ω hload hcenter hweak hrows hHfinite
    obtain ⟨hloadLp, hloadEq⟩ := hload
    have hrep : F ω =ᵐ[volumeMeasureOn (openCubeSet Q)]
        fun x => HilbertBlockVec.ofBlockVec (bandLoad M n terminal σ e ω x) := by
      rw [hloadEq]
      exact coeFn_toHilbertBlockL2OfBlockField hloadLp
    let mean : BlockVec 2 := upperCellResetMeanValue Q (F ω)
    let u : Vec 2 → Vec 2 := fun x => (bandLoad M n terminal σ e ω x).2
    let f : Vec 2 → Vec 2 := fun x => u x-mean.2
    let grad : Vec 2 → Fin 2 → Vec 2 := fun x i =>
      (realize (upperCellResetDerivativeRowRepr D i) ω x).toVec
    have huCoord (i : Fin 2) : MemLp (fun x => u x i) 2 (normalizedCubeMeasure Q) :=
      memLp_normalized_of_memL2On
        (memScalarL2_coord_of_memVectorL2 (memVectorL2_snd_of_memBlockL2 hloadLp) i)
    have hu : MemLp u 2 (normalizedCubeMeasure Q) :=
      memLp_pi_iff.mpr (fun i => huCoord i)
    have hmean (i : Fin 2) : mean.2 i = cubeAverage Q (fun x => u x i) := by
      have hm := upper_cell_reset_mean_of_ae_field Q (F ω)
        (fun x => bandLoad M n terminal σ e ω x) hrep (.inr i)
      change mean.2 i = cubeAverage Q (fun x => (bandLoad M n terminal σ e ω x).2 i)
      exact hm
    have hf : MemLp f 2 (normalizedCubeMeasure Q) := by
      dsimp [f]
      exact hu.sub (memLp_const mean.2)
    have hmeanZero (i : Fin 2) : cubeAverage Q (fun x => f x i)=0 := by
      dsimp [f]
      rw [cubeAverage_sub_const_of_memLp_two Q (huCoord i), hmean i, sub_self]
    have hweakU (i : Fin 2) : HasWeakGradientOn (openCubeSet Q)
        (fun x => u x i) (grad · i) := by
      have hwi := hweak i
      simpa [u, grad, bandLoad, terminal, c, σ, D,
        upperCellResetPhysicalDerivative] using hwi
    have hweakF (i : Fin 2) : HasWeakGradientOn (openCubeSet Q)
        (fun x => f x i) (grad · i) := by
      apply upper_cell_reset_weak_gradient_sub_const (openCubeSet Q)
        (fun x => u x i) (grad · i)
        (memL2On_openCubeSet_of_memLp_normalizedCubeMeasure Q (huCoord i))
        (mean.2 i) (hweakU i)
    have hgradMem (i j : Fin 2) :
        MemLp (fun x => grad x i j) 2 (normalizedCubeMeasure Q) := by
      exact memLp_normalized_of_memL2On
        ((((ContinuousLinearMap.proj j : Vec 2 →L[ℝ] ℝ).comp
          (HilbertVec.continuousLinearEquivVec 2).toContinuousLinearMap).comp_memLp'
            (hrows i)))
    have hpoi := upper_cell_reset_vector_poincare Q f grad hf
      hgradMem hweakF hmeanZero
    have hEnergyEq : ∑ i : Fin 2, ∑ j : Fin 2,
        energy Q (fun x => grad x i j) = G ω := by
      unfold G
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      rw [energy_eq_integral_sq, ← cubeAverage_eq_integral_normalizedCubeMeasure]
    have hPbound : positiveSourceEnergy Q f ≤ B*G ω := by
      calc
        positiveSourceEnergy Q f ≤ upperCellResetPoincareConstant*cubeScaleFactor Q^2*
            ∑ i : Fin 2, ∑ j : Fin 2, energy Q (fun x => grad x i j) := hpoi.2
        _ = B*G ω := by rw [hEnergyEq]
    have hPnonneg : 0 ≤ positiveSourceEnergy Q f := positive_source_energy_nonneg Q f
    have hdet := upper_cell_reset_bottom_hilbert_energy Q M.nu σ M.nu_pos
      hsigma (oldCutoffSkewCoefficient terminal Q ω) f hpoi.1 (Fcenter ω) hcenter
    have hdet' : ENNReal.ofReal (E ω) ≤ H ω*ENNReal.ofReal (positiveSourceEnergy Q f) := by
      simpa [E, Y, Fcenter, H, Q, terminal, σ] using hdet
    have hHrealEq : ENNReal.ofReal (Hreal ω)=H ω :=
      ENNReal.ofReal_toReal (ne_of_lt hHfinite)
    have hEreal : E ω ≤ Hreal ω*positiveSourceEnergy Q f := by
      rw [← hHrealEq, ← ENNReal.ofReal_mul (ENNReal.toReal_nonneg)] at hdet'
      exact (ENNReal.ofReal_le_ofReal_iff
        (mul_nonneg (ENNReal.toReal_nonneg) hPnonneg)).mp hdet'
    have hH0 : 0 ≤ Hreal ω := ENNReal.toReal_nonneg
    calc
      E ω ≤ Hreal ω*positiveSourceEnergy Q f := hEreal
      _ ≤ Hreal ω*(B*G ω) := mul_le_mul_of_nonneg_left hPbound hH0
      _ = B*(Hreal ω*G ω) := by ring

  have hBnonneg : 0 ≤ B := by
    have hbase0 : 0 ≤ sourceHaarBase :=
      zero_le_one.trans source_haar_base_gt_one.le
    have hbase9 : sourceHaarBase < 9 := by
      have hp := Real.rpow_le_rpow_of_exponent_le
        (by norm_num : (1:ℝ) ≤ 3) (by norm_num : (1/4:ℝ) ≤ 1)
      rw [Real.rpow_one] at hp
      exact hp.trans_lt (by norm_num)
    have hden : 0 < Real.pi^2*(1-sourceHaarBase/9) := by
      have hpi : 0 < Real.pi^2 := sq_pos_of_pos Real.pi_pos
      have hfactor : 0 < 1-sourceHaarBase/9 := by
        have hratio : sourceHaarBase/9 < 1 :=
          (div_lt_one (by norm_num : (0:ℝ) < 9)).2 hbase9
        linarith
      exact mul_pos hpi hfactor
    dsimp [B, upperCellResetPoincareConstant]
    exact mul_nonneg (div_nonneg hbase0 hden.le) (sq_nonneg (cubeScaleFactor Q))
  have hGnonneg : ∀ ω, 0 ≤ G ω := by
    intro ω
    unfold G
    apply Finset.sum_nonneg
    intro i hi
    apply Finset.sum_nonneg
    intro j hj
    apply cubeAverage_nonneg_of_nonneg_on
    intro x hx
    exact sq_nonneg _
  have hHolder := upper_cell_reset_holder_product μ Hreal G
    hHistNonneg hGnonneg hGdata.1 histCap hHistCapNonneg hHistCap gCap
    (by simpa [G, μ, D, upperCellResetPhysicalDerivative, gCap] using hGdata.2)
  have hMajorInt : Integrable (fun ω => B*(Hreal ω*G ω)) μ :=
    hHolder.1.const_mul B
  have hEnormBound : ∀ᵐ ω ∂μ,
      ‖E ω‖ ≤ B*(Hreal ω*G ω) := by
    filter_upwards [hEnergyBoundAE] with ω hω
    rw [Real.norm_eq_abs, abs_of_nonneg (hEnonneg ω)]
    exact hω
  have hEint : Integrable E μ := hMajorInt.mono' hEmeas.aestronglyMeasurable hEnormBound
  have hExpected : (∫ ω, E ω ∂μ) ≤ B*(histCap*gCap) := by
    calc
      (∫ ω, E ω ∂μ) ≤ ∫ ω, B*(Hreal ω*G ω) ∂μ :=
        integral_mono_ae hEint hMajorInt hEnergyBoundAE
      _ = B*(∫ ω, Hreal ω*G ω ∂μ) := by rw [integral_const_mul]
      _ ≤ B*(histCap*gCap) := mul_le_mul_of_nonneg_left hHolder.2 hBnonneg

  have hpayment := upper_cell_reset_poincare_payment
  have hcore : B*gCap ≤ 10*M.gamma/(3:ℝ)^28 := by
    dsimp [B, gCap]
    calc
      upperCellResetPoincareConstant*cubeScaleFactor Q^2*
          (Real.sqrt 3*(156/5:ℝ)*
            upperCellBandVariance M h (upperCellPhysicalBandLabel n height)
              (fun _ => c) 1) =
        (Real.sqrt 3*upperCellResetPoincareConstant*(156/5:ℝ))*
          (cubeScaleFactor Q^2*upperCellBandVariance M h
            (upperCellPhysicalBandLabel n height) (fun _ => c) 1) := by ring
      _ ≤ 10*(M.gamma/(3:ℝ)^28) := by
        exact mul_le_mul hpayment hscaledVariance
          (mul_nonneg (sq_nonneg (cubeScaleFactor Q)) hVnonneg) (by norm_num)
      _ = 10*M.gamma/(3:ℝ)^28 := by ring
  have hresult : (∫ ω, E ω ∂μ) ≤ histCap*(10*M.gamma/(3:ℝ)^28) := by
    calc
      _ ≤ B*(histCap*gCap) := hExpected
      _ = histCap*(B*gCap) := by ring
      _ ≤ histCap*(10*M.gamma/(3:ℝ)^28) :=
        mul_le_mul_of_nonneg_left hcore hHistCapNonneg
  constructor
  · simpa [E, μ, Q, σ, terminal, height, Y, Fcenter] using hEint
  · rw [upperCellResidualProfile]
    change (∫ ω, E ω ∂μ) ≤
      10*upperCellHistoryProfile M.gamma (M.gamma*(height:ℝ))*M.gamma/(3:ℝ)^28
    calc
      _ ≤ histCap*(10*M.gamma/(3:ℝ)^28) := hresult
      _ = 10*histCap*M.gamma/(3:ℝ)^28 := by ring

end
end ASDExplicitGamma.Scalar
