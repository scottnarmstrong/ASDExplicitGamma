module

public import ASDExplicitGamma.Inverse.PureFluxGeneratorOpenBridge
public import ASDExplicitGamma.Inverse.PureFluxGeneratorQ3Map
public import ASDExplicitGamma.Main.Q3RowProduct
public import ASDExplicitGamma.Main.Q3ResidualCoordinates
public import ASDExplicitGamma.Main.Q3ResidualHilbertSchmidt
public import ASDExplicitGamma.Triadic.DiagInterpolant
public import ASDExplicitGamma.Triadic.PlanarDirectionVolume
public import ASDExplicitGamma.Triadic.SensitivityWeakEnergy

/-! The actual q3 response source is the projected DIAG row source for each
affine load. -/

@[expose] public section

open Homogenization MeasureTheory ASDExplicitGamma.Gaussian ASDExplicitGamma.Main
  ASDExplicitGamma.Model ASDExplicitGamma.Response ASDExplicitGamma.Triadic
  ASDExplicitGamma.Variational
  ASDExplicitGamma.Scalar

namespace ASDExplicitGamma.Inverse

local instance pureFluxRowSourceFiniteMeasure (Q : TriadicCube 2) :
    IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
  (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume

/-- The response-frame q3 multiplier, including the physical factor that
appears in the actual shear. -/
noncomputable def pureFluxMainQ3FrameMultiplier (n : ℤ) (b σ : ℝ)
    (L : {l : ℝ // 0 < l}) (l : ℕ) : H1Function (openCubeSet (originCube 2 n)) :=
  (σ⁻¹ : ℝ) •
    (mainQ3DirectionW2 (originCube 2 n) b L (gaussEnumerated whiteBasis l)).value

/-- The same response multiplier indexed directly by the actual white-noise
basis, so source traces do not couple a Gaussian enumeration index to a mesh
depth. -/
noncomputable def pureFluxMainQ3BasisFrameMultiplier (n : ℤ) (b σ : ℝ)
    (L : {l : ℝ // 0 < l}) (l : whiteBasisIndex) :
    H1Function (openCubeSet (originCube 2 n)) :=
  (σ⁻¹ : ℝ) •
    (mainQ3DirectionW2 (originCube 2 n) b L (whiteBasis l)).value

/-- On a descendant tile, the source row splits exactly into the centered
receiver residual used by the covariance Hilbert--Schmidt estimate and the
cell-mean multiplier times the interpolant gradient. This identity isolates
the low-frequency mean term that must be included in the full source trace. -/
theorem pureFluxMainQ3Row_decomposition
    (n : ℤ) (b σ : ℝ) (hσ : 0 < σ) (L : {l : ℝ // 0 < l}) (m : ℕ)
    (l : whiteBasisIndex)
    (p : Vec 2) (r : H10Function (openCubeSet (originCube 2 n)))
    (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth (originCube 2 n) m)
    (x : Vec 2) :
    let Q := originCube 2 n
    let v := lemmaVAffinePotential (isOpenBoundedConvexDomain_openCubeSet Q) p r
    let I := diagInterpolant Q m
    lemmaVPlanarRowField I
        (pureFluxMainQ3BasisFrameMultiplier n b σ L l) v x =
      planarQuarterTurn (fun i => σ⁻¹ *
        (mainQ3ResidualCoordinate whiteBasis b L Q m v U l x i +
          cubeAverage U
            (fun y => q3Convolution b L h3Zero (whiteBasis l) y) *
            (I v).grad x i)) := by
  let Q := originCube 2 n
  let v := lemmaVAffinePotential (isOpenBoundedConvexDomain_openCubeSet Q) p r
  let I := diagInterpolant Q m
  let η := mainQ3DirectionW2 Q b L (whiteBasis l)
  have hη : pureFluxMainQ3BasisFrameMultiplier n b σ L l =
      (σ⁻¹ : ℝ) • η.value := by
    rfl
  have hgrad (i : Fin 2) (y : Vec 2) : η.value.grad y i =
      (fderiv ℝ (q3Convolution b L h3Zero (whiteBasis l)) y) (basisVec i) := by
    have hj₁ := mainQ3DirectionW2_jet Q b L (whiteBasis l) (.first i) y
    change η.value.grad y i =
      q3Convolution b L (mainQ3JetIndex (.first i)) (whiteBasis l) y at hj₁
    have hderiv : (fderiv ℝ (q3Convolution b L h3Zero (whiteBasis l)) y)
        (basisVec i) =
      q3Convolution b L (mainQ3JetIndex (.first i)) (whiteBasis l) y := by
      rw [q3Convolution_fderiv_basis b L h3Zero (by decide)]
      fin_cases i <;> norm_num [mainQ3JetIndex, h3Next, h3Zero,
        Model.Q3SpatialJet.count]
    exact hj₁.trans hderiv.symm
  change lemmaVPlanarRowField I (pureFluxMainQ3BasisFrameMultiplier n b σ L l) v x = _
  rw [hη, lemmaVH2_rowField_eq]
  apply congrArg planarQuarterTurn
  funext i
  simp only [H1Function.smul_toFun, H1Function.smul_grad, Pi.smul_apply, smul_eq_mul]
  rw [mainQ3DirectionW2_value, hgrad]
  simp only [mainQ3ResidualCoordinate, mainQ3DirectionW2_value]
  ring

/-- The actual q3 covariance controls the square sum of all cell-mean
coefficients. This is the low-frequency source contribution needed beside
the centered residual Hilbert--Schmidt estimate. -/
theorem pureFluxMainQ3_cellMeanSquare_bound {ι : Type*}
    (e : HilbertBasis ι ℝ WhiteNoise) (s : Finset ι) (b : ℝ)
    (L : {l : ℝ // 0 < l}) (U : TriadicCube 2) :
    ∑ l ∈ s,
      (cubeAverage U (fun x => q3Convolution b L h3Zero (e l) x)) ^ 2 ≤ b ^ 2 := by
  let f := mainQ3FiniteValue e s b L
  have hf : MemLp f 2 (normalizedCubeMeasure U) :=
    (main_continuous_memLp_top U (mainQ3FiniteValue_contDiff e s b L).continuous).mono_exponent
      (by simp : (2 : ENNReal) ≤ ⊤)
  have hcov (x : Vec 2) :
      ∑ l ∈ s, (q3Convolution b L h3Zero (e l) x) ^ 2 ≤ b ^ 2 := by
    have hc := mainQ3DirectionW2_jet_covariance e U b L .value .value x
    have hs : Summable (fun l => (q3Convolution b L h3Zero (e l) x) ^ 2) := by
      simpa only [mainQ3DirectionW2_jet, q3DirectionJet, mainQ3DirectionW2_value,
        pow_two] using hc.summable
    have htsum : (∑' l, (q3Convolution b L h3Zero (e l) x) ^ 2) = b ^ 2 := by
      simpa only [mainQ3DirectionW2_jet, q3DirectionJet, mainQ3DirectionW2_value, pow_two,
        q3ScaledJetCovariance_value_diagonal] using hc.tsum_eq
    calc
      ∑ l ∈ s, (q3Convolution b L h3Zero (e l) x) ^ 2 ≤
          ∑' l, (q3Convolution b L h3Zero (e l) x) ^ 2 :=
        hs.sum_le_tsum s (fun l _ => sq_nonneg _)
      _ = b ^ 2 := htsum
  have hpoint (x : Vec 2) : ‖f x‖ ^ 2 ≤ b ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    change (∑ l : s, (q3Convolution b L h3Zero (e l) x) ^ 2) ≤ b ^ 2
    calc
      _ = ∑ l ∈ s, (q3Convolution b L h3Zero (e l) x) ^ 2 :=
        Finset.sum_coe_sort s _
      _ ≤ b ^ 2 := hcov x
  have henergy : hilbertEnergy U f ≤ b ^ 2 := by
    unfold hilbertEnergy
    calc
      (∫ x, ‖f x‖ ^ 2 ∂normalizedCubeMeasure U) ≤
          ∫ _x, (b : ℝ) ^ 2 ∂normalizedCubeMeasure U :=
        integral_mono_ae (hf.integrable_norm_pow (by norm_num))
          (integrable_const _) (Filter.Eventually.of_forall hpoint)
      _ = b ^ 2 := by
        rw [integral_const]
        simp only [Measure.real_def, normalizedCubeMeasure_apply_univ,
          ENNReal.toReal_one, one_smul]
  have hmean := main_hilbert_cube_mean_sq_le U hf
  have hmeanEq : ‖hilbertCubeAverage U f‖ ^ 2 =
      ∑ l ∈ s, (cubeAverage U
        (fun x => q3Convolution b L h3Zero (e l) x)) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    change (∑ l : s, (hilbertCubeAverage U
      (mainQ3FiniteValue e s b L)).ofLp l ^ 2) = _
    simp_rw [mainQ3FiniteValue_average_coordinate]
    exact Finset.sum_coe_sort s (fun l : ι =>
      (cubeAverage U (fun x => q3Convolution b L h3Zero (e l) x)) ^ 2)
  calc
    ∑ l ∈ s, (cubeAverage U
        (fun x => q3Convolution b L h3Zero (e l) x)) ^ 2 =
      ‖hilbertCubeAverage U f‖ ^ 2 := hmeanEq.symm
    _ ≤ hilbertEnergy U f := hmean
    _ ≤ b ^ 2 := henergy

/-- Broken positive-Haar energy of the actual cell-mean part of one q3 source
row, averaged over the DIAG cells. -/
noncomputable def pureFluxMainQ3MeanFieldEnergy
    (n : ℤ) (b σ : ℝ) (L : {l : ℝ // 0 < l}) (m : ℕ)
    (p : Vec 2) (u : H10Function (openCubeSet (originCube 2 n)))
    (l : whiteBasisIndex) : ℝ :=
  let Q := originCube 2 n
  let v := lemmaVAffinePotential (isOpenBoundedConvexDomain_openCubeSet Q) p u
  descendantsAverage Q m (fun U => vectorPositiveHaarEnergy U (fun x i =>
    σ⁻¹ * cubeAverage U (fun y => q3Convolution b L h3Zero (whiteBasis l) y) *
      (diagInterpolant Q m v).grad x i))

/-- Broken positive-Haar energy of one actual q3 source row, averaged over
the DIAG cells. -/
noncomputable def pureFluxMainQ3RowEnergy
    (n : ℤ) (b σ : ℝ) (L : {l : ℝ // 0 < l}) (m : ℕ)
    (p : Vec 2) (u : H10Function (openCubeSet (originCube 2 n)))
    (l : whiteBasisIndex) : ℝ :=
  let Q := originCube 2 n
  let v := lemmaVAffinePotential (isOpenBoundedConvexDomain_openCubeSet Q) p u
  descendantsAverage Q m (fun U => vectorPositiveHaarEnergy U
    (lemmaVPlanarRowField (diagInterpolant Q m)
      (pureFluxMainQ3BasisFrameMultiplier n b σ L l) v))

end ASDExplicitGamma.Inverse
