module

public import ASDExplicitGamma.Scalar.OldHessianTrialFrozenErrorIdentity
public import ASDExplicitGamma.Scalar.OldHessianTrialFrozenErrorFrobenius
public import ASDExplicitGamma.Native.OldSignedFlatMeans
public import ASDExplicitGamma.Native.OldSignedFlatCoordinateSeries

/-! MA-E-COVARIANCE, step 8 (covariance interface NOTE §4): the cell-constant
covariance matrix `N^±_U = Σ_n a_{n,U} m^±_{n,U}` of the finite-parent flat fields
and its boundary error `E^±_U = N^±_U - (v/2) J`, for BOTH signs (the minus case
is the SC-OLD-HESSIAN-TRIAL chain; here it is run generically in the sign flag). -/

@[expose] public section

namespace ASDExplicitGamma.Main

open Homogenization MeasureTheory ASDExplicitGamma.Native ASDExplicitGamma.Scalar
  ASDExplicitGamma.Response ASDExplicitGamma.Triadic ASDExplicitGamma.Variational
  ASDExplicitGamma.Gaussian ASDExplicitGamma.Inverse

noncomputable section

theorem hotCov_flat_value_series (Q : TriadicCube 2) (b : ℝ) (L : {l : ℝ // 0 < l})
    (plus : Bool) (a : Fin 2 × Fin 2) :
    Summable (fun n : whiteBasisIndex => energy Q (oldSignedFlatCoordinate Q b L plus n a).toFun) := by
  cases plus
  · exact old_signed_flat_minus_value_series Q b L a
  · exact old_signed_flat_plus_value_series Q b L a

theorem hotCov_flat_gradient_series (Q : TriadicCube 2) (b : ℝ) (L : {l : ℝ // 0 < l})
    (plus : Bool) (a : Fin 2 × Fin 2) (j : Fin 2) :
    Summable (fun n : whiteBasisIndex =>
      energy Q (fun x => (oldSignedFlatCoordinate Q b L plus n a).grad x j)) := by
  cases plus
  · exact old_signed_flat_minus_gradient_series Q b L a j
  · exact old_signed_flat_plus_gradient_series Q b L a j

/-- The Hilbert-valued kernel of the finite-parent flat coordinate `(i,k)`. -/
def hotCovFlatKernel (Q : TriadicCube 2) (b : ℝ) (L : {l : ℝ // 0 < l}) (plus : Bool)
    (i k : Fin 2) : HilbertH1Function (openCubeSet Q) WhiteNoise :=
  oldSignedNormalizedH1Kernel Q whiteBasis
    (fun j => oldSignedFlatCoordinate Q b L plus j (i, k))
    (hotCov_flat_value_series Q b L plus (i, k))
    (hotCov_flat_gradient_series Q b L plus (i, k))

/-- Cell mean `m^±_{n,i,k}` of the flat coordinate `(i,k)`. -/
def hotCovFlatMean (Q : TriadicCube 2) (b : ℝ) (L : {l : ℝ // 0 < l}) (plus : Bool)
    (U : TriadicCube 2) (n : whiteBasisIndex) (i k : Fin 2) : ℝ :=
  cubeAverage U (fun x => oldSignedFlatCoordinate Q b L plus n (i, k) x)

/-- The frozen covariance matrix `N_U(k,i) = Σ_n a_{n,U} m_{n,i,k}`. -/
def hotCovMeanCov (Q U : TriadicCube 2) (b : ℝ) (L : {l : ℝ // 0 < l}) (plus : Bool) :
    Mat 2 := fun k i => ∑' j : whiteBasisIndex,
  cubeAverage U (q3Convolution b L h3Zero (whiteBasis j)) *
    hotCovFlatMean Q b L plus U j i k

/-- Boundary error `E_U = N_U - (v/2) J`. -/
def hotCovMeanCovErr (Q U : TriadicCube 2) (b : ℝ) (L : {l : ℝ // 0 < l}) (plus : Bool) :
    Mat 2 := hotCovMeanCov Q U b L plus - (b ^ 2 / 2) • responsePlanarJ

theorem hotCov_flat_kernel_coefficient (Q : TriadicCube 2) (depth : ℕ)
    (b : ℝ) (L : {l : ℝ // 0 < l}) (plus : Bool) (U : TriadicCube 2)
    (hU : U ∈ descendantsAtDepth Q depth) (i k : Fin 2) (j : whiteBasisIndex) :
    (fun x => inner ℝ (whiteBasis j) ((hotCovFlatKernel Q b L plus i k).toFun x)) =ᵐ[
      normalizedCubeMeasure U] fun x => oldSignedFlatCoordinate Q b L plus j (i, k) x := by
  have hc := old_signed_h1_kernel_coefficient Q whiteBasis
    (fun j => oldSignedFlatCoordinate Q b L plus j (i, k))
    (hotCov_flat_value_series Q b L plus (i, k))
    (hotCov_flat_gradient_series Q b L plus (i, k)) j
  have hu := ae_restrict_of_ae_restrict_of_subset
    (openCubeSet_subset_of_mem_descendantsAtDepth hU) hc
  unfold normalizedCubeMeasure cubeMeasure
  apply Measure.ae_smul_measure
  rw [volume_restrict_cubeSet_eq_volume_restrict_openCubeSet]
  exact hu

theorem hotCov_flat_kernel_mean (Q : TriadicCube 2) (depth : ℕ)
    (b : ℝ) (L : {l : ℝ // 0 < l}) (plus : Bool) (U : TriadicCube 2)
    (hU : U ∈ descendantsAtDepth Q depth) (i k : Fin 2) (j : whiteBasisIndex) :
    inner ℝ (whiteBasis j) (hilbertCubeAverage U (hotCovFlatKernel Q b L plus i k).toFun) =
      hotCovFlatMean Q b L plus U j i k := by
  let u := (hotCovFlatKernel Q b L plus i k).restrict
    (openCubeSet_subset_of_mem_descendantsAtDepth hU) (measurableSet_openCubeSet Q)
  have hm : MemLp (hotCovFlatKernel Q b L plus i k).toFun 2 (normalizedCubeMeasure U) :=
    u.memL2_normalized U
  rw [← hilbertCubeAverage_inner U (whiteBasis j) hm]
  change cubeAverage U _ = cubeAverage U _
  simp only [cubeAverage_eq_integral_normalizedCubeMeasure]
  exact integral_congr_ae (hotCov_flat_kernel_coefficient Q depth b L plus U hU i k j)

theorem hotCov_remainder_kernel_coefficient (Q : TriadicCube 2) (depth : ℕ)
    (b : ℝ) (L : {l : ℝ // 0 < l}) (plus : Bool) (U : TriadicCube 2)
    (hU : U ∈ descendantsAtDepth Q depth) (i k : Fin 2) (j : whiteBasisIndex) :
    (fun x => inner ℝ (whiteBasis j) ((oldSignedRemainderKernel Q b L plus (i, k)).toFun x)) =ᵐ[
      normalizedCubeMeasure U] oldSignedRemainderCoordinate Q b L plus j (i, k) := by
  have hc := old_signed_h1_kernel_coefficient Q whiteBasis
    (fun j => oldSignedRemainderCoordinate Q b L plus j (i, k))
    (old_signed_coordinate_value_summable Q _
      (old_signed_remainder_coordinate_value_trace Q b L plus).summable (i, k))
    (old_signed_coordinate_derivative_summable Q _
      (old_signed_remainder_coordinate_gradient_bound Q b L plus).1 (i, k)) j
  have hu := ae_restrict_of_ae_restrict_of_subset
    (openCubeSet_subset_of_mem_descendantsAtDepth hU) hc
  unfold normalizedCubeMeasure cubeMeasure
  apply Measure.ae_smul_measure
  rw [volume_restrict_cubeSet_eq_volume_restrict_openCubeSet]
  exact hu

/-- The finite-parent flat kernel is the whole-plane projected kernel plus the
actual parent harmonic correction, on the same cell. -/
theorem hotCov_flat_kernel_decomposition (Q : TriadicCube 2) (depth : ℕ)
    (b : ℝ) (L : {l : ℝ // 0 < l}) (plus : Bool) (U : TriadicCube 2)
    (hU : U ∈ descendantsAtDepth Q depth) (i k : Fin 2) :
    (hotCovFlatKernel Q b L plus i k).toFun =ᵐ[normalizedCubeMeasure U]
      fun x => oldHessianProjectedMinusKernel b L x i k +
        (oldSignedRemainderKernel Q b L plus (i, k)).toFun x := by
  have hc : ∀ᵐ x ∂normalizedCubeMeasure U, ∀ j : whiteBasisIndex,
      inner ℝ (whiteBasis j) ((hotCovFlatKernel Q b L plus i k).toFun x) =
        inner ℝ (whiteBasis j) (oldHessianProjectedMinusKernel b L x i k +
          (oldSignedRemainderKernel Q b L plus (i, k)).toFun x) := by
    rw [ae_all_iff]
    intro j
    filter_upwards [hotCov_flat_kernel_coefficient Q depth b L plus U hU i k j,
      hotCov_remainder_kernel_coefficient Q depth b L plus U hU i k j] with x hx hy
    rw [hx, inner_add_right, old_hessian_projected_minus_kernel_coefficient, hy]
    exact old_signed_flat_coordinate_decomposition Q b L plus j i k x
  filter_upwards [hc] with x hx
  apply whiteBasis.repr.injective
  ext j
  simpa only [HilbertBasis.repr_apply_apply] using hx j

theorem hotCov_flat_point_covariance (Q : TriadicCube 2) (depth : ℕ)
    (b : ℝ) (L : {l : ℝ // 0 < l}) (plus : Bool) (U : TriadicCube 2)
    (hU : U ∈ descendantsAtDepth Q depth) (i k : Fin 2) :
    (fun x => inner ℝ (q3Section b L h3Zero x) ((hotCovFlatKernel Q b L plus i k).toFun x)) =ᵐ[
      normalizedCubeMeasure U]
      fun x => (b ^ 2 / 2) * responsePlanarJ k i +
        inner ℝ (q3Section b L h3Zero x)
          ((oldSignedRemainderKernel Q b L plus (i, k)).toFun x) := by
  filter_upwards [hotCov_flat_kernel_decomposition Q depth b L plus U hU i k] with x hx
  rw [hx, inner_add_right, old_hessian_projected_minus_point_covariance]

theorem hotCov_meanCov_kernel (Q : TriadicCube 2) (depth : ℕ)
    (b : ℝ) (L : {l : ℝ // 0 < l}) (plus : Bool) (U : TriadicCube 2)
    (hU : U ∈ descendantsAtDepth Q depth) (i k : Fin 2) :
    HasSum (fun j : whiteBasisIndex => cubeAverage U (q3Convolution b L h3Zero (whiteBasis j)) *
        hotCovFlatMean Q b L plus U j i k)
      (inner ℝ (hilbertCubeAverage U (q3Section b L h3Zero))
        (hilbertCubeAverage U (hotCovFlatKernel Q b L plus i k).toFun)) := by
  have hs := whiteBasis.hasSum_inner_mul_inner
    (hilbertCubeAverage U (q3Section b L h3Zero))
    (hilbertCubeAverage U (hotCovFlatKernel Q b L plus i k).toFun)
  apply hs.congr_fun
  intro j
  rw [real_inner_comm (whiteBasis j), hotCov_flat_kernel_mean Q depth b L plus U hU i k j,
    ← old_hessian_white_section_mean U b L j]

theorem hotCov_meanCov_entry (Q : TriadicCube 2) (depth : ℕ)
    (b : ℝ) (L : {l : ℝ // 0 < l}) (plus : Bool) (U : TriadicCube 2)
    (hU : U ∈ descendantsAtDepth Q depth) (i k : Fin 2) :
    HasSum (fun j : whiteBasisIndex => cubeAverage U (q3Convolution b L h3Zero (whiteBasis j)) *
        hotCovFlatMean Q b L plus U j i k) (hotCovMeanCov Q U b L plus k i) :=
  (hotCov_meanCov_kernel Q depth b L plus U hU i k).summable.hasSum

/-- Exact error identity: the harmonic parent covariance minus the joint centered
covariance. -/
theorem hotCov_meanCov_error_identity (Q : TriadicCube 2) (depth : ℕ)
    (b : ℝ) (L : {l : ℝ // 0 < l}) (plus : Bool) (U : TriadicCube 2)
    (hU : U ∈ descendantsAtDepth Q depth) (i k : Fin 2) :
    let F := q3Section b L h3Zero
    let G := (hotCovFlatKernel Q b L plus i k).toFun
    hotCovMeanCovErr Q U b L plus k i =
      cubeAverage U (fun x => inner ℝ (F x)
          ((oldSignedRemainderKernel Q b L plus (i, k)).toFun x)) -
        cubeAverage U (fun x => inner ℝ (F x - hilbertCubeAverage U F)
          (G x - hilbertCubeAverage U G)) := by
  intro F G
  let g := (hotCovFlatKernel Q b L plus i k).restrict
    (openCubeSet_subset_of_mem_descendantsAtDepth hU) (measurableSet_openCubeSet Q)
  let R := (oldSignedRemainderKernel Q b L plus (i, k)).restrict
    (openCubeSet_subset_of_mem_descendantsAtDepth hU) (measurableSet_openCubeSet Q)
  have hF : MemLp F 2 (normalizedCubeMeasure U) := old_hessian_white_section_memLp U b L
  have hG : MemLp G 2 (normalizedCubeMeasure U) := g.memL2_normalized U
  have hR : MemLp R.toFun 2 (normalizedCubeMeasure U) := R.memL2_normalized U
  have hcent := old_hessian_hilbert_covariance_centering U F G hF hG
  have havg : cubeAverage U (fun x => inner ℝ (F x) (G x)) =
      (b ^ 2 / 2) * responsePlanarJ k i +
        cubeAverage U (fun x => inner ℝ (F x) (R.toFun x)) := by
    have he := integral_congr_ae (hotCov_flat_point_covariance Q depth b L plus U hU i k)
    have hi := old_hessian_hilbert_pairing_integrable U F R.toFun hF hR
    change (∫ x, inner ℝ (F x) (G x) ∂normalizedCubeMeasure U) =
      ∫ x, (b ^ 2 / 2) * responsePlanarJ k i + inner ℝ (F x) (R.toFun x)
        ∂normalizedCubeMeasure U at he
    rw [integral_add (integrable_const _) hi] at he
    simpa only [cubeAverage_eq_integral_normalizedCubeMeasure, integral_const, Measure.real_def,
      normalizedCubeMeasure_apply_univ, ENNReal.toReal_one, one_smul] using he
  have hRfun : R.toFun = (oldSignedRemainderKernel Q b L plus (i, k)).toFun := rfl
  rw [hRfun] at havg
  have hN : hotCovMeanCov Q U b L plus k i =
      inner ℝ (hilbertCubeAverage U F) (hilbertCubeAverage U G) :=
    (hotCov_meanCov_kernel Q depth b L plus U hU i k).tsum_eq
  change hotCovMeanCov Q U b L plus k i - (b ^ 2 / 2) * responsePlanarJ k i = _
  rw [hN, hcent, havg]
  ring

end

end ASDExplicitGamma.Main
