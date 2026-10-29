module

public import ASDExplicitGamma.Scalar.Lambda8ParentProjectionFamily
public import ASDExplicitGamma.Gaussian.Q3H3Range
public import ASDExplicitGamma.Gaussian.HilbertKernel
public import ASDExplicitGamma.Gaussian.SupMeanKernelCrossIntegral
public import ASDExplicitGamma.Gaussian.ShellFrameClock

/-! The full parent-projection oscillation trace for the q3 one-load input. -/

@[expose] public section

open MeasureTheory Homogenization
open ASDExplicitGamma.Triadic ASDExplicitGamma.Gaussian ASDExplicitGamma.Response
open ASDExplicitGamma.Model Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3
open scoped RealInnerProductSpace

namespace ASDExplicitGamma.Scalar

noncomputable section

def lambda8Q3FirstIndex (i : Fin 2) : Gaussian.H3Index :=
  Gaussian.h3Next Gaussian.h3Zero i (by norm_num [Gaussian.h3Zero, Gaussian.H3Index])

/-- The directional first-derivative kernel on a parent square. -/
noncomputable def lambda8Q3DirectionalSpatialKernel (Q : TriadicCube 2)
    (β : ℝ) (L : {l : ℝ // 0 < l}) (v : Vec 2) :
    Lp Gaussian.WhiteNoise 2 (volume.restrict (openCubeSet Q)) := by
  letI : IsFiniteMeasure (volume.restrict (openCubeSet Q)) :=
    (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume
  exact v 0 • Gaussian.q3SpatialKernel (openCubeSet Q) β L (lambda8Q3FirstIndex 0) +
    v 1 • Gaussian.q3SpatialKernel (openCubeSet Q) β L (lambda8Q3FirstIndex 1)

/-- The scalar source in one white-noise basis direction. -/
noncomputable def lambda8Q3GaussianModeDerivative
    (β : ℝ) (L : {l : ℝ // 0 < l}) (v : Vec 2)
    (n : Gaussian.whiteBasisIndex) (x : Vec 2) : ℝ :=
  (fderiv ℝ (Gaussian.q3Convolution β L Gaussian.h3Zero
    (Gaussian.whiteBasis n)) x) v

/-- Each component of the Gaussian one-load vector field is genuine H¹ data. -/
noncomputable def lambda8Q3GaussianModeLoadH1 (Q : TriadicCube 2)
    (β : ℝ) (L : {l : ℝ // 0 < l}) (v : Vec 2)
    (n : Gaussian.whiteBasisIndex) (i : Fin 2) :
    H1Function (openCubeSet Q) := by
  let ψ := Gaussian.q3Convolution β L Gaussian.h3Zero (Gaussian.whiteBasis n)
  exact H1Function.ofContDiffOnIsOpenBoundedConvexDomain
    (isOpenBoundedConvexDomain_openCubeSet Q)
    ((Gaussian.q3Convolution_contDiff_one β L Gaussian.h3Zero
      (by norm_num [Gaussian.h3Zero, Gaussian.H3Index])
      (Gaussian.whiteBasis n)).mul
      (contDiff_const : ContDiff ℝ 1 (fun _ : Vec 2 => v i)))

theorem lambda8Q3GaussianModeLoadH1_divergence (Q : TriadicCube 2)
    (β : ℝ) (L : {l : ℝ // 0 < l}) (v : Vec 2)
    (n : Gaussian.whiteBasisIndex) (x : Vec 2) :
    lambda8H1ComponentDivergence
      (fun i => lambda8Q3GaussianModeLoadH1 Q β L v n i) x =
        lambda8Q3GaussianModeDerivative β L v n x := by
  rw [lambda8H1ComponentDivergence]
  let ψ := Gaussian.q3Convolution β L Gaussian.h3Zero (Gaussian.whiteBasis n)
  have hgrad (i : Fin 2) :
      (lambda8Q3GaussianModeLoadH1 Q β L v n i).grad x i =
        v i * (fderiv ℝ ψ x) (basisVec i) := by
    have hd := Gaussian.q3Convolution_hasFDerivAt β L Gaussian.h3Zero
      (by norm_num [Gaussian.h3Zero, Gaussian.H3Index])
      (Gaussian.whiteBasis n) x
    have hmul := hd.mul_const (v i)
    change (fderiv ℝ (fun y => ψ y * v i) x) (basisVec i) = _
    rw [hmul.fderiv, hd.fderiv]
    fin_cases i <;> simp [basisVec_apply, smul_eq_mul]
  rw [Finset.sum_congr rfl (fun i _ => hgrad i)]
  have hv : v = ∑ i : Fin 2, v i • basisVec i := by
    ext i
    simp [basisVec_apply]
  change ∑ i : Fin 2, v i * (fderiv ℝ ψ x) (basisVec i) =
    (fderiv ℝ ψ x) v
  calc
    ∑ i : Fin 2, v i * (fderiv ℝ ψ x) (basisVec i) =
        ∑ i : Fin 2, (fderiv ℝ ψ x) (v i • basisVec i) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [map_smul, smul_eq_mul]
    _ = (fderiv ℝ ψ x) (∑ i : Fin 2, v i • basisVec i) :=
      (map_sum (fderiv ℝ ψ x) _ _).symm
    _ = (fderiv ℝ ψ x) v := by rw [← hv]

private theorem lambda8Q3DirectionalSpatialKernel_norm_sq (Q : TriadicCube 2)
    (β : ℝ) (L : {l : ℝ // 0 < l}) (v : Vec 2) :
    ‖lambda8Q3DirectionalSpatialKernel Q β L v‖ ^ 2 =
      (volume (openCubeSet Q)).toReal *
        (β ^ 2 / L.1 ^ 2 * (78 / 5 : ℝ) * (v 0 ^ 2 + v 1 ^ 2)) := by
  letI : IsFiniteMeasure (volume.restrict (openCubeSet Q)) :=
    (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume
  let μ := volume.restrict (openCubeSet Q)
  let K := lambda8Q3DirectionalSpatialKernel Q β L v
  have hk : ∀ᵐ x ∂μ,
      ‖K x‖ ^ 2 = β ^ 2 / L.1 ^ 2 * (78 / 5 : ℝ) * (v 0 ^ 2 + v 1 ^ 2) := by
    have h0 := (Gaussian.q3Section_memLp (openCubeSet Q) β L
      (lambda8Q3FirstIndex 0)).coeFn_toLp
    have h1 := (Gaussian.q3Section_memLp (openCubeSet Q) β L
      (lambda8Q3FirstIndex 1)).coeFn_toLp
    have hK : K =ᵐ[μ] fun x => v 0 • Gaussian.q3Section β L
          (lambda8Q3FirstIndex 0) x +
        v 1 • Gaussian.q3Section β L
          (lambda8Q3FirstIndex 1) x := by
      let K0 := Gaussian.q3SpatialKernel (openCubeSet Q) β L
        (lambda8Q3FirstIndex 0)
      let K1 := Gaussian.q3SpatialKernel (openCubeSet Q) β L
        (lambda8Q3FirstIndex 1)
      change ⇑(v 0 • K0 + v 1 • K1) =ᵐ[μ] _
      filter_upwards [Lp.coeFn_add (v 0 • K0) (v 1 • K1),
        Lp.coeFn_smul (v 0) K0, Lp.coeFn_smul (v 1) K1, h0, h1]
        with x hadd hs0 hs1 hx0 hx1
      change (v 0 • K0 + v 1 • K1) x = (v 0 • K0) x + (v 1 • K1) x at hadd
      change (v 0 • K0) x = v 0 • K0 x at hs0
      change (v 1 • K1) x = v 1 • K1 x at hs1
      change K0 x = Gaussian.q3Section β L (lambda8Q3FirstIndex 0) x at hx0
      change K1 x = Gaussian.q3Section β L (lambda8Q3FirstIndex 1) x at hx1
      calc
        (v 0 • K0 + v 1 • K1) x = (v 0 • K0) x + (v 1 • K1) x := hadd
        _ = v 0 • Gaussian.q3Section β L (lambda8Q3FirstIndex 0) x +
            v 1 • Gaussian.q3Section β L (lambda8Q3FirstIndex 1) x := by rw [hs0, hs1, hx0, hx1]
    filter_upwards [hK] with x hxK
    rw [hxK]
    have horth := Gaussian.supMean_kernel_cross_orthogonal β L
      (lambda8Q3FirstIndex 0) (lambda8Q3FirstIndex 1) x (by
        norm_num [lambda8Q3FirstIndex, Gaussian.h3Next,
          Gaussian.h3Zero, Gaussian.H3Index])
    have hn0 : ‖Gaussian.q3Section β L (lambda8Q3FirstIndex 0) x‖ ^ 2 =
        β ^ 2 / L.1 ^ 2 * (78 / 5 : ℝ) := by
      rw [Gaussian.gaussQ3Section_norm_sq]
      norm_num [lambda8Q3FirstIndex, Gaussian.h3Next,
        Gaussian.h3Zero, Gaussian.H3Index,
        Gaussian.q3DerivativeMoment]
      field_simp [L.2.ne']
    have hn1 : ‖Gaussian.q3Section β L (lambda8Q3FirstIndex 1) x‖ ^ 2 =
        β ^ 2 / L.1 ^ 2 * (78 / 5 : ℝ) := by
      rw [Gaussian.gaussQ3Section_norm_sq]
      norm_num [lambda8Q3FirstIndex, Gaussian.h3Next,
        Gaussian.h3Zero, Gaussian.H3Index,
        Gaussian.q3DerivativeMoment]
      field_simp [L.2.ne']
    have hcross : inner ℝ
        (v 0 • Gaussian.q3Section β L (lambda8Q3FirstIndex 0) x)
        (v 1 • Gaussian.q3Section β L (lambda8Q3FirstIndex 1) x) = 0 := by
      rw [real_inner_smul_left, real_inner_smul_right, horth]
      ring
    calc
      ‖v 0 • Gaussian.q3Section β L (lambda8Q3FirstIndex 0) x +
          v 1 • Gaussian.q3Section β L (lambda8Q3FirstIndex 1) x‖ ^ 2 =
        inner ℝ (v 0 • Gaussian.q3Section β L (lambda8Q3FirstIndex 0) x +
          v 1 • Gaussian.q3Section β L (lambda8Q3FirstIndex 1) x)
          (v 0 • Gaussian.q3Section β L (lambda8Q3FirstIndex 0) x +
          v 1 • Gaussian.q3Section β L (lambda8Q3FirstIndex 1) x) :=
            (real_inner_self_eq_norm_sq _).symm
      _ = ‖v 0 • Gaussian.q3Section β L (lambda8Q3FirstIndex 0) x‖ ^ 2 +
          ‖v 1 • Gaussian.q3Section β L (lambda8Q3FirstIndex 1) x‖ ^ 2 := by
        have hcross' : inner ℝ
            (v 1 • Gaussian.q3Section β L (lambda8Q3FirstIndex 1) x)
            (v 0 • Gaussian.q3Section β L (lambda8Q3FirstIndex 0) x) = 0 := by
          rw [real_inner_comm]
          exact hcross
        calc
          inner ℝ (v 0 • Gaussian.q3Section β L (lambda8Q3FirstIndex 0) x +
              v 1 • Gaussian.q3Section β L (lambda8Q3FirstIndex 1) x)
              (v 0 • Gaussian.q3Section β L (lambda8Q3FirstIndex 0) x +
              v 1 • Gaussian.q3Section β L (lambda8Q3FirstIndex 1) x) =
            inner ℝ (v 0 • Gaussian.q3Section β L (lambda8Q3FirstIndex 0) x)
                (v 0 • Gaussian.q3Section β L (lambda8Q3FirstIndex 0) x) +
              inner ℝ (v 1 • Gaussian.q3Section β L (lambda8Q3FirstIndex 1) x)
                (v 1 • Gaussian.q3Section β L (lambda8Q3FirstIndex 1) x) := by
                  simp only [inner_add_left, inner_add_right, hcross, hcross']
                  ring
          _ = _ := by rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
      _ = β ^ 2 / L.1 ^ 2 * (78 / 5 : ℝ) * (v 0 ^ 2 + v 1 ^ 2) := by
        have hv0 : ‖v 0 • Gaussian.q3Section β L (lambda8Q3FirstIndex 0) x‖ ^ 2 =
            (v 0) ^ 2 * ‖Gaussian.q3Section β L (lambda8Q3FirstIndex 0) x‖ ^ 2 := by
          rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
        have hv1 : ‖v 1 • Gaussian.q3Section β L (lambda8Q3FirstIndex 1) x‖ ^ 2 =
            (v 1) ^ 2 * ‖Gaussian.q3Section β L (lambda8Q3FirstIndex 1) x‖ ^ 2 := by
          rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
        rw [hv0, hv1, hn0, hn1]
        ring
  calc
    ‖K‖ ^ 2 = ∫ x, ‖K x‖ ^ 2 ∂μ := Gaussian.l2_norm_sq μ K
    _ = ∫ x in openCubeSet Q,
        β ^ 2 / L.1 ^ 2 * (78 / 5 : ℝ) * (v 0 ^ 2 + v 1 ^ 2) := by
      apply integral_congr_ae
      exact hk
    _ = _ := by
      rw [integral_const, Measure.real, Measure.restrict_apply_univ, smul_eq_mul]

/-- Parseval gives the exact parent-square energy trace of the q3 directional
derivative family, in the volume-normalized convention used by `energy`. -/
theorem lambda8Q3GaussianModeDerivative_energy_tsum (Q : TriadicCube 2)
    (β : ℝ) (L : {l : ℝ // 0 < l}) (v : Vec 2) :
    Summable (fun n : Gaussian.whiteBasisIndex =>
        energy Q (lambda8Q3GaussianModeDerivative β L v n)) ∧
      (∑' n : Gaussian.whiteBasisIndex,
        energy Q (lambda8Q3GaussianModeDerivative β L v n)) =
        β ^ 2 / L.1 ^ 2 * (78 / 5 : ℝ) * (v 0 ^ 2 + v 1 ^ 2) := by
  letI : IsFiniteMeasure (volume.restrict (openCubeSet Q)) :=
    (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume
  let μ := volume.restrict (openCubeSet Q)
  let K := lambda8Q3DirectionalSpatialKernel Q β L v
  let T := Gaussian.hilbertKernel μ K
  have hmode (n : Gaussian.whiteBasisIndex) :
      T (Gaussian.whiteBasis n) =ᵐ[μ]
        lambda8Q3GaussianModeDerivative β L v n := by
    have hT := Gaussian.hilbertKernel_ae μ K (Gaussian.whiteBasis n)
    have hK : K =ᵐ[μ] fun x => v 0 • Gaussian.q3Section β L
          (lambda8Q3FirstIndex 0) x +
        v 1 • Gaussian.q3Section β L (lambda8Q3FirstIndex 1) x := by
      have h0 := (Gaussian.q3Section_memLp (openCubeSet Q) β L
        (lambda8Q3FirstIndex 0)).coeFn_toLp
      have h1 := (Gaussian.q3Section_memLp (openCubeSet Q) β L
        (lambda8Q3FirstIndex 1)).coeFn_toLp
      let K0 := Gaussian.q3SpatialKernel (openCubeSet Q) β L
        (lambda8Q3FirstIndex 0)
      let K1 := Gaussian.q3SpatialKernel (openCubeSet Q) β L
        (lambda8Q3FirstIndex 1)
      change ⇑(v 0 • K0 + v 1 • K1) =ᵐ[μ] _
      filter_upwards [Lp.coeFn_add (v 0 • K0) (v 1 • K1),
        Lp.coeFn_smul (v 0) K0, Lp.coeFn_smul (v 1) K1, h0, h1]
        with x hadd hs0 hs1 hx0 hx1
      change (v 0 • K0 + v 1 • K1) x = (v 0 • K0) x + (v 1 • K1) x at hadd
      change (v 0 • K0) x = v 0 • K0 x at hs0
      change (v 1 • K1) x = v 1 • K1 x at hs1
      change K0 x = Gaussian.q3Section β L (lambda8Q3FirstIndex 0) x at hx0
      change K1 x = Gaussian.q3Section β L (lambda8Q3FirstIndex 1) x at hx1
      calc
        (v 0 • K0 + v 1 • K1) x = (v 0 • K0) x + (v 1 • K1) x := hadd
        _ = v 0 • Gaussian.q3Section β L (lambda8Q3FirstIndex 0) x +
            v 1 • Gaussian.q3Section β L (lambda8Q3FirstIndex 1) x := by
          rw [hs0, hs1, hx0, hx1]
    have hderiv (x : Vec 2) :
        lambda8Q3GaussianModeDerivative β L v n x =
          v 0 * Gaussian.q3Convolution β L (lambda8Q3FirstIndex 0)
              (Gaussian.whiteBasis n) x +
            v 1 * Gaussian.q3Convolution β L (lambda8Q3FirstIndex 1)
              (Gaussian.whiteBasis n) x := by
      let ψ := Gaussian.q3Convolution β L Gaussian.h3Zero
        (Gaussian.whiteBasis n)
      have hd := Gaussian.q3Convolution_hasFDerivAt β L Gaussian.h3Zero
        (by norm_num [Gaussian.h3Zero, Gaussian.H3Index])
        (Gaussian.whiteBasis n) x
      rw [lambda8Q3GaussianModeDerivative, hd.fderiv]
      simp [lambda8Q3FirstIndex, Gaussian.h3Next, Gaussian.h3Zero,
        ContinuousLinearMap.proj_apply, smul_eq_mul]
      ring_nf
    filter_upwards [hT, hK] with x hxT hxK
    rw [hxT, hxK]
    calc
      ⟪Gaussian.whiteBasis n,
          v 0 • Gaussian.q3Section β L (lambda8Q3FirstIndex 0) x +
            v 1 • Gaussian.q3Section β L (lambda8Q3FirstIndex 1) x⟫ =
        v 0 * ⟪Gaussian.whiteBasis n,
            Gaussian.q3Section β L (lambda8Q3FirstIndex 0) x⟫ +
          v 1 * ⟪Gaussian.whiteBasis n,
            Gaussian.q3Section β L (lambda8Q3FirstIndex 1) x⟫ := by
          rw [inner_add_right, real_inner_smul_right, real_inner_smul_right]
      _ = lambda8Q3GaussianModeDerivative β L v n x := by
          simpa only [Gaussian.q3Convolution] using (hderiv x).symm
  have hnorm (n : Gaussian.whiteBasisIndex) :
      ‖T (Gaussian.whiteBasis n)‖ ^ 2 =
        ∫ x in openCubeSet Q,
          (lambda8Q3GaussianModeDerivative β L v n x) ^ 2 ∂volume := by
    rw [Gaussian.l2_norm_sq]
    apply integral_congr_ae
    filter_upwards [hmode n] with x hx
    rw [hx, Real.norm_eq_abs, sq_abs]
  have henergy (n : Gaussian.whiteBasisIndex) :
      energy Q (lambda8Q3GaussianModeDerivative β L v n) =
        (cubeVolume Q)⁻¹ * ‖T (Gaussian.whiteBasis n)‖ ^ 2 := by
    rw [energy_eq_integral_sq, integral_normalized_eq_open, hnorm n]
  have hsT : Summable (fun n : Gaussian.whiteBasisIndex =>
      ‖T (Gaussian.whiteBasis n)‖ ^ 2) :=
    Gaussian.hilbertKernel_summable μ K Gaussian.whiteBasis
      Gaussian.whiteBasis.orthonormal
  have hsE : Summable (fun n : Gaussian.whiteBasisIndex =>
      energy Q (lambda8Q3GaussianModeDerivative β L v n)) := by
    convert hsT.mul_left (cubeVolume Q)⁻¹ using 1
    ext n
    exact henergy n
  refine ⟨hsE, ?_⟩
  calc
    (∑' n : Gaussian.whiteBasisIndex,
        energy Q (lambda8Q3GaussianModeDerivative β L v n)) =
      (cubeVolume Q)⁻¹ * ∑' n : Gaussian.whiteBasisIndex,
        ‖T (Gaussian.whiteBasis n)‖ ^ 2 := by
          rw [show (fun n : Gaussian.whiteBasisIndex =>
            energy Q (lambda8Q3GaussianModeDerivative β L v n)) =
            fun n => (cubeVolume Q)⁻¹ * ‖T (Gaussian.whiteBasis n)‖ ^ 2 by
              funext n
              exact henergy n,
            ← tsum_mul_left]
    _ = (cubeVolume Q)⁻¹ * ‖K‖ ^ 2 := by
      rw [Gaussian.hilbertKernel_basis_tsum_eq μ K Gaussian.whiteBasis]
    _ = β ^ 2 / L.1 ^ 2 * (78 / 5 : ℝ) * (v 0 ^ 2 + v 1 ^ 2) := by
      rw [lambda8Q3DirectionalSpatialKernel_norm_sq]
      rw [volume_openCubeSet_toReal]
      field_simp [ne_of_gt (cubeVolume_pos Q)]

/-- The actual parent-square potential of one q3 basis load. -/
noncomputable def lambda8Q3GaussianModeParentPotential (Q : TriadicCube 2)
    (β : ℝ) (L : {l : ℝ // 0 < l}) (v : Vec 2)
    (n : Gaussian.whiteBasisIndex) : H10Function (openCubeSet Q) :=
  Classical.choose (lambda8DirichletProjection_hessian_source Q
    (fun i => lambda8Q3GaussianModeLoadH1 Q β L v n i))

/-- The H² witness attached to the actual parent-square potential. -/
noncomputable def lambda8Q3GaussianModeParentHessian (Q : TriadicCube 2)
    (β : ℝ) (L : {l : ℝ // 0 < l}) (v : Vec 2)
    (n : Gaussian.whiteBasisIndex) :
    HasWeakHessianOn (openCubeSet Q)
      (lambda8Q3GaussianModeParentPotential Q β L v n).toH1Function :=
  Classical.choose (Classical.choose_spec
    (lambda8DirichletProjection_hessian_source Q
      (fun i => lambda8Q3GaussianModeLoadH1 Q β L v n i)))

/-- The parent potential is the actual local Dirichlet projection and its
weak Laplacian is the q3 directional derivative source. -/
theorem lambda8Q3GaussianModeParentPotential_spec (Q : TriadicCube 2)
    (β : ℝ) (L : {l : ℝ // 0 < l}) (v : Vec 2)
    (n : Gaussian.whiteBasisIndex) :
    lambda8DirichletProjection (isOpenBoundedConvexDomain_openCubeSet Q)
      (toHilbertVectorL2OfVecField
        (lambda8H1ComponentField_memVectorL2
          (fun i => lambda8Q3GaussianModeLoadH1 Q β L v n i))) =
        (lambda8Q3GaussianModeParentPotential Q β L v n).toH1Function.gradToHilbertVectorL2 ∧
      dirichletWeakLaplacian (lambda8Q3GaussianModeParentHessian Q β L v n) =ᵐ[
        normalizedCubeMeasure Q] lambda8Q3GaussianModeDerivative β L v n := by
  have h := Classical.choose_spec (Classical.choose_spec
    (lambda8DirichletProjection_hessian_source Q
      (fun i => lambda8Q3GaussianModeLoadH1 Q β L v n i)))
  refine ⟨h.1, ?_⟩
  exact h.2.1.trans (Filter.Eventually.of_forall
    (lambda8Q3GaussianModeLoadH1_divergence Q β L v n))

/-- Summing the actual parent-projection oscillations over the q3 white-noise
basis costs exactly the deterministic parent Hessian trace. Each mode is
projected on the parent square before its descendant oscillations are taken. -/
theorem lambda8Q3GaussianMode_parentProjection_descendant_trace
    (Q : TriadicCube 2) (depth : ℕ) (β : ℝ)
    (L : {l : ℝ // 0 < l}) (v : Vec 2) :
    Summable (fun n : Gaussian.whiteBasisIndex =>
      descendantsAverage Q depth (fun R =>
        hilbertPositiveCircHaarNorm R ((3 : ℝ) ^ (2 * (1 / 4 : ℝ)))
          (fun x => HilbertVec.ofVec
            ((lambda8Q3GaussianModeParentPotential Q β L v n).toH1Function.grad x)) ^ 2)) ∧
      (∑' n : Gaussian.whiteBasisIndex,
        descendantsAverage Q depth (fun R =>
          hilbertPositiveCircHaarNorm R ((3 : ℝ) ^ (2 * (1 / 4 : ℝ)))
            (fun x => HilbertVec.ofVec
              ((lambda8Q3GaussianModeParentPotential Q β L v n).toH1Function.grad x)) ^ 2)) ≤
        (cubeScaleFactor Q ^ 2 / (9 : ℝ) ^ depth * planarC0 ^ 2) *
          (β ^ 2 / L.1 ^ 2 * (78 / 5 : ℝ) * (v 0 ^ 2 + v 1 ^ 2)) := by
  classical
  let u : Gaussian.whiteBasisIndex → H10Function (openCubeSet Q) :=
    fun n => lambda8Q3GaussianModeParentPotential Q β L v n
  let H : ∀ n, HasWeakHessianOn (openCubeSet Q) (u n).toH1Function :=
    fun n => lambda8Q3GaussianModeParentHessian Q β L v n
  have hdiv (n : Gaussian.whiteBasisIndex) :
      dirichletWeakLaplacian (H n) =ᵐ[normalizedCubeMeasure Q]
        lambda8Q3GaussianModeDerivative β L v n := by
    exact (lambda8Q3GaussianModeParentPotential_spec Q β L v n).2
  have htrace := lambda8Q3GaussianModeDerivative_energy_tsum Q β L v
  have hfamily := lambda8_parentProjection_family_oscillation_sq_le
    Q depth (fun n => lambda8Q3GaussianModeDerivative β L v n) u H hdiv htrace.1
  refine ⟨?_, ?_⟩
  · simpa only [u] using hfamily.1
  · calc
      (∑' n : Gaussian.whiteBasisIndex,
          descendantsAverage Q depth (fun R =>
            hilbertPositiveCircHaarNorm R ((3 : ℝ) ^ (2 * (1 / 4 : ℝ)))
              (fun x => HilbertVec.ofVec
                ((lambda8Q3GaussianModeParentPotential Q β L v n).toH1Function.grad x)) ^ 2)) ≤
          (cubeScaleFactor Q ^ 2 / (9 : ℝ) ^ depth * planarC0 ^ 2) *
            ∑' n : Gaussian.whiteBasisIndex,
              energy Q (lambda8Q3GaussianModeDerivative β L v n) := hfamily.2
      _ = (cubeScaleFactor Q ^ 2 / (9 : ℝ) ^ depth * planarC0 ^ 2) *
            (β ^ 2 / L.1 ^ 2 * (78 / 5 : ℝ) * (v 0 ^ 2 + v 1 ^ 2)) := by
            rw [htrace.2]

private theorem lambda8Q3_parentScaleRatio (k : ℤ) :
    cubeScaleFactor (originCube 2 (k + 128)) /
        (3 : ℝ) ^ k / (3 : ℝ) ^ (134 : ℤ) = lambda8Rho := by
  rw [cubeScaleFactor_originCube]
  have h3 : (3 : ℝ) ≠ 0 := by norm_num
  rw [← zpow_sub₀ h3 (k + 128) k,
    ← zpow_sub₀ h3 ((k + 128) - k) 134]
  unfold lambda8Rho
  congr 1
  omega

private theorem lambda8Q3_parentScaleRatio_sq (k : ℤ) :
    cubeScaleFactor (originCube 2 (k + 128)) ^ 2 / (9 : ℝ) ^ 134 /
      ((3 : ℝ) ^ k) ^ 2 = lambda8Rho ^ 2 := by
  have h9 : (9 : ℝ) ^ 134 = ((3 : ℝ) ^ (134 : ℤ)) ^ (2 : ℤ) := by
    calc
      (9 : ℝ) ^ 134 = (9 : ℝ) ^ (134 : ℤ) := by simp
      _ = ((3 : ℝ) ^ (2 : ℤ)) ^ (134 : ℤ) := by
        rw [show (9 : ℝ) = (3 : ℝ) ^ (2 : ℤ) by norm_num]
      _ = ((3 : ℝ) ^ (134 : ℤ)) ^ (2 : ℤ) := by
        rw [← zpow_mul, ← zpow_mul]
        congr 1
  rw [h9]
  have hfactor :
      cubeScaleFactor (originCube 2 (k + 128)) ^ 2 / ((3 : ℝ) ^ (134 : ℤ)) ^ 2 /
        ((3 : ℝ) ^ k) ^ 2 =
      (cubeScaleFactor (originCube 2 (k + 128)) /
        (3 : ℝ) ^ k / (3 : ℝ) ^ (134 : ℤ)) ^ 2 := by
    field_simp [zpow_ne_zero k (by norm_num : (3 : ℝ) ≠ 0)]
  calc
    _ = (cubeScaleFactor (originCube 2 (k + 128)) /
        (3 : ℝ) ^ k / (3 : ℝ) ^ (134 : ℤ)) ^ 2 := hfactor
    _ = lambda8Rho ^ 2 := by rw [lambda8Q3_parentScaleRatio k]

/-- One-load scale for the all-basis parent-projection
oscillation. The parent is 128 levels above the shell, and the 134 descendant
levels leave exactly the source ratio rho = 3^-6. -/
noncomputable def lambda8Q3ParentModePotential (M : ABKModel 2) (h : ℝ)
    (e : Vec 2) (k : ℤ) (n : Gaussian.whiteBasisIndex) :
    H10Function (openCubeSet (originCube 2 (k + 128))) :=
  lambda8Q3GaussianModeParentPotential (originCube 2 (k + 128))
    (Gaussian.q3ModelAmplitude M h k) (Gaussian.q3ModelLength k)
    (-(matVecMul responsePlanarJ e)) n

/-- The descendant-averaged positive quarter-order oscillation of one q3
white-noise direction, using its actual large-parent Dirichlet projection. -/
noncomputable def lambda8Q3ParentModeOscillation (M : ABKModel 2) (h : ℝ)
    (e : Vec 2) (k : ℤ) (n : Gaussian.whiteBasisIndex) : ℝ :=
  descendantsAverage (originCube 2 (k + 128)) 134 (fun R =>
    hilbertPositiveCircHaarNorm R ((3 : ℝ) ^ (2 * (1 / 4 : ℝ)))
      (fun x => HilbertVec.ofVec
        ((lambda8Q3ParentModePotential M h e k n).toH1Function.grad x)) ^ 2)

/-- The total one-load Lambda8 oscillation trace is bounded with the stated
outward coefficient and physical shell variance. The basis sum is over the
actual q3 covariance directions. -/
theorem lambda8Q3_one_load_delta_sq_le
    (M : ABKModel 2) (h : ℝ)
    (e : Vec 2) (he : Book.Ch02.vecNorm e = 1) (k : ℤ) :
    Summable (fun n : Gaussian.whiteBasisIndex =>
      lambda8Q3ParentModeOscillation M h e k n) ∧
    (∑' n : Gaussian.whiteBasisIndex,
      lambda8Q3ParentModeOscillation M h e k n) ≤
      lambda8DeltaN ^ 2 * (h ^ 2 * (3 : ℝ) ^ (2 * M.gamma * (k : ℝ))) := by
  let Q := originCube 2 (k + 128)
  let β := Gaussian.q3ModelAmplitude M h k
  let L := Gaussian.q3ModelLength k
  let v := -(matVecMul responsePlanarJ e)
  have htrace := lambda8Q3GaussianMode_parentProjection_descendant_trace
    Q 134 β L v
  have hv : v 0 ^ 2 + v 1 ^ 2 = 1 := by
    have hsq : vecNormSq v = 1 := by
      have hJ : vecNormSq (matVecMul responsePlanarJ e) = 1 := by
        rw [responsePlanarJ_vecNormSq,
          ← Book.Ch02.vecNorm_sq_eq_vecNormSq, he]
        norm_num
      simpa [v, vecNormSq, vecDot, Fin.sum_univ_two] using hJ
    simpa [vecNormSq, vecDot, Fin.sum_univ_two, pow_two] using hsq
  have hc0 : planarC0 ^ 2 ≤ (467 / 1000 : ℝ) ^ 2 := by
    have h := planarC0_decimal_bounds.2
    have hnn : 0 ≤ planarC0 := Real.sqrt_nonneg _
    have hout : planarC0 < (467 / 1000 : ℝ) := by
      norm_num at h ⊢
      linarith
    exact (sq_le_sq₀ hnn (by norm_num)).2 hout.le
  have hbeta : β ^ 2 = h ^ 2 * (3 : ℝ) ^ (2 * M.gamma * (k : ℝ)) := by
    exact Gaussian.q3ModelAmplitude_sq M h k
  have hlength : L.1 = (3 : ℝ) ^ k := by rfl
  have hscale := lambda8Q3_parentScaleRatio_sq k
  refine ⟨?_, ?_⟩
  · simpa only [lambda8Q3ParentModeOscillation, lambda8Q3ParentModePotential,
      Q, β, L, v] using htrace.1
  · have htrace' :
        (∑' n : Gaussian.whiteBasisIndex,
          lambda8Q3ParentModeOscillation M h e k n) ≤
          (cubeScaleFactor Q ^ 2 / (9 : ℝ) ^ 134 * planarC0 ^ 2) *
            (β ^ 2 / L.1 ^ 2 * (78 / 5 : ℝ)) := by
      have := htrace.2
      rw [hv] at this
      have hraw :
          (∑' n : Gaussian.whiteBasisIndex,
            lambda8Q3ParentModeOscillation M h e k n) ≤
            (cubeScaleFactor Q ^ 2 / (9 : ℝ) ^ 134 * planarC0 ^ 2) *
              (β ^ 2 / L.1 ^ 2 * (78 / 5 : ℝ) * 1) := by
        simpa only [lambda8Q3ParentModeOscillation,
          lambda8Q3ParentModePotential, Q, β, L, v] using this
      calc
        _ ≤ (cubeScaleFactor Q ^ 2 / (9 : ℝ) ^ 134 * planarC0 ^ 2) *
              (β ^ 2 / L.1 ^ 2 * (78 / 5 : ℝ) * 1) := hraw
        _ = _ := by ring
    calc
      (∑' n : Gaussian.whiteBasisIndex,
          lambda8Q3ParentModeOscillation M h e k n) ≤
          (cubeScaleFactor Q ^ 2 / (9 : ℝ) ^ 134 * planarC0 ^ 2) *
            (β ^ 2 / L.1 ^ 2 * (78 / 5 : ℝ)) := htrace'
      _ ≤ (cubeScaleFactor Q ^ 2 / (9 : ℝ) ^ 134 *
            (467 / 1000 : ℝ) ^ 2) *
            (β ^ 2 / L.1 ^ 2 * (78 / 5 : ℝ)) := by
        have hA : 0 ≤ cubeScaleFactor Q ^ 2 / (9 : ℝ) ^ 134 := by positivity
        have hB : 0 ≤ β ^ 2 / L.1 ^ 2 * (78 / 5 : ℝ) := by positivity
        calc
          _ = ((cubeScaleFactor Q ^ 2 / (9 : ℝ) ^ 134) * planarC0 ^ 2) *
                (β ^ 2 / L.1 ^ 2 * (78 / 5 : ℝ)) := by ring
          _ ≤ ((cubeScaleFactor Q ^ 2 / (9 : ℝ) ^ 134) *
                (467 / 1000 : ℝ) ^ 2) *
                (β ^ 2 / L.1 ^ 2 * (78 / 5 : ℝ)) := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hc0 hA) hB
          _ = _ := by ring
      _ = lambda8DeltaN ^ 2 * (h ^ 2 * (3 : ℝ) ^ (2 * M.gamma * (k : ℝ))) := by
        rw [show cubeScaleFactor Q = cubeScaleFactor (originCube 2 (k + 128)) by rfl,
          hlength, hbeta]
        have hscale' : cubeScaleFactor Q ^ 2 / (9 : ℝ) ^ 134 /
            ((3 : ℝ) ^ k) ^ 2 = lambda8Rho ^ 2 := by
          simpa only [Q] using hscale
        calc
          (cubeScaleFactor Q ^ 2 / (9 : ℝ) ^ 134 * (467 / 1000 : ℝ) ^ 2) *
              (h ^ 2 * (3 : ℝ) ^ (2 * M.gamma * (k : ℝ)) /
                ((3 : ℝ) ^ k) ^ 2 * (78 / 5 : ℝ)) =
              (467 / 1000 : ℝ) ^ 2 * lambda8Rho ^ 2 * (78 / 5 : ℝ) *
                (h ^ 2 * (3 : ℝ) ^ (2 * M.gamma * (k : ℝ))) := by
                calc
                  _ = (467 / 1000 : ℝ) ^ 2 *
                      ((cubeScaleFactor Q ^ 2 / (9 : ℝ) ^ 134) /
                        ((3 : ℝ) ^ k) ^ 2) * (78 / 5 : ℝ) *
                        (h ^ 2 * (3 : ℝ) ^ (2 * M.gamma * (k : ℝ))) := by ring
                  _ = _ := by rw [hscale']
          _ = lambda8DeltaN ^ 2 *
                (h ^ 2 * (3 : ℝ) ^ (2 * M.gamma * (k : ℝ))) := by
                rw [lambda8DeltaN_sq]

end
end ASDExplicitGamma.Scalar
