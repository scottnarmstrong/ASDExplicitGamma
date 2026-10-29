module

public import ASDExplicitGamma.Scalar.FlatSourceQ3FiniteGradient
public import ASDExplicitGamma.Response.FrameAlgebra

/-! The finite q3 source product has a common-noise spatial-gradient trace. -/

@[expose] public section

open MeasureTheory Homogenization
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Triadic
open Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3
open scoped ENNReal Topology RealInnerProductSpace

namespace ASDExplicitGamma.Scalar

local instance flatSourceQ3GradientTraceFiniteMeasure (Q : TriadicCube 2) :
    IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
  (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume

private theorem enumerated_memLp
    {ι : Type*} [Countable ι] {F : ι → Vec 2 → ℝ}
    (μ : Measure (Vec 2)) (n : ℕ)
    (hF : ∀ q, MemLp (F q) 2 μ) :
    MemLp (gaussEnumerated F n) 2 μ := by
  classical
  let := Encodable.ofCountable ι
  by_cases hn : n ∈ Set.range (Encodable.encode : ι → ℕ)
  · obtain ⟨q, rfl⟩ := hn
    rw [enumerated_encode]
    exact hF q
  · rw [gaussEnumerated, Function.extend_apply' _ _ _ hn]
    exact MemLp.zero

/-- The finite parent-projection load modes inherit the sharp physical half-variance
trace from the actual source shell law. -/
theorem flat_source_q3_finite_projected_load_energy_le
    (Q : TriadicCube 2) {a₀ b₀ c₀ d₀ : ℝ}
    (hab : a₀ < b₀) (hcd : c₀ < d₀)
    (hQ : openCubeSet Q ⊆ openRectangle a₀ b₀ c₀ d₀)
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (e : Vec 2) (he : Book.Ch02.vecNorm e = 1) (k : ℤ) (N : ℕ) :
    let β := q3ModelAmplitude M h k
    let L := q3ModelLength k
    (∑ i : Fin 2, ∑ n ∈ Finset.range N,
      ∫ x, (flatSourceQ3FiniteProjectedMode Q β L e i n x) ^ 2
        ∂volumeMeasureOn (openCubeSet Q)) ≤
      (volume (openCubeSet Q)).toReal *
        (h ^ 2 * (3 : ℝ) ^ (2 * M.gamma * (k : ℝ)) / 2) := by
  classical
  let β := q3ModelAmplitude M h k
  let L := q3ModelLength k
  let dirs := q3H3Directions a₀ b₀ c₀ d₀ β L whiteBasis
  let R : Q3H3Range a₀ b₀ c₀ d₀ β L →L[ℝ]
      HilbertVectorL2 (openCubeSet Q) :=
    (lambda8Q3ProjectedLoadClass
      (isOpenBoundedConvexDomain_openCubeSet Q)
      a₀ b₀ c₀ d₀ hab hcd e).comp
      (q3H3RangeValue a₀ b₀ c₀ d₀ β L)
  let b : Fin 2 → ℕ → Vec 2 → ℝ := fun i n x =>
    flatSourceQ3FiniteProjectedMode Q β L e i n x
  have hmode (n : ℕ) :
      (∑ i : Fin 2, ∫ x in openCubeSet Q, (b i n x) ^ 2 ∂volume) =
        ‖R (dirs n)‖ ^ 2 := by
    letI := Encodable.ofCountable whiteBasisIndex
    by_cases hn : n ∈ Set.range (Encodable.encode : whiteBasisIndex → ℕ)
    · obtain ⟨j, rfl⟩ := hn
      let W := lambda8Q3GaussianModeParentPotential Q β L
        (matVecMul ASDExplicitGamma.Response.responsePlanarJ e) j
      have hproj :
          R (dirs (Encodable.encode j)) = W.toH1Function.gradToHilbertVectorL2 := by
        dsimp [R, dirs, W, q3H3Directions]
        rw [enumerated_encode,
          flat_source_q3_projected_mode_eq_parent_gradient
            Q hab hcd hQ β L e j]
      have hbmode (i : Fin 2) :
          b i (Encodable.encode j) = fun x => W.toH1Function.grad x i := by
        funext x
        simp [b, W, flatSourceQ3FiniteProjectedMode, enumerated_encode]
      have hgradmem : MemVectorL2 (openCubeSet Q) W.toH1Function.grad :=
        W.toH1Function.grad_memVectorL2
      have hgradmem' (i : Fin 2) :
          MemLp (fun x => W.toH1Function.grad x i) 2
            (volume.restrict (openCubeSet Q)) := by
        change MemLp W.toH1Function.grad 2
          (volume.restrict (openCubeSet Q)) at hgradmem
        exact (memLp_pi_iff.mp hgradmem) i
      have hnorm :
          ‖W.toH1Function.gradToHilbertVectorL2‖ ^ 2 =
            ∑ i : Fin 2, ∫ x in openCubeSet Q,
              (W.toH1Function.grad x i) ^ 2 ∂volume := by
        calc
          _ = inner ℝ W.toH1Function.gradToHilbertVectorL2
              W.toH1Function.gradToHilbertVectorL2 :=
            (real_inner_self_eq_norm_sq _).symm
          _ = ∫ x in openCubeSet Q,
                vecDot (W.toH1Function.grad x) (W.toH1Function.grad x) ∂volume := by
            simpa only [H1Function.gradToHilbertVectorL2] using
              (inner_toHilbertVectorL2OfVecField_eq_integral
                (U := openCubeSet Q) hgradmem hgradmem)
          _ = ∑ i : Fin 2, ∫ x in openCubeSet Q,
                (W.toH1Function.grad x i) ^ 2 ∂volume := by
            have hInt (i : Fin 2) : Integrable
                (fun x => (W.toH1Function.grad x i) ^ 2)
                (volume.restrict (openCubeSet Q)) :=
              (hgradmem' i).integrable_sq
            calc
              _ = ∫ x in openCubeSet Q, ∑ i : Fin 2,
                    (W.toH1Function.grad x i) ^ 2 ∂volume := by
                apply integral_congr_ae
                filter_upwards [] with x
                simp [vecDot, pow_two]
              _ = _ := by
                rw [integral_finsetSum Finset.univ (fun i hi => hInt i)]
      calc
        _ = ∑ i : Fin 2, ∫ x in openCubeSet Q,
              (W.toH1Function.grad x i) ^ 2 ∂volume := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [hbmode i]
        _ = ‖W.toH1Function.gradToHilbertVectorL2‖ ^ 2 := hnorm.symm
        _ = _ := by rw [← hproj]
    · have hdir : dirs n = 0 := by
        dsimp [dirs, q3H3Directions]
        exact Function.extend_apply' _ _ _ hn
      have hbzero (i : Fin 2) : b i n = 0 := by
        funext x
        dsimp [b, flatSourceQ3FiniteProjectedMode]
        rw [gaussEnumerated, Function.extend_apply' _ _ _ hn]
        rfl
      simp [hbzero, hdir, R]
  have hdirs : Summable (fun n : ℕ => ‖R (dirs n)‖ ^ 2) :=
    @summable_sq_bounded_image ℕ
      (Q3H3Range a₀ b₀ c₀ d₀ β L)
      (HilbertVectorL2 (openCubeSet Q)) inferInstance
      (instQ3H3RangeInnerProductSpace a₀ b₀ c₀ d₀ β L).toNormedSpace
      inferInstance inferInstance dirs
      (q3H3Directions_summable a₀ b₀ c₀ d₀ β L whiteBasis) R
  have hvol : 0 < (volume (openCubeSet Q)).toReal := by
    rw [volume_openCubeSet_eq_volume_cubeSet, volume_cubeSet_toReal]
    exact cubeVolume_pos Q
  have htrace := lambda8Q3ProjectedLoad_modes_energy_le
    (hU := isOpenBoundedConvexDomain_openCubeSet Q) (ne_of_gt hvol)
    hQ hab hcd e M h hM he k
  have hpartial :
      (∑ n ∈ Finset.range N, ‖R (dirs n)‖ ^ 2) ≤
        (volume (openCubeSet Q)).toReal *
          (h ^ 2 * (3 : ℝ) ^ (2 * M.gamma * (k : ℝ)) / 2) := by
    calc
      _ ≤ ∑' n, ‖R (dirs n)‖ ^ 2 :=
        hdirs.sum_le_tsum (Finset.range N) (fun n hn => sq_nonneg _)
      _ ≤ _ := htrace
  calc
    _ = ∑ n ∈ Finset.range N, ‖R (dirs n)‖ ^ 2 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro n hn
      simpa [b, volumeMeasureOn] using hmode n
    _ ≤ _ := hpartial

private theorem lambda8_q3_parent_hessian_open_energy_eq
    (Q : TriadicCube 2) (β : ℝ) (L : {l : ℝ // 0 < l})
    (v : Vec 2) (n : Gaussian.whiteBasisIndex) :
    (∑ i : Fin 2, ∑ j : Fin 2,
      ∫ x in openCubeSet Q,
        ((lambda8Q3GaussianModeParentHessian Q β L v n).hess i j x) ^ 2
          ∂volume) =
      cubeVolume Q *
        (lambda8Q3GaussianModeParentHessian Q β L v n).frobeniusNormalizedL2 Q ^ 2 := by
  classical
  let H := lambda8Q3GaussianModeParentHessian Q β L v n
  have hsum :
      (∑ i : Fin 2, ∑ j : Fin 2,
        energy Q (fun x => H.hess i j x)) = H.frobeniusNormalizedL2 Q ^ 2 := by
    calc
      _ = (cubeVolume Q)⁻¹ *
          ∑ i : Fin 2, ∑ j : Fin 2, ‖H.hessCoordToScalarL2 i j‖ ^ 2 := by
        simp_rw [energy_eq_integral_sq, H.integral_hess_sq_normalizedCubeMeasure Q]
        simp only [Finset.mul_sum]
      _ = H.frobeniusNormalizedL2 Q ^ 2 :=
        (H.frobeniusNormalizedL2_sq Q).symm
  have hopen (i j : Fin 2) :
      ∫ x in openCubeSet Q, (H.hess i j x) ^ 2 ∂volume =
        cubeVolume Q * energy Q (fun x => H.hess i j x) := by
    have henergy := energy_eq_integral_sq Q (fun x => H.hess i j x)
    rw [integral_normalized_eq_open] at henergy
    calc
      _ = cubeVolume Q * ((cubeVolume Q)⁻¹ *
            ∫ x in openCubeSet Q, (H.hess i j x) ^ 2 ∂volume) := by
          field_simp [ne_of_gt (cubeVolume_pos Q)]
      _ = cubeVolume Q * energy Q (fun x => H.hess i j x) := by
          rw [← henergy]
  calc
    _ = cubeVolume Q *
        (∑ i : Fin 2, ∑ j : Fin 2, energy Q (fun x => H.hess i j x)) := by
      calc
        _ = ∑ i : Fin 2, ∑ j : Fin 2,
              cubeVolume Q * energy Q (fun x => H.hess i j x) := by
          apply Finset.sum_congr rfl
          intro i hi
          apply Finset.sum_congr rfl
          intro j hj
          exact hopen i j
        _ = ∑ i : Fin 2,
              cubeVolume Q * (∑ j : Fin 2, energy Q (fun x => H.hess i j x)) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [Finset.mul_sum]
        _ = _ := by rw [Finset.mul_sum]
    _ = _ := by rw [hsum]

/-- The finite Hessian modes have the exact projected q3 derivative trace. -/
theorem flat_source_q3_finite_projected_hessian_energy_le
    (Q : TriadicCube 2) (β : ℝ) (L : {l : ℝ // 0 < l})
    (e : Vec 2) (he : Book.Ch02.vecNorm e = 1) (N : ℕ) :
    (∑ i : Fin 2, ∑ j : Fin 2, ∑ n ∈ Finset.range N,
      ∫ x, (flatSourceQ3FiniteProjectedGradientMode Q β L e i j n x) ^ 2
        ∂volumeMeasureOn (openCubeSet Q)) ≤
      (volume (openCubeSet Q)).toReal * (β ^ 2 / L.1 ^ 2 * (78 / 5 : ℝ)) := by
  classical
  let v := matVecMul ASDExplicitGamma.Response.responsePlanarJ e
  let f : Gaussian.whiteBasisIndex → ℝ := fun n =>
    (lambda8Q3GaussianModeParentHessian Q β L v n).frobeniusNormalizedL2 Q
  have hfEnergy (n : Gaussian.whiteBasisIndex) :
      f n ^ 2 = energy Q (lambda8Q3GaussianModeDerivative β L v n) := by
    dsimp [f]
    let u := lambda8Q3GaussianModeParentPotential Q β L v n
    let K := lambda8Q3GaussianModeParentHessian Q β L v n
    have hdiv := (lambda8Q3GaussianModeParentPotential_spec Q β L v n).2
    have hmemLap : MemLp (dirichletWeakLaplacian K) 2 (normalizedCubeMeasure Q) :=
      memLp_dirichlet_weak_laplacian K
    have hmemDeriv : MemLp (lambda8Q3GaussianModeDerivative β L v n) 2
        (normalizedCubeMeasure Q) := (memLp_congr_ae hdiv).mp hmemLap
    have hnorm : cubeLpNorm Q 2 (dirichletWeakLaplacian K) =
        cubeLpNorm Q 2 (lambda8Q3GaussianModeDerivative β L v n) := by
      unfold cubeLpNorm
      exact congrArg ENNReal.toReal (eLpNorm_congr_ae hdiv)
    calc
      _ = cubeLpNorm Q 2 (dirichletWeakLaplacian K) ^ 2 := by
        rw [dirichlet_square_hessian_identity Q u K]
      _ = cubeLpNorm Q 2 (lambda8Q3GaussianModeDerivative β L v n) ^ 2 := by
        rw [hnorm]
      _ = _ := (energy_eq_cubeLpNorm_sq Q hmemDeriv).symm
  have hfSummable : Summable (fun n : Gaussian.whiteBasisIndex => ‖f n‖ ^ 2) := by
    have henergy :=
      (lambda8Q3GaussianModeDerivative_energy_tsum Q β L v).1
    apply henergy.congr
    intro n
    simpa [f, Real.norm_eq_abs, sq_abs] using (hfEnergy n).symm
  have henumSummable : Summable (fun n : ℕ => (gaussEnumerated f n) ^ 2) := by
    simpa [Real.norm_eq_abs, sq_abs] using enumerated_summable_sq f hfSummable
  have hmode (n : ℕ) :
      (∑ i : Fin 2, ∑ j : Fin 2,
        ∫ x in openCubeSet Q,
          (flatSourceQ3FiniteProjectedGradientMode Q β L e i j n x) ^ 2
            ∂volume) = cubeVolume Q * (gaussEnumerated f n) ^ 2 := by
    letI := Encodable.ofCountable Gaussian.whiteBasisIndex
    by_cases hn : n ∈ Set.range (Encodable.encode : Gaussian.whiteBasisIndex → ℕ)
    · obtain ⟨q, rfl⟩ := hn
      have hcoord (i j : Fin 2) :
          flatSourceQ3FiniteProjectedGradientMode Q β L e i j
              (Encodable.encode q) = fun x =>
                (lambda8Q3GaussianModeParentHessian Q β L v q).hess i j x := by
        funext x
        simp [flatSourceQ3FiniteProjectedGradientMode, v, enumerated_encode]
      calc
        _ = ∑ i : Fin 2, ∑ j : Fin 2,
            ∫ x in openCubeSet Q,
              ((lambda8Q3GaussianModeParentHessian Q β L v q).hess i j x) ^ 2
                ∂volume := by
          apply Finset.sum_congr rfl
          intro i hi
          apply Finset.sum_congr rfl
          intro j hj
          rw [hcoord i j]
        _ = cubeVolume Q *
              (lambda8Q3GaussianModeParentHessian Q β L v q).frobeniusNormalizedL2 Q ^ 2 :=
          lambda8_q3_parent_hessian_open_energy_eq Q β L v q
        _ = cubeVolume Q * (gaussEnumerated f (Encodable.encode q)) ^ 2 := by
          simp [f, enumerated_encode]
    · have hzero (i j : Fin 2) :
          flatSourceQ3FiniteProjectedGradientMode Q β L e i j n = 0 := by
        funext x
        change (gaussEnumerated (fun q : Gaussian.whiteBasisIndex => fun y : Vec 2 =>
          (lambda8Q3GaussianModeParentHessian Q β L v q).hess i j y) n) x = 0
        rw [gaussEnumerated, Function.extend_apply' _ _ _ hn]
        rfl
      have henumerated : gaussEnumerated f n = 0 := by
        dsimp [gaussEnumerated]
        exact Function.extend_apply' _ _ _ hn
      simp [hzero, henumerated]
  have hJ : vecNormSq v = 1 := by
    change vecNormSq (matVecMul ASDExplicitGamma.Response.responsePlanarJ e) = 1
    rw [ASDExplicitGamma.Response.responsePlanarJ_vecNormSq,
      ← Book.Ch02.vecNorm_sq_eq_vecNormSq, he]
    norm_num
  have hJcoord : v 0 ^ 2 + v 1 ^ 2 = 1 := by
    simpa [vecNormSq, vecDot, Fin.sum_univ_two, pow_two] using hJ
  have htrace := lambda8Q3GaussianModeParent_hessian_energy_trace Q β L v
  have htrace' : (∑' n : Gaussian.whiteBasisIndex, f n ^ 2) =
      β ^ 2 / L.1 ^ 2 * (78 / 5 : ℝ) := by
    simpa [f, hJcoord] using htrace
  have hpartial :
      (∑ n ∈ Finset.range N, cubeVolume Q * (gaussEnumerated f n) ^ 2) ≤
        cubeVolume Q * (β ^ 2 / L.1 ^ 2 * (78 / 5 : ℝ)) := by
    calc
      _ = cubeVolume Q * ∑ n ∈ Finset.range N, (gaussEnumerated f n) ^ 2 := by
        rw [Finset.mul_sum]
      _ ≤ cubeVolume Q * ∑' n, (gaussEnumerated f n) ^ 2 := by
        exact mul_le_mul_of_nonneg_left
          (henumSummable.sum_le_tsum (Finset.range N) (fun n hn => sq_nonneg _))
          (cubeVolume_nonneg Q)
      _ = cubeVolume Q * ∑' n : Gaussian.whiteBasisIndex, f n ^ 2 := by
        congr 1
        exact enumerated_tsum_apply f (fun x : ℝ => x ^ 2) (by simp)
      _ = cubeVolume Q * (β ^ 2 / L.1 ^ 2 * (78 / 5 : ℝ)) := by
        rw [htrace']
  have hvol : (volume (openCubeSet Q)).toReal = cubeVolume Q := by
    rw [volume_openCubeSet_toReal]
  calc
    _ = ∑ n ∈ Finset.range N,
        (∑ i : Fin 2, ∑ j : Fin 2,
          ∫ x in openCubeSet Q,
            (flatSourceQ3FiniteProjectedGradientMode Q β L e i j n x) ^ 2
              ∂volume) := by
      calc
        _ = ∑ i : Fin 2, ∑ n ∈ Finset.range N, ∑ j : Fin 2,
              ∫ x in openCubeSet Q,
                (flatSourceQ3FiniteProjectedGradientMode Q β L e i j n x) ^ 2
                  ∂volume := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [Finset.sum_comm]
        _ = _ := by rw [Finset.sum_comm]
    _ = ∑ n ∈ Finset.range N, cubeVolume Q * (gaussEnumerated f n) ^ 2 := by
      apply Finset.sum_congr rfl
      intro n hn
      exact hmode n
    _ ≤ _ := by simpa [hvol] using hpartial

/-- The finite product's actual weak-gradient trace is bounded using the
pointwise Parseval caps for the scalar value and its two derivatives. The
remaining finite load and Hessian mode energies are explicit on the right;
the producer traces bound them independently. -/
theorem flat_source_q3_finite_product_gradient_trace_bound
    (Q : TriadicCube 2) {a₀ b₀ c₀ d₀ : ℝ}
    (hab : a₀ < b₀) (hcd : c₀ < d₀)
    (hQ : openCubeSet Q ⊆ openRectangle a₀ b₀ c₀ d₀)
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (e : Vec 2) (he : Book.Ch02.vecNorm e = 1) (k : ℤ) (N : ℕ) :
    let β := q3ModelAmplitude M h k
    let L := q3ModelLength k
    Integrable (fun ω => ∫ x,
      ∑ i : Fin 2, ∑ j : Fin 2,
        (flatSourceQ3FiniteProductComponent Q β L e N ω i).grad x j ^ 2
      ∂volumeMeasureOn (openCubeSet Q)) standardGaussianInfinitePi ∧
    (∫ ω, ∫ x,
      ∑ i : Fin 2, ∑ j : Fin 2,
        (flatSourceQ3FiniteProductComponent Q β L e N ω i).grad x j ^ 2
      ∂volumeMeasureOn (openCubeSet Q) ∂standardGaussianInfinitePi) ≤
      (volume (openCubeSet Q)).toReal *
        ((936 / 5 : ℝ) * β ^ 4 / L.1 ^ 2) := by
  classical
  let β := q3ModelAmplitude M h k
  let L := q3ModelLength k
  let μ := volumeMeasureOn (openCubeSet Q)
  let A : ℝ := β ^ 2
  let AD : ℝ := β ^ 2 / L.1 ^ 2 * (156 / 5 : ℝ)
  let e' := matVecMul ASDExplicitGamma.Response.responsePlanarJ e
  let a : ℕ → Vec 2 → ℝ := fun n x =>
    flatSourceQ3FiniteClampedValueMode β L hab hcd n x
  let da : Fin 2 → ℕ → Vec 2 → ℝ := fun i n x =>
    flatSourceQ3FiniteClampedDerivativeMode β L hab hcd i n x
  let b : Fin 2 → ℕ → Vec 2 → ℝ := fun i n x =>
    flatSourceQ3FiniteProjectedMode Q β L e i n x
  let db : Fin 2 → Fin 2 → ℕ → Vec 2 → ℝ := fun i j n x =>
    flatSourceQ3FiniteProjectedGradientMode Q β L e i j n x
  have hclamp : Continuous (lambda8CovarianceClamp a₀ b₀ c₀ d₀ hab hcd) :=
    flat_source_clamp_continuous a₀ b₀ c₀ d₀ hab hcd
  have hclampReal : Continuous (fun x =>
      (lambda8CovarianceClamp a₀ b₀ c₀ d₀ hab hcd x).1) :=
    continuous_subtype_val.comp hclamp
  have hzero : h3Zero.1.1.val + h3Zero.1.2.val ≤ 2 := by
    norm_num [h3Zero, H3Index]
  have hnext (i : Fin 2) :
      (flatSourceQ3DerivativeIndex i).1.1.val +
        (flatSourceQ3DerivativeIndex i).1.2.val ≤ 2 := by
    fin_cases i <;>
      norm_num [flatSourceQ3DerivativeIndex, h3Next,
        h3Zero, H3Index]
  have haMeas (n : ℕ) : Measurable (a n) := by
    dsimp [a, flatSourceQ3FiniteClampedValueMode]
    exact ((q3Convolution_contDiff_one β L h3Zero hzero
      (gaussEnumerated whiteBasis n)).continuous.comp hclampReal).measurable
  have hdaMeas (i : Fin 2) (n : ℕ) : Measurable (da i n) := by
    dsimp [da, flatSourceQ3FiniteClampedDerivativeMode]
    exact ((q3Convolution_contDiff_one β L
      (flatSourceQ3DerivativeIndex i) (hnext i)
      (gaussEnumerated whiteBasis n)).continuous.comp hclampReal).measurable
  have hcap (x : Vec 2) :=
    flat_source_q3_clamped_finite_variance_caps (β := β) hab hcd L N x
  have ha (x : Vec 2) :
      ∑ n ∈ Finset.range N, (a n x) ^ 2 ≤ A := by
    simpa [a, A] using (hcap x).1
  have hda (x : Vec 2) :
      ∑ i : Fin 2, ∑ n ∈ Finset.range N, (da i n x) ^ 2 ≤ AD := by
    simpa [da, AD] using (hcap x).2
  have hb (i : Fin 2) (n : ℕ) : MemLp (b i n) 2 μ := by
    dsimp [b, flatSourceQ3FiniteProjectedMode]
    apply enumerated_memLp μ n
    intro q
    change MemLp (fun x =>
      (lambda8Q3GaussianModeParentPotential Q β L e' q).toH1Function.grad x i)
      2 μ
    exact (lambda8Q3GaussianModeParentPotential Q β L e' q).toH1Function.grad_memL2 i
  have hdb (i j : Fin 2) (n : ℕ) : MemLp (db i j n) 2 μ := by
    dsimp [db, flatSourceQ3FiniteProjectedGradientMode]
    apply enumerated_memLp μ n
    intro q
    change MemLp (fun x =>
      (lambda8Q3GaussianModeParentHessian Q β L e' q).hess i j x) 2 μ
    exact (lambda8Q3GaussianModeParentHessian Q β L e' q).hess_memL2 i j
  have hwick := flat_source_finite_mode_spatial_gradient_bound
    μ N a da b db A AD haMeas hdaMeas ha hda hb hdb
  have hvalue_eq (x : Vec 2) (hx : x ∈ openCubeSet Q) (n : ℕ) :
      a n x = flatSourceQ3FiniteValueMode β L n x := by
    dsimp [a, flatSourceQ3FiniteClampedValueMode,
      flatSourceQ3FiniteValueMode]
    rw [lambda8CovarianceClamp_eq_of_mem a₀ b₀ c₀ d₀ hab hcd (hQ hx)]
  have hderiv_eq (x : Vec 2) (hx : x ∈ openCubeSet Q)
      (i : Fin 2) (n : ℕ) :
      da i n x = flatSourceQ3FiniteValueDerivativeMode β L i n x := by
    dsimp [da, flatSourceQ3FiniteClampedDerivativeMode,
      flatSourceQ3FiniteValueDerivativeMode]
    rw [lambda8CovarianceClamp_eq_of_mem a₀ b₀ c₀ d₀ hab hcd (hQ hx)]
    rw [q3Convolution_fderiv_basis β L h3Zero hzero
      (gaussEnumerated whiteBasis n) x i]
    rfl
  have hformula (ω : ℕ → ℝ) (x : Vec 2) (hx : x ∈ openCubeSet Q)
      (i j : Fin 2) :
      (flatSourceQ3FiniteProductComponent Q β L e N ω i).grad x j =
        gaussianScalarPartialSum (fun n => da j n x) N ω *
            gaussianScalarPartialSum (fun n => b i n x) N ω +
          gaussianScalarPartialSum (fun n => a n x) N ω *
            gaussianScalarPartialSum (fun n => db i j n x) N ω := by
    rw [flat_source_q3_finite_product_gradient_formula]
    unfold b db flatSourceQ3FiniteProjectedMode
      flatSourceQ3FiniteProjectedGradientMode
    have hvalue :
        gaussianScalarPartialSum (fun n => a n x) N ω =
          gaussianScalarPartialSum
            (fun n => flatSourceQ3FiniteValueMode β L n x) N ω := by
      unfold gaussianScalarPartialSum
      apply Finset.sum_congr rfl
      intro n hn
      exact congrArg (fun z : ℝ => ω n * z) (hvalue_eq x hx n)
    have hderiv :
        gaussianScalarPartialSum (fun n => da j n x) N ω =
          gaussianScalarPartialSum
            (fun n => flatSourceQ3FiniteValueDerivativeMode β L j n x) N ω := by
      unfold gaussianScalarPartialSum
      apply Finset.sum_congr rfl
      intro n hn
      exact congrArg (fun z : ℝ => ω n * z) (hderiv_eq x hx j n)
    rw [hvalue, hderiv]
    ring
  have hintegrand (ω : ℕ → ℝ) :
      (∫ x, ∑ i : Fin 2, ∑ j : Fin 2,
          (flatSourceQ3FiniteProductComponent Q β L e N ω i).grad x j ^ 2 ∂μ) =
        ∫ x, ∑ i : Fin 2, ∑ j : Fin 2,
          (gaussianScalarPartialSum (fun n => da j n x) N ω *
              gaussianScalarPartialSum (fun n => b i n x) N ω +
            gaussianScalarPartialSum (fun n => a n x) N ω *
              gaussianScalarPartialSum (fun n => db i j n x) N ω) ^ 2 ∂μ := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem (measurableSet_openCubeSet Q)] with x hx
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    exact congrArg (fun z : ℝ => z ^ 2) (hformula ω x hx i j)
  have hβsq : β ^ 2 = h ^ 2 * (3 : ℝ) ^ (2 * M.gamma * (k : ℝ)) := by
    dsimp [β]
    exact q3ModelAmplitude_sq M h k
  have hload := flat_source_q3_finite_projected_load_energy_le
    Q hab hcd hQ M h hM e he k N
  have hload' :
      (∑ i : Fin 2, ∑ n ∈ Finset.range N,
        ∫ x, (flatSourceQ3FiniteProjectedMode Q β L e i n x) ^ 2
          ∂volumeMeasureOn (openCubeSet Q)) ≤
        (volume (openCubeSet Q)).toReal * (β ^ 2 / 2) := by
    rw [hβsq]
    exact hload
  have hHessian := flat_source_q3_finite_projected_hessian_energy_le
    Q β L e he N
  have hgradCap :
      (∫ ω, ∫ x, ∑ i : Fin 2, ∑ j : Fin 2,
        (flatSourceQ3FiniteProductComponent Q β L e N ω i).grad x j ^ 2
        ∂μ ∂standardGaussianInfinitePi) ≤
      (volume (openCubeSet Q)).toReal *
        ((936 / 5 : ℝ) * β ^ 4 / L.1 ^ 2) := by
    calc
      _ = ∫ ω, ∫ x, ∑ i : Fin 2, ∑ j : Fin 2,
            (gaussianScalarPartialSum (fun n => da j n x) N ω *
                gaussianScalarPartialSum (fun n => b i n x) N ω +
              gaussianScalarPartialSum (fun n => a n x) N ω *
                gaussianScalarPartialSum (fun n => db i j n x) N ω) ^ 2 ∂μ
            ∂standardGaussianInfinitePi := by
        apply integral_congr_ae
        filter_upwards [] with ω
        exact hintegrand ω
      _ ≤ 6 * AD *
            (∑ i : Fin 2, ∑ n ∈ Finset.range N,
              ∫ x, (b i n x) ^ 2 ∂μ) +
          6 * A *
            (∑ i : Fin 2, ∑ j : Fin 2, ∑ n ∈ Finset.range N,
              ∫ x, (db i j n x) ^ 2 ∂μ) := hwick.2
      _ ≤ 6 * AD * ((volume (openCubeSet Q)).toReal * (β ^ 2 / 2)) +
          6 * A * ((volume (openCubeSet Q)).toReal *
            (β ^ 2 / L.1 ^ 2 * (78 / 5 : ℝ))) := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_left hload' (by positivity)
        · exact mul_le_mul_of_nonneg_left hHessian (by positivity)
      _ = (volume (openCubeSet Q)).toReal *
            ((936 / 5 : ℝ) * β ^ 4 / L.1 ^ 2) := by
        dsimp [AD, A]
        ring
  refine ⟨?_, ?_⟩
  · have hInt := hwick.1
    apply hInt.congr
    exact ae_of_all _ fun ω => (hintegrand ω).symm
  · exact hgradCap

end ASDExplicitGamma.Scalar
