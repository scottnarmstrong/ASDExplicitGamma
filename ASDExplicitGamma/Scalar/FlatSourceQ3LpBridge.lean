module

public import ASDExplicitGamma.Scalar.FlatSourceQ3SeriesProduct

/-! Source-specific finite-cutoff representatives in the physical spatial Lp spaces. -/

@[expose] public section

open MeasureTheory Filter Homogenization
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Triadic
open Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3
open scoped ENNReal Topology

namespace ASDExplicitGamma.Scalar

local instance flatSourceLpBridgeOpenCubeFiniteMeasure (Q : TriadicCube 2) :
    IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
  (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume

theorem flat_source_q3_value_partial_sum_ae
    (Q : TriadicCube 2) {a₀ b₀ c₀ d₀ : ℝ}
    (hab : a₀ < b₀) (hcd : c₀ < d₀)
    (N : ℕ) (ω : ℕ → ℝ) (β : ℝ) (L : {l : ℝ // 0 < l}) :
    flatSourceQ3ValueLInf Q hab hcd β L
        (gaussianPartialSum
          (q3H3Directions a₀ b₀ c₀ d₀ β L whiteBasis) N ω) =ᵐ[
        volumeMeasureOn (openCubeSet Q)]
      (fun x => gaussianScalarPartialSum
          (fun n => q3H3RangeValue a₀ b₀ c₀ d₀ β L
            (q3H3Directions a₀ b₀ c₀ d₀ β L whiteBasis n)
            (lambda8CovarianceClamp a₀ b₀ c₀ d₀ hab hcd x)) N ω) := by
  classical
  let μ := volumeMeasureOn (openCubeSet Q)
  let dirs := q3H3Directions a₀ b₀ c₀ d₀ β L whiteBasis
  let a : ℕ → Vec 2 → ℝ := fun n x =>
    q3H3RangeValue a₀ b₀ c₀ d₀ β L (dirs n)
      (lambda8CovarianceClamp a₀ b₀ c₀ d₀ hab hcd x)
  have hdecomp : flatSourceQ3ValueLInf Q hab hcd β L
      (gaussianPartialSum dirs N ω) =
        ∑ n ∈ Finset.range N, ω n •
          flatSourceQ3ValueLInf Q hab hcd β L (dirs n) := by
    simp [gaussianPartialSum, dirs, map_sum]
  have hmode (n : ℕ) :
      flatSourceQ3ValueLInf Q hab hcd β L (dirs n) =ᵐ[μ] fun x => a n x := by
    let clamp : C(Vec 2, closedRectangle a₀ b₀ c₀ d₀) :=
      ⟨lambda8CovarianceClamp a₀ b₀ c₀ d₀ hab hcd,
        flat_source_clamp_continuous a₀ b₀ c₀ d₀ hab hcd⟩
    let h3ToBounded : C(closedRectangle a₀ b₀ c₀ d₀, ℝ) →L[ℝ]
        BoundedContinuousFunction (closedRectangle a₀ b₀ c₀ d₀) ℝ :=
      (ContinuousMap.linearIsometryBoundedOfCompact
        (closedRectangle a₀ b₀ c₀ d₀) ℝ ℝ).toContinuousLinearEquiv.toContinuousLinearMap
    have hbcf :
        (BoundedContinuousFunction.compContinuousCLM ℝ ℝ clamp)
            (h3ToBounded (q3H3RangeValue a₀ b₀ c₀ d₀ β L (dirs n))) =ᵐ[μ]
          fun x => a n x := by
      filter_upwards [BoundedContinuousFunction.coeFn_toLp
        (∞ : ℝ≥0∞) μ ℝ
        ((BoundedContinuousFunction.compContinuousCLM ℝ ℝ clamp)
          (h3ToBounded (q3H3RangeValue a₀ b₀ c₀ d₀ β L (dirs n))))] with x hx
      simp [a, clamp, h3ToBounded,
        BoundedContinuousFunction.compContinuousCLM_apply]
    change BoundedContinuousFunction.toLp (∞ : ℝ≥0∞) μ ℝ
        ((BoundedContinuousFunction.compContinuousCLM ℝ ℝ clamp).comp
          (h3ToBounded.comp (q3H3RangeValue a₀ b₀ c₀ d₀ β L)) (dirs n)) =ᵐ[μ]
      fun x => a n x
    exact (BoundedContinuousFunction.coeFn_toLp (∞ : ℝ≥0∞) μ ℝ _).trans hbcf
  have hterms (n : ℕ) :
      (ω n • flatSourceQ3ValueLInf Q hab hcd β L (dirs n)) =ᵐ[μ]
        fun x => ω n * a n x := by
    filter_upwards [Lp.coeFn_smul (ω n)
        (flatSourceQ3ValueLInf Q hab hcd β L (dirs n)), hmode n] with x hs hm
    calc
      (ω n • flatSourceQ3ValueLInf Q hab hcd β L (dirs n)) x =
          ω n • (flatSourceQ3ValueLInf Q hab hcd β L (dirs n)) x := by
        simpa only [Pi.smul_apply] using hs
      _ = ω n * a n x := by rw [hm, smul_eq_mul]
  rw [hdecomp]
  have hsum := Lp.coeFn_fun_finsetSum (Finset.range N)
    (fun n => ω n • flatSourceQ3ValueLInf Q hab hcd β L (dirs n))
  filter_upwards [hsum, ae_all_iff.mpr fun n => hterms n] with x hsum hx
  rw [hsum]
  simp only [gaussianScalarPartialSum]
  apply Finset.sum_congr rfl
  intro n hn
  exact hx n

/-- A projected q3 direction has the parent-gradient component used in the
source Wick cap, with the same zero-padding convention. -/
theorem flat_source_q3_projected_direction_component_eq_parent_mode_ae
    (Q : TriadicCube 2) {a₀ b₀ c₀ d₀ : ℝ}
    (hab : a₀ < b₀) (hcd : c₀ < d₀)
    (hQ : openCubeSet Q ⊆ openRectangle a₀ b₀ c₀ d₀)
    (e : Vec 2) (β : ℝ) (L : {l : ℝ // 0 < l}) (n : ℕ) (i : Fin 2) :
    (fun x => (flatSourceQ3ProjectedL2 Q hab hcd e β L
      (q3H3Directions a₀ b₀ c₀ d₀ β L whiteBasis n) x).toVec i) =ᵐ[
        volumeMeasureOn (openCubeSet Q)]
      (fun x => gaussEnumerated (fun j : whiteBasisIndex => fun y : Vec 2 =>
        (lambda8Q3GaussianModeParentPotential Q β L
          (matVecMul ASDExplicitGamma.Response.responsePlanarJ e) j).toH1Function.grad y i)
        n x) := by
  classical
  let := Encodable.ofCountable whiteBasisIndex
  let dirs := q3H3Directions a₀ b₀ c₀ d₀ β L whiteBasis
  by_cases hn : n ∈ Set.range (Encodable.encode : whiteBasisIndex → ℕ)
  · obtain ⟨j, rfl⟩ := hn
    let W := lambda8Q3GaussianModeParentPotential Q β L
      (matVecMul ASDExplicitGamma.Response.responsePlanarJ e) j
    have hproj : flatSourceQ3ProjectedL2 Q hab hcd e β L
        (dirs (Encodable.encode j)) = W.toH1Function.gradToHilbertVectorL2 := by
      dsimp [flatSourceQ3ProjectedL2, dirs, q3H3Directions]
      rw [enumerated_encode]
      exact flat_source_q3_projected_mode_eq_parent_gradient
        Q hab hcd hQ β L e j
    filter_upwards [W.toH1Function.coeFn_gradToHilbertVectorL2] with x hx
    rw [hproj, hx]
    simp [W, enumerated_encode, hilbertifyVecField]
  · have hdir : dirs n = 0 := by
      dsimp [dirs, q3H3Directions, gaussEnumerated]
      exact Function.extend_apply' _ _ _ hn
    have hzero : flatSourceQ3ProjectedL2 Q hab hcd e β L (dirs n) = 0 := by
      rw [hdir]
      simp [flatSourceQ3ProjectedL2]
    have hb : gaussEnumerated (fun j : whiteBasisIndex => fun y : Vec 2 =>
        (lambda8Q3GaussianModeParentPotential Q β L
          (matVecMul ASDExplicitGamma.Response.responsePlanarJ e) j).toH1Function.grad y i)
        n = 0 := by
      dsimp [gaussEnumerated]
      exact Function.extend_apply' _ _ _ hn
    have hzeroAE : (fun x => flatSourceQ3ProjectedL2 Q hab hcd e β L
        (dirs n) x) =ᵐ[volumeMeasureOn (openCubeSet Q)] 0 := by
      rw [hzero]
      filter_upwards [Lp.coeFn_zero (E := HilbertVec 2) 2
        (volumeMeasureOn (openCubeSet Q))] with x hx
      exact hx
    filter_upwards [hzeroAE] with x hx
    rw [hx, hb]
    simp [HilbertVec.toVec]

/-- Each component of the actual projected finite q3 load is represented by
the same finite Gaussian sum of the projected source modes. -/
theorem flat_source_q3_projected_partial_sum_component_ae
    (Q : TriadicCube 2) {a₀ b₀ c₀ d₀ : ℝ}
    (hab : a₀ < b₀) (hcd : c₀ < d₀) (e : Vec 2)
    (N : ℕ) (ω : ℕ → ℝ) (β : ℝ) (L : {l : ℝ // 0 < l}) (i : Fin 2) :
    (fun x => (flatSourceQ3ProjectedL2 Q hab hcd e β L
        (gaussianPartialSum
          (q3H3Directions a₀ b₀ c₀ d₀ β L whiteBasis) N ω) x).toVec i) =ᵐ[
        volumeMeasureOn (openCubeSet Q)]
      (fun x => gaussianScalarPartialSum
        (fun n => (flatSourceQ3ProjectedL2 Q hab hcd e β L
          (q3H3Directions a₀ b₀ c₀ d₀ β L whiteBasis n) x).toVec i) N ω) := by
  classical
  let μ := volumeMeasureOn (openCubeSet Q)
  let dirs := q3H3Directions a₀ b₀ c₀ d₀ β L whiteBasis
  have hdecomp : flatSourceQ3ProjectedL2 Q hab hcd e β L
      (gaussianPartialSum dirs N ω) =
        ∑ n ∈ Finset.range N, ω n •
          flatSourceQ3ProjectedL2 Q hab hcd e β L (dirs n) := by
    simp [gaussianPartialSum, dirs, map_sum]
  have hsum := Lp.coeFn_fun_finsetSum (Finset.range N)
    (fun n => ω n • flatSourceQ3ProjectedL2 Q hab hcd e β L (dirs n))
  have hterms (n : ℕ) :
      (ω n • flatSourceQ3ProjectedL2 Q hab hcd e β L (dirs n)) =ᵐ[μ]
        fun x => ω n • flatSourceQ3ProjectedL2 Q hab hcd e β L (dirs n) x := by
    filter_upwards [Lp.coeFn_smul (ω n)
      (flatSourceQ3ProjectedL2 Q hab hcd e β L (dirs n))] with x hx
    simpa only [Pi.smul_apply] using hx
  filter_upwards [hsum, ae_all_iff.mpr fun n => hterms n] with x hsum hterms
  have hsum' :
      (∑ n ∈ Finset.range N,
        (ω n • flatSourceQ3ProjectedL2 Q hab hcd e β L (dirs n)) x) =
      ∑ n ∈ Finset.range N,
        ω n • flatSourceQ3ProjectedL2 Q hab hcd e β L (dirs n) x := by
    apply Finset.sum_congr rfl
    intro n hn
    exact hterms n
  calc
    (flatSourceQ3ProjectedL2 Q hab hcd e β L
      (gaussianPartialSum dirs N ω) x).toVec i =
        ((∑ n ∈ Finset.range N,
          ω n • flatSourceQ3ProjectedL2 Q hab hcd e β L (dirs n)) x).toVec i := by
            rw [hdecomp]
    _ =
        (∑ n ∈ Finset.range N,
          (ω n • flatSourceQ3ProjectedL2 Q hab hcd e β L (dirs n)) x).toVec i := by
            rw [hsum]
    _ = ∑ n ∈ Finset.range N,
          ω n * (flatSourceQ3ProjectedL2 Q hab hcd e β L (dirs n) x).toVec i := by
      rw [hsum']
      simp [HilbertVec.toVec, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    _ = gaussianScalarPartialSum
          (fun n => (flatSourceQ3ProjectedL2 Q hab hcd e β L (dirs n) x).toVec i)
          N ω := by
      simp [gaussianScalarPartialSum]

/-- The finite q3 scalar-times-projected-load product has exactly the spatial
Wick integrand of its actual source modes. -/
theorem flat_source_q3_finite_product_norm_sq_eq_wick_integral
    (Q : TriadicCube 2) {a₀ b₀ c₀ d₀ : ℝ}
    (hab : a₀ < b₀) (hcd : c₀ < d₀) (e : Vec 2)
    (N : ℕ) (ω : ℕ → ℝ) (β : ℝ) (L : {l : ℝ // 0 < l}) :
    let μ := volumeMeasureOn (openCubeSet Q)
    let dirs := q3H3Directions a₀ b₀ c₀ d₀ β L whiteBasis
    ‖flatSourceQ3ValueLInf Q hab hcd β L
        (gaussianPartialSum dirs N ω) •
      flatSourceQ3ProjectedL2 Q hab hcd e β L
        (gaussianPartialSum dirs N ω)‖ ^ 2 =
      ∫ x,
        (gaussianScalarPartialSum
          (fun n => q3H3RangeValue a₀ b₀ c₀ d₀ β L (dirs n)
            (lambda8CovarianceClamp a₀ b₀ c₀ d₀ hab hcd x)) N ω) ^ 2 *
        ∑ i : Fin 2,
          (gaussianScalarPartialSum
            (fun n => (flatSourceQ3ProjectedL2 Q hab hcd e β L
              (dirs n) x).toVec i) N ω) ^ 2 ∂μ := by
  classical
  let μ := volumeMeasureOn (openCubeSet Q)
  let dirs := q3H3Directions a₀ b₀ c₀ d₀ β L whiteBasis
  change ‖flatSourceQ3ValueLInf Q hab hcd β L
      (gaussianPartialSum dirs N ω) •
    flatSourceQ3ProjectedL2 Q hab hcd e β L
      (gaussianPartialSum dirs N ω)‖ ^ 2 = _
  rw [lp_smul_norm_sq_eq_integral]
  apply integral_congr_ae
  have hscalar := flat_source_q3_value_partial_sum_ae
    Q hab hcd N ω β L
  have hvector : ∀ᵐ x ∂μ, ∀ i : Fin 2,
      (flatSourceQ3ProjectedL2 Q hab hcd e β L
        (gaussianPartialSum dirs N ω) x).toVec i =
      gaussianScalarPartialSum
        (fun n => (flatSourceQ3ProjectedL2 Q hab hcd e β L
          (dirs n) x).toVec i) N ω := by
    rw [ae_all_iff]
    intro i
    exact flat_source_q3_projected_partial_sum_component_ae
      Q hab hcd e N ω β L i
  filter_upwards [hscalar, hvector] with x hscalar hvector
  rw [hscalar, HilbertVec.norm_sq_eq_sum_sq]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  simpa only [HilbertVec.toVec] using
    congrArg (fun y : ℝ => y ^ 2) (hvector i)

/-- The expected squared spatial L² norm of a finite actual q3 product obeys
the sharp parent-mode Wick cap. The proof first identifies the physical
projected modes with the parent-gradient family, then swaps the spatial and
Gaussian integrals using joint integrability. -/
theorem flat_source_q3_finite_product_expected_norm_sq_le
    (Q : TriadicCube 2) {a₀ b₀ c₀ d₀ : ℝ}
    (hab : a₀ < b₀) (hcd : c₀ < d₀)
    (hQ : openCubeSet Q ⊆ openRectangle a₀ b₀ c₀ d₀)
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (e : Vec 2) (he : Book.Ch02.vecNorm e = 1) (k : ℤ) (N : ℕ) :
    let β := q3ModelAmplitude M h k
    let L := q3ModelLength k
    Integrable (fun ω =>
      ‖flatSourceQ3ValueLInf Q hab hcd β L
          (gaussianPartialSum
            (q3H3Directions a₀ b₀ c₀ d₀ β L whiteBasis) N ω) •
        flatSourceQ3ProjectedL2 Q hab hcd e β L
          (gaussianPartialSum
            (q3H3Directions a₀ b₀ c₀ d₀ β L whiteBasis) N ω)‖ ^ 2)
      standardGaussianInfinitePi ∧
    (∫ ω,
      ‖flatSourceQ3ValueLInf Q hab hcd β L
          (gaussianPartialSum
            (q3H3Directions a₀ b₀ c₀ d₀ β L whiteBasis) N ω) •
        flatSourceQ3ProjectedL2 Q hab hcd e β L
          (gaussianPartialSum
            (q3H3Directions a₀ b₀ c₀ d₀ β L whiteBasis) N ω)‖ ^ 2
      ∂standardGaussianInfinitePi ≤
      (3 / 2 : ℝ) * (volume (openCubeSet Q)).toReal *
        (h ^ 2 * (3 : ℝ) ^ (2 * M.gamma * (k : ℝ))) ^ 2) := by
  classical
  let μ := volumeMeasureOn (openCubeSet Q)
  let β := q3ModelAmplitude M h k
  let L := q3ModelLength k
  let dirs := q3H3Directions a₀ b₀ c₀ d₀ β L whiteBasis
  let a : ℕ → Vec 2 → ℝ := fun n x =>
    q3H3RangeValue a₀ b₀ c₀ d₀ β L (dirs n)
      (lambda8CovarianceClamp a₀ b₀ c₀ d₀ hab hcd x)
  let b : Fin 2 → ℕ → Vec 2 → ℝ := fun i n x =>
    gaussEnumerated (fun j : whiteBasisIndex => fun y : Vec 2 =>
      (lambda8Q3GaussianModeParentPotential Q β L
        (matVecMul ASDExplicitGamma.Response.responsePlanarJ e) j).toH1Function.grad y i)
      n x
  have hcap := flat_source_q3_finite_mode_parent_product_cap
    Q hab hcd hQ M h hM e he k N
  have hmode (i : Fin 2) (n : ℕ) :
      (fun x => (flatSourceQ3ProjectedL2 Q hab hcd e β L
        (dirs n) x).toVec i) =ᵐ[μ] (fun x => b i n x) := by
    simpa [b, β, L, dirs] using
      flat_source_q3_projected_direction_component_eq_parent_mode_ae
        Q hab hcd hQ e β L n i
  have hmodeAll (i : Fin 2) : ∀ᵐ x ∂μ, ∀ n,
      (flatSourceQ3ProjectedL2 Q hab hcd e β L (dirs n) x).toVec i =
        b i n x := by
    rw [ae_all_iff]
    intro n
    exact hmode i n
  have hspatial (ω : ℕ → ℝ) :
      ‖flatSourceQ3ValueLInf Q hab hcd β L (gaussianPartialSum dirs N ω) •
        flatSourceQ3ProjectedL2 Q hab hcd e β L
          (gaussianPartialSum dirs N ω)‖ ^ 2 =
      ∫ x, (gaussianScalarPartialSum (fun n => a n x) N ω) ^ 2 *
        ∑ i : Fin 2, (gaussianScalarPartialSum (fun n => b i n x) N ω) ^ 2 ∂μ := by
    rw [flat_source_q3_finite_product_norm_sq_eq_wick_integral]
    apply integral_congr_ae
    have hvectorSums : ∀ᵐ x ∂μ, ∀ i : Fin 2,
        gaussianScalarPartialSum
          (fun n => (flatSourceQ3ProjectedL2 Q hab hcd e β L
            (dirs n) x).toVec i) N ω =
          gaussianScalarPartialSum (fun n => b i n x) N ω := by
      rw [ae_all_iff]
      intro i
      filter_upwards [hmodeAll i] with x hmode
      unfold gaussianScalarPartialSum
      apply Finset.sum_congr rfl
      intro n hn
      exact congrArg (fun y : ℝ => ω n * y) (hmode n)
    filter_upwards [hvectorSums] with x hvectorSums
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    exact congrArg (fun y : ℝ => y ^ 2) (hvectorSums i)
  have houter : Integrable (fun ω => ∫ x,
      (gaussianScalarPartialSum (fun n => a n x) N ω) ^ 2 *
        ∑ i : Fin 2,
          (gaussianScalarPartialSum (fun n => b i n x) N ω) ^ 2 ∂μ)
      standardGaussianInfinitePi := by
    simpa [a, b, μ] using hcap.1
  have hnormIntegrable : Integrable (fun ω =>
      ‖flatSourceQ3ValueLInf Q hab hcd β L (gaussianPartialSum dirs N ω) •
        flatSourceQ3ProjectedL2 Q hab hcd e β L (gaussianPartialSum dirs N ω)‖ ^ 2)
      standardGaussianInfinitePi := by
    apply houter.congr
    exact ae_of_all _ fun ω => (hspatial ω).symm
  have hbound :
      (∫ ω,
        ‖flatSourceQ3ValueLInf Q hab hcd β L (gaussianPartialSum dirs N ω) •
          flatSourceQ3ProjectedL2 Q hab hcd e β L (gaussianPartialSum dirs N ω)‖ ^ 2
        ∂standardGaussianInfinitePi) ≤
        (3 / 2 : ℝ) * (volume (openCubeSet Q)).toReal *
          (h ^ 2 * (3 : ℝ) ^ (2 * M.gamma * (k : ℝ))) ^ 2 := by
    calc
    (∫ ω,
      ‖flatSourceQ3ValueLInf Q hab hcd β L (gaussianPartialSum dirs N ω) •
        flatSourceQ3ProjectedL2 Q hab hcd e β L
          (gaussianPartialSum dirs N ω)‖ ^ 2 ∂standardGaussianInfinitePi) =
        ∫ ω, ∫ x,
          (gaussianScalarPartialSum (fun n => a n x) N ω) ^ 2 *
            ∑ i : Fin 2,
              (gaussianScalarPartialSum (fun n => b i n x) N ω) ^ 2 ∂μ
          ∂standardGaussianInfinitePi := by
      apply integral_congr_ae
      filter_upwards [] with ω
      exact hspatial ω
    _ ≤ (3 / 2 : ℝ) * (volume (openCubeSet Q)).toReal *
        (h ^ 2 * (3 : ℝ) ^ (2 * M.gamma * (k : ℝ))) ^ 2 := by
      simpa [a, b, β, L, dirs, μ] using hcap.2.2
  exact ⟨hnormIntegrable, hbound⟩

/-- The fixed physical shell value, read as an L∞ function on the parent. -/
noncomputable def flatSourceQ3ShellValueLInf
    (Q : TriadicCube 2) {a₀ b₀ c₀ d₀ : ℝ}
    (hab : a₀ < b₀) (hcd : c₀ < d₀) :
    C(closedRectangle a₀ b₀ c₀ d₀, ℝ) →L[ℝ]
      Lp ℝ ∞ (volumeMeasureOn (openCubeSet Q)) := by
  let clamp : C(Vec 2, closedRectangle a₀ b₀ c₀ d₀) :=
    ⟨lambda8CovarianceClamp a₀ b₀ c₀ d₀ hab hcd,
      flat_source_clamp_continuous a₀ b₀ c₀ d₀ hab hcd⟩
  let h3ToBounded : C(closedRectangle a₀ b₀ c₀ d₀, ℝ) →L[ℝ]
      BoundedContinuousFunction (closedRectangle a₀ b₀ c₀ d₀) ℝ :=
    (ContinuousMap.linearIsometryBoundedOfCompact
      (closedRectangle a₀ b₀ c₀ d₀) ℝ ℝ).toContinuousLinearEquiv.toContinuousLinearMap
  exact (BoundedContinuousFunction.toLp (∞ : ℝ≥0∞)
      (volumeMeasureOn (openCubeSet Q)) ℝ).comp
    ((BoundedContinuousFunction.compContinuousCLM ℝ ℝ clamp).comp h3ToBounded)

/-- The fixed physical scalar-times-projected-load product as a function of
the continuous shell field on the source rectangle. -/
noncomputable def flatSourceQ3ShellProduct
    (Q : TriadicCube 2) {a₀ b₀ c₀ d₀ : ℝ}
    (hab : a₀ < b₀) (hcd : c₀ < d₀) (e : Vec 2)
    (z : C(closedRectangle a₀ b₀ c₀ d₀, ℝ)) :
    HilbertVectorL2 (openCubeSet Q) :=
  flatSourceQ3ShellValueLInf Q hab hcd z •
    lambda8Q3ProjectedLoadClass (isOpenBoundedConvexDomain_openCubeSet Q)
      a₀ b₀ c₀ d₀ hab hcd e z

end ASDExplicitGamma.Scalar
