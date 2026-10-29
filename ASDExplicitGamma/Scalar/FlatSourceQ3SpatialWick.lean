module

public import ASDExplicitGamma.Scalar.FlatSourceSpatialWick
public import ASDExplicitGamma.Scalar.FlatSourceProjectedModeTrace
public import ASDExplicitGamma.Gaussian.HilbertBasisVariance

/-! A finite-mode spatial Wick bound for the actual q3 value modes and the
parent Dirichlet projections of their one-load vector modes. -/

@[expose] public section

open MeasureTheory Homogenization
open Set
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Triadic
open Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3
open scoped RealInnerProductSpace

namespace ASDExplicitGamma.Scalar

local instance flatSourceOpenCubeFiniteMeasure (Q : TriadicCube 2) :
    IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
  (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume

/-- A q3 scalar basis direction followed by the physical local load and
Dirichlet projection is exactly the parent-gradient mode used in the spatial
Wick estimate. -/
theorem flat_source_q3_projected_mode_eq_parent_gradient
    (Q : TriadicCube 2)
    {a₀ b₀ c₀ d₀ : ℝ}
    (hab : a₀ < b₀) (hcd : c₀ < d₀)
    (hQ : openCubeSet Q ⊆ openRectangle a₀ b₀ c₀ d₀)
    (β : ℝ) (L : {l : ℝ // 0 < l}) (e : Vec 2)
    (j : whiteBasisIndex) :
    lambda8Q3ProjectedLoadClass (isOpenBoundedConvexDomain_openCubeSet Q)
        a₀ b₀ c₀ d₀ hab hcd e
        (q3H3RangeValue a₀ b₀ c₀ d₀ β L
          (q3H3RangeFactor a₀ b₀ c₀ d₀ β L (whiteBasis j))) =
      (lambda8Q3GaussianModeParentPotential Q β L
        (matVecMul ASDExplicitGamma.Response.responsePlanarJ e) j).toH1Function.gradToHilbertVectorL2 := by
  let hDom := isOpenBoundedConvexDomain_openCubeSet Q
  let f : C(closedRectangle a₀ b₀ c₀ d₀, ℝ) :=
    q3H3RangeValue a₀ b₀ c₀ d₀ β L
      (q3H3RangeFactor a₀ b₀ c₀ d₀ β L (whiteBasis j))
  have hfvalue (x : closedRectangle a₀ b₀ c₀ d₀) :
      f x = q3Convolution β L h3Zero (whiteBasis j) x.1 := by
    dsimp [f]
    rw [q3H3RangeValue_factor a₀ b₀ c₀ d₀ β hab hcd L (whiteBasis j)]
    rfl
  let source : Fin 2 → H1Function (openCubeSet Q) := fun i =>
    lambda8Q3GaussianModeLoadH1 Q β L
      (matVecMul ASDExplicitGamma.Response.responsePlanarJ e) j i
  have hfield (x : Vec 2) (hx : x ∈ openCubeSet Q) :
      lambda8Q3LoadField a₀ b₀ c₀ d₀ hab hcd e f x =
        lambda8H1ComponentField source x := by
    ext i
    change f (lambda8CovarianceClamp a₀ b₀ c₀ d₀ hab hcd x) *
        matVecMul ASDExplicitGamma.Response.responsePlanarJ e i =
      source i x
    let xRect : closedRectangle a₀ b₀ c₀ d₀ :=
      ⟨x, ⟨Ioo_subset_Icc_self (hQ hx).1, Ioo_subset_Icc_self (hQ hx).2⟩⟩
    rw [lambda8CovarianceClamp_eq_of_mem a₀ b₀ c₀ d₀ hab hcd (hQ hx)]
    rw [hfvalue xRect]
    change q3Convolution β L h3Zero (whiteBasis j) x *
        (matVecMul ASDExplicitGamma.Response.responsePlanarJ e) i =
      q3Convolution β L h3Zero (whiteBasis j) x *
        (matVecMul ASDExplicitGamma.Response.responsePlanarJ e) i
    rfl
  have hsourceClass :
      lambda8Q3LoadClass hDom.1.measurableSet a₀ b₀ c₀ d₀ hab hcd e f =
        toHilbertVectorL2OfVecField
          (lambda8H1ComponentField_memVectorL2 source) := by
    change toHilbertVectorL2OfVecField
        (lambda8Q3LoadField_memVectorL2 hDom.1.measurableSet
          a₀ b₀ c₀ d₀ hab hcd e f) = _
    apply Lp.ext
    have hae : lambda8Q3LoadField a₀ b₀ c₀ d₀ hab hcd e f =ᵐ[
        volumeMeasureOn (openCubeSet Q)] lambda8H1ComponentField source := by
      filter_upwards [ae_restrict_mem (measurableSet_openCubeSet Q)] with x hx
      exact hfield x hx
    filter_upwards [
      coeFn_toHilbertVectorL2OfVecField
        (lambda8Q3LoadField_memVectorL2 hDom.1.measurableSet
          a₀ b₀ c₀ d₀ hab hcd e f),
      coeFn_toHilbertVectorL2OfVecField
        (lambda8H1ComponentField_memVectorL2 source), hae] with x hload hsource hfield'
    rw [hload, hsource]
    exact congrArg HilbertVec.ofVec hfield'
  change lambda8DirichletProjection hDom
      (lambda8Q3LoadClass hDom.1.measurableSet a₀ b₀ c₀ d₀ hab hcd e f) = _
  rw [hsourceClass]
  exact (lambda8Q3GaussianModeParentPotential_spec Q β L
    (matVecMul ASDExplicitGamma.Response.responsePlanarJ e) j).1

/-- The finite spatial Wick estimate for the physical q3 value series paired
with its actual parent-square Dirichlet-projection modes. The vector modes are
the zero-padded enumeration of the H¹ gradients supplied by the source
projection, so scalar and vector coefficients use the same white-noise input. -/
theorem flat_source_q3_finite_mode_parent_product_bound
    (Q : TriadicCube 2) {a₀ b₀ c₀ d₀ : ℝ}
    (hab : a₀ < b₀) (hcd : c₀ < d₀)
    (β : ℝ) (L : {l : ℝ // 0 < l}) (v : Vec 2) (N : ℕ) :
    let a : ℕ → Vec 2 → ℝ := fun n x =>
      q3H3RangeValue a₀ b₀ c₀ d₀ β L
        (q3H3Directions a₀ b₀ c₀ d₀ β L whiteBasis n)
        (lambda8CovarianceClamp a₀ b₀ c₀ d₀ hab hcd x)
    let b : Fin 2 → ℕ → Vec 2 → ℝ := fun i n x =>
      gaussEnumerated (fun j : whiteBasisIndex => fun y : Vec 2 =>
        (lambda8Q3GaussianModeParentPotential Q β L v j).toH1Function.grad y i) n x
    (∫ x, ∫ ω,
      (gaussianScalarPartialSum (fun n => a n x) N ω) ^ 2 *
        ∑ i : Fin 2, (gaussianScalarPartialSum (fun n => b i n x) N ω) ^ 2
      ∂standardGaussianInfinitePi ∂(volume.restrict (openCubeSet Q))) ≤
      3 * β ^ 2 * (∑ i : Fin 2, ∑ n ∈ Finset.range N,
        ∫ x, (b i n x) ^ 2 ∂(volume.restrict (openCubeSet Q))) := by
  classical
  let a : ℕ → Vec 2 → ℝ := fun n x =>
    q3H3RangeValue a₀ b₀ c₀ d₀ β L
      (q3H3Directions a₀ b₀ c₀ d₀ β L whiteBasis n)
      (lambda8CovarianceClamp a₀ b₀ c₀ d₀ hab hcd x)
  let b : Fin 2 → ℕ → Vec 2 → ℝ := fun i n x =>
    gaussEnumerated (fun j : whiteBasisIndex => fun y : Vec 2 =>
      (lambda8Q3GaussianModeParentPotential Q β L v j).toH1Function.grad y i) n x
  have hclamp : Continuous (lambda8CovarianceClamp a₀ b₀ c₀ d₀ hab hcd) := by
    exact Continuous.subtype_mk (by
      change Continuous (fun x : Vec 2 => fun i =>
        if i = 0 then max a₀ (min (x i) b₀) else max c₀ (min (x i) d₀))
      exact continuous_pi fun i => by
        fin_cases i
        · simpa using continuous_const.max ((continuous_apply 0).min continuous_const)
        · simpa using continuous_const.max ((continuous_apply 1).min continuous_const))
      (fun x => by
        change max a₀ (min (x 0) b₀) ∈ Icc a₀ b₀ ∧
          max c₀ (min (x 1) d₀) ∈ Icc c₀ d₀
        constructor
        · exact ⟨le_max_left _ _, max_le_iff.mpr ⟨hab.le, min_le_right _ _⟩⟩
        · exact ⟨le_max_left _ _, max_le_iff.mpr ⟨hcd.le, min_le_right _ _⟩⟩)
  have haMeas (n : ℕ) : Measurable (a n) := by
    dsimp [a]
    exact (q3H3RangeValue a₀ b₀ c₀ d₀ β L
      (q3H3Directions a₀ b₀ c₀ d₀ β L whiteBasis n)).continuous.comp
        hclamp |>.measurable
  have ha (x : Vec 2) : ∑ n ∈ Finset.range N, (a n x) ^ 2 ≤ β ^ 2 := by
    let coeff : whiteBasisIndex → ℝ := fun j =>
      ⟪whiteBasis j, q3Section β L h3Zero
        (lambda8CovarianceClamp a₀ b₀ c₀ d₀ hab hcd x).1⟫
    have hcoeff : Summable (fun j : whiteBasisIndex => (coeff j) ^ 2) :=
      hilbertBasis_summable_sq whiteBasis
        (q3Section β L h3Zero
          (lambda8CovarianceClamp a₀ b₀ c₀ d₀ hab hcd x).1)
    let := Encodable.ofCountable whiteBasisIndex
    have haeq (n : ℕ) : a n x = gaussEnumerated coeff n := by
      by_cases hn : n ∈ Set.range (Encodable.encode : whiteBasisIndex → ℕ)
      · obtain ⟨j, rfl⟩ := hn
        dsimp [a, q3H3Directions]
        rw [enumerated_encode,
          q3H3RangeValue_factor a₀ b₀ c₀ d₀ β hab hcd L (whiteBasis j)]
        rw [enumerated_encode]
      · dsimp [a, q3H3Directions]
        have hzero : q3H3Directions a₀ b₀ c₀ d₀ β L whiteBasis n = 0 := by
          dsimp [q3H3Directions, gaussEnumerated]
          exact Function.extend_apply' _ _ _ hn
        have hzeroCoeff : gaussEnumerated coeff n = 0 := by
          dsimp [gaussEnumerated]
          exact Function.extend_apply' _ _ _ hn
        change q3H3RangeValue a₀ b₀ c₀ d₀ β L
          (q3H3Directions a₀ b₀ c₀ d₀ β L whiteBasis n)
          (lambda8CovarianceClamp a₀ b₀ c₀ d₀ hab hcd x) = gaussEnumerated coeff n
        rw [hzero, hzeroCoeff]
        simp [q3H3RangeValue]
    have hs : Summable (fun n => (a n x) ^ 2) := by
      have heq : (fun n => (a n x) ^ 2) =
          (fun n => ‖gaussEnumerated coeff n‖ ^ 2) := by
        funext n
        rw [haeq n]
        simp only [Real.norm_eq_abs, sq_abs]
      rw [heq]
      have hcoeffNorm : Summable (fun j => ‖coeff j‖ ^ 2) := by
        simpa only [Real.norm_eq_abs, sq_abs] using hcoeff
      exact enumerated_summable_sq coeff hcoeffNorm
    have hvar := q3_value_mode_variance (a := a₀) (b := b₀)
      (c := c₀) (d := d₀) (β := β) hab hcd L
      (lambda8CovarianceClamp a₀ b₀ c₀ d₀ hab hcd x)
    calc
      _ ≤ ∑' n, (a n x) ^ 2 := hs.sum_le_tsum (Finset.range N)
        (fun n hn => sq_nonneg _)
      _ = β ^ 2 := by simpa [a] using hvar
  have hb (i : Fin 2) (n : ℕ) :
      MemLp (b i n) 2 (volume.restrict (openCubeSet Q)) := by
    let := Encodable.ofCountable whiteBasisIndex
    change MemLp (fun x => gaussEnumerated (fun j : whiteBasisIndex => fun y : Vec 2 =>
      (lambda8Q3GaussianModeParentPotential Q β L v j).toH1Function.grad y i) n x)
      2 (volume.restrict (openCubeSet Q))
    by_cases hn : n ∈ Set.range (Encodable.encode : whiteBasisIndex → ℕ)
    · obtain ⟨j, rfl⟩ := hn
      rw [enumerated_encode]
      exact (lambda8Q3GaussianModeParentPotential Q β L v j).toH1Function.grad_memL2 i
    · rw [gaussEnumerated, Function.extend_apply' _ _ _ hn]
      exact MemLp.zero
  simpa [a, b] using
    flat_source_finite_mode_spatial_product_bound
      (volume.restrict (openCubeSet Q)) N a b (β ^ 2) haMeas ha hb

/-- The finite-mode spatial Wick estimate has the sharp physical half-variance
cap after summing the actual local-projection modes. This is the finite-cutoff
source estimate; the fixed-series passage and reset-bank averaging are separate. -/
theorem flat_source_q3_finite_mode_parent_product_cap
    (Q : TriadicCube 2) {a₀ b₀ c₀ d₀ : ℝ}
    (hab : a₀ < b₀) (hcd : c₀ < d₀)
    (hQ : openCubeSet Q ⊆ openRectangle a₀ b₀ c₀ d₀)
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (e : Vec 2) (he : Book.Ch02.vecNorm e = 1) (k : ℤ) (N : ℕ) :
    let β := q3ModelAmplitude M h k
    let L := q3ModelLength k
    let a : ℕ → Vec 2 → ℝ := fun n x =>
      q3H3RangeValue a₀ b₀ c₀ d₀ β L
        (q3H3Directions a₀ b₀ c₀ d₀ β L whiteBasis n)
        (lambda8CovarianceClamp a₀ b₀ c₀ d₀ hab hcd x)
    let b : Fin 2 → ℕ → Vec 2 → ℝ := fun i n x =>
      gaussEnumerated (fun j : whiteBasisIndex => fun y : Vec 2 =>
        (lambda8Q3GaussianModeParentPotential Q β L
          (matVecMul ASDExplicitGamma.Response.responsePlanarJ e) j).toH1Function.grad y i) n x
    Integrable (fun ω => ∫ x,
      (gaussianScalarPartialSum (fun n => a n x) N ω) ^ 2 *
        ∑ i : Fin 2,
          (gaussianScalarPartialSum (fun n => b i n x) N ω) ^ 2
      ∂(volume.restrict (openCubeSet Q))) standardGaussianInfinitePi ∧
    ((∫ x, ∫ ω,
      (gaussianScalarPartialSum (fun n => a n x) N ω) ^ 2 *
        ∑ i : Fin 2,
          (gaussianScalarPartialSum (fun n => b i n x) N ω) ^ 2
      ∂standardGaussianInfinitePi ∂(volume.restrict (openCubeSet Q))) ≤
      (3 / 2 : ℝ) * (volume (openCubeSet Q)).toReal *
        (h ^ 2 * (3 : ℝ) ^ (2 * M.gamma * (k : ℝ))) ^ 2) ∧
    ((∫ ω, ∫ x,
      (gaussianScalarPartialSum (fun n => a n x) N ω) ^ 2 *
        ∑ i : Fin 2,
          (gaussianScalarPartialSum (fun n => b i n x) N ω) ^ 2
      ∂(volume.restrict (openCubeSet Q)) ∂standardGaussianInfinitePi) ≤
      (3 / 2 : ℝ) * (volume (openCubeSet Q)).toReal *
        (h ^ 2 * (3 : ℝ) ^ (2 * M.gamma * (k : ℝ))) ^ 2) := by
  classical
  let β := q3ModelAmplitude M h k
  let L := q3ModelLength k
  have instRangeIP : InnerProductSpace ℝ (Q3H3Range a₀ b₀ c₀ d₀ β L) :=
    instQ3H3RangeInnerProductSpace a₀ b₀ c₀ d₀ β L
  let dirs := q3H3Directions a₀ b₀ c₀ d₀ β L whiteBasis
  let a : ℕ → Vec 2 → ℝ := fun n x =>
    q3H3RangeValue a₀ b₀ c₀ d₀ β L
      (q3H3Directions a₀ b₀ c₀ d₀ β L whiteBasis n)
      (lambda8CovarianceClamp a₀ b₀ c₀ d₀ hab hcd x)
  let R : Q3H3Range a₀ b₀ c₀ d₀ β L →L[ℝ] HilbertVectorL2 (openCubeSet Q) :=
    (lambda8Q3ProjectedLoadClass (isOpenBoundedConvexDomain_openCubeSet Q)
      a₀ b₀ c₀ d₀ hab hcd e).comp (q3H3RangeValue a₀ b₀ c₀ d₀ β L)
  let b : Fin 2 → ℕ → Vec 2 → ℝ := fun i n x =>
    gaussEnumerated (fun j : whiteBasisIndex => fun y : Vec 2 =>
      (lambda8Q3GaussianModeParentPotential Q β L
        (matVecMul ASDExplicitGamma.Response.responsePlanarJ e) j).toH1Function.grad y i) n x
  have hclamp : Continuous (lambda8CovarianceClamp a₀ b₀ c₀ d₀ hab hcd) := by
    exact Continuous.subtype_mk (by
      change Continuous (fun x : Vec 2 => fun i =>
        if i = 0 then max a₀ (min (x i) b₀) else max c₀ (min (x i) d₀))
      exact continuous_pi fun i => by
        fin_cases i
        · simpa using continuous_const.max ((continuous_apply 0).min continuous_const)
        · simpa using continuous_const.max ((continuous_apply 1).min continuous_const))
      (fun x => by
        change max a₀ (min (x 0) b₀) ∈ Icc a₀ b₀ ∧
          max c₀ (min (x 1) d₀) ∈ Icc c₀ d₀
        constructor
        · exact ⟨le_max_left _ _, max_le_iff.mpr ⟨hab.le, min_le_right _ _⟩⟩
        · exact ⟨le_max_left _ _, max_le_iff.mpr ⟨hcd.le, min_le_right _ _⟩⟩)
  have haMeas (n : ℕ) : Measurable (a n) := by
    dsimp [a]
    exact (q3H3RangeValue a₀ b₀ c₀ d₀ β L
      (q3H3Directions a₀ b₀ c₀ d₀ β L whiteBasis n)).continuous.comp
        hclamp |>.measurable
  have ha (x : Vec 2) : ∑ n ∈ Finset.range N, (a n x) ^ 2 ≤ β ^ 2 := by
    let coeff : whiteBasisIndex → ℝ := fun j =>
      ⟪whiteBasis j, q3Section β L h3Zero
        (lambda8CovarianceClamp a₀ b₀ c₀ d₀ hab hcd x).1⟫
    have hcoeff : Summable (fun j : whiteBasisIndex => (coeff j) ^ 2) :=
      hilbertBasis_summable_sq whiteBasis
        (q3Section β L h3Zero
          (lambda8CovarianceClamp a₀ b₀ c₀ d₀ hab hcd x).1)
    let := Encodable.ofCountable whiteBasisIndex
    have haeq (n : ℕ) : a n x = gaussEnumerated coeff n := by
      by_cases hn : n ∈ Set.range (Encodable.encode : whiteBasisIndex → ℕ)
      · obtain ⟨j, rfl⟩ := hn
        dsimp [a, q3H3Directions]
        rw [enumerated_encode,
          q3H3RangeValue_factor a₀ b₀ c₀ d₀ β hab hcd L (whiteBasis j)]
        rw [enumerated_encode]
      · dsimp [a, q3H3Directions]
        have hzero : q3H3Directions a₀ b₀ c₀ d₀ β L whiteBasis n = 0 := by
          dsimp [q3H3Directions, gaussEnumerated]
          exact Function.extend_apply' _ _ _ hn
        have hzeroCoeff : gaussEnumerated coeff n = 0 := by
          dsimp [gaussEnumerated]
          exact Function.extend_apply' _ _ _ hn
        change q3H3RangeValue a₀ b₀ c₀ d₀ β L
          (q3H3Directions a₀ b₀ c₀ d₀ β L whiteBasis n)
          (lambda8CovarianceClamp a₀ b₀ c₀ d₀ hab hcd x) = gaussEnumerated coeff n
        rw [hzero, hzeroCoeff]
        simp [q3H3RangeValue]
    have hs : Summable (fun n => (a n x) ^ 2) := by
      have heq : (fun n => (a n x) ^ 2) =
          (fun n => ‖gaussEnumerated coeff n‖ ^ 2) := by
        funext n
        rw [haeq n]
        simp only [Real.norm_eq_abs, sq_abs]
      rw [heq]
      have hcoeffNorm : Summable (fun j => ‖coeff j‖ ^ 2) := by
        simpa only [Real.norm_eq_abs, sq_abs] using hcoeff
      exact enumerated_summable_sq coeff hcoeffNorm
    have hvar := q3_value_mode_variance (a := a₀) (b := b₀)
      (c := c₀) (d := d₀) (β := β) hab hcd L
      (lambda8CovarianceClamp a₀ b₀ c₀ d₀ hab hcd x)
    calc
      _ ≤ ∑' n, (a n x) ^ 2 := hs.sum_le_tsum (Finset.range N)
        (fun n hn => sq_nonneg _)
      _ = β ^ 2 := by simpa [a] using hvar
  have hb (i : Fin 2) (n : ℕ) :
      MemLp (b i n) 2 (volume.restrict (openCubeSet Q)) := by
    let := Encodable.ofCountable whiteBasisIndex
    change MemLp (fun x => gaussEnumerated (fun j : whiteBasisIndex => fun y : Vec 2 =>
      (lambda8Q3GaussianModeParentPotential Q β L
        (matVecMul ASDExplicitGamma.Response.responsePlanarJ e) j).toH1Function.grad y i)
      n x) 2 (volume.restrict (openCubeSet Q))
    by_cases hn : n ∈ Set.range (Encodable.encode : whiteBasisIndex → ℕ)
    · obtain ⟨j, rfl⟩ := hn
      rw [enumerated_encode]
      exact (lambda8Q3GaussianModeParentPotential Q β L
        (matVecMul ASDExplicitGamma.Response.responsePlanarJ e) j).toH1Function.grad_memL2 i
    · rw [gaussEnumerated, Function.extend_apply' _ _ _ hn]
      exact MemLp.zero
  have hvol : 0 < (volume (openCubeSet Q)).toReal := by
    rw [volume_openCubeSet_eq_volume_cubeSet, volume_cubeSet_toReal]
    exact cubeVolume_pos Q
  have hmode (n : ℕ) :
      ∑ i : Fin 2, ∫ x in openCubeSet Q, (b i n x) ^ 2 ∂volume =
        ‖R (q3H3Directions a₀ b₀ c₀ d₀ β L whiteBasis n)‖ ^ 2 := by
    let := Encodable.ofCountable whiteBasisIndex
    by_cases hn : n ∈ Set.range (Encodable.encode : whiteBasisIndex → ℕ)
    · obtain ⟨j, rfl⟩ := hn
      let W := lambda8Q3GaussianModeParentPotential Q β L
        (matVecMul ASDExplicitGamma.Response.responsePlanarJ e) j
      have hproj : R (q3H3Directions a₀ b₀ c₀ d₀ β L whiteBasis (Encodable.encode j)) =
          W.toH1Function.gradToHilbertVectorL2 := by
        dsimp [R, dirs, W, q3H3Directions]
        rw [enumerated_encode,
          flat_source_q3_projected_mode_eq_parent_gradient
            Q hab hcd hQ β L e j]
      have hbmode (i : Fin 2) :
          b i (Encodable.encode j) = fun x => W.toH1Function.grad x i := by
        funext x
        simp [b, W, enumerated_encode]
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
          ‖W.toH1Function.gradToHilbertVectorL2‖ ^ 2 =
              inner ℝ W.toH1Function.gradToHilbertVectorL2
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
    · have hdir : q3H3Directions a₀ b₀ c₀ d₀ β L whiteBasis n = 0 := by
        dsimp [q3H3Directions, gaussEnumerated]
        exact Function.extend_apply' _ _ _ hn
      have hbzero (i : Fin 2) : b i n = 0 := by
        funext x
        change (gaussEnumerated (fun j : whiteBasisIndex => fun y : Vec 2 =>
          (lambda8Q3GaussianModeParentPotential Q β L
            (matVecMul ASDExplicitGamma.Response.responsePlanarJ e) j).toH1Function.grad y i) n) x = 0
        have hext : gaussEnumerated (fun j : whiteBasisIndex => fun y : Vec 2 =>
            (lambda8Q3GaussianModeParentPotential Q β L
              (matVecMul ASDExplicitGamma.Response.responsePlanarJ e) j).toH1Function.grad y i) n = 0 := by
          dsimp [gaussEnumerated]
          exact Function.extend_apply' _ _ _ hn
        rw [hext]
        rfl
      simp [hbzero, hdir, R]
  have hdirs : Summable (fun n : ℕ => ‖R (dirs n)‖ ^ 2) :=
    @summable_sq_bounded_image ℕ
      (Q3H3Range a₀ b₀ c₀ d₀ β L) (HilbertVectorL2 (openCubeSet Q))
      inferInstance (instQ3H3RangeInnerProductSpace a₀ b₀ c₀ d₀ β L).toNormedSpace
      inferInstance inferInstance dirs
      (q3H3Directions_summable a₀ b₀ c₀ d₀ β L whiteBasis) R
  have htrace := lambda8Q3ProjectedLoad_modes_energy_le
    (hU := isOpenBoundedConvexDomain_openCubeSet Q) (ne_of_gt hvol) hQ hab hcd e M h hM he k
  have hpartial :
      (∑ n ∈ Finset.range N, ‖R (dirs n)‖ ^ 2) ≤
        (volume (openCubeSet Q)).toReal *
          (h ^ 2 * (3 : ℝ) ^ (2 * M.gamma * (k : ℝ)) / 2) := by
    calc
      _ ≤ ∑' n, ‖R (dirs n)‖ ^ 2 := hdirs.sum_le_tsum (Finset.range N)
        (fun n hn => sq_nonneg _)
      _ ≤ _ := htrace
  have hwick := flat_source_q3_finite_mode_parent_product_bound
    Q hab hcd β L (matVecMul ASDExplicitGamma.Response.responsePlanarJ e) N
  have henergy :
      (∑ i : Fin 2, ∑ n ∈ Finset.range N,
        ∫ x, (b i n x) ^ 2 ∂(volume.restrict (openCubeSet Q))) =
        ∑ n ∈ Finset.range N, ‖R (dirs n)‖ ^ 2 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro n hn
    simpa only [dirs] using hmode n
  have hforward :
      (∫ x, ∫ ω,
        (gaussianScalarPartialSum (fun n => a n x) N ω) ^ 2 *
          ∑ i : Fin 2,
            (gaussianScalarPartialSum (fun n => b i n x) N ω) ^ 2
        ∂standardGaussianInfinitePi ∂(volume.restrict (openCubeSet Q))) ≤
        (3 / 2 : ℝ) * (volume (openCubeSet Q)).toReal *
          (h ^ 2 * (3 : ℝ) ^ (2 * M.gamma * (k : ℝ))) ^ 2 := by
    calc
      _ ≤ 3 * β ^ 2 *
          (∑ i : Fin 2, ∑ n ∈ Finset.range N,
            ∫ x, (b i n x) ^ 2 ∂(volume.restrict (openCubeSet Q))) := by
        simpa [b, β, L] using hwick
      _ = 3 * β ^ 2 * (∑ n ∈ Finset.range N, ‖R (dirs n)‖ ^ 2) := by
        rw [henergy]
      _ ≤ 3 * β ^ 2 *
          ((volume (openCubeSet Q)).toReal *
            (h ^ 2 * (3 : ℝ) ^ (2 * M.gamma * (k : ℝ)) / 2)) := by
        exact mul_le_mul_of_nonneg_left hpartial (by positivity)
      _ = (3 / 2 : ℝ) * (volume (openCubeSet Q)).toReal *
          (h ^ 2 * (3 : ℝ) ^ (2 * M.gamma * (k : ℝ))) ^ 2 := by
        have hβ : β ^ 2 = h ^ 2 * (3 : ℝ) ^ (2 * M.gamma * (k : ℝ)) := by
          dsimp [β]
          exact q3ModelAmplitude_sq M h k
        rw [hβ]
        ring
  have hswap := flat_source_finite_mode_spatial_product_integral_swap
    (volume.restrict (openCubeSet Q)) N a b (β ^ 2) haMeas ha hb
  rcases hswap with ⟨hintegrable, hswap⟩
  refine ⟨?_, ?_, ?_⟩
  · simpa [a, b] using hintegrable
  · simpa [a, b, β, L] using hforward
  · rw [← hswap]
    simpa [a, b, β, L] using hforward

end ASDExplicitGamma.Scalar
