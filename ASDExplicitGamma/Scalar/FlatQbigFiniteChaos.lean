module

public import ASDExplicitGamma.Scalar.FlatSourceFiniteChaos
public import ASDExplicitGamma.Scalar.FlatQbigTile
public import ASDExplicitGamma.Scalar.ChaosHilbertSymmetrization
public import ASDExplicitGamma.Scalar.FlatSourceQ3PositiveHaar
public import ASDExplicitGamma.Scalar.FlatSourceC1Multiplier
public import ASDExplicitGamma.Main.CMRegularity
public import ASDExplicitGamma.Gaussian.Q3SobolevOperator

/-! Q_big flat successor: the finite q3 H¹ chaos envelope with the tile-side Poincaré constant
(copy of `FlatSourceFiniteH1Chaos` with `cubeScaleFactor Q` replaced by `tileSide Q`). -/

@[expose] public section

open MeasureTheory ProbabilityTheory Homogenization
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Triadic
open ASDExplicitGamma.Response ASDExplicitGamma.Main
open Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3
open scoped ENNReal Topology RealInnerProductSpace BigOperators

namespace ASDExplicitGamma.Scalar

private theorem enumerated_h1_toFun
    {ι : Type*} [Countable ι] {U : Set (Vec 2)}
    (F : ι → H1Function U) (n : ℕ) (x : Vec 2) :
    (gaussEnumerated F n).toFun x = gaussEnumerated (fun q => (F q).toFun x) n := by
  classical
  let := Encodable.ofCountable ι
  by_cases hn : n ∈ Set.range (Encodable.encode : ι → ℕ)
  · obtain ⟨q, rfl⟩ := hn
    rw [enumerated_encode, enumerated_encode]
  · rw [gaussEnumerated, gaussEnumerated,
      Function.extend_apply' _ _ _ hn, Function.extend_apply' _ _ _ hn]
    rfl

private theorem enumerated_h1_grad
    {ι : Type*} [Countable ι] {U : Set (Vec 2)}
    (F : ι → H1Function U) (n : ℕ) (x : Vec 2) (i : Fin 2) :
    (gaussEnumerated F n).grad x i =
      gaussEnumerated (fun q => (F q).grad x i) n := by
  classical
  let := Encodable.ofCountable ι
  by_cases hn : n ∈ Set.range (Encodable.encode : ι → ℕ)
  · obtain ⟨q, rfl⟩ := hn
    rw [enumerated_encode, enumerated_encode]
  · rw [gaussEnumerated, gaussEnumerated,
      Function.extend_apply' _ _ _ hn, Function.extend_apply' _ _ _ hn]
    rfl

private theorem enumerated_fun_apply
    {ι : Type*} [Countable ι] (F : ι → Vec 2 → ℝ)
    (n : ℕ) (x : Vec 2) :
    gaussEnumerated F n x = gaussEnumerated (fun q => F q x) n := by
  classical
  let := Encodable.ofCountable ι
  by_cases hn : n ∈ Set.range (Encodable.encode : ι → ℕ)
  · obtain ⟨q, rfl⟩ := hn
    rw [enumerated_encode, enumerated_encode]
  · rw [gaussEnumerated, gaussEnumerated,
      Function.extend_apply' _ _ _ hn, Function.extend_apply' _ _ _ hn]
    rfl

private theorem h1_finite_sum_smul_value
    {ι : Type*} [DecidableEq ι] {U : Set (Vec 2)}
    (s : Finset ι) (c : ι → ℝ) (u : ι → H1Function U) (x : Vec 2) :
    (∑ i ∈ s, c i • u i).toFun x = ∑ i ∈ s, c i * u i x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp [Finset.sum_insert, ha, ih]

private theorem h1_finite_sum_smul_gradient
    {ι : Type*} [DecidableEq ι] {U : Set (Vec 2)}
    (s : Finset ι) (c : ι → ℝ) (u : ι → H1Function U)
    (x : Vec 2) (j : Fin 2) :
    (∑ i ∈ s, c i • u i).grad x j = ∑ i ∈ s, c i * (u i).grad x j := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp [Finset.sum_insert, ha, ih]

private theorem h1_fintype_sum_smul_value
    {ι : Type*} [Fintype ι] {U : Set (Vec 2)}
    (c : ι → ℝ) (u : ι → H1Function U) (x : Vec 2) :
    (∑ i : ι, c i • u i).toFun x = ∑ i : ι, c i * u i x := by
  classical
  exact h1_finite_sum_smul_value Finset.univ c u x

private theorem h1_fintype_sum_smul_gradient
    {ι : Type*} [Fintype ι] {U : Set (Vec 2)}
    (c : ι → ℝ) (u : ι → H1Function U) (x : Vec 2) (i : Fin 2) :
    (∑ j : ι, c j • u j).grad x i = ∑ j : ι, c j * (u j).grad x i := by
  classical
  exact h1_finite_sum_smul_gradient Finset.univ c u x i

private theorem h1_fintype_sum_value_toLp
    (Q : TriadicCube 2) {ι : Type*} [Fintype ι]
    (c : ι → ℝ) (u : ι → H1Function (openCubeSet Q)) :
    (∑ i : ι, c i • (u i).memL2_normalizedCubeMeasure.toLp (u i).toFun) =
      (∑ i : ι, c i • u i).memL2_normalizedCubeMeasure.toLp
        (∑ i : ι, c i • u i).toFun := by
  classical
  apply Lp.ext
  have hsum := Lp.coeFn_fun_finsetSum Finset.univ
    (fun i : ι => c i • (u i).memL2_normalizedCubeMeasure.toLp (u i).toFun)
  have hrep := ((∑ i : ι, c i • u i).memL2_normalizedCubeMeasure).coeFn_toLp
  have hterm (i : ι) :
      (c i • (u i).memL2_normalizedCubeMeasure.toLp (u i).toFun) =ᵐ[
        normalizedCubeMeasure Q] fun x => c i * (u i).toFun x := by
    filter_upwards [Lp.coeFn_smul (c i)
        ((u i).memL2_normalizedCubeMeasure.toLp (u i).toFun),
      (u i).memL2_normalizedCubeMeasure.coeFn_toLp] with x hs hu
    calc
      (c i • (u i).memL2_normalizedCubeMeasure.toLp (u i).toFun) x =
          c i * ((u i).memL2_normalizedCubeMeasure.toLp (u i).toFun) x := by
        simpa only [Pi.smul_apply, smul_eq_mul] using hs
      _ = c i * (u i).toFun x := by rw [hu]
  filter_upwards [hsum, hrep, ae_all_iff.mpr hterm] with x hs hr ht
  calc
    (∑ i : ι, c i • (u i).memL2_normalizedCubeMeasure.toLp (u i).toFun) x =
        ∑ i : ι, c i * (u i).toFun x := by
      rw [hs]
      apply Finset.sum_congr rfl
      intro i hi
      exact ht i
    _ = (∑ i : ι, c i • u i).memL2_normalizedCubeMeasure.toLp
        (∑ i : ι, c i • u i).toFun x := by
      rw [hr, h1_fintype_sum_smul_value]

private theorem h1_fintype_sum_gradient_toLp
    (Q : TriadicCube 2) {ι : Type*} [Fintype ι]
    (c : ι → ℝ) (u : ι → H1Function (openCubeSet Q)) (j : Fin 2) :
    (∑ i : ι, c i • ((u i).grad_memL2_normalizedCubeMeasure j).toLp
        (fun x => (u i).grad x j)) =
      ((∑ i : ι, c i • u i).grad_memL2_normalizedCubeMeasure j).toLp
        (fun x => (∑ i : ι, c i • u i).grad x j) := by
  classical
  apply Lp.ext
  have hsum := Lp.coeFn_fun_finsetSum Finset.univ
    (fun i : ι => c i • ((u i).grad_memL2_normalizedCubeMeasure j).toLp
        (fun x => (u i).grad x j))
  have hrep := ((∑ i : ι, c i • u i).grad_memL2_normalizedCubeMeasure j).coeFn_toLp
  have hterm (i : ι) :
      c i • ((u i).grad_memL2_normalizedCubeMeasure j).toLp
        (fun x => (u i).grad x j) =ᵐ[normalizedCubeMeasure Q]
        fun x => c i * (u i).grad x j := by
    filter_upwards [Lp.coeFn_smul (c i)
        (((u i).grad_memL2_normalizedCubeMeasure j).toLp
          (fun x => (u i).grad x j)),
      (u i).grad_memL2_normalizedCubeMeasure j |>.coeFn_toLp] with x hs hu
    calc
      (c i • ((u i).grad_memL2_normalizedCubeMeasure j).toLp
          (fun x => (u i).grad x j)) x =
          c i * ((u i).grad_memL2_normalizedCubeMeasure j).toLp
            (fun x => (u i).grad x j) x := by
        simpa only [Pi.smul_apply, smul_eq_mul] using hs
      _ = c i * (u i).grad x j := by rw [hu]
  filter_upwards [hsum, hrep, ae_all_iff.mpr hterm] with x hs hr ht
  calc
    (∑ i : ι, c i • ((u i).grad_memL2_normalizedCubeMeasure j).toLp
        (fun x => (u i).grad x j)) x =
        ∑ i : ι, c i * (u i).grad x j := by
      rw [hs]
      apply Finset.sum_congr rfl
      intro i hi
      exact ht i
    _ = ((∑ i : ι, c i • u i).grad_memL2_normalizedCubeMeasure j).toLp
        (fun x => (∑ i : ι, c i • u i).grad x j) x := by
      rw [hr, h1_fintype_sum_smul_gradient]

private theorem gaussianScalarPartialSum_fin
    (a : ℕ → ℝ) (N : ℕ) (ω : ℕ → ℝ) :
    gaussianScalarPartialSum a N ω =
      ∑ i : Fin N, ω i.val * a i.val := by
  unfold gaussianScalarPartialSum
  exact (Fin.sum_univ_eq_sum_range (fun i : ℕ => ω i * a i) N).symm

private theorem weighted_pair_sum_factor
    {N : ℕ} (ω a b : Fin N → ℝ) :
    (∑ n : Fin N, ω n * ∑ m : Fin N, ω m * (a n * b m)) =
      (∑ n : Fin N, ω n * a n) * (∑ m : Fin N, ω m * b m) := by
  calc
    _ = ∑ n : Fin N, ∑ m : Fin N,
        (ω n * a n) * (ω m * b m) := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m hm
      ring
    _ = _ := by
      simpa using (Finset.sum_mul_sum Finset.univ Finset.univ
        (fun n : Fin N => ω n * a n) (fun m : Fin N => ω m * b m)).symm

private theorem weighted_pair_sum_factor_add
    {N : ℕ} (ω a d b c : Fin N → ℝ) :
    (∑ n : Fin N, ω n * ∑ m : Fin N,
      ω m * (a n * b m + c m * d n)) =
      (∑ n : Fin N, ω n * a n) * (∑ m : Fin N, ω m * b m) +
        (∑ m : Fin N, ω m * c m) * (∑ n : Fin N, ω n * d n) := by
  have hsplit :
      (∑ n : Fin N, ω n * ∑ m : Fin N,
        ω m * (a n * b m + c m * d n)) =
      (∑ n : Fin N, ω n * ∑ m : Fin N, ω m * (a n * b m)) +
        (∑ n : Fin N, ω n * ∑ m : Fin N, ω m * (c m * d n)) := by
    simp only [mul_add, Finset.sum_add_distrib]
  rw [hsplit, weighted_pair_sum_factor]
  have hcomm :
      (∑ n : Fin N, ω n * ∑ m : Fin N, ω m * (c m * d n)) =
        ∑ n : Fin N, ω n * ∑ m : Fin N, ω m * (d n * c m) := by
    apply Finset.sum_congr rfl
    intro n hn
    congr 1
    apply Finset.sum_congr rfl
    intro m hm
    ring
  rw [hcomm, weighted_pair_sum_factor]
  ring

private theorem double_finite_sum_smul_commute
    {W : Type*} [NormedAddCommGroup W] [Module ℝ W] {N : ℕ}
    (a b : Fin N → ℝ) (c : ℝ) (B : Fin N → Fin N → W) :
    (∑ n : Fin N, a n • ∑ m : Fin N, b m • (c • B n m)) =
      c • ∑ n : Fin N, a n • ∑ m : Fin N, b m • B n m := by
  simp only [Finset.smul_sum, smul_smul]
  apply Finset.sum_congr rfl
  intro n hn
  apply Finset.sum_congr rfl
  intro m hm
  congr 1
  ring

/-- The H¹ coefficient mode for one scalar q3 coordinate times one projected
parent-load coordinate. -/
noncomputable def tFlatSourceQ3PairProductH1
    (Q : TriadicCube 2) (β : ℝ) (L : {l : ℝ // 0 < l})
    (e : Vec 2) (n m : ℕ) (i : Fin 2) :
    H1Function (openCubeSet Q) := by
  let hU := isOpenBoundedConvexDomain_openCubeSet Q
  let φ : Vec 2 → ℝ :=
    q3Convolution β L h3Zero (gaussEnumerated whiteBasis n)
  let modes : whiteBasisIndex → H1Function (openCubeSet Q) := fun j =>
    (lambda8Q3GaussianModeParentHessian Q β L
      (matVecMul responsePlanarJ e) j).gradCoordH1Function i
  let u : H1Function (openCubeSet Q) := gaussEnumerated modes m
  have hφ3 : ContDiff ℝ 3 φ := by
    dsimp [φ]
    exact main_q3_value_direction_contDiff_three β L
      (gaussEnumerated whiteBasis n)
  have hφ : ContDiff ℝ 1 φ := hφ3.of_le (by norm_num)
  have hφtop := contDiffOne_memLpTop_of_bounded_open_domain hU hφ
  exact h1_mul_contDiffOne_memLpTop hU
    (Book.Ch02.openCubeSet_nonempty Q) u hφ hφtop.1 hφtop.2

/-- The pair product coefficient has its expected scalar product value. -/
theorem flat_source_q3_pair_product_h1_toFun
    (Q : TriadicCube 2) (β : ℝ) (L : {l : ℝ // 0 < l})
    (e : Vec 2) (n m : ℕ) (i : Fin 2) (x : Vec 2) :
    (tFlatSourceQ3PairProductH1 Q β L e n m i).toFun x =
      flatSourceQ3FiniteValueMode β L n x *
        flatSourceQ3FiniteProjectedMode Q β L e i m x := by
  simp only [tFlatSourceQ3PairProductH1, h1_mul_contDiffOne_memLpTop]
  rw [flatSourceQ3FiniteValueMode, flatSourceQ3FiniteProjectedMode,
    enumerated_h1_toFun]
  simp only [Homogenization.HasWeakHessianOn.gradCoordH1Function_apply]
  rw [enumerated_fun_apply]

/-- Its weak gradient is the ordinary product rule for the two source modes. -/
theorem flat_source_q3_pair_product_h1_grad
    (Q : TriadicCube 2) (β : ℝ) (L : {l : ℝ // 0 < l})
    (e : Vec 2) (n m : ℕ) (i j : Fin 2) (x : Vec 2) :
    (tFlatSourceQ3PairProductH1 Q β L e n m i).grad x j =
      flatSourceQ3FiniteValueMode β L n x *
          flatSourceQ3FiniteProjectedGradientMode Q β L e i j m x +
        flatSourceQ3FiniteProjectedMode Q β L e i m x *
          flatSourceQ3FiniteValueDerivativeMode β L j n x := by
  simp only [tFlatSourceQ3PairProductH1, h1_mul_contDiffOne_memLpTop]
  rw [flatSourceQ3FiniteValueMode, flatSourceQ3FiniteProjectedMode,
    flatSourceQ3FiniteProjectedGradientMode, flatSourceQ3FiniteValueDerivativeMode,
    enumerated_h1_grad, enumerated_h1_toFun]
  simp only [Homogenization.HasWeakHessianOn.gradCoordH1Function_apply,
    Homogenization.HasWeakHessianOn.gradCoordH1Function_grad_apply]
  rw [enumerated_fun_apply, enumerated_fun_apply]

abbrev tFlatSourceH1ChaosIndex := Fin 2 ⊕ (Fin 2 × Fin 2)

abbrev tFlatSourceH1ChaosSpace (Q : TriadicCube 2) :=
  PiLp 2 (fun _ : tFlatSourceH1ChaosIndex =>
    Lp ℝ 2 (normalizedCubeMeasure Q))

/-- One H¹ pair coefficient embedded as the value and scaled-gradient vector
in the spatial Hilbert sum. -/
noncomputable def tFlatSourceQ3PairEnergyVector
    (Q : TriadicCube 2) (β : ℝ) (L : {l : ℝ // 0 < l})
    (e : Vec 2) (n m : ℕ) : tFlatSourceH1ChaosSpace Q := by
  let c : ℝ := (467 / 1000 : ℝ) * tileSide Q
  exact WithLp.toLp 2 (fun a : tFlatSourceH1ChaosIndex =>
    match a with
    | Sum.inl i =>
        let u := tFlatSourceQ3PairProductH1 Q β L e n m i
        u.memL2_normalizedCubeMeasure.toLp u.toFun
    | Sum.inr ij =>
        let u := tFlatSourceQ3PairProductH1 Q β L e n m ij.1
        c • (u.grad_memL2_normalizedCubeMeasure ij.2).toLp
          (fun x => u.grad x ij.2))

/-- The separated finite source sum of the H¹ pair modes. Its two finite sums
retain the common Gaussian coordinates. -/
noncomputable def tFlatSourceQ3FiniteH1PairExpansion
    (Q : TriadicCube 2) (β : ℝ) (L : {l : ℝ // 0 < l})
    (e : Vec 2) (N : ℕ) (ω : ℕ → ℝ) (i : Fin 2) :
    H1Function (openCubeSet Q) :=
  ∑ n : Fin N, ω n.val • ∑ m : Fin N, ω m.val •
    tFlatSourceQ3PairProductH1 Q β L e n.val m.val i

/-- The separated H¹ pair sum has the actual finite source product as its
value representative. -/
theorem flat_source_q3_finite_h1_pair_expansion_toFun
    (Q : TriadicCube 2) (β : ℝ) (L : {l : ℝ // 0 < l})
    (e : Vec 2) (N : ℕ) (ω : ℕ → ℝ) (i : Fin 2) (x : Vec 2) :
    (tFlatSourceQ3FiniteH1PairExpansion Q β L e N ω i).toFun x =
      (flatSourceQ3FiniteProductComponent Q β L e N ω i).toFun x := by
  simp only [tFlatSourceQ3FiniteH1PairExpansion,
    h1_fintype_sum_smul_value,
    flat_source_q3_pair_product_h1_toFun]
  rw [flat_source_q3_finite_product_component_toFun]
  change _ = flatSourceQ3FiniteScalar β L N ω x *
    flatSourceQ3FiniteProjectedComponent Q β L e N ω i x
  rw [flat_source_q3_finite_projected_component_value]
  simp only [flatSourceQ3FiniteScalar, flatSourceQ3FiniteValueMode]
  rw [gaussianScalarPartialSum_fin, gaussianScalarPartialSum_fin]
  exact weighted_pair_sum_factor (fun n : Fin N => ω n.val)
    (fun n => flatSourceQ3FiniteValueMode β L n.val x)
    (fun m => flatSourceQ3FiniteProjectedMode Q β L e i m.val x)

/-- The separated H¹ pair sum has the actual weak gradient of the finite
source product. -/
theorem flat_source_q3_finite_h1_pair_expansion_grad
    (Q : TriadicCube 2) (β : ℝ) (L : {l : ℝ // 0 < l})
    (e : Vec 2) (N : ℕ) (ω : ℕ → ℝ) (i j : Fin 2) (x : Vec 2) :
    (tFlatSourceQ3FiniteH1PairExpansion Q β L e N ω i).grad x j =
      (flatSourceQ3FiniteProductComponent Q β L e N ω i).grad x j := by
  simp only [tFlatSourceQ3FiniteH1PairExpansion,
    h1_fintype_sum_smul_gradient,
    flat_source_q3_pair_product_h1_grad]
  rw [flat_source_q3_finite_product_gradient_formula]
  simp only [gaussianScalarPartialSum_fin]
  exact weighted_pair_sum_factor_add (fun n : Fin N => ω n.val)
    (fun n => flatSourceQ3FiniteValueMode β L n.val x)
    (fun n => flatSourceQ3FiniteValueDerivativeMode β L j n.val x)
    (fun m => flatSourceQ3FiniteProjectedGradientMode Q β L e i j m.val x)
    (fun m => flatSourceQ3FiniteProjectedMode Q β L e i m.val x)

/-- The six normalized-cell L² coordinates of the separated H¹ pair sum. -/
noncomputable def tFlatSourceQ3FiniteH1PairExpansionVector
    (Q : TriadicCube 2) (β : ℝ) (L : {l : ℝ // 0 < l})
    (e : Vec 2) (N : ℕ) (ω : ℕ → ℝ) : tFlatSourceH1ChaosSpace Q := by
  let c : ℝ := (467 / 1000 : ℝ) * tileSide Q
  exact WithLp.toLp 2 (fun a : tFlatSourceH1ChaosIndex =>
    match a with
    | Sum.inl i =>
        let u := tFlatSourceQ3FiniteH1PairExpansion Q β L e N ω i
        u.memL2_normalizedCubeMeasure.toLp u.toFun
    | Sum.inr ij =>
        let u := tFlatSourceQ3FiniteH1PairExpansion Q β L e N ω ij.1
        c • (u.grad_memL2_normalizedCubeMeasure ij.2).toLp
          (fun x => u.grad x ij.2))

/-- The actual finite source product as its value and scaled-gradient L²
coordinates. -/
noncomputable def tFlatSourceQ3FiniteH1ProductVector
    (Q : TriadicCube 2) (β : ℝ) (L : {l : ℝ // 0 < l})
    (e : Vec 2) (N : ℕ) (ω : ℕ → ℝ) : tFlatSourceH1ChaosSpace Q := by
  let c : ℝ := (467 / 1000 : ℝ) * tileSide Q
  exact WithLp.toLp 2 (fun a : tFlatSourceH1ChaosIndex =>
    match a with
    | Sum.inl i =>
        let u := flatSourceQ3FiniteProductComponent Q β L e N ω i
        u.memL2_normalizedCubeMeasure.toLp u.toFun
    | Sum.inr ij =>
        let u := flatSourceQ3FiniteProductComponent Q β L e N ω ij.1
        c • (u.grad_memL2_normalizedCubeMeasure ij.2).toLp
          (fun x => u.grad x ij.2))

/-- The pair expansion's six L² classes are exactly those of the actual finite
source product and its weak gradient. -/
theorem flat_source_q3_finite_h1_pair_expansion_vector_eq_product
    (Q : TriadicCube 2) (β : ℝ) (L : {l : ℝ // 0 < l})
    (e : Vec 2) (N : ℕ) (ω : ℕ → ℝ) :
    tFlatSourceQ3FiniteH1PairExpansionVector Q β L e N ω =
      tFlatSourceQ3FiniteH1ProductVector Q β L e N ω := by
  apply PiLp.ext
  intro a
  cases a with
  | inl i =>
      change (tFlatSourceQ3FiniteH1PairExpansion Q β L e N ω i).memL2_normalizedCubeMeasure.toLp
          (tFlatSourceQ3FiniteH1PairExpansion Q β L e N ω i).toFun =
        (flatSourceQ3FiniteProductComponent Q β L e N ω i).memL2_normalizedCubeMeasure.toLp
          (flatSourceQ3FiniteProductComponent Q β L e N ω i).toFun
      apply MemLp.toLp_congr
      exact ae_of_all _ (fun x =>
        flat_source_q3_finite_h1_pair_expansion_toFun Q β L e N ω i x)
  | inr ij =>
      change ((467 / 1000 : ℝ) * tileSide Q) •
          ((tFlatSourceQ3FiniteH1PairExpansion Q β L e N ω ij.1).grad_memL2_normalizedCubeMeasure ij.2).toLp
            (fun x => (tFlatSourceQ3FiniteH1PairExpansion Q β L e N ω ij.1).grad x ij.2) =
        ((467 / 1000 : ℝ) * tileSide Q) •
          ((flatSourceQ3FiniteProductComponent Q β L e N ω ij.1).grad_memL2_normalizedCubeMeasure ij.2).toLp
            (fun x => (flatSourceQ3FiniteProductComponent Q β L e N ω ij.1).grad x ij.2)
      congr 1
      apply MemLp.toLp_congr
      exact ae_of_all _ (fun x =>
        flat_source_q3_finite_h1_pair_expansion_grad Q β L e N ω ij.1 ij.2 x)

/-- The raw pair-coefficient polynomial is the six-coordinate vector of the
separated H¹ pair expansion. -/
theorem flat_source_q3_finite_h1_raw_pair_sum_eq_expansion_vector
    (Q : TriadicCube 2) (β : ℝ) (L : {l : ℝ // 0 < l})
    (e : Vec 2) (N : ℕ) (ω : ℕ → ℝ) :
    (∑ n : Fin N, ∑ m : Fin N,
      (ω n.val * ω m.val) • tFlatSourceQ3PairEnergyVector Q β L e n.val m.val) =
      tFlatSourceQ3FiniteH1PairExpansionVector Q β L e N ω := by
  calc
    _ = ∑ n : Fin N, ω n.val • ∑ m : Fin N, ω m.val •
        tFlatSourceQ3PairEnergyVector Q β L e n.val m.val := by
      simp_rw [← smul_smul, ← Finset.smul_sum]
    _ = tFlatSourceQ3FiniteH1PairExpansionVector Q β L e N ω := by
      apply WithLp.ofLp_injective 2
      funext a
      simp only [tFlatSourceQ3FiniteH1PairExpansionVector,
        tFlatSourceQ3PairEnergyVector, WithLp.ofLp_toLp,
        WithLp.ofLp_smul, WithLp.ofLp_sum, Finset.sum_apply,
        Pi.smul_apply]
      cases a with
      | inl i =>
          change (∑ n : Fin N, ω n.val • ∑ m : Fin N, ω m.val •
              (tFlatSourceQ3PairProductH1 Q β L e n.val m.val i).memL2_normalizedCubeMeasure.toLp
                (tFlatSourceQ3PairProductH1 Q β L e n.val m.val i).toFun) =
            (tFlatSourceQ3FiniteH1PairExpansion Q β L e N ω i).memL2_normalizedCubeMeasure.toLp
              (tFlatSourceQ3FiniteH1PairExpansion Q β L e N ω i).toFun
          have hinner (n : Fin N) :
              (∑ m : Fin N, ω m.val •
                (tFlatSourceQ3PairProductH1 Q β L e n.val m.val i).memL2_normalizedCubeMeasure.toLp
                  (tFlatSourceQ3PairProductH1 Q β L e n.val m.val i).toFun) =
                (∑ m : Fin N, ω m.val •
                  tFlatSourceQ3PairProductH1 Q β L e n.val m.val i).memL2_normalizedCubeMeasure.toLp
                    (∑ m : Fin N, ω m.val •
                      tFlatSourceQ3PairProductH1 Q β L e n.val m.val i).toFun :=
            h1_fintype_sum_value_toLp Q (fun m : Fin N => ω m.val)
              (fun m => tFlatSourceQ3PairProductH1 Q β L e n.val m.val i)
          simp_rw [hinner]
          exact h1_fintype_sum_value_toLp Q (fun n : Fin N => ω n.val)
            (fun n => ∑ m : Fin N, ω m.val •
              tFlatSourceQ3PairProductH1 Q β L e n.val m.val i)
      | inr ij =>
          let c : ℝ := (467 / 1000 : ℝ) * tileSide Q
          change (∑ n : Fin N, ω n.val • ∑ m : Fin N, ω m.val •
              (c • ((tFlatSourceQ3PairProductH1 Q β L e n.val m.val ij.1).grad_memL2_normalizedCubeMeasure ij.2).toLp
                (fun x => (tFlatSourceQ3PairProductH1 Q β L e n.val m.val ij.1).grad x ij.2))) =
            c • ((tFlatSourceQ3FiniteH1PairExpansion Q β L e N ω ij.1).grad_memL2_normalizedCubeMeasure ij.2).toLp
              (fun x => (tFlatSourceQ3FiniteH1PairExpansion Q β L e N ω ij.1).grad x ij.2)
          rw [double_finite_sum_smul_commute]
          congr 1
          have hinner (n : Fin N) :
              (∑ m : Fin N, ω m.val •
                ((tFlatSourceQ3PairProductH1 Q β L e n.val m.val ij.1).grad_memL2_normalizedCubeMeasure ij.2).toLp
                  (fun x => (tFlatSourceQ3PairProductH1 Q β L e n.val m.val ij.1).grad x ij.2)) =
                ((∑ m : Fin N, ω m.val •
                  tFlatSourceQ3PairProductH1 Q β L e n.val m.val ij.1).grad_memL2_normalizedCubeMeasure ij.2).toLp
                    (fun x => (∑ m : Fin N, ω m.val •
                      tFlatSourceQ3PairProductH1 Q β L e n.val m.val ij.1).grad x ij.2) :=
            h1_fintype_sum_gradient_toLp Q (fun m : Fin N => ω m.val)
              (fun m => tFlatSourceQ3PairProductH1 Q β L e n.val m.val ij.1) ij.2
          simp_rw [hinner]
          exact h1_fintype_sum_gradient_toLp Q (fun n : Fin N => ω n.val)
            (fun n => ∑ m : Fin N, ω m.val •
              tFlatSourceQ3PairProductH1 Q β L e n.val m.val ij.1) ij.2

/-- Adding the diagonal trace turns a centered Hilbert quadratic into its
ordinary uncentered finite-mode polynomial. -/
theorem finite_hilbert_quadratic_add_diagonal
    {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    {N : ℕ} (B : Fin N → Fin N → W) (x : EuclideanSpace ℝ (Fin N)) :
    (∑ i : Fin N, B i i) + finiteHilbertGaussianQuadratic B x =
      ∑ i : Fin N, ∑ j : Fin N, (x i * x j) • B i j := by
  unfold finiteHilbertGaussianQuadratic
  simp_rw [sub_smul, Finset.sum_sub_distrib]
  have hdiag :
      (∑ i : Fin N, ∑ j : Fin N,
        (if i = j then (1 : ℝ) else 0) • B i j) =
        ∑ i : Fin N, B i i := by
    simp [Finset.mem_univ]
  rw [hdiag]
  abel

private theorem finite_hilbert_quadratic_uncentered_symmetrize
    {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    {N : ℕ} (B : Fin N → Fin N → W) (x : EuclideanSpace ℝ (Fin N)) :
    (∑ i : Fin N, ∑ j : Fin N,
      (x i * x j) • hilbertQuadraticSymmetrization B i j) =
      ∑ i : Fin N, ∑ j : Fin N, (x i * x j) • B i j := by
  let A : W := ∑ i : Fin N, ∑ j : Fin N, (x i * x j) • B i j
  let T : W := ∑ i : Fin N, ∑ j : Fin N, (x i * x j) • B j i
  have hT : T = A := by
    dsimp [T, A]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    congr 1
    ring
  have hfactor (C : Fin N → Fin N → W) :
      (∑ i : Fin N, x i • ∑ j : Fin N, x j • C i j) =
        ∑ i : Fin N, ∑ j : Fin N, (x i * x j) • C i j := by
    simp only [Finset.smul_sum, smul_smul]
  have hExpand :
      (∑ i : Fin N, ∑ j : Fin N,
        (x i * x j) • ((1 / 2 : ℝ) • (B i j + B j i))) =
        (1 / 2 : ℝ) • (A + T) := by
    simp_rw [smul_smul]
    simp_rw [show ∀ i j : Fin N,
      (x i * x j) * (1 / 2 : ℝ) = (1 / 2 : ℝ) * (x i * x j) by
        intro i j
        ring]
    simp_rw [smul_add]
    simp only [Finset.sum_add_distrib]
    simp_rw [← smul_smul, ← Finset.smul_sum]
    dsimp [A, T]
    rw [← hfactor B, ← hfactor (fun i j => B j i)]
  change (∑ i : Fin N, ∑ j : Fin N,
      (x i * x j) • ((1 / 2 : ℝ) • (B i j + B j i))) = A
  calc
    _ = (1 / 2 : ℝ) • (A + T) := hExpand
    _ = A := by
      rw [hT, smul_add, ← add_smul]
      norm_num

/-- The coefficient matrix for the finite source Hilbert quadratic. -/
noncomputable def tFlatSourceQ3FiniteH1Coefficient
    (Q : TriadicCube 2) (β : ℝ) (L : {l : ℝ // 0 < l})
    (e : Vec 2) (N : ℕ) : Fin N → Fin N → tFlatSourceH1ChaosSpace Q :=
  fun n m => tFlatSourceQ3PairEnergyVector Q β L e n.val m.val

noncomputable def tFlatSourceQ3FiniteH1SymmetricCoefficient
    (Q : TriadicCube 2) (β : ℝ) (L : {l : ℝ // 0 < l})
    (e : Vec 2) (N : ℕ) : Fin N → Fin N → tFlatSourceH1ChaosSpace Q :=
  hilbertQuadraticSymmetrization
    (tFlatSourceQ3FiniteH1Coefficient Q β L e N)

noncomputable def tFlatSourceQ3FiniteH1Mean
    (Q : TriadicCube 2) (β : ℝ) (L : {l : ℝ // 0 < l})
    (e : Vec 2) (N : ℕ) : tFlatSourceH1ChaosSpace Q :=
  ∑ n : Fin N, tFlatSourceQ3FiniteH1SymmetricCoefficient Q β L e N n n

theorem flat_source_q3_finite_h1_symmetric_coefficient
    (Q : TriadicCube 2) (β : ℝ) (L : {l : ℝ // 0 < l})
    (e : Vec 2) (N : ℕ) (n m : Fin N) :
    tFlatSourceQ3FiniteH1SymmetricCoefficient Q β L e N n m =
      tFlatSourceQ3FiniteH1SymmetricCoefficient Q β L e N m n := by
  exact hilbert_quadratic_symmetrization_symmetric _ _ _

/-- The centered Gaussian envelope's vector field is exactly the uncentered
finite pair-mode polynomial. -/
theorem flat_source_q3_finite_h1_envelope_field
    (Q : TriadicCube 2) (β : ℝ) (L : {l : ℝ // 0 < l})
    (e : Vec 2) (N : ℕ) (x : EuclideanSpace ℝ (Fin N)) :
    tFlatSourceQ3FiniteH1Mean Q β L e N +
      finiteHilbertGaussianQuadratic
        (tFlatSourceQ3FiniteH1SymmetricCoefficient Q β L e N) x =
      ∑ n : Fin N, ∑ m : Fin N,
        (x n * x m) • tFlatSourceQ3FiniteH1Coefficient Q β L e N n m := by
  calc
    _ = ∑ n : Fin N, ∑ m : Fin N,
          (x n * x m) •
            tFlatSourceQ3FiniteH1SymmetricCoefficient Q β L e N n m :=
      finite_hilbert_quadratic_add_diagonal _ x
    _ = ∑ n : Fin N, ∑ m : Fin N,
          (x n * x m) • tFlatSourceQ3FiniteH1Coefficient Q β L e N n m :=
      finite_hilbert_quadratic_uncentered_symmetrize _ x

/-- The raw finite q3 coefficient polynomial is the actual finite source
H¹ vector, including all two value and four scaled gradient
coordinates. -/
theorem flat_source_q3_finite_h1_raw_pair_sum_eq_product_vector
    (Q : TriadicCube 2) (β : ℝ) (L : {l : ℝ // 0 < l})
    (e : Vec 2) (N : ℕ) (ω : ℕ → ℝ) :
    (∑ n : Fin N, ∑ m : Fin N,
      (ω n.val * ω m.val) • tFlatSourceQ3PairEnergyVector Q β L e n.val m.val) =
      tFlatSourceQ3FiniteH1ProductVector Q β L e N ω := by
  calc
    _ = tFlatSourceQ3FiniteH1PairExpansionVector Q β L e N ω :=
      flat_source_q3_finite_h1_raw_pair_sum_eq_expansion_vector Q β L e N ω
    _ = tFlatSourceQ3FiniteH1ProductVector Q β L e N ω :=
      flat_source_q3_finite_h1_pair_expansion_vector_eq_product Q β L e N ω

/-- The finite Hilbert Gaussian envelope for the q3 H¹ coefficient matrix is
the squared spatial H¹-vector norm of the actual finite source product. -/
theorem flat_source_q3_finite_h1_envelope_eq_product_norm_sq
    (Q : TriadicCube 2) (β : ℝ) (L : {l : ℝ // 0 < l})
    (e : Vec 2) (N : ℕ) (ω : ℕ → ℝ) :
    finiteHilbertGaussianEnvelope
        (tFlatSourceQ3FiniteH1Mean Q β L e N)
        (tFlatSourceQ3FiniteH1SymmetricCoefficient Q β L e N)
        (WithLp.toLp 2 (fun n : Fin N => ω n.val)) =
      ‖tFlatSourceQ3FiniteH1ProductVector Q β L e N ω‖ ^ 2 := by
  unfold finiteHilbertGaussianEnvelope
  rw [flat_source_q3_finite_h1_envelope_field]
  have hcoords (n : Fin N) :
      (WithLp.toLp 2 (fun i : Fin N => ω i.val)) n = ω n.val := rfl
  rw [show (∑ n : Fin N, ∑ m : Fin N,
        ((WithLp.toLp 2 (fun i : Fin N => ω i.val)) n *
            (WithLp.toLp 2 (fun i : Fin N => ω i.val)) m) •
          tFlatSourceQ3FiniteH1Coefficient Q β L e N n m) =
      ∑ n : Fin N, ∑ m : Fin N,
        (ω n.val * ω m.val) •
          tFlatSourceQ3PairEnergyVector Q β L e n.val m.val by
        apply Finset.sum_congr rfl
        intro n hn
        apply Finset.sum_congr rfl
        intro m hm
        simp [tFlatSourceQ3FiniteH1Coefficient, hcoords]]
  exact congrArg (fun v : tFlatSourceH1ChaosSpace Q => ‖v‖ ^ 2)
    (flat_source_q3_finite_h1_raw_pair_sum_eq_product_vector Q β L e N ω)

/-- The squared Hilbert norm of the finite H¹ vector is the normalized-cell
value energy plus its scaled weak-gradient energy. -/
private theorem h1_toLp_norm_sq_eq_energy
    (Q : TriadicCube 2) (u : H1Function (openCubeSet Q)) :
    ‖u.memL2_normalizedCubeMeasure.toLp u.toFun‖ ^ 2 =
      energy Q (fun x => u.toFun x) := by
  rw [lp_two_norm_sq_eq_integral]
  rw [energy_eq_integral_sq Q (fun x => u.toFun x)]
  apply integral_congr_ae
  filter_upwards [u.memL2_normalizedCubeMeasure.coeFn_toLp] with x hx
  rw [hx, Real.norm_eq_abs, sq_abs]

private theorem h1_grad_toLp_norm_sq_eq_energy
    (Q : TriadicCube 2) (u : H1Function (openCubeSet Q)) (j : Fin 2) :
    ‖(u.grad_memL2_normalizedCubeMeasure j).toLp (fun x => u.grad x j)‖ ^ 2 =
      energy Q (fun x => u.grad x j) := by
  rw [lp_two_norm_sq_eq_integral]
  rw [energy_eq_integral_sq Q (fun x => u.grad x j)]
  apply integral_congr_ae
  filter_upwards [
    (u.grad_memL2_normalizedCubeMeasure j).coeFn_toLp] with x hx
  rw [hx, Real.norm_eq_abs, sq_abs]

theorem flat_source_q3_finite_h1_product_vector_norm_sq_eq_energy
    (Q : TriadicCube 2) (β : ℝ) (L : {l : ℝ // 0 < l})
    (e : Vec 2) (N : ℕ) (ω : ℕ → ℝ) :
    ‖tFlatSourceQ3FiniteH1ProductVector Q β L e N ω‖ ^ 2 =
      (∑ i : Fin 2, energy Q (fun x =>
        (flatSourceQ3FiniteProductComponent Q β L e N ω i).toFun x)) +
      (467 / 1000 : ℝ) ^ 2 * tileSide Q ^ 2 *
        ∑ i : Fin 2, ∑ j : Fin 2, energy Q (fun x =>
          (flatSourceQ3FiniteProductComponent Q β L e N ω i).grad x j) := by
  have hnorm :
      ‖tFlatSourceQ3FiniteH1ProductVector Q β L e N ω‖ ^ 2 =
        (∑ i : Fin 2,
          ‖(flatSourceQ3FiniteProductComponent Q β L e N ω i).memL2_normalizedCubeMeasure.toLp
              (flatSourceQ3FiniteProductComponent Q β L e N ω i).toFun‖ ^ 2) +
          ∑ i : Fin 2, ∑ j : Fin 2,
            ‖((467 / 1000 : ℝ) * tileSide Q) •
              ((flatSourceQ3FiniteProductComponent Q β L e N ω i).grad_memL2_normalizedCubeMeasure j).toLp
                (fun x => (flatSourceQ3FiniteProductComponent Q β L e N ω i).grad x j)‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    simp [tFlatSourceQ3FiniteH1ProductVector, Fintype.sum_sum_type,
      Fintype.sum_prod_type]
  have hscaled (i j : Fin 2) :
      ‖((467 / 1000 : ℝ) * tileSide Q) •
        ((flatSourceQ3FiniteProductComponent Q β L e N ω i).grad_memL2_normalizedCubeMeasure j).toLp
          (fun x => (flatSourceQ3FiniteProductComponent Q β L e N ω i).grad x j)‖ ^ 2 =
        (467 / 1000 : ℝ) ^ 2 * tileSide Q ^ 2 *
          energy Q (fun x => (flatSourceQ3FiniteProductComponent Q β L e N ω i).grad x j) := by
    have hc : 0 ≤ (467 / 1000 : ℝ) * tileSide Q :=
      mul_nonneg (by norm_num) (tileSide_pos Q).le
    calc
      _ = (((467 / 1000 : ℝ) * tileSide Q) ^ 2) *
          ‖((flatSourceQ3FiniteProductComponent Q β L e N ω i).grad_memL2_normalizedCubeMeasure j).toLp
            (fun x => (flatSourceQ3FiniteProductComponent Q β L e N ω i).grad x j)‖ ^ 2 := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hc, mul_pow]
      _ = (467 / 1000 : ℝ) ^ 2 * tileSide Q ^ 2 *
          energy Q (fun x => (flatSourceQ3FiniteProductComponent Q β L e N ω i).grad x j) := by
        rw [h1_grad_toLp_norm_sq_eq_energy Q]
        ring
  calc
    _ = (∑ i : Fin 2,
          ‖(flatSourceQ3FiniteProductComponent Q β L e N ω i).memL2_normalizedCubeMeasure.toLp
              (flatSourceQ3FiniteProductComponent Q β L e N ω i).toFun‖ ^ 2) +
          ∑ i : Fin 2, ∑ j : Fin 2,
            ‖((467 / 1000 : ℝ) * tileSide Q) •
              ((flatSourceQ3FiniteProductComponent Q β L e N ω i).grad_memL2_normalizedCubeMeasure j).toLp
                (fun x => (flatSourceQ3FiniteProductComponent Q β L e N ω i).grad x j)‖ ^ 2 := hnorm
    _ = (∑ i : Fin 2, energy Q (fun x =>
          (flatSourceQ3FiniteProductComponent Q β L e N ω i).toFun x)) +
          (467 / 1000 : ℝ) ^ 2 * tileSide Q ^ 2 *
            ∑ i : Fin 2, ∑ j : Fin 2, energy Q (fun x =>
              (flatSourceQ3FiniteProductComponent Q β L e N ω i).grad x j) := by
      congr 1
      · apply Finset.sum_congr rfl
        intro i hi
        exact h1_toLp_norm_sq_eq_energy Q
          (flatSourceQ3FiniteProductComponent Q β L e N ω i)
      · simp_rw [hscaled]
        calc
          (∑ i : Fin 2, ∑ j : Fin 2,
              (467 / 1000 : ℝ) ^ 2 * tileSide Q ^ 2 *
                energy Q (fun x =>
                  (flatSourceQ3FiniteProductComponent Q β L e N ω i).grad x j)) =
              ∑ i : Fin 2, (467 / 1000 : ℝ) ^ 2 * tileSide Q ^ 2 *
                ∑ j : Fin 2, energy Q (fun x =>
                  (flatSourceQ3FiniteProductComponent Q β L e N ω i).grad x j) := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [← Finset.mul_sum]
          _ = (467 / 1000 : ℝ) ^ 2 * tileSide Q ^ 2 *
              ∑ i : Fin 2, ∑ j : Fin 2, energy Q (fun x =>
                (flatSourceQ3FiniteProductComponent Q β L e N ω i).grad x j) := by
            rw [← Finset.mul_sum]

/-- The expected squared H¹-vector norm of the finite q3 product retains the
sharp finite value trace and the actual weak-gradient trace. -/
theorem flat_source_q3_finite_h1_product_vector_expected_norm_sq_le
    (Q : TriadicCube 2) {a₀ b₀ c₀ d₀ : ℝ}
    (hab : a₀ < b₀) (hcd : c₀ < d₀)
    (hQ : openCubeSet Q ⊆ openRectangle a₀ b₀ c₀ d₀)
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (e : Vec 2) (he : Book.Ch02.vecNorm e = 1) (k : ℤ) (N : ℕ) :
    let β := q3ModelAmplitude M h k
    let L := q3ModelLength k
    Integrable (fun ω : ℕ → ℝ =>
      ‖tFlatSourceQ3FiniteH1ProductVector Q β L e N ω‖ ^ 2)
      standardGaussianInfinitePi ∧
    (∫ ω, ‖tFlatSourceQ3FiniteH1ProductVector Q β L e N ω‖ ^ 2
      ∂standardGaussianInfinitePi) ≤
      (3 / 2 : ℝ) * β ^ 4 +
        (467 / 1000 : ℝ) ^ 2 * tileSide Q ^ 2 *
          ((936 / 5 : ℝ) * β ^ 4 / L.1 ^ 2) := by
  classical
  let β := q3ModelAmplitude M h k
  let L := q3ModelLength k
  let dirs := q3H3Directions a₀ b₀ c₀ d₀ β L whiteBasis
  let V : (ℕ → ℝ) → HilbertVectorL2 (openCubeSet Q) := fun ω =>
    flatSourceQ3ValueLInf Q hab hcd β L
        (gaussianPartialSum dirs N ω) •
      flatSourceQ3ProjectedL2 Q hab hcd e β L
        (gaussianPartialSum dirs N ω)
  let G : (ℕ → ℝ) → ℝ := fun ω =>
    ∫ x, ∑ i : Fin 2, ∑ j : Fin 2,
      (flatSourceQ3FiniteProductComponent Q β L e N ω i).grad x j ^ 2
      ∂volumeMeasureOn (openCubeSet Q)
  let C : ℝ := (467 / 1000 : ℝ) ^ 2 * tileSide Q ^ 2
  let R : (ℕ → ℝ) → ℝ := fun ω =>
    (cubeVolume Q)⁻¹ * ‖V ω‖ ^ 2 + C * (cubeVolume Q)⁻¹ * G ω
  have hVnorm := flat_source_q3_finite_product_expected_norm_sq_le
    Q hab hcd hQ M h hM e he k N
  have hβsq : β ^ 2 = h ^ 2 * (3 : ℝ) ^ (2 * M.gamma * (k : ℝ)) := by
    dsimp [β]
    exact q3ModelAmplitude_sq M h k
  have hβfour : β ^ 4 =
      (h ^ 2 * (3 : ℝ) ^ (2 * M.gamma * (k : ℝ))) ^ 2 := by
    calc
      β ^ 4 = (β ^ 2) ^ 2 := by ring
      _ = _ := congrArg (fun x : ℝ => x ^ 2) hβsq
  have hVnorm' : Integrable (fun ω => ‖V ω‖ ^ 2) standardGaussianInfinitePi ∧
      (∫ ω, ‖V ω‖ ^ 2 ∂standardGaussianInfinitePi) ≤
        (3 / 2 : ℝ) * (volume (openCubeSet Q)).toReal * β ^ 4 := by
    simpa [V, β, L, dirs, hβfour] using hVnorm
  have hgrad := flat_source_q3_finite_product_gradient_trace_bound
    Q hab hcd hQ M h hM e he k N
  have hgrad' : Integrable G standardGaussianInfinitePi ∧
      (∫ ω, G ω ∂standardGaussianInfinitePi) ≤
        (volume (openCubeSet Q)).toReal *
          ((936 / 5 : ℝ) * β ^ 4 / L.1 ^ 2) := by
    simpa [G, β, L] using hgrad
  have hvol : (volume (openCubeSet Q)).toReal = cubeVolume Q := by
    rw [volume_openCubeSet_toReal]
  have henergy (ω : ℕ → ℝ) :
      (∑ i : Fin 2, energy Q (fun x =>
        (flatSourceQ3FiniteProductComponent Q β L e N ω i).toFun x)) =
        (cubeVolume Q)⁻¹ * ‖V ω‖ ^ 2 := by
    let Vω := V ω
    let Vplain := hilbertVectorL2ToVectorL2 (U := openCubeSet Q) Vω
    let W : Vec 2 → Vec 2 := fun x => Vplain x
    have hW : MemVectorL2 (openCubeSet Q) W := by
      change MemLp Vplain 2 (volumeMeasureOn (openCubeSet Q))
      exact MeasureTheory.Lp.memLp Vplain
    have hWclass : toHilbertVectorL2OfVecField hW = Vω := by
      calc
        toHilbertVectorL2OfVecField hW =
            vectorL2ToHilbertVectorL2 (U := openCubeSet Q) (toVectorL2 hW) := by
          exact (vectorL2ToHilbertVectorL2_toVectorL2 hW).symm
        _ = vectorL2ToHilbertVectorL2 (U := openCubeSet Q) Vplain := by
          congr 1
          apply Lp.ext
          exact hW.coeFn_toLp
        _ = Vω := vectorL2ToHilbertVectorL2_hilbertVectorL2ToVectorL2 Vω
    have hVint : ‖Vω‖ ^ 2 =
        ∫ x in openCubeSet Q, vecDot (W x) (W x) ∂volume := by
      calc
        ‖Vω‖ ^ 2 = inner ℝ Vω Vω := (real_inner_self_eq_norm_sq Vω).symm
        _ = inner ℝ (toHilbertVectorL2OfVecField hW)
              (toHilbertVectorL2OfVecField hW) := by rw [hWclass]
        _ = ∫ x in openCubeSet Q, vecDot (W x) (W x) ∂volume :=
          inner_toHilbertVectorL2OfVecField_eq_integral hW hW
    have hcoords : ∀ᵐ x ∂volumeMeasureOn (openCubeSet Q), ∀ i : Fin 2,
        W x i = (flatSourceQ3FiniteProductComponent Q β L e N ω i).toFun x := by
      rw [ae_all_iff]
      intro i
      filter_upwards [coeFn_hilbertVectorL2ToVectorL2 (U := openCubeSet Q) Vω,
        flat_source_q3_finite_product_component_ae
          Q hab hcd hQ e N ω β L i] with x hxV hxU
      simpa [W, Vplain] using congrArg (fun z : Vec 2 => z i) hxV |>.trans hxU
    calc
      _ = ∑ i : Fin 2, ∫ x,
            (flatSourceQ3FiniteProductComponent Q β L e N ω i).toFun x ^ 2
              ∂normalizedCubeMeasure Q := by
        apply Finset.sum_congr rfl
        intro i hi
        exact energy_eq_integral_sq Q _
      _ = (cubeVolume Q)⁻¹ * ∑ i : Fin 2, ∫ x in openCubeSet Q,
            (flatSourceQ3FiniteProductComponent Q β L e N ω i).toFun x ^ 2
              ∂volume := by
        simp_rw [integral_normalized_eq_open]
        rw [← Finset.mul_sum]
      _ = (cubeVolume Q)⁻¹ * ∫ x in openCubeSet Q,
            ∑ i : Fin 2,
              (flatSourceQ3FiniteProductComponent Q β L e N ω i).toFun x ^ 2
              ∂volume := by
        congr 1
        symm
        rw [integral_finsetSum Finset.univ (fun i _ =>
          integrableOn_of_integrable_normalizedCubeMeasure Q
            (flatSourceQ3FiniteProductComponent Q β L e N ω i).memL2_normalizedCubeMeasure.integrable_sq |>.mono_set
              (openCubeSet_subset_cubeSet Q))]
      _ = (cubeVolume Q)⁻¹ * ‖Vω‖ ^ 2 := by
        congr 1
        calc
          (∫ x in openCubeSet Q, ∑ i : Fin 2,
              (flatSourceQ3FiniteProductComponent Q β L e N ω i).toFun x ^ 2
              ∂volume) =
              ∫ x in openCubeSet Q, vecDot (W x) (W x) ∂volume := by
            apply integral_congr_ae
            filter_upwards [hcoords] with x hx
            simp [vecDot, Fin.sum_univ_two, pow_two, hx]
          _ = ‖Vω‖ ^ 2 := hVint.symm
  have hgradEnergy (ω : ℕ → ℝ) :
      (∑ i : Fin 2, ∑ j : Fin 2, energy Q (fun x =>
        (flatSourceQ3FiniteProductComponent Q β L e N ω i).grad x j)) =
        (cubeVolume Q)⁻¹ * G ω := by
    calc
      _ = ∑ i : Fin 2, ∑ j : Fin 2, ∫ x,
            (flatSourceQ3FiniteProductComponent Q β L e N ω i).grad x j ^ 2
              ∂normalizedCubeMeasure Q := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        exact energy_eq_integral_sq Q _
      _ = (cubeVolume Q)⁻¹ * ∑ i : Fin 2, ∑ j : Fin 2, ∫ x in openCubeSet Q,
            (flatSourceQ3FiniteProductComponent Q β L e N ω i).grad x j ^ 2
              ∂volume := by
        simp_rw [integral_normalized_eq_open]
        calc
          (∑ i : Fin 2, ∑ j : Fin 2,
              (cubeVolume Q)⁻¹ * ∫ x in openCubeSet Q,
                (flatSourceQ3FiniteProductComponent Q β L e N ω i).grad x j ^ 2
                  ∂volume) =
              ∑ i : Fin 2, (cubeVolume Q)⁻¹ * ∑ j : Fin 2,
                ∫ x in openCubeSet Q,
                  (flatSourceQ3FiniteProductComponent Q β L e N ω i).grad x j ^ 2
                    ∂volume := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [← Finset.mul_sum]
          _ = (cubeVolume Q)⁻¹ * ∑ i : Fin 2, ∑ j : Fin 2,
                ∫ x in openCubeSet Q,
                  (flatSourceQ3FiniteProductComponent Q β L e N ω i).grad x j ^ 2
                    ∂volume := by rw [← Finset.mul_sum]
      _ = (cubeVolume Q)⁻¹ * G ω := by
        dsimp [G]
        congr 1
        symm
        rw [integral_finsetSum Finset.univ (fun i _ =>
          integrable_finsetSum Finset.univ (fun j _ =>
            (integrableOn_of_integrable_normalizedCubeMeasure Q
              ((flatSourceQ3FiniteProductComponent Q β L e N ω i).grad_memL2_normalizedCubeMeasure j).integrable_sq).mono_set
                (openCubeSet_subset_cubeSet Q)))]
        apply Finset.sum_congr rfl
        intro i hi
        rw [integral_finsetSum Finset.univ (fun j _ =>
          (integrableOn_of_integrable_normalizedCubeMeasure Q
            ((flatSourceQ3FiniteProductComponent Q β L e N ω i).grad_memL2_normalizedCubeMeasure j).integrable_sq).mono_set
              (openCubeSet_subset_cubeSet Q))]
  have hnormEq (ω : ℕ → ℝ) :
      ‖tFlatSourceQ3FiniteH1ProductVector Q β L e N ω‖ ^ 2 = R ω := by
    rw [flat_source_q3_finite_h1_product_vector_norm_sq_eq_energy,
      henergy, hgradEnergy]
    dsimp [R, C]
    ring
  have hRint : Integrable R standardGaussianInfinitePi := by
    dsimp [R]
    exact (hVnorm'.1.const_mul _).add (hgrad'.1.const_mul _)
  have hRbound : (∫ ω, R ω ∂standardGaussianInfinitePi) ≤
      (3 / 2 : ℝ) * β ^ 4 +
        (467 / 1000 : ℝ) ^ 2 * tileSide Q ^ 2 *
          ((936 / 5 : ℝ) * β ^ 4 / L.1 ^ 2) := by
    have hcalc : (∫ ω, R ω ∂standardGaussianInfinitePi) =
        (cubeVolume Q)⁻¹ * (∫ ω, ‖V ω‖ ^ 2 ∂standardGaussianInfinitePi) +
          C * (cubeVolume Q)⁻¹ * (∫ ω, G ω ∂standardGaussianInfinitePi) := by
      dsimp [R]
      rw [integral_add (hVnorm'.1.const_mul _) (hgrad'.1.const_mul _),
        integral_const_mul, integral_const_mul]
    rw [hcalc]
    have hvolInv : 0 ≤ (cubeVolume Q)⁻¹ := inv_nonneg.mpr (cubeVolume_pos Q).le
    have hCinv : 0 ≤ C * (cubeVolume Q)⁻¹ :=
      mul_nonneg (by dsimp [C]; positivity) hvolInv
    calc
      _ ≤ (cubeVolume Q)⁻¹ *
            ((3 / 2 : ℝ) * (volume (openCubeSet Q)).toReal * β ^ 4) +
          C * (cubeVolume Q)⁻¹ *
            ((volume (openCubeSet Q)).toReal *
              ((936 / 5 : ℝ) * β ^ 4 / L.1 ^ 2)) := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left hVnorm'.2 hvolInv)
          (mul_le_mul_of_nonneg_left hgrad'.2 hCinv)
      _ = (3 / 2 : ℝ) * β ^ 4 +
          (467 / 1000 : ℝ) ^ 2 * tileSide Q ^ 2 *
            ((936 / 5 : ℝ) * β ^ 4 / L.1 ^ 2) := by
        rw [hvol]
        dsimp [C]
        field_simp [ne_of_gt (cubeVolume_pos Q)]
  have hEq :
      (fun ω : ℕ → ℝ => ‖tFlatSourceQ3FiniteH1ProductVector Q β L e N ω‖ ^ 2) =ᵐ[
        standardGaussianInfinitePi] R := ae_of_all _ hnormEq
  constructor
  · exact hRint.congr hEq.symm
  · rw [integral_congr_ae hEq]
    exact hRbound

/-- The actual finite source positive-Haar energy has an L^(128/127) bound
from the H¹ Hilbert-chaos envelope, with the sharp finite trace on its right. -/
theorem finite_tiled_energy_L128
    (Q : TriadicCube 2) {a₀ b₀ c₀ d₀ : ℝ}
    (hab : a₀ < b₀) (hcd : c₀ < d₀)
    (hQ : openCubeSet Q ⊆ openRectangle a₀ b₀ c₀ d₀)
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (e : Vec 2) (he : Book.Ch02.vecNorm e = 1) (k : ℤ) (N : ℕ)
    (T : (ℕ → ℝ) → ℝ) (hTmeas : Measurable T) (hTnonneg : ∀ ω, 0 ≤ T ω)
    (hTle : ∀ ω, T ω ≤
      (∑ i : Fin 2, energy Q (fun x =>
        (flatSourceQ3FiniteProductComponent Q (q3ModelAmplitude M h k) (q3ModelLength k) e N ω i).toFun x)) +
        (467 / 1000 : ℝ) ^ 2 * tileSide Q ^ 2 *
          ∑ i : Fin 2, ∑ j : Fin 2, energy Q (fun x =>
            (flatSourceQ3FiniteProductComponent Q (q3ModelAmplitude M h k) (q3ModelLength k) e N ω i).grad x j)) :
    let β := q3ModelAmplitude M h k
    let L := q3ModelLength k
    eLpNorm T
      (ENNReal.ofReal (128 / 127 : ℝ)) Gaussian.standardGaussianInfinitePi ≤
      ENNReal.ofReal ((513 / 500 : ℝ) *
        ((3 / 2 : ℝ) * β ^ 4 +
          (467 / 1000 : ℝ) ^ 2 * tileSide Q ^ 2 *
            ((936 / 5 : ℝ) * β ^ 4 / L.1 ^ 2))) := by
  classical
  let β := q3ModelAmplitude M h k
  let L := q3ModelLength k
  let mean := tFlatSourceQ3FiniteH1Mean Q β L e N
  let coeff := tFlatSourceQ3FiniteH1SymmetricCoefficient Q β L e N
  let Fenv : EuclideanSpace ℝ (Fin N) → ℝ :=
    finiteHilbertGaussianEnvelope mean coeff
  let F : (Fin N → ℝ) → ℝ := fun z => Fenv (WithLp.toLp 2 z)
  have hsymm : ∀ i j : Fin N, coeff i j = coeff j i := by
    intro i j
    exact flat_source_q3_finite_h1_symmetric_coefficient Q β L e N i j
  have hFenvCont : Continuous Fenv := by
    change Continuous (fun x : EuclideanSpace ℝ (Fin N) =>
      ‖mean + finiteHilbertGaussianQuadratic coeff x‖ ^ 2)
    unfold finiteHilbertGaussianQuadratic
    fun_prop
  have hF : AEStronglyMeasurable F (Gaussian.standardGaussianPi N) := by
    dsimp [F]
    exact (hFenvCont.comp (by fun_prop)).aestronglyMeasurable
  have hmap : (Gaussian.standardGaussianPi N).map (WithLp.toLp 2) =
      ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin N)) := by
    simpa [Gaussian.standardGaussianPi] using
      (ProbabilityTheory.map_pi_eq_stdGaussian (ι := Fin N))
  have htoLp : AEMeasurable (WithLp.toLp 2 :
      (Fin N → ℝ) → EuclideanSpace ℝ (Fin N)) (Gaussian.standardGaussianPi N) :=
    (PiLp.continuous_toLp (p := (2 : ℝ≥0∞))
      (β := fun _ : Fin N => ℝ)).aemeasurable
  have hFenvMap : AEStronglyMeasurable Fenv
      ((Gaussian.standardGaussianPi N).map (WithLp.toLp 2)) := by
    rw [hmap]
    exact hFenvCont.aestronglyMeasurable
  have hfiniteIntegral :
      (∫ x : EuclideanSpace ℝ (Fin N), Fenv x
        ∂ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin N))) =
      ∫ z : Fin N → ℝ, F z ∂Gaussian.standardGaussianPi N := by
    rw [← hmap]
    change (∫ y : EuclideanSpace ℝ (Fin N), Fenv y
        ∂(Gaussian.standardGaussianPi N).map (WithLp.toLp 2)) =
      ∫ z : Fin N → ℝ, Fenv (WithLp.toLp 2 z) ∂Gaussian.standardGaussianPi N
    exact integral_map htoLp hFenvMap
  have hfirst := Gaussian.integral_standardGaussian_firstCoordinates N F hF
  have hExpected := flat_source_q3_finite_h1_product_vector_expected_norm_sq_le
    Q hab hcd hQ M h hM e he k N
  have hEnvelopeEq (ω : ℕ → ℝ) :
      F (fun n : Fin N => ω n.val) =
        ‖tFlatSourceQ3FiniteH1ProductVector Q β L e N ω‖ ^ 2 := by
    simpa [F, Fenv, mean, coeff] using
      flat_source_q3_finite_h1_envelope_eq_product_norm_sq Q β L e N ω
  have hFiniteCap :
      (∫ x : EuclideanSpace ℝ (Fin N), Fenv x
        ∂ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin N))) ≤
        (3 / 2 : ℝ) * β ^ 4 +
          (467 / 1000 : ℝ) ^ 2 * tileSide Q ^ 2 *
            ((936 / 5 : ℝ) * β ^ 4 / L.1 ^ 2) := by
    calc
      _ = ∫ z : Fin N → ℝ, F z ∂Gaussian.standardGaussianPi N := hfiniteIntegral
      _ = ∫ ω : ℕ → ℝ, F (fun n : Fin N => ω n.val)
          ∂Gaussian.standardGaussianInfinitePi := hfirst.symm
      _ = ∫ ω : ℕ → ℝ,
          ‖tFlatSourceQ3FiniteH1ProductVector Q β L e N ω‖ ^ 2
          ∂Gaussian.standardGaussianInfinitePi := by
        apply integral_congr_ae
        exact ae_of_all _ hEnvelopeEq
      _ ≤ _ := hExpected.2
  have hEnvelopeLp := finite_hilbert_gaussian_envelope_128_bound_infinite
    mean coeff hsymm
  have hEnvelopeCap :
      eLpNorm (fun ω : ℕ → ℝ => finiteHilbertGaussianEnvelope mean coeff
          (WithLp.toLp 2 (fun i : Fin N => ω i.val)))
          (ENNReal.ofReal (128 / 127 : ℝ)) Gaussian.standardGaussianInfinitePi ≤
        ENNReal.ofReal ((513 / 500 : ℝ) *
          ((3 / 2 : ℝ) * β ^ 4 +
            (467 / 1000 : ℝ) ^ 2 * tileSide Q ^ 2 *
              ((936 / 5 : ℝ) * β ^ 4 / L.1 ^ 2))) := by
    calc
      _ ≤ ENNReal.ofReal ((513 / 500 : ℝ) *
          (∫ x : EuclideanSpace ℝ (Fin N), Fenv x
            ∂ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin N)))) := by
        simpa [mean, coeff, Fenv] using hEnvelopeLp
      _ ≤ _ := ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_left hFiniteCap (by norm_num))
  have hTenv (ω : ℕ → ℝ) :
      T ω ≤ finiteHilbertGaussianEnvelope mean coeff
        (WithLp.toLp 2 (fun i : Fin N => ω i.val)) := by
    have hhaar := hTle ω
    have hnorm := flat_source_q3_finite_h1_product_vector_norm_sq_eq_energy
      Q β L e N ω
    have hpos : T ω ≤
        ‖tFlatSourceQ3FiniteH1ProductVector Q β L e N ω‖ ^ 2 := by
      exact hhaar.trans_eq hnorm.symm
    calc
      _ ≤ ‖tFlatSourceQ3FiniteH1ProductVector Q β L e N ω‖ ^ 2 := hpos
      _ = _ := (flat_source_q3_finite_h1_envelope_eq_product_norm_sq
        Q β L e N ω).symm
  have hEnvelopeNonneg (ω : ℕ → ℝ) :
      0 ≤ finiteHilbertGaussianEnvelope mean coeff
        (WithLp.toLp 2 (fun i : Fin N => ω i.val)) := by
    unfold finiteHilbertGaussianEnvelope
    exact sq_nonneg _
  have hNormPoint : ∀ ω : ℕ → ℝ,
      ‖T ω‖ ≤ ‖finiteHilbertGaussianEnvelope mean coeff
        (WithLp.toLp 2 (fun i : Fin N => ω i.val))‖ := by
    intro ω
    rw [Real.norm_of_nonneg (hTnonneg ω),
      Real.norm_of_nonneg (hEnvelopeNonneg ω)]
    exact hTenv ω
  have hmono := eLpNorm_mono_ae (f := T)
    (g := fun ω : ℕ → ℝ => finiteHilbertGaussianEnvelope mean coeff
      (WithLp.toLp 2 (fun i : Fin N => ω i.val)))
    (μ := Gaussian.standardGaussianInfinitePi)
    (p := ENNReal.ofReal (128 / 127 : ℝ))
    hTmeas.aestronglyMeasurable (ae_of_all _ hNormPoint)
  simpa [mean, coeff] using hmono.trans hEnvelopeCap

end ASDExplicitGamma.Scalar
