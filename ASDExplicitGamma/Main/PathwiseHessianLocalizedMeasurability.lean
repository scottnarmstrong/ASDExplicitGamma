module

public import ASDExplicitGamma.Main.PathwiseHessianKernelBounds
public import ASDExplicitGamma.Main.PathwiseHessianLocalizedCovariance
public import ASDExplicitGamma.Gaussian.Q3ConvolutionRegularity
public import ASDExplicitGamma.Gaussian.HilbertBasisEnumeration
public import ASDExplicitGamma.Gaussian.ZeroPaddedOrthonormal

/-! Measurability and integrability of the actual localized q3 covariance terms. -/

@[expose] public section

namespace ASDExplicitGamma.Main

open MeasureTheory Homogenization ASDExplicitGamma.Gaussian ASDExplicitGamma.Native
  ASDExplicitGamma.Response ASDExplicitGamma.Triadic
open scoped ENNReal

/-- The actual localized DIAG q3 signed covariance term is a.e. measurable
on every descendant cell. The only noncontinuous factors are the two actual
H¹ gradients, whose cellwise L² representatives supply a.e. measurability. -/
theorem main_diag_q3_signed_localized_gradient_term_aemeasurable
    (b : ℝ) (L : {l : ℝ // 0 < l}) (Q : TriadicCube 2) (mesh : ℕ)
    (φ : H1Function (openCubeSet Q)) (U : TriadicCube 2)
    (hU : U ∈ descendantsAtDepth Q mesh) (k : ℕ) :
    AEMeasurable
      (fun x => mainDiagQ3SignedLocalizedGradientTerm b L Q mesh φ k x)
      (normalizedCubeMeasure U) := by
  let I := diagInterpolant Q mesh
  let μ := normalizedCubeMeasure U
  have hA (i : Fin 2) : MemLp (fun x => (I φ).grad x i) 2 μ :=
    memLp_on_descendant_of_memLp hU ((I φ).grad_memL2_normalizedCubeMeasure i)
  have hB (i : Fin 2) : MemLp (fun x => (φ - I φ).grad x i) 2 μ :=
    memLp_on_descendant_of_memLp hU ((φ - I φ).grad_memL2_normalizedCubeMeasure i)
  have hscale : Continuous (fun x : Vec 2 => L.1⁻¹ • x) :=
    continuous_const_smul (L.1⁻¹)
  have hP (i j : Fin 2) : Continuous (fun x : Vec 2 =>
      oldSignedProjectedWhiteKernel b L (L.1⁻¹ • x) i j) :=
    (main_old_signed_projected_white_kernel_continuous b L i j).comp hscale
  have hconv (e : WhiteNoise) : AEMeasurable
      (fun x => q3Convolution b L h3Zero e x) μ :=
    (q3Convolution_continuous b L h3Zero e).measurable.aemeasurable
  change AEMeasurable
      (fun x => q3Convolution b L h3Zero (gaussEnumerated whiteBasis k) x *
        inner ℝ (gaussEnumerated whiteBasis k)
          (∑ i : Fin 2, ∑ j : Fin 2,
            ((I φ).grad x i * (φ - I φ).grad x j) •
              oldSignedRotatedWhiteKernel b L (L.1⁻¹ • x) i j)) μ
  apply AEMeasurable.mul (hconv _)
  simp only [inner_sum, real_inner_smul_right]
  apply Finset.aemeasurable_fun_sum
  intro i hi
  apply Finset.aemeasurable_fun_sum
  intro j hj
  have hI : AEMeasurable (fun x => (I φ).grad x i) μ :=
    hA i |>.aestronglyMeasurable.aemeasurable
  have hR : AEMeasurable (fun x => (φ - I φ).grad x j) μ :=
    hB j |>.aestronglyMeasurable.aemeasurable
  have hK : AEMeasurable (fun x => inner ℝ (gaussEnumerated whiteBasis k)
      (oldSignedRotatedWhiteKernel b L (L.1⁻¹ • x) i j)) μ := by
    have hrot : Continuous (fun x : Vec 2 =>
        oldSignedRotatedWhiteKernel b L (L.1⁻¹ • x) i j) := by
      unfold oldSignedRotatedWhiteKernel
      apply continuous_finsetSum
      intro a ha
      apply continuous_finsetSum
      intro c hc
      exact (continuous_const_smul
        (responsePlanarJ i a * responsePlanarJ c j)).comp (hP a c)
    exact (continuous_const.inner hrot).measurable.aemeasurable
  exact (hI.mul hR).mul hK

/-- Each actual localized DIAG q3 signed covariance mode is integrable on a
descendant cell. The q3 convolution is uniformly bounded by its section norm;
the projected kernel is uniformly bounded in position; and the remaining
gradient products are L¹ by the two cellwise H¹ gradient bounds. -/
theorem main_diag_q3_signed_localized_gradient_term_integrable
    (b : ℝ) (L : {l : ℝ // 0 < l}) (Q : TriadicCube 2) (mesh : ℕ)
    (φ : H1Function (openCubeSet Q)) (U : TriadicCube 2)
    (hU : U ∈ descendantsAtDepth Q mesh) (k : ℕ) :
    Integrable (fun x => mainDiagQ3SignedLocalizedGradientTerm b L Q mesh φ k x)
      (normalizedCubeMeasure U) := by
  let I := diagInterpolant Q mesh
  let μ := normalizedCubeMeasure U
  let e := gaussEnumerated whiteBasis k
  let S₀ := q3Section b L h3Zero 0
  let C := ∑ a : Fin 2, ∑ c : Fin 2,
    ‖oldSignedProjectedWhiteKernel b L 0 a c‖
  have hA (i : Fin 2) : MemLp (fun x => (I φ).grad x i) 2 μ :=
    memLp_on_descendant_of_memLp hU ((I φ).grad_memL2_normalizedCubeMeasure i)
  have hB (i : Fin 2) : MemLp (fun x => (φ - I φ).grad x i) 2 μ :=
    memLp_on_descendant_of_memLp hU ((φ - I φ).grad_memL2_normalizedCubeMeasure i)
  have hS (x : Vec 2) : ‖q3Section b L h3Zero x‖ = ‖S₀‖ := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [gaussQ3Section_norm_sq, gaussQ3Section_norm_sq]
  have he : ‖e‖ ≤ 1 := by
    dsimp [e]
    exact enumerated_norm_le_one whiteBasis whiteBasis.orthonormal k
  have hkernel (i j : Fin 2) (x : Vec 2) :
      ‖oldSignedRotatedWhiteKernel b L (L.1⁻¹ • x) i j‖ ≤ C :=
    main_old_signed_rotated_white_kernel_norm_le b L _ i j
  have hvec (x : Vec 2) :
      ‖∑ i : Fin 2, ∑ j : Fin 2,
        (((I φ).grad x i * (φ - I φ).grad x j) : ℝ) •
          oldSignedRotatedWhiteKernel b L (L.1⁻¹ • x) i j‖ ≤
        ∑ i : Fin 2, ∑ j : Fin 2,
          (|(I φ).grad x i| * |(φ - I φ).grad x j| * C) := by
    calc
      _ ≤ ∑ i : Fin 2, ‖∑ j : Fin 2,
          (((I φ).grad x i * (φ - I φ).grad x j) : ℝ) •
            oldSignedRotatedWhiteKernel b L (L.1⁻¹ • x) i j‖ := norm_sum_le _ _
      _ ≤ ∑ i : Fin 2, ∑ j : Fin 2,
          ‖(((I φ).grad x i * (φ - I φ).grad x j) : ℝ) •
            oldSignedRotatedWhiteKernel b L (L.1⁻¹ • x) i j‖ := by
        apply Finset.sum_le_sum
        intro i hi
        exact norm_sum_le _ _
      _ ≤ ∑ i : Fin 2, ∑ j : Fin 2,
          (|(I φ).grad x i| * |(φ - I φ).grad x j| * C) := by
        apply Finset.sum_le_sum
        intro i hi
        apply Finset.sum_le_sum
        intro j hj
        rw [norm_smul, Real.norm_eq_abs, abs_mul]
        exact mul_le_mul_of_nonneg_left
          (hkernel i j x) (mul_nonneg (abs_nonneg _) (abs_nonneg _))
  have hconv (x : Vec 2) :
      ‖q3Convolution b L h3Zero e x‖ ≤ ‖S₀‖ := by
    rw [q3Convolution]
    calc
      ‖inner ℝ e (q3Section b L h3Zero x)‖ ≤
          ‖e‖ * ‖q3Section b L h3Zero x‖ := norm_inner_le_norm _ _
      _ ≤ 1 * ‖S₀‖ := by rw [hS x]; exact mul_le_mul_of_nonneg_right he (norm_nonneg _)
      _ = ‖S₀‖ := one_mul _
  have hinner (x : Vec 2) :
      ‖inner ℝ e
        (∑ i : Fin 2, ∑ j : Fin 2,
          (((I φ).grad x i * (φ - I φ).grad x j) : ℝ) •
            oldSignedRotatedWhiteKernel b L (L.1⁻¹ • x) i j)‖ ≤
      ‖∑ i : Fin 2, ∑ j : Fin 2,
          (((I φ).grad x i * (φ - I φ).grad x j) : ℝ) •
            oldSignedRotatedWhiteKernel b L (L.1⁻¹ • x) i j‖ := by
    calc
      _ ≤ ‖e‖ * ‖∑ i : Fin 2, ∑ j : Fin 2,
          (((I φ).grad x i * (φ - I φ).grad x j) : ℝ) •
            oldSignedRotatedWhiteKernel b L (L.1⁻¹ • x) i j‖ := norm_inner_le_norm _ _
      _ ≤ 1 * ‖∑ i : Fin 2, ∑ j : Fin 2,
          (((I φ).grad x i * (φ - I φ).grad x j) : ℝ) •
            oldSignedRotatedWhiteKernel b L (L.1⁻¹ • x) i j‖ :=
          mul_le_mul_of_nonneg_right he (norm_nonneg _)
      _ = _ := one_mul _
  have hpoint (x : Vec 2) :
      ‖mainDiagQ3SignedLocalizedGradientTerm b L Q mesh φ k x‖ ≤
        ‖S₀‖ * (∑ i : Fin 2, ∑ j : Fin 2,
          (|(I φ).grad x i| * |(φ - I φ).grad x j| * C)) := by
    rw [mainDiagQ3SignedLocalizedGradientTerm]
    calc
      _ ≤ ‖q3Convolution b L h3Zero e x‖ *
          ‖inner ℝ e (∑ i : Fin 2, ∑ j : Fin 2,
            (((I φ).grad x i * (φ - I φ).grad x j) : ℝ) •
              oldSignedRotatedWhiteKernel b L (L.1⁻¹ • x) i j)‖ := norm_mul_le _ _
      _ ≤ ‖S₀‖ * (∑ i : Fin 2, ∑ j : Fin 2,
          (|(I φ).grad x i| * |(φ - I φ).grad x j| * C)) := by
        gcongr
        · exact hconv x
        · exact hinner x |>.trans (hvec x)
  have hprod (i j : Fin 2) : Integrable
      (fun x => |(I φ).grad x i| * |(φ - I φ).grad x j|) μ := by
    have hm := (hA i).integrable_mul (hB j)
    have hn := hm.norm
    convert hn using 1
    funext x
    change |(I φ).grad x i| * |(φ - I φ).grad x j| =
      |(I φ).grad x i * (φ - I φ).grad x j|
    rw [abs_mul]
  have hmajor : Integrable (fun x => ‖S₀‖ *
      (∑ i : Fin 2, ∑ j : Fin 2,
        (|(I φ).grad x i| * |(φ - I φ).grad x j| * C))) μ := by
    have hsum (i : Fin 2) : Integrable
        (fun x => ∑ j : Fin 2,
          (|(I φ).grad x i| * |(φ - I φ).grad x j| * C)) μ := by
      apply integrable_finsetSum
      intro j hj
      have hc := (hprod i j).const_mul C
      convert hc using 1
      funext x
      ring
    have hdouble : Integrable
        (fun x => ∑ i : Fin 2, ∑ j : Fin 2,
          (|(I φ).grad x i| * |(φ - I φ).grad x j| * C)) μ := by
      apply integrable_finsetSum
      intro i hi
      exact hsum i
    exact hdouble.const_mul ‖S₀‖
  have hmeas := main_diag_q3_signed_localized_gradient_term_aemeasurable
    b L Q mesh φ U hU k
  apply hmajor.mono' hmeas.aestronglyMeasurable
  filter_upwards [] with x
  exact hpoint x

private theorem main_basis_abs_inner_product_bound
    {ι H : Type*} [Countable ι] [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (B : HilbertBasis ι ℝ H) (S K : H) :
    Summable (fun i => |inner ℝ S (B i) * inner ℝ (B i) K|) ∧
      (∑' i, |inner ℝ S (B i) * inner ℝ (B i) K|) ≤ ‖S‖ * ‖K‖ := by
  let f := B.repr S
  let g := B.repr K
  have hpq : (2 : ℝ≥0∞).toReal.HolderConjugate (2 : ℝ≥0∞).toReal := by
    rw [Real.holderConjugate_iff]
    norm_num
  have hh := lp.tsum_mul_le_mul_norm hpq f g
  have heq (i : ι) : |inner ℝ S (B i) * inner ℝ (B i) K| =
      ‖f i‖ * ‖g i‖ := by
    have hcomm : inner ℝ S (B i) = inner ℝ (B i) S := real_inner_comm _ _
    rw [hcomm, B.repr_apply_apply, B.repr_apply_apply]
    simp only [Real.norm_eq_abs, abs_mul]
  constructor
  · have heqf : (fun i => |inner ℝ S (B i) * inner ℝ (B i) K|) =
        (fun i => ‖f i‖ * ‖g i‖) := funext heq
    rw [heqf]
    exact hh.1
  · have heqf : (fun i => |inner ℝ S (B i) * inner ℝ (B i) K|) =
        (fun i => ‖f i‖ * ‖g i‖) := funext heq
    rw [heqf]
    calc
      _ ≤ ‖f‖ * ‖g‖ := hh.2
      _ = ‖S‖ * ‖K‖ := by
        rw [show f = B.repr S from rfl, show g = B.repr K from rfl,
          B.repr.norm_map, B.repr.norm_map]

private noncomputable def mainDiagQ3SignedModeAbs
    (b : ℝ) (L : {l : ℝ // 0 < l}) (x : Vec 2)
    (K e : WhiteNoise) : ℝ :=
  |q3Convolution b L h3Zero e x * inner ℝ e K|

/-- The complete zero-padded white-noise basis sum of localized q3 mode norms
is bounded pointwise by the actual gradient products and the fixed kernel
constant. The bound is a Hilbert-basis Cauchy--Schwarz estimate, not a finite
mode or covariance hypothesis. -/
theorem main_diag_q3_signed_localized_gradient_term_norm_tsum_bound
    (b : ℝ) (L : {l : ℝ // 0 < l}) (Q : TriadicCube 2) (mesh : ℕ)
    (φ : H1Function (openCubeSet Q)) (x : Vec 2) :
    Summable (fun k : ℕ =>
      ‖mainDiagQ3SignedLocalizedGradientTerm b L Q mesh φ k x‖) ∧
    (∑' k : ℕ,
      ‖mainDiagQ3SignedLocalizedGradientTerm b L Q mesh φ k x‖) ≤
      ‖q3Section b L h3Zero 0‖ *
        (∑ i : Fin 2, ∑ j : Fin 2,
          (|(diagInterpolant Q mesh φ).grad x i| *
            |(φ - diagInterpolant Q mesh φ).grad x j| *
            (∑ a : Fin 2, ∑ c : Fin 2,
              ‖oldSignedProjectedWhiteKernel b L 0 a c‖))) := by
  let I := diagInterpolant Q mesh
  let S := q3Section b L h3Zero x
  let K : WhiteNoise := ∑ i : Fin 2, ∑ j : Fin 2,
      ((I φ).grad x i * (φ - I φ).grad x j) •
        oldSignedRotatedWhiteKernel b L (L.1⁻¹ • x) i j
  let f : WhiteNoise → ℝ := fun e => mainDiagQ3SignedModeAbs b L x K e
  have hf0 : f 0 = 0 := by
    simp [f, mainDiagQ3SignedModeAbs, q3Convolution]
  have hbasis := main_basis_abs_inner_product_bound whiteBasis S K
  have hseq : Summable (fun i => f (whiteBasis i)) := by
    apply hbasis.1.congr
    intro i
    simp [f, mainDiagQ3SignedModeAbs, S, K, q3Convolution,
      real_inner_comm]
  have hnat : Summable (fun k : ℕ => f (gaussEnumerated whiteBasis k)) := by
    classical
    let := Encodable.ofCountable whiteBasisIndex
    have he : (fun k : ℕ => f (gaussEnumerated whiteBasis k)) =
        Function.extend Encodable.encode (fun i => f (whiteBasis i)) 0 := by
      funext k
      by_cases hk : k ∈ Set.range (Encodable.encode : whiteBasisIndex → ℕ)
      · obtain ⟨i, rfl⟩ := hk
        rw [enumerated_encode, Function.Injective.extend_apply Encodable.encode_injective]
      · rw [gaussEnumerated, Function.extend_apply' _ _ _ hk,
          Function.extend_apply' _ _ _ hk]
        exact hf0
    rw [he]
    exact (summable_extend_zero Encodable.encode_injective).mpr hseq
  have htsumEq : (∑' k : ℕ, f (gaussEnumerated whiteBasis k)) =
      ∑' i : whiteBasisIndex, f (whiteBasis i) :=
    enumerated_tsum_apply whiteBasis f hf0
  have htsumBound : (∑' k : ℕ, f (gaussEnumerated whiteBasis k)) ≤
      ‖S‖ * ‖K‖ := by
    rw [htsumEq]
    convert hbasis.2 using 1
    congr 1
    funext i
    simp [f, mainDiagQ3SignedModeAbs, S, K, q3Convolution,
      real_inner_comm]
  have hS (y : Vec 2) : ‖q3Section b L h3Zero y‖ =
      ‖q3Section b L h3Zero 0‖ := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [gaussQ3Section_norm_sq, gaussQ3Section_norm_sq]
  let C := ∑ a : Fin 2, ∑ c : Fin 2,
    ‖oldSignedProjectedWhiteKernel b L 0 a c‖
  have hkernel (i j : Fin 2) :
      ‖oldSignedRotatedWhiteKernel b L (L.1⁻¹ • x) i j‖ ≤ C :=
    main_old_signed_rotated_white_kernel_norm_le b L _ i j
  have hK : ‖K‖ ≤
      ∑ i : Fin 2, ∑ j : Fin 2,
        (|(I φ).grad x i| * |(φ - I φ).grad x j| * C) := by
    dsimp [K]
    calc
      _ ≤ ∑ i : Fin 2, ‖∑ j : Fin 2,
          (((I φ).grad x i * (φ - I φ).grad x j) : ℝ) •
            oldSignedRotatedWhiteKernel b L (L.1⁻¹ • x) i j‖ := norm_sum_le _ _
      _ ≤ ∑ i : Fin 2, ∑ j : Fin 2,
          ‖(((I φ).grad x i * (φ - I φ).grad x j) : ℝ) •
            oldSignedRotatedWhiteKernel b L (L.1⁻¹ • x) i j‖ := by
        apply Finset.sum_le_sum
        intro i hi
        exact norm_sum_le _ _
      _ ≤ ∑ i : Fin 2, ∑ j : Fin 2,
          (|(I φ).grad x i| * |(φ - I φ).grad x j| * C) := by
        apply Finset.sum_le_sum
        intro i hi
        apply Finset.sum_le_sum
        intro j hj
        rw [norm_smul, Real.norm_eq_abs, abs_mul]
        exact mul_le_mul_of_nonneg_left (hkernel i j)
          (mul_nonneg (abs_nonneg _) (abs_nonneg _))
  have hnormSeq : (fun k : ℕ =>
      ‖mainDiagQ3SignedLocalizedGradientTerm b L Q mesh φ k x‖) =
      fun k => f (gaussEnumerated whiteBasis k) := by
    funext k
    rw [mainDiagQ3SignedLocalizedGradientTerm]
    rw [Real.norm_eq_abs]
    rfl
  have hnormSum : ∑' k : ℕ,
      ‖mainDiagQ3SignedLocalizedGradientTerm b L Q mesh φ k x‖ =
      ∑' k : ℕ, f (gaussEnumerated whiteBasis k) := by
    rw [hnormSeq]
  refine ⟨?_, ?_⟩
  · rw [hnormSeq]
    exact hnat
  · rw [hnormSum]
    calc
      (∑' k : ℕ, f (gaussEnumerated whiteBasis k)) ≤ ‖S‖ * ‖K‖ := htsumBound
      _ ≤ ‖q3Section b L h3Zero 0‖ *
          (∑ i : Fin 2, ∑ j : Fin 2,
            (|(I φ).grad x i| * |(φ - I φ).grad x j| * C)) := by
        rw [show S = q3Section b L h3Zero x from rfl, hS]
        exact mul_le_mul_of_nonneg_left hK (norm_nonneg _)

/-- The sum of L¹ norms of the actual localized q3 covariance modes is
summable on each descendant cell. This derives the Fubini hypothesis from
the actual H¹ gradient bounds and the uniform projected-kernel estimate. -/
theorem main_diag_q3_signed_localized_gradient_term_norm_integral_summable
    (b : ℝ) (L : {l : ℝ // 0 < l}) (Q : TriadicCube 2) (mesh : ℕ)
    (φ : H1Function (openCubeSet Q)) (U : TriadicCube 2)
    (hU : U ∈ descendantsAtDepth Q mesh) :
    Summable (fun k : ℕ =>
      ∫ x, ‖mainDiagQ3SignedLocalizedGradientTerm b L Q mesh φ k x‖
        ∂(normalizedCubeMeasure U)) := by
  let I := diagInterpolant Q mesh
  let μ := normalizedCubeMeasure U
  let C := ∑ a : Fin 2, ∑ c : Fin 2,
    ‖oldSignedProjectedWhiteKernel b L 0 a c‖
  let M : Vec 2 → ℝ := fun x => ‖q3Section b L h3Zero 0‖ *
    (∑ i : Fin 2, ∑ j : Fin 2,
      (|(I φ).grad x i| * |(φ - I φ).grad x j| * C))
  have hA (i : Fin 2) : MemLp (fun x => (I φ).grad x i) 2 μ :=
    memLp_on_descendant_of_memLp hU ((I φ).grad_memL2_normalizedCubeMeasure i)
  have hB (i : Fin 2) : MemLp (fun x => (φ - I φ).grad x i) 2 μ :=
    memLp_on_descendant_of_memLp hU ((φ - I φ).grad_memL2_normalizedCubeMeasure i)
  have hterm (k : ℕ) : Integrable
      (fun x => ‖mainDiagQ3SignedLocalizedGradientTerm b L Q mesh φ k x‖) μ :=
    (main_diag_q3_signed_localized_gradient_term_integrable
      b L Q mesh φ U hU k).norm
  have hprod (i j : Fin 2) : Integrable
      (fun x => |(I φ).grad x i| * |(φ - I φ).grad x j|) μ := by
    have hm := (hA i).integrable_mul (hB j)
    have hn := hm.norm
    convert hn using 1
    funext x
    change |(I φ).grad x i| * |(φ - I φ).grad x j| =
      |(I φ).grad x i * (φ - I φ).grad x j|
    rw [abs_mul]
  have hmajor : Integrable M μ := by
    have hsum (i : Fin 2) : Integrable
        (fun x => ∑ j : Fin 2,
          (|(I φ).grad x i| * |(φ - I φ).grad x j| * C)) μ := by
      apply integrable_finsetSum
      intro j hj
      have hc := (hprod i j).const_mul C
      convert hc using 1
      funext x
      ring
    have hdouble : Integrable
        (fun x => ∑ i : Fin 2, ∑ j : Fin 2,
          (|(I φ).grad x i| * |(φ - I φ).grad x j| * C)) μ := by
      apply integrable_finsetSum
      intro i hi
      exact hsum i
    dsimp [M]
    exact hdouble.const_mul ‖q3Section b L h3Zero 0‖
  have hpoint (x : Vec 2) :
      Summable (fun k : ℕ =>
        ‖mainDiagQ3SignedLocalizedGradientTerm b L Q mesh φ k x‖) ∧
      (∑' k : ℕ,
        ‖mainDiagQ3SignedLocalizedGradientTerm b L Q mesh φ k x‖) ≤ M x := by
    simpa only [M, I, C] using
      main_diag_q3_signed_localized_gradient_term_norm_tsum_bound b L Q mesh φ x
  apply summable_of_sum_le
  · intro k
    exact integral_nonneg (fun x => norm_nonneg _)
  · intro s
    calc
      (∑ k ∈ s, ∫ x,
          ‖mainDiagQ3SignedLocalizedGradientTerm b L Q mesh φ k x‖ ∂μ) =
          ∫ x, ∑ k ∈ s,
            ‖mainDiagQ3SignedLocalizedGradientTerm b L Q mesh φ k x‖ ∂μ := by
        symm
        apply integral_finsetSum
        intro k hk
        exact hterm k
      _ ≤ ∫ x, M x ∂μ := by
        apply integral_mono
        · exact integrable_finsetSum s (fun k hk => hterm k)
        · exact hmajor
        · intro x
          calc
            _ ≤ ∑' k : ℕ,
                ‖mainDiagQ3SignedLocalizedGradientTerm b L Q mesh φ k x‖ :=
                  (hpoint x).1.sum_le_tsum s (fun k hk => norm_nonneg _)
            _ ≤ M x := (hpoint x).2

/-- The spatial q3 contraction now instantiates its Fubini hypotheses on each
actual descendant cell without an additional summability assumption. -/
theorem main_diag_q3_signed_localized_gradient_covariance_integral_of_descendant
    (b : ℝ) (L : {l : ℝ // 0 < l}) (Q : TriadicCube 2) (mesh : ℕ)
    (φ : H1Function (openCubeSet Q)) (U : TriadicCube 2)
    (hU : U ∈ descendantsAtDepth Q mesh) :
    (∑' k : ℕ,
      ∫ x, mainDiagQ3SignedLocalizedGradientTerm b L Q mesh φ k x
        ∂(normalizedCubeMeasure U)) =
      ∫ x, -(b ^ 2 / 2) *
        (∑ i : Fin 2, (diagInterpolant Q mesh φ).grad x i *
          (φ - diagInterpolant Q mesh φ).grad x i)
        ∂(normalizedCubeMeasure U) := by
  exact main_diag_q3_signed_localized_gradient_covariance_integral
    b L Q mesh φ U
    (fun k => main_diag_q3_signed_localized_gradient_term_integrable
      b L Q mesh φ U hU k)
    (main_diag_q3_signed_localized_gradient_term_norm_integral_summable
      b L Q mesh φ U hU)

end ASDExplicitGamma.Main
