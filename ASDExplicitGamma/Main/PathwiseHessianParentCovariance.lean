module

public import ASDExplicitGamma.Main.PathwiseHessianLocalizedMeasurability
public import ASDExplicitGamma.Main.PathwiseHessianLocalizedCovariance
public import ASDExplicitGamma.Triadic.DiagEstimates
public import ASDExplicitGamma.Triadic.SensitivityWeakEnergy
public import ASDExplicitGamma.Variational.LemmaVMinimizer

/-! The localized q3 signed contraction on the whole source cube. -/

@[expose] public section

namespace ASDExplicitGamma.Main

open MeasureTheory Homogenization ASDExplicitGamma.Gaussian ASDExplicitGamma.Native
  ASDExplicitGamma.Response ASDExplicitGamma.Triadic ASDExplicitGamma.Variational

local instance pathwiseHessianParentFiniteMeasure (Q : TriadicCube 2) :
    IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
  (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume

/-- Each actual localized q3 mode is integrable on the whole source cube,
using the original H¹ bounds rather than a descendant restriction. -/
theorem main_diag_q3_signed_localized_gradient_term_integrable_parent
    (b : ℝ) (L : {l : ℝ // 0 < l}) (Q : TriadicCube 2) (mesh : ℕ)
    (φ : H1Function (openCubeSet Q)) (k : ℕ) :
    Integrable (fun x => mainDiagQ3SignedLocalizedGradientTerm b L Q mesh φ k x)
      (normalizedCubeMeasure Q) := by
  let I := diagInterpolant Q mesh
  let μ := normalizedCubeMeasure Q
  let e := gaussEnumerated whiteBasis k
  let S₀ := q3Section b L h3Zero 0
  let C := ∑ a : Fin 2, ∑ c : Fin 2,
    ‖oldSignedProjectedWhiteKernel b L 0 a c‖
  have hA (i : Fin 2) : MemLp (fun x => (I φ).grad x i) 2 μ :=
    (I φ).grad_memL2_normalizedCubeMeasure i
  have hB (i : Fin 2) : MemLp (fun x => (φ - I φ).grad x i) 2 μ :=
    (φ - I φ).grad_memL2_normalizedCubeMeasure i
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
      _ ≤ 1 * ‖S₀‖ := by
        rw [hS x]
        exact mul_le_mul_of_nonneg_right he (norm_nonneg _)
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
        · exact (hinner x).trans (hvec x)
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
  have hscale : Continuous (fun x : Vec 2 => L.1⁻¹ • x) :=
    continuous_const_smul (L.1⁻¹)
  have hP (i j : Fin 2) : Continuous (fun x : Vec 2 =>
      oldSignedProjectedWhiteKernel b L (L.1⁻¹ • x) i j) :=
    (main_old_signed_projected_white_kernel_continuous b L i j).comp hscale
  have hconvMeas (e : WhiteNoise) : Measurable
      (fun x => q3Convolution b L h3Zero e x) :=
    (q3Convolution_continuous b L h3Zero e).measurable
  have hmeas : AEMeasurable
      (fun x => mainDiagQ3SignedLocalizedGradientTerm b L Q mesh φ k x) μ := by
    let μ := normalizedCubeMeasure Q
    have hA' (i : Fin 2) : MemLp (fun x => (I φ).grad x i) 2 μ := hA i
    have hB' (i : Fin 2) : MemLp (fun x => (φ - I φ).grad x i) 2 μ := hB i
    change AEMeasurable
      (fun x => q3Convolution b L h3Zero e x *
        inner ℝ e (∑ i : Fin 2, ∑ j : Fin 2,
          ((I φ).grad x i * (φ - I φ).grad x j) •
            oldSignedRotatedWhiteKernel b L (L.1⁻¹ • x) i j)) μ
    apply AEMeasurable.mul ((hconvMeas e).aemeasurable)
    simp only [inner_sum, real_inner_smul_right]
    apply Finset.aemeasurable_fun_sum
    intro i hi
    apply Finset.aemeasurable_fun_sum
    intro j hj
    have hI : AEMeasurable (fun x => (I φ).grad x i) μ :=
      hA' i |>.aestronglyMeasurable.aemeasurable
    have hR : AEMeasurable (fun x => (φ - I φ).grad x j) μ :=
      hB' j |>.aestronglyMeasurable.aemeasurable
    have hK : AEMeasurable (fun x => inner ℝ e
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
  apply hmajor.mono' hmeas.aestronglyMeasurable
  filter_upwards [] with x
  exact hpoint x

/-- The sum of whole-cube L¹ mode norms is summable; the majorant is the
finite sum of products of the actual interpolant and residual gradients. -/
theorem main_diag_q3_signed_localized_gradient_term_norm_integral_summable_parent
    (b : ℝ) (L : {l : ℝ // 0 < l}) (Q : TriadicCube 2) (mesh : ℕ)
    (φ : H1Function (openCubeSet Q)) :
    Summable (fun k : ℕ =>
      ∫ x, ‖mainDiagQ3SignedLocalizedGradientTerm b L Q mesh φ k x‖
        ∂(normalizedCubeMeasure Q)) := by
  let I := diagInterpolant Q mesh
  let μ := normalizedCubeMeasure Q
  let C := ∑ a : Fin 2, ∑ c : Fin 2,
    ‖oldSignedProjectedWhiteKernel b L 0 a c‖
  let M : Vec 2 → ℝ := fun x => ‖q3Section b L h3Zero 0‖ *
    (∑ i : Fin 2, ∑ j : Fin 2,
      (|(I φ).grad x i| * |(φ - I φ).grad x j| * C))
  have hA (i : Fin 2) : MemLp (fun x => (I φ).grad x i) 2 μ :=
    (I φ).grad_memL2_normalizedCubeMeasure i
  have hB (i : Fin 2) : MemLp (fun x => (φ - I φ).grad x i) 2 μ :=
    (φ - I φ).grad_memL2_normalizedCubeMeasure i
  have hterm (k : ℕ) : Integrable
      (fun x => ‖mainDiagQ3SignedLocalizedGradientTerm b L Q mesh φ k x‖) μ :=
    (main_diag_q3_signed_localized_gradient_term_integrable_parent
      b L Q mesh φ k).norm
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

/-- On the parent cube, the localized signed q3 covariance contraction is
now integrated with no auxiliary Fubini hypotheses. -/
theorem main_diag_q3_signed_localized_gradient_covariance_integral_parent
    (b : ℝ) (L : {l : ℝ // 0 < l}) (Q : TriadicCube 2) (mesh : ℕ)
    (φ : H1Function (openCubeSet Q)) :
    (∑' k : ℕ,
      ∫ x, mainDiagQ3SignedLocalizedGradientTerm b L Q mesh φ k x
        ∂(normalizedCubeMeasure Q)) =
      ∫ x, -(b ^ 2 / 2) *
        (∑ i : Fin 2, (diagInterpolant Q mesh φ).grad x i *
          (φ - diagInterpolant Q mesh φ).grad x i)
        ∂(normalizedCubeMeasure Q) := by
  exact main_diag_q3_signed_localized_gradient_covariance_integral
    b L Q mesh φ Q
    (fun k => main_diag_q3_signed_localized_gradient_term_integrable_parent
      b L Q mesh φ k)
    (main_diag_q3_signed_localized_gradient_term_norm_integral_summable_parent
      b L Q mesh φ)

/-- For the actual affine-potential trial, the integrated signed covariance
keeps its affine load and interpolated H10 correction as separate factors.
This is the form used when pairing the q3 contraction with the trial. -/
theorem main_diag_q3_signed_localized_gradient_covariance_integral_affine_potential
    (b : ℝ) (L : {l : ℝ // 0 < l}) (Q : TriadicCube 2) (mesh : ℕ)
    (p : Vec 2) (r : H10Function (openCubeSet Q)) :
    (∑' k : ℕ,
      ∫ x, mainDiagQ3SignedLocalizedGradientTerm b L Q mesh
        (lemmaVAffinePotential (isOpenBoundedConvexDomain_openCubeSet Q) p r) k x
        ∂(normalizedCubeMeasure Q)) =
      ∫ x, -(b ^ 2 / 2) *
        (∑ i : Fin 2,
          (p i + (diagInterpolant Q mesh r.toH1Function).grad x i) *
            (r.toH1Function - diagInterpolant Q mesh r.toH1Function).grad x i)
        ∂(normalizedCubeMeasure Q) := by
  let φ := lemmaVAffinePotential (isOpenBoundedConvexDomain_openCubeSet Q) p r
  have hI : diagInterpolant Q mesh φ =
      diagAffineLinear Q p + diagInterpolant Q mesh r.toH1Function := by
    dsimp [φ]
    exact diagInterpolant_affinePotential Q mesh p r
  have hres : φ - diagInterpolant Q mesh φ =
      r.toH1Function - diagInterpolant Q mesh r.toH1Function := by
    dsimp [φ]
    exact diagInterpolant_affinePotential_residual Q mesh p r
  have hgrad (x : Vec 2) (i : Fin 2) :
      (diagInterpolant Q mesh φ).grad x i =
        p i + (diagInterpolant Q mesh r.toH1Function).grad x i := by
    rw [hI]
    simp only [H1Function.add_grad, Pi.add_apply, diagAffineLinear,
      LinearMap.coe_mk, AddHom.coe_mk,
      H1Function.affineOnIsSobolevRegularDomain_grad]
  calc
    _ = ∫ x, -(b ^ 2 / 2) *
        (∑ i : Fin 2,
          (diagInterpolant Q mesh φ).grad x i *
            (φ - diagInterpolant Q mesh φ).grad x i)
        ∂(normalizedCubeMeasure Q) :=
          main_diag_q3_signed_localized_gradient_covariance_integral_parent
            b L Q mesh φ
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with x
      simp_rw [hgrad x]
      rw [hres]

/-- The constant affine load vanishes when the integrated signed covariance
is paired with the actual zero-trace DIAG correction. -/
theorem main_diag_q3_signed_localized_gradient_covariance_integral_affine_corrector
    (b : ℝ) (L : {l : ℝ // 0 < l}) (Q : TriadicCube 2) (mesh : ℕ)
    (p : Vec 2) (r : H10Function (openCubeSet Q)) :
    (∑' k : ℕ,
      ∫ x, mainDiagQ3SignedLocalizedGradientTerm b L Q mesh
        (lemmaVAffinePotential (isOpenBoundedConvexDomain_openCubeSet Q) p r) k x
        ∂(normalizedCubeMeasure Q)) =
      ∫ x, -(b ^ 2 / 2) *
        (∑ i : Fin 2,
          (diagInterpolant Q mesh r.toH1Function).grad x i *
            (r.toH1Function - diagInterpolant Q mesh r.toH1Function).grad x i)
        ∂(normalizedCubeMeasure Q) := by
  let φ := lemmaVAffinePotential (isOpenBoundedConvexDomain_openCubeSet Q) p r
  let ψ := r.toH1Function - diagInterpolant Q mesh r.toH1Function
  let c : ℝ := -(b ^ 2 / 2)
  let Pfun : Vec 2 → ℝ := fun x => ∑ i : Fin 2, p i * ψ.grad x i
  let Ifun : Vec 2 → ℝ := fun x => ∑ i : Fin 2,
    (diagInterpolant Q mesh r.toH1Function).grad x i * ψ.grad x i
  have hψmem : MemH10 (openCubeSet Q) ψ.toFun := by
    have h := diagInterpolant_affine_residual_memH10 Q mesh p r
    rw [diagInterpolant_affinePotential_residual Q mesh p r] at h
    exact h
  have hmean (i : Fin 2) : cubeAverage Q (fun x => ψ.grad x i) = 0 :=
    diagH1_mean_gradient_zero Q ψ hψmem i
  have hmeanInt (i : Fin 2) :
      ∫ x, ψ.grad x i ∂(normalizedCubeMeasure Q) = 0 := by
    rw [← cubeAverage_eq_integral_normalizedCubeMeasure Q (fun x => ψ.grad x i)]
    exact hmean i
  have hψgrad (i : Fin 2) :
      MemLp (fun x => ψ.grad x i) 2 (normalizedCubeMeasure Q) := by
    exact ψ.grad_memL2_normalizedCubeMeasure i
  have hIgrad (i : Fin 2) :
      MemLp (fun x => (diagInterpolant Q mesh r.toH1Function).grad x i)
        2 (normalizedCubeMeasure Q) := by
    exact (diagInterpolant Q mesh r.toH1Function).grad_memL2_normalizedCubeMeasure i
  have hPterm (i : Fin 2) :
      Integrable (fun x => p i * ψ.grad x i) (normalizedCubeMeasure Q) := by
    simpa only [mul_comm] using (hψgrad i).integrable one_le_two |>.const_mul (p i)
  have hIterm (i : Fin 2) :
      Integrable (fun x => (diagInterpolant Q mesh r.toH1Function).grad x i *
        ψ.grad x i) (normalizedCubeMeasure Q) :=
    (hIgrad i).integrable_mul (hψgrad i)
  have hPsum : Integrable Pfun (normalizedCubeMeasure Q) := by
    apply integrable_finsetSum
    intro i hi
    exact hPterm i
  have hIsum : Integrable Ifun (normalizedCubeMeasure Q) := by
    apply integrable_finsetSum
    intro i hi
    exact hIterm i
  have hPint : ∫ x, Pfun x ∂(normalizedCubeMeasure Q) = 0 := by
    rw [integral_finsetSum Finset.univ (fun i _ => hPterm i)]
    simp [integral_const_mul, hmeanInt]
  have hPscaled : Integrable (fun x => c * Pfun x) (normalizedCubeMeasure Q) := by
    simpa [Pfun, mul_comm] using hPsum.const_mul c
  have hIscaled : Integrable (fun x => c * Ifun x) (normalizedCubeMeasure Q) := by
    simpa [Ifun, mul_comm] using hIsum.const_mul c
  have hPscaledInt :
      ∫ x, c * Pfun x ∂(normalizedCubeMeasure Q) = 0 := by
    rw [integral_const_mul, hPint]
    simp
  have hpoint (x : Vec 2) :
      c * (∑ i : Fin 2,
        (p i + (diagInterpolant Q mesh r.toH1Function).grad x i) * ψ.grad x i) =
        c * Pfun x + c * Ifun x := by
    dsimp [Pfun, Ifun]
    calc
      _ = c * (∑ i : Fin 2,
          (p i * ψ.grad x i +
            (diagInterpolant Q mesh r.toH1Function).grad x i * ψ.grad x i)) := by
        congr 1
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = _ := by rw [Finset.sum_add_distrib]; ring
  have hsplitIntegral :
      (∫ x, c * (∑ i : Fin 2,
        (p i + (diagInterpolant Q mesh r.toH1Function).grad x i) * ψ.grad x i)
        ∂(normalizedCubeMeasure Q)) =
        (∫ x, c * Pfun x ∂(normalizedCubeMeasure Q)) +
          (∫ x, c * Ifun x ∂(normalizedCubeMeasure Q)) := by
    calc
      _ = ∫ x, (c * Pfun x + c * Ifun x) ∂(normalizedCubeMeasure Q) := by
        apply integral_congr_ae
        filter_upwards [] with x
        exact hpoint x
      _ = _ := integral_add hPscaled hIscaled
  rw [main_diag_q3_signed_localized_gradient_covariance_integral_affine_potential]
  change (∫ x, c * (∑ i : Fin 2,
      (p i + (diagInterpolant Q mesh r.toH1Function).grad x i) * ψ.grad x i)
      ∂(normalizedCubeMeasure Q)) = ∫ x, c * Ifun x ∂(normalizedCubeMeasure Q)
  rw [hsplitIntegral, hPscaledInt, zero_add]

/-- Absolute size of the signed q3 covariance cross after the constant affine
load has cancelled. It is controlled by the actual L² energies of the
interpolated and residual corrector gradients. -/
theorem main_diag_q3_signed_covariance_integral_affine_corrector_abs_le
    (b : ℝ) (L : {l : ℝ // 0 < l}) (Q : TriadicCube 2) (mesh : ℕ)
    (p : Vec 2) (r : H10Function (openCubeSet Q)) :
    |∑' k : ℕ,
      ∫ x, mainDiagQ3SignedLocalizedGradientTerm b L Q mesh
        (lemmaVAffinePotential (isOpenBoundedConvexDomain_openCubeSet Q) p r) k x
        ∂(normalizedCubeMeasure Q)| ≤
      (b ^ 2 / 2) * ∑ i : Fin 2,
        l2Norm Q (fun x => (diagInterpolant Q mesh r.toH1Function).grad x i) *
          l2Norm Q (fun x =>
            (r.toH1Function - diagInterpolant Q mesh r.toH1Function).grad x i) := by
  let μ := normalizedCubeMeasure Q
  let I := diagInterpolant Q mesh r.toH1Function
  let ψ := r.toH1Function - I
  have hI (i : Fin 2) : MemLp (fun x => I.grad x i) 2 μ :=
    I.grad_memL2_normalizedCubeMeasure i
  have hψ (i : Fin 2) : MemLp (fun x => ψ.grad x i) 2 μ :=
    ψ.grad_memL2_normalizedCubeMeasure i
  have hprod (i : Fin 2) : Integrable (fun x => I.grad x i * ψ.grad x i) μ :=
    (hI i).integrable_mul (hψ i)
  have hsumInt : Integrable (fun x => ∑ i : Fin 2, I.grad x i * ψ.grad x i) μ := by
    apply integrable_finsetSum
    intro i hi
    exact hprod i
  have hsumPair :
      (∫ x, ∑ i : Fin 2, I.grad x i * ψ.grad x i ∂μ) =
        ∑ i : Fin 2, pairing Q (fun x => I.grad x i) (fun x => ψ.grad x i) := by
    rw [integral_finsetSum Finset.univ (fun i _ => hprod i)]
    apply Finset.sum_congr rfl
    intro i hi
    rw [pairing, cubeAverage_eq_integral_normalizedCubeMeasure]
  have hcov :=
    main_diag_q3_signed_localized_gradient_covariance_integral_affine_corrector
      b L Q mesh p r
  have hcovPair :
      (∑' k : ℕ,
        ∫ x, mainDiagQ3SignedLocalizedGradientTerm b L Q mesh
          (lemmaVAffinePotential (isOpenBoundedConvexDomain_openCubeSet Q) p r) k x
          ∂μ) =
        -(b ^ 2 / 2) *
          ∑ i : Fin 2,
            pairing Q (fun x => I.grad x i) (fun x => ψ.grad x i) := by
    calc
      _ = ∫ x, -(b ^ 2 / 2) *
          (∑ i : Fin 2, I.grad x i * ψ.grad x i) ∂μ := by
            simpa only [μ, I, ψ] using hcov
      _ = -(b ^ 2 / 2) *
          (∫ x, ∑ i : Fin 2, I.grad x i * ψ.grad x i ∂μ) := by
            rw [integral_const_mul]
      _ = _ := by rw [hsumPair]
  have hc : 0 ≤ b ^ 2 / 2 := by positivity
  rw [hcovPair]
  calc
    |-(b ^ 2 / 2) *
        ∑ i : Fin 2, pairing Q (fun x => I.grad x i) (fun x => ψ.grad x i)| =
        (b ^ 2 / 2) *
          |∑ i : Fin 2, pairing Q (fun x => I.grad x i) (fun x => ψ.grad x i)| := by
            rw [abs_mul, abs_neg, abs_of_nonneg hc]
    _ ≤ (b ^ 2 / 2) *
        ∑ i : Fin 2, |pairing Q (fun x => I.grad x i) (fun x => ψ.grad x i)| :=
          mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) hc
    _ ≤ (b ^ 2 / 2) *
        ∑ i : Fin 2,
          l2Norm Q (fun x => I.grad x i) * l2Norm Q (fun x => ψ.grad x i) :=
          mul_le_mul_of_nonneg_left
            (Finset.sum_le_sum fun i _ => abs_pairing_le Q (hI i) (hψ i)) hc

/-- Source-norm form of the preceding covariance bound: the signed cross is
the weak/positive DIAG pairing between the zero-trace correction and its
interpolant. -/
theorem main_diag_q3_signed_covariance_integral_affine_corrector_tiled_le
    (b : ℝ) (L : {l : ℝ // 0 < l}) (Q : TriadicCube 2) (mesh : ℕ)
    (p : Vec 2) (r : H10Function (openCubeSet Q)) :
    |∑' k : ℕ,
      ∫ x, mainDiagQ3SignedLocalizedGradientTerm b L Q mesh
        (lemmaVAffinePotential (isOpenBoundedConvexDomain_openCubeSet Q) p r) k x
        ∂(normalizedCubeMeasure Q)| ≤
      (b ^ 2 / 2) *
        Real.sqrt (lemmaVTiledWeakEnergy Q mesh
          (r.toH1Function - diagInterpolant Q mesh r.toH1Function).grad) *
        Real.sqrt (lemmaVTiledPositiveEnergy Q mesh
          (diagInterpolant Q mesh r.toH1Function).grad) := by
  let μ := normalizedCubeMeasure Q
  let I := diagInterpolant Q mesh r.toH1Function
  let ψ := r.toH1Function - I
  have hI (i : Fin 2) : MemLp (fun x => I.grad x i) 2 μ :=
    I.grad_memL2_normalizedCubeMeasure i
  have hψ (i : Fin 2) : MemLp (fun x => ψ.grad x i) 2 μ :=
    ψ.grad_memL2_normalizedCubeMeasure i
  have hIpos (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth Q mesh)
      (i : Fin 2) :
      Summable (fun k => (Real.sqrt 3) ^ (k + 1) *
        energy U (cubeIncrement U (k + 1) (fun x => I.grad x i))) := by
    have hzero : lemmaVAffinePotential
        (isOpenBoundedConvexDomain_openCubeSet Q) 0 r = r.toH1Function := by
      ext x
      · simp only [lemmaVAffinePotential, H1Function.add_toFun,
          H1Function.affineOnIsSobolevRegularDomain_apply]
        simp
      · simp only [lemmaVAffinePotential, H1Function.add_grad,
          H1Function.affineOnIsSobolevRegularDomain_grad]
        simp
    have h := diagInterpolant_gradient_summable Q mesh 0 r U hU i
    rw [hzero] at h
    simpa only [I] using h
  have hpair := lemmaV_tiled_pairing_le Q mesh hψ hI hIpos
  have hsumInt : Integrable (fun x =>
      ∑ i : Fin 2, I.grad x i * ψ.grad x i) μ := by
    apply integrable_finsetSum
    intro i hi
    exact (hI i).integrable_mul (hψ i)
  have hsumEq :
      (∫ x, ∑ i : Fin 2, I.grad x i * ψ.grad x i ∂μ) =
        cubeAverage Q (fun x => vecDot (ψ.grad x) (I.grad x)) := by
    have hsumPair :
        (∫ x, ∑ i : Fin 2, I.grad x i * ψ.grad x i ∂μ) =
          vectorPairing Q ψ.grad I.grad := by
      have hsum :
          (∫ x, ∑ i : Fin 2, I.grad x i * ψ.grad x i ∂μ) =
            ∑ i : Fin 2, ∫ x, I.grad x i * ψ.grad x i ∂μ :=
        integral_finsetSum Finset.univ (fun i _ => (hI i).integrable_mul (hψ i))
      calc
        _ = ∑ i : Fin 2, pairing Q (fun x => ψ.grad x i) (fun x => I.grad x i) := by
          rw [hsum]
          apply Finset.sum_congr rfl
          intro i hi
          calc
            _ = ∫ x, ψ.grad x i * I.grad x i ∂μ := by
              apply integral_congr_ae
              exact Filter.Eventually.of_forall fun x => by ring
            _ = pairing Q (fun x => ψ.grad x i) (fun x => I.grad x i) := by
              rw [pairing, cubeAverage_eq_integral_normalizedCubeMeasure]
        _ = vectorPairing Q ψ.grad I.grad := rfl
    calc
      _ = vectorPairing Q ψ.grad I.grad := hsumPair
      _ = _ := (lemmaV_cubeAverage_vecDot_eq_vectorPairing Q hψ hI).symm
  have hcov :=
    main_diag_q3_signed_localized_gradient_covariance_integral_affine_corrector
      b L Q mesh p r
  have hcovPair :
      (∑' k : ℕ,
        ∫ x, mainDiagQ3SignedLocalizedGradientTerm b L Q mesh
          (lemmaVAffinePotential (isOpenBoundedConvexDomain_openCubeSet Q) p r) k x
          ∂μ) =
        -(b ^ 2 / 2) *
          cubeAverage Q (fun x => vecDot (ψ.grad x) (I.grad x)) := by
    calc
      _ = ∫ x, -(b ^ 2 / 2) *
          (∑ i : Fin 2, I.grad x i * ψ.grad x i) ∂μ := by
            simpa only [μ, I, ψ] using hcov
      _ = -(b ^ 2 / 2) *
          (∫ x, ∑ i : Fin 2, I.grad x i * ψ.grad x i ∂μ) := by
            rw [integral_const_mul]
      _ = _ := by rw [hsumEq]
  have hc : 0 ≤ b ^ 2 / 2 := by positivity
  rw [hcovPair]
  change |-(b ^ 2 / 2) *
      cubeAverage Q (fun x => vecDot (ψ.grad x) (I.grad x))| ≤
    (b ^ 2 / 2) *
      Real.sqrt (lemmaVTiledWeakEnergy Q mesh ψ.grad) *
        Real.sqrt (lemmaVTiledPositiveEnergy Q mesh I.grad)
  calc
    |-(b ^ 2 / 2) *
        cubeAverage Q (fun x => vecDot (ψ.grad x) (I.grad x))| =
        (b ^ 2 / 2) *
          |cubeAverage Q (fun x => vecDot (ψ.grad x) (I.grad x))| := by
            rw [abs_mul, abs_neg, abs_of_nonneg hc]
    _ ≤ (b ^ 2 / 2) *
        (Real.sqrt (lemmaVTiledWeakEnergy Q mesh ψ.grad) *
          Real.sqrt (lemmaVTiledPositiveEnergy Q mesh I.grad)) :=
        mul_le_mul_of_nonneg_left hpair hc
    _ = (b ^ 2 / 2) *
        Real.sqrt (lemmaVTiledWeakEnergy Q mesh ψ.grad) *
          Real.sqrt (lemmaVTiledPositiveEnergy Q mesh I.grad) := by ring

/-- A sum-of-squares form of the affine-corrector covariance estimate. This
is convenient when the signed cross is charged to the positive local error
budget, and does not discard the exact covariance cancellation proved above. -/
theorem main_diag_q3_signed_covariance_integral_affine_corrector_tiled_sum_le
    (b : ℝ) (L : {l : ℝ // 0 < l}) (Q : TriadicCube 2) (mesh : ℕ)
    (p : Vec 2) (r : H10Function (openCubeSet Q)) :
    |∑' k : ℕ,
      ∫ x, mainDiagQ3SignedLocalizedGradientTerm b L Q mesh
        (lemmaVAffinePotential (isOpenBoundedConvexDomain_openCubeSet Q) p r) k x
        ∂(normalizedCubeMeasure Q)| ≤
      (b ^ 2 / 4) *
        (lemmaVTiledWeakEnergy Q mesh
            (r.toH1Function - diagInterpolant Q mesh r.toH1Function).grad +
          lemmaVTiledPositiveEnergy Q mesh
            (diagInterpolant Q mesh r.toH1Function).grad) := by
  have hcross := main_diag_q3_signed_covariance_integral_affine_corrector_tiled_le
    b L Q mesh p r
  have hW := lemmaVTiledWeakEnergy_nonneg Q mesh
    (r.toH1Function - diagInterpolant Q mesh r.toH1Function).grad
  have hP := lemmaVTiledPositiveEnergy_nonneg Q mesh
    (diagInterpolant Q mesh r.toH1Function).grad
  let W := lemmaVTiledWeakEnergy Q mesh
    (r.toH1Function - diagInterpolant Q mesh r.toH1Function).grad
  let P := lemmaVTiledPositiveEnergy Q mesh
    (diagInterpolant Q mesh r.toH1Function).grad
  have hW' : 0 ≤ W := by dsimp [W]; exact hW
  have hP' : 0 ≤ P := by dsimp [P]; exact hP
  have hroot : Real.sqrt W * Real.sqrt P ≤ (W + P) / 2 := by
    have hsq := sq_nonneg (Real.sqrt W - Real.sqrt P)
    have hw2 : Real.sqrt W ^ 2 = W := Real.sq_sqrt hW'
    have hp2 : Real.sqrt P ^ 2 = P := Real.sq_sqrt hP'
    nlinarith only [hsq, hw2, hp2]
  have hc : 0 ≤ b ^ 2 / 2 := by positivity
  calc
    _ ≤ (b ^ 2 / 2) * (Real.sqrt W * Real.sqrt P) := by
      calc
        _ ≤ (b ^ 2 / 2) *
            Real.sqrt (lemmaVTiledWeakEnergy Q mesh
              (r.toH1Function - diagInterpolant Q mesh r.toH1Function).grad) *
              Real.sqrt (lemmaVTiledPositiveEnergy Q mesh
                (diagInterpolant Q mesh r.toH1Function).grad) := hcross
        _ = _ := by simp only [W, P]; ring
    _ ≤ (b ^ 2 / 2) * ((W + P) / 2) :=
      mul_le_mul_of_nonneg_left hroot hc
    _ = (b ^ 2 / 4) * (W + P) := by ring

private theorem main_dualEnergy_le_primalEnergy_of_increment_series
    (Q : TriadicCube 2) {q : ℝ} (hq : 1 < q) {f : Vec 2 → ℝ}
    (hf : MemLp f 2 (normalizedCubeMeasure Q))
    (hpos : Summable (fun k : ℕ => q ^ (k + 1) *
      energy Q (cubeIncrement Q (k + 1) f))) :
    dualEnergy Q q f ≤ primalEnergy Q q f := by
  have hdual := summable_dual_increments Q hq hf
  have hqinv : q⁻¹ ≤ q := by
    calc
      q⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hq.le
      _ ≤ q := hq.le
  have hterms (k : ℕ) :
      (q⁻¹) ^ (k + 1) * energy Q (cubeIncrement Q (k + 1) f) ≤
        q ^ (k + 1) * energy Q (cubeIncrement Q (k + 1) f) :=
    mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (by positivity) hqinv (k + 1))
      (energy_nonneg Q _)
  unfold dualEnergy primalEnergy
  exact add_le_add_right (hdual.tsum_le_tsum hterms hpos) _

private theorem main_vectorWeakHaarEnergy_le_positive_of_summable
    (Q : TriadicCube 2) (F : Vec 2 → Fin 2 → ℝ)
    (hF : ∀ i : Fin 2, MemLp (fun x => F x i) 2 (normalizedCubeMeasure Q))
    (hpos : ∀ i : Fin 2, Summable (fun k : ℕ => (Real.sqrt 3) ^ (k + 1) *
      energy Q (cubeIncrement Q (k + 1) (fun x => F x i)))) :
    vectorWeakHaarEnergy Q F ≤ vectorPositiveHaarEnergy Q F := by
  unfold vectorWeakHaarEnergy vectorPositiveHaarEnergy
  apply Finset.sum_le_sum
  intro i hi
  exact main_dualEnergy_le_primalEnergy_of_increment_series Q
    (by
      have hs := Real.sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ 1)
        (by norm_num : (1 : ℝ) < 3)
      simpa using hs)
    (hF i) (hpos i)

private theorem main_tiledWeakEnergy_sub_le (Q : TriadicCube 2) (mesh : ℕ)
    (f g : H1Function (openCubeSet Q)) :
    lemmaVTiledWeakEnergy Q mesh (f - g).grad ≤
      2 * lemmaVTiledWeakEnergy Q mesh f.grad +
        2 * lemmaVTiledWeakEnergy Q mesh g.grad := by
  have hpoint (R : TriadicCube 2) (hR : R ∈ descendantsAtDepth Q mesh) :
      vectorWeakHaarEnergy R (f - g).grad ≤
        2 * vectorWeakHaarEnergy R f.grad +
          2 * vectorWeakHaarEnergy R g.grad := by
    have hF (i : Fin 2) : MemLp (fun x => f.grad x i) 2 (normalizedCubeMeasure R) :=
      memLp_on_descendant_of_memLp hR (f.grad_memL2_normalizedCubeMeasure i)
    have hG (i : Fin 2) : MemLp (fun x => g.grad x i) 2 (normalizedCubeMeasure R) :=
      memLp_on_descendant_of_memLp hR (g.grad_memL2_normalizedCubeMeasure i)
    have hpara := sensitivity_vectorWeakEnergy_parallelogram R f.grad g.grad hF hG
    have hnonneg := vectorWeakHaarEnergy_nonneg R
      (fun x i => f.grad x i + g.grad x i)
    have hsub : (f - g).grad = fun x i => f.grad x i - g.grad x i := by
      funext x i
      simp
    rw [hsub]
    linarith
  unfold lemmaVTiledWeakEnergy descendantsAverage
  calc
    _ ≤ ((descendantsAtDepth Q mesh).card : ℝ)⁻¹ *
        ∑ R ∈ descendantsAtDepth Q mesh,
          (2 * vectorWeakHaarEnergy R f.grad +
            2 * vectorWeakHaarEnergy R g.grad) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Finset.sum_le_sum hpoint
    _ = 2 * lemmaVTiledWeakEnergy Q mesh f.grad +
        2 * lemmaVTiledWeakEnergy Q mesh g.grad := by
      simp only [lemmaVTiledWeakEnergy, descendantsAverage]
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      ring

/-- The integrated signed covariance of the actual affine-corrector DIAG
trial is bounded by the original affine source weak energy, with no residual
or interpolant energy left in the conclusion. -/
theorem main_diag_q3_signed_covariance_integral_affine_corrector_source_le
    (b : ℝ) (L : {l : ℝ // 0 < l}) (Q : TriadicCube 2) (mesh : ℕ)
    (p : Vec 2) (r : H10Function (openCubeSet Q)) :
    |∑' k : ℕ,
      ∫ x, mainDiagQ3SignedLocalizedGradientTerm b L Q mesh
        (lemmaVAffinePotential (isOpenBoundedConvexDomain_openCubeSet Q) p r) k x
        ∂(normalizedCubeMeasure Q)| ≤
      b ^ 2 * lemmaVTiledWeakEnergy Q mesh
        (lemmaVAffinePotential (isOpenBoundedConvexDomain_openCubeSet Q) p r).grad := by
  let v := lemmaVAffinePotential (isOpenBoundedConvexDomain_openCubeSet Q) p r
  let I := diagInterpolant Q mesh r.toH1Function
  let ψ := r.toH1Function - I
  let Wv := lemmaVTiledWeakEnergy Q mesh v.grad
  let Wψ := lemmaVTiledWeakEnergy Q mesh ψ.grad
  let WI := lemmaVTiledWeakEnergy Q mesh I.grad
  let PI := lemmaVTiledPositiveEnergy Q mesh I.grad
  have hzero : lemmaVAffinePotential
      (isOpenBoundedConvexDomain_openCubeSet Q) 0 r = r.toH1Function := by
    ext x
    · simp only [lemmaVAffinePotential, H1Function.add_toFun,
        H1Function.affineOnIsSobolevRegularDomain_apply]
      simp
    · simp only [lemmaVAffinePotential, H1Function.add_grad,
        H1Function.affineOnIsSobolevRegularDomain_grad]
      simp
  have hcross := main_diag_q3_signed_covariance_integral_affine_corrector_tiled_le
    b L Q mesh p r
  have hIpos (R : TriadicCube 2) (hR : R ∈ descendantsAtDepth Q mesh)
      (i : Fin 2) :
      Summable (fun k : ℕ => (Real.sqrt 3) ^ (k + 1) * energy R
        (cubeIncrement R (k + 1) (fun x => I.grad x i))) := by
    have h := diagInterpolant_gradient_summable Q mesh 0 r R hR i
    rw [hzero] at h
    simpa only [I] using h
  have hweakPos (R : TriadicCube 2) (hR : R ∈ descendantsAtDepth Q mesh) :
      vectorWeakHaarEnergy R I.grad ≤ vectorPositiveHaarEnergy R I.grad := by
    exact main_vectorWeakHaarEnergy_le_positive_of_summable R I.grad
      (fun i => memLp_on_descendant_of_memLp hR
        (I.grad_memL2_normalizedCubeMeasure i)) (hIpos R hR)
  have hWI : WI ≤ PI := by
    unfold WI PI lemmaVTiledWeakEnergy lemmaVTiledPositiveEnergy descendantsAverage
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Finset.sum_le_sum
    intro R hR
    exact hweakPos R hR
  have hwr : lemmaVTiledWeakEnergy Q mesh r.toH1Function.grad ≤ Wv := by
    dsimp [Wv, v]
    exact diagTiledWeakEnergy_correction_le Q mesh p r
  have hpi0 : PI ≤ lemmaVTiledWeakEnergy Q mesh r.toH1Function.grad := by
    dsimp [PI, I]
    have hp := diagInterpolant_gradient_energy_le Q mesh 0 r
    rw [hzero] at hp
    simpa only using hp
  have hpi : PI ≤ Wv := hpi0.trans hwr
  have hWv : 0 ≤ Wv := by
    dsimp [Wv]
    exact lemmaVTiledWeakEnergy_nonneg Q mesh v.grad
  have hWψ : Wψ ≤ 4 * Wv := by
    have hsub := main_tiledWeakEnergy_sub_le Q mesh r.toH1Function I
    have hWψ' : Wψ ≤ 2 * lemmaVTiledWeakEnergy Q mesh r.toH1Function.grad +
        2 * WI := by simpa [Wψ, ψ] using hsub
    calc
      Wψ ≤ 2 * lemmaVTiledWeakEnergy Q mesh r.toH1Function.grad + 2 * WI := hWψ'
      _ ≤ 2 * Wv + 2 * PI := add_le_add
          (mul_le_mul_of_nonneg_left hwr (by norm_num))
          (mul_le_mul_of_nonneg_left hWI (by norm_num))
      _ ≤ 2 * Wv + 2 * Wv := add_le_add (le_refl _)
          (mul_le_mul_of_nonneg_left hpi (by norm_num))
      _ = 4 * Wv := by ring
  have hrootW : Real.sqrt Wψ ≤ 2 * Real.sqrt Wv := by
    apply (Real.sqrt_le_iff).2
    constructor
    · positivity
    · calc
        Wψ ≤ 4 * Wv := hWψ
        _ = (2 * Real.sqrt Wv) ^ 2 := by rw [mul_pow, Real.sq_sqrt hWv]; ring
  have hrootI : Real.sqrt PI ≤ Real.sqrt Wv := Real.sqrt_le_sqrt hpi
  have hprod : Real.sqrt Wψ * Real.sqrt PI ≤ 2 * Wv := by
    calc
      _ ≤ (2 * Real.sqrt Wv) * Real.sqrt PI :=
        mul_le_mul_of_nonneg_right hrootW (Real.sqrt_nonneg _)
      _ ≤ (2 * Real.sqrt Wv) * Real.sqrt Wv :=
        mul_le_mul_of_nonneg_left hrootI (by positivity)
      _ = 2 * Wv := by
        calc
          _ = 2 * Real.sqrt Wv ^ 2 := by ring
          _ = 2 * Wv := by rw [Real.sq_sqrt hWv]
  have hc : 0 ≤ b ^ 2 / 2 := by positivity
  change |∑' k : ℕ,
      ∫ x, mainDiagQ3SignedLocalizedGradientTerm b L Q mesh v k x
        ∂(normalizedCubeMeasure Q)| ≤ b ^ 2 * Wv
  calc
    _ ≤ (b ^ 2 / 2) *
        Real.sqrt (lemmaVTiledWeakEnergy Q mesh
          (r.toH1Function - diagInterpolant Q mesh r.toH1Function).grad) *
        Real.sqrt (lemmaVTiledPositiveEnergy Q mesh
          (diagInterpolant Q mesh r.toH1Function).grad) := hcross
    _ = (b ^ 2 / 2) * (Real.sqrt Wψ * Real.sqrt PI) := by
      simp only [Wψ, ψ, PI, I]
      ring
    _ ≤ (b ^ 2 / 2) * (2 * Wv) := mul_le_mul_of_nonneg_left hprod hc
    _ = b ^ 2 * Wv := by ring

/-- The source-energy covariance estimate sums across any finite family of
actual affine DIAG correctors without a dimension-dependent constant. -/
theorem main_diag_q3_signed_covariance_integral_affine_corrector_finite_source_le
    {ι : Type*} (s : Finset ι) (b : ℝ) (L : {l : ℝ // 0 < l})
    (Q : TriadicCube 2) (mesh : ℕ) (p : ι → Vec 2)
    (r : ι → H10Function (openCubeSet Q)) :
    |∑ i ∈ s, ∑' k : ℕ,
      ∫ x, mainDiagQ3SignedLocalizedGradientTerm b L Q mesh
        (lemmaVAffinePotential (isOpenBoundedConvexDomain_openCubeSet Q) (p i) (r i))
        k x ∂(normalizedCubeMeasure Q)| ≤
      b ^ 2 * ∑ i ∈ s, lemmaVTiledWeakEnergy Q mesh
        (lemmaVAffinePotential (isOpenBoundedConvexDomain_openCubeSet Q) (p i) (r i)).grad := by
  let C := b ^ 2
  have hC : 0 ≤ C := sq_nonneg b
  have hrow (i : ι) :
      |∑' k : ℕ,
        ∫ x, mainDiagQ3SignedLocalizedGradientTerm b L Q mesh
          (lemmaVAffinePotential (isOpenBoundedConvexDomain_openCubeSet Q) (p i) (r i))
          k x ∂(normalizedCubeMeasure Q)| ≤
        C * lemmaVTiledWeakEnergy Q mesh
          (lemmaVAffinePotential (isOpenBoundedConvexDomain_openCubeSet Q) (p i) (r i)).grad := by
    simpa only [C] using
      main_diag_q3_signed_covariance_integral_affine_corrector_source_le
        b L Q mesh (p i) (r i)
  calc
    _ ≤ ∑ i ∈ s, |∑' k : ℕ,
        ∫ x, mainDiagQ3SignedLocalizedGradientTerm b L Q mesh
          (lemmaVAffinePotential (isOpenBoundedConvexDomain_openCubeSet Q) (p i) (r i))
          k x ∂(normalizedCubeMeasure Q)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ s, C * lemmaVTiledWeakEnergy Q mesh
          (lemmaVAffinePotential (isOpenBoundedConvexDomain_openCubeSet Q) (p i) (r i)).grad := by
      apply Finset.sum_le_sum
      intro i hi
      exact hrow i
    _ = C * ∑ i ∈ s, lemmaVTiledWeakEnergy Q mesh
          (lemmaVAffinePotential (isOpenBoundedConvexDomain_openCubeSet Q) (p i) (r i)).grad := by
      rw [Finset.mul_sum]
    _ = _ := by simp only [C]

end ASDExplicitGamma.Main
