module

public import ASDExplicitGamma.Inverse.ClippedMatrix
public import ASDExplicitGamma.Inverse.PhysicalGaussianShear
public import ASDExplicitGamma.Variational.AdapterConstantSkew

/-! All-order matrix concentration with an independent later-shell shear family. -/

@[expose] public section
namespace ASDExplicitGamma.Inverse

open Homogenization MeasureTheory ProbabilityTheory Algsuperdiff.Section3
open scoped ENNReal NNReal Matrix.Norms.Elementwise
noncomputable section

/-- Independent centered variables with individual interval radii retain the
exact weighted square sum. -/
theorem independent_entry_variable_radius_Lp {Ω I : Type*} [MeasurableSpace Ω]
    [Fintype I] (μ : Measure Ω) [IsProbabilityMeasure μ] (X : I → Ω → ℝ)
    (hind : iIndepFun X μ) (hm : ∀ i, Measurable (X i)) (G : I → ℝ)
    (hG : ∀ i, 0 ≤ G i)
    (hb : ∀ i, ∀ᵐ ω ∂μ, |X i ω| ≤ G i) (w : I → ℝ) (p : ℝ) (hp : 1 ≤ p) :
    eLpNorm (fun ω => ∑ i, w i*(X i ω-∫ ζ, X i ζ ∂μ)) (ENNReal.ofReal p) μ ≤
      ENNReal.ofReal (2*Real.sqrt p*Real.sqrt (∑ i, (w i*G i)^2)) := by
  let Y : I → Ω → ℝ := fun i ω => w i*(X i ω-∫ ζ, X i ζ ∂μ)
  let c : I → ℝ≥0 := fun i => ⟨(w i*G i)^2, sq_nonneg _⟩
  have hc (i : I) : HasSubgaussianMGF (Y i) (c i) μ := by
    have h0 := hasSubgaussianMGF_of_mem_Icc (hm i).aemeasurable
      ((hb i).mono (fun ω hω => abs_le.mp hω))
    have h1 := h0.const_mul (w i)
    convert h1 using 1
    apply NNReal.eq
    change (w i*G i)^2 = (w i)^2*(|G i- -G i|/2)^2
    rw [abs_of_nonneg (by linarith only [hG i] : 0 ≤ G i- -G i)]
    ring
  have hi : iIndepFun Y μ := hind.comp (fun i x => w i*(x-∫ ζ, X i ζ ∂μ))
    (fun _ => measurable_const.mul (measurable_id.sub_const _))
  have hs : HasSubgaussianMGF (fun ω => ∑ i, Y i ω) (∑ i, c i) μ :=
    HasSubgaussianMGF.sum_of_iIndepFun hi (fun i _ => hc i)
  have hh := clipped_subGaussian_Lp μ (fun ω => ∑ i, Y i ω) (∑ i, c i) hs p hp
  apply hh.trans_eq
  congr 1
  have he : ((∑ i, c i : ℝ≥0):ℝ) = ∑ i, (w i*G i)^2 := by
    rw [NNReal.coe_sum]
    change (∑ i, (w i*G i)^2) = _
    rfl
  rw [he]

/-- The colored version of the variable-radius Hoeffding estimate. -/
theorem colored_entry_variable_radius_Lp {Ω I K : Type*} [MeasurableSpace Ω]
    [Fintype I] [Fintype K] [DecidableEq K]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : I → Ω → ℝ) (color : I → K)
    (hind : ∀ k, iIndepFun (fun i : {i // color i=k} => X i.1) μ)
    (hm : ∀ i, Measurable (X i)) (G : I → ℝ) (hG : ∀ i, 0 ≤ G i)
    (hb : ∀ i, ∀ᵐ ω ∂μ, |X i ω| ≤ G i) (w : I → ℝ) (p : ℝ) (hp : 1 ≤ p) :
    eLpNorm (fun ω => ∑ i, w i*(X i ω-∫ ζ, X i ζ ∂μ)) (ENNReal.ofReal p) μ ≤
      ENNReal.ofReal (2*Real.sqrt p*Real.sqrt (∑ i, (w i*G i)^2)*
        Real.sqrt (Fintype.card K:ℝ)) := by
  let C : K → Ω → ℝ := fun k ω =>
    ∑ i : {i // color i=k}, w i.1*(X i.1 ω-∫ ζ, X i.1 ζ ∂μ)
  let V : K → ℝ := fun k => ∑ i : {i // color i=k}, (w i.1*G i.1)^2
  have hc (k : K) := independent_entry_variable_radius_Lp μ
    (fun i : {i // color i=k} => X i.1) (hind k) (fun i => hm i.1)
    (fun i => G i.1) (fun i => hG i.1) (fun i => hb i.1) (fun i => w i.1) p hp
  have he : (fun ω => ∑ i, w i*(X i ω-∫ ζ, X i ζ ∂μ)) = ∑ k, C k := by
    funext ω
    simp only [Finset.sum_apply,C]
    exact (Fintype.sum_fiberwise color (fun i => w i*(X i ω-∫ ζ, X i ζ ∂μ))).symm
  rw [he]
  apply (eLpNorm_sum_le (ENNReal.one_le_ofReal.mpr hp)).trans
  calc
    _ ≤ ∑ k, ENNReal.ofReal (2*Real.sqrt p*Real.sqrt (V k)) :=
      Finset.sum_le_sum (fun k _ => hc k)
    _ = ENNReal.ofReal (∑ k, 2*Real.sqrt p*Real.sqrt (V k)) := by
      exact (ENNReal.ofReal_sum_of_nonneg (fun k _ => by positivity)).symm
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      rw [← Finset.mul_sum]
      have hC : 0 ≤ 2*Real.sqrt p := by positivity
      have hs := mul_le_mul_of_nonneg_left
        (localization_color_sqrt_sum V (fun _ => by dsimp [V]; positivity)) hC
      have hV : (∑ k, V k) = ∑ i, (w i*G i)^2 := by
        exact Fintype.sum_fiberwise color (fun i => (w i*G i)^2)
      rw [hV] at hs
      simpa only [mul_assoc] using hs

/-- A product-space Lp estimate from uniform bounds on all second-coordinate
sections. -/
theorem eLpNorm_product_sections_le {α β E : Type*} [MeasurableSpace α]
    [MeasurableSpace β] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [ContinuousENorm E]
    (μ : Measure α) (ν : Measure β) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (p : ℝ) (hp : 1 ≤ p) (f : α × β → E) (g : α → ℝ)
    (hf : Measurable f) (hg : Measurable g) (hg0 : ∀ a, 0 ≤ g a)
    (hsec : ∀ a, eLpNorm (fun b => f (a,b)) (ENNReal.ofReal p) ν ≤ ENNReal.ofReal (g a)) :
    eLpNorm f (ENNReal.ofReal p) (μ.prod ν) ≤ eLpNorm g (ENNReal.ofReal p) μ := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hq0 : ENNReal.ofReal p ≠ 0 := (ENNReal.ofReal_pos.mpr hp0).ne'
  have hqtop : ENNReal.ofReal p ≠ ∞ := ENNReal.ofReal_ne_top
  have hpow (a : α) :
      (∫⁻ b, ‖f (a,b)‖ₑ ^ p ∂ν) ^ (1/p) ≤ ENNReal.ofReal (g a) := by
    have hs := hsec a
    have hfsec : Measurable (fun b => f (a,b)) := by
      exact hf.comp (measurable_const.prodMk measurable_id)
    have hformula := eLpNorm_eq_lintegral_rpow_enorm_toReal (μ := ν)
      hq0 hqtop hfsec.aestronglyMeasurable
    rw [hformula, ENNReal.toReal_ofReal hp0.le] at hs
    simpa only [ENNReal.toReal_ofReal hp0.le] using hs
  have hpow' (a : α) :
      ∫⁻ b, ‖f (a,b)‖ₑ ^ p ∂ν ≤ ENNReal.ofReal (g a)^p := by
    have hh := ENNReal.rpow_le_rpow (hpow a) hp0.le
    have hleft : ((∫⁻ b, ‖f (a,b)‖ₑ ^ p ∂ν) ^ (1/p)) ^ p =
        ∫⁻ b, ‖f (a,b)‖ₑ ^ p ∂ν := by
      rw [← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hp0.ne', ENNReal.rpow_one]
    rw [hleft] at hh
    exact hh
  have hF : AEMeasurable (fun z : α × β => ‖f z‖ₑ ^ p) (μ.prod ν) :=
    (hf.enorm.pow_const p).aemeasurable
  have hprod := lintegral_prod (fun z : α × β => ‖f z‖ₑ ^ p) hF
  have hInt :
      ∫⁻ z, ‖f z‖ₑ ^ p ∂(μ.prod ν) ≤ ∫⁻ a, ‖g a‖ₑ ^ p ∂μ := by
    rw [hprod]
    exact lintegral_mono (fun a => by
      rw [Real.enorm_eq_ofReal (hg0 a)]
      exact hpow' a)
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hq0 hqtop hf.aestronglyMeasurable,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hq0 hqtop hg.aestronglyMeasurable]
  simpa only [ENNReal.toReal_ofReal hp0.le] using
    ENNReal.rpow_le_rpow hInt (one_div_nonneg.mpr hp0.le)

/-- The Lp norm of a weighted Euclidean family is bounded by the Euclidean
sum of its coordinate Lp bounds when p is at least two. -/
theorem weighted_shear_radius_Lp {β I : Type*} [MeasurableSpace β]
    [Fintype I] (μ : Measure β) (p : ℝ) (hp : 2 ≤ p)
    (A : I → β → ℝ) (hAmeas : ∀ i, Measurable (A i))
    (hA0 : ∀ i b, 0 ≤ A i b) (w L : I → ℝ)
    (hL : ∀ i, 0 ≤ L i)
    (hA : ∀ i, eLpNorm (A i) (ENNReal.ofReal p) μ ≤ ENNReal.ofReal (L i)) :
    eLpNorm (fun b => Real.sqrt (∑ i, w i^2 * (A i b)^2))
      (ENNReal.ofReal p) μ ≤ ENNReal.ofReal (Real.sqrt (∑ i, (w i*L i)^2)) := by
  have hp0 : 0 < p := by linarith
  have hhalf : 1 ≤ p/2 := by linarith
  let U : β → ℝ := fun b => ∑ i, w i^2 * (A i b)^2
  have hUmeas : Measurable U := by
    dsimp [U]
    exact Finset.measurable_sum _ (fun i _ =>
      measurable_const.mul ((hAmeas i).pow_const 2))
  have hU0 (b : β) : 0 ≤ U b := by
    dsimp [U]
    exact Finset.sum_nonneg (fun i _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))
  have hterm (i : I) :
      eLpNorm (fun b => w i^2 * (A i b)^2) (ENNReal.ofReal (p/2)) μ ≤
        ENNReal.ofReal ((w i*L i)^2) := by
    have hpow : eLpNorm (fun b => (A i b)^2) (ENNReal.ofReal (p/2)) μ =
        (eLpNorm (A i) (ENNReal.ofReal p) μ)^2 := by
      have hnorm : (fun b => ‖A i b‖ ^ (2:ℝ)) = fun b => (A i b)^2 := by
        funext b
        calc
          ‖A i b‖ ^ (2:ℝ) = A i b ^ (2:ℝ) := by
            rw [Real.norm_eq_abs, abs_of_nonneg (hA0 i b)]
          _ = (A i b)^2 := Real.rpow_natCast (A i b) 2
      rw [← hnorm]
      rw [eLpNorm_norm_rpow (A i) (hAmeas i).aestronglyMeasurable
        (by norm_num : (0:ℝ) < 2)]
      have hmul : ENNReal.ofReal (p/2) * ENNReal.ofReal 2 = ENNReal.ofReal p := by
        have h := ENNReal.ofReal_mul (p := p/2) (q := 2)
          (by positivity : 0 ≤ p/2)
        calc
          _ = ENNReal.ofReal ((p/2)*2) := h.symm
          _ = ENNReal.ofReal p := by congr 1; ring
      rw [hmul]
      exact ENNReal.rpow_natCast _ 2
    calc
      eLpNorm (fun b => w i^2 * (A i b)^2) (ENNReal.ofReal (p/2)) μ =
          ENNReal.ofReal (w i^2) * eLpNorm (fun b => (A i b)^2)
            (ENNReal.ofReal (p/2)) μ := by
          rw [show (fun b => w i^2 * (A i b)^2) = (w i^2) • (fun b => (A i b)^2) by
            funext b
            simp only [Pi.smul_apply, smul_eq_mul]]
          rw [eLpNorm_const_smul, Real.enorm_eq_ofReal (sq_nonneg (w i))]
      _ = ENNReal.ofReal (w i^2) * (eLpNorm (A i) (ENNReal.ofReal p) μ)^2 := by
          rw [hpow]
      _ ≤ ENNReal.ofReal (w i^2) * (ENNReal.ofReal (L i))^2 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left' (hA i) 2) bot_le
      _ = ENNReal.ofReal ((w i*L i)^2) := by
          rw [← ENNReal.ofReal_pow (hL i) 2]
          rw [← ENNReal.ofReal_mul (sq_nonneg (w i))]
          congr 1
          ring
  have hsum := finite_density_sum_Lp μ (ENNReal.ofReal (p/2))
    (ENNReal.one_le_ofReal.mpr hhalf) (fun i b => w i^2 * (A i b)^2)
    (fun _ => 1) (fun i => (w i*L i)^2) (fun _ => by norm_num)
    (fun i => sq_nonneg (w i*L i)) hterm
  have hU : eLpNorm U (ENNReal.ofReal (p/2)) μ ≤
      ENNReal.ofReal (∑ i, (w i*L i)^2) := by
    simpa [U] using hsum
  have hroot := density_sqrt_Lp μ U hUmeas.aestronglyMeasurable hU0
    (p/2) (∑ i, (w i*L i)^2) (by linarith) (by positivity) hU
  have hpEq : 2*(p/2) = p := by ring
  rw [hpEq] at hroot
  exact hroot

/-- Colored full-matrix concentration when each summand has its own
deterministic entry radius. -/
theorem colored_matrix_variable_radius_Lp {Ω I K n : Type*}
    [MeasurableSpace Ω] [Fintype I] [Fintype K] [DecidableEq K]
    [Fintype n] [DecidableEq n] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y : I → Ω → Matrix n n ℝ) (mean : I → Matrix n n ℝ)
    (hmean : ∀ i a b, mean i a b = ∫ ζ, Y i ζ a b ∂μ) (color : I → K)
    (hind : ∀ k, iIndepFun (fun i : {i // color i=k} => Y i.1) μ)
    (hm : ∀ i, Measurable (Y i)) (G : I → ℝ) (hG : ∀ i, 0 ≤ G i)
    (hb : ∀ i a b, ∀ᵐ ω ∂μ, |Y i ω a b| ≤ G i)
    (w : I → ℝ) (p : ℝ) (hp : 1 ≤ p) :
    eLpNorm (fun ω => ‖Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ)
      (∑ i, w i • (Y i ω-mean i))‖)
      (ENNReal.ofReal p) μ ≤ ENNReal.ofReal ((Fintype.card n:ℝ)^2 *
        (2*Real.sqrt p*Real.sqrt (∑ i, (w i*G i)^2)*Real.sqrt (Fintype.card K:ℝ))) := by
  let F : Ω → Matrix n n ℝ := fun ω a b =>
    ∑ i, w i*(Y i ω a b-mean i a b)
  have hFm (a b : n) : Measurable (fun ω => F ω a b) := by
    simp only [F]
    exact Finset.measurable_sum _ (fun i _ =>
      ((measurable_pi_apply b).comp ((measurable_pi_apply a).comp (hm i))).sub_const _ |>.const_mul _)
  have hentry (a b : n) :
      eLpNorm (fun ω => F ω a b) (ENNReal.ofReal p) μ ≤
        ENNReal.ofReal (2*Real.sqrt p*Real.sqrt (∑ i, (w i*G i)^2)*
          Real.sqrt (Fintype.card K:ℝ)) := by
    have hi (k : K) : iIndepFun
        (fun i : {i // color i=k} => fun ω => Y i.1 ω a b) μ :=
      (hind k).comp (fun _ A => A a b)
        (fun _ => (measurable_pi_apply b).comp (measurable_pi_apply a))
    have hh := colored_entry_variable_radius_Lp μ (fun i ω => Y i ω a b)
      color hi (fun i => (measurable_pi_apply b).comp ((measurable_pi_apply a).comp (hm i)))
      G hG (fun i => hb i a b) w p hp
    simpa only [F, hmean] using hh
  have hh := clipped_matrix_Lp_of_entries μ F hFm (ENNReal.ofReal p)
    (ENNReal.one_le_ofReal.mpr hp)
    (2*Real.sqrt p*Real.sqrt (∑ i, (w i*G i)^2)*Real.sqrt (Fintype.card K:ℝ))
    (by positivity) hentry
  have he (ω : Ω) : F ω =
      ∑ i, w i • (Y i ω-mean i) := by
    ext a b
    simp only [F, Matrix.sum_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
  have hefun : (fun ω => ‖Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ) (F ω)‖) =
      fun ω => ‖Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ)
        (∑ i, w i • (Y i ω-mean i))‖ := by
    funext ω
    exact congrArg (fun A : Matrix n n ℝ =>
      ‖Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ) A‖) (he ω)
  simpa only [hefun] using hh

/-- Matrix Bochner integrals commute with entry evaluation. -/
theorem integral_matrix_entry_eq {β n : Type*} [MeasurableSpace β]
    [Fintype n] (μ : Measure β) (F : β → Matrix n n ℝ)
    (hF : Integrable F μ) (a b : n) :
    (∫ z, F z ∂μ) a b = ∫ z, F z a b ∂μ := by
  let L : Matrix n n ℝ →ₗ[ℝ] ℝ :=
    { toFun := fun A => A a b
      map_add' := by intro A B; rfl
      map_smul' := by intro c A; rfl }
  let E : Matrix n n ℝ →L[ℝ] ℝ := ⟨L,L.continuous_of_finiteDimensional⟩
  exact (E.integral_comp_comm hF).symm

/-- Operator-norm control for a matrix congruence. -/
theorem matrix_congruence_opNorm_le (R A : FullBlockMat 2) (G : ℝ)
    (_hG : 0 ≤ G)
    (hA : ‖Matrix.toEuclideanCLM (n := BlockCoord 2) (𝕜 := ℝ) A‖ ≤ G) :
    ‖Matrix.toEuclideanCLM (n := BlockCoord 2) (𝕜 := ℝ)
      (R.transpose*A*R)‖ ≤ G*‖Matrix.toEuclideanCLM (n := BlockCoord 2) (𝕜 := ℝ) R‖^2 := by
  let T := Matrix.toEuclideanCLM (n := BlockCoord 2) (𝕜 := ℝ)
  have htr : star R = R.transpose := by
    rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
  have hmap : T (R.transpose*A*R) = star (T R) * T A * T R := by
    calc
      T (R.transpose*A*R) = T (R.transpose*A) * T R := map_mul T _ _
      _ = T R.transpose * T A * T R := by rw [map_mul]
      _ = star (T R) * T A * T R := by rw [← htr, map_star]
  calc
    ‖T (R.transpose*A*R)‖ = ‖star (T R) * T A * T R‖ := by rw [hmap]
    _ ≤ ‖star (T R)‖*‖T A‖*‖T R‖ := by
      calc
        _ ≤ ‖star (T R) * T A‖*‖T R‖ := norm_mul_le _ _
        _ ≤ (‖star (T R)‖*‖T A‖)*‖T R‖ :=
          mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
    _ = ‖T R‖*‖T A‖*‖T R‖ := by
      have hs : ‖star (T R)‖ = ‖T R‖ := by
        rw [ContinuousLinearMap.star_eq_adjoint]
        exact ContinuousLinearMap.adjoint.norm_map _
      rw [hs]
    _ ≤ G*‖T R‖^2 := by nlinarith only [hA, norm_nonneg (T R), _hG]

/-- The flattened Euclidean carrier and the doubled Hilbert block carrier have
the same coordinate norm. -/
theorem hilbertBlockVec_euclidean_norm_eq
    (x : EuclideanSpace ℝ (BlockCoord 2)) :
    ‖x‖ = ‖HilbertBlockVec.ofBlockVec (ofFullBlockVec x.ofLp)‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [EuclideanSpace.norm_sq_eq, HilbertBlockVec.norm_sq_ofBlockVec]
  simp [Homogenization.blockVecDot, Homogenization.vecDot,
    Homogenization.ofFullBlockVec, Fintype.sum_sum_type] <;> ring

/-- The full matrix operator norm is controlled by the identical action on the
source's doubled Euclidean block carrier. -/
theorem fullMatrix_opNorm_le_hilbertBlockMat (A : FullBlockMat 2) :
    ‖Matrix.toEuclideanCLM (n := BlockCoord 2) (𝕜 := ℝ) A‖ ≤
      ‖HilbertBlockVec.applyBlockMat (ofFullBlockMat A)‖ := by
  let T := Matrix.toEuclideanCLM (n := BlockCoord 2) (𝕜 := ℝ)
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) ?_
  intro x
  let v : BlockVec 2 := ofFullBlockVec x.ofLp
  have hx : x = WithLp.toLp 2 (toFullBlockVec v) := by
    ext a
    cases a <;> rfl
  have happly : T A x = WithLp.toLp 2
      (toFullBlockVec (blockMatVecMul (ofFullBlockMat A) v)) := by
    rw [hx]
    simp [T, Matrix.toEuclideanCLM_toLp, toFullBlockVec_blockMatVecMul]
  have hout : ‖T A x‖ =
      ‖HilbertBlockVec.applyBlockMat (ofFullBlockMat A)
        (HilbertBlockVec.ofBlockVec v)‖ := by
    rw [happly, HilbertBlockVec.applyBlockMat_apply]
    have hn := hilbertBlockVec_euclidean_norm_eq
      (WithLp.toLp 2 (toFullBlockVec (blockMatVecMul (ofFullBlockMat A) v)) :
        EuclideanSpace ℝ (BlockCoord 2))
    simpa [v, Homogenization.ofFullBlockVec_toFullBlockVec] using hn
  calc
    ‖T A x‖ =
        ‖HilbertBlockVec.applyBlockMat (ofFullBlockMat A)
          (HilbertBlockVec.ofBlockVec v)‖ := hout
    _ ≤ ‖HilbertBlockVec.applyBlockMat (ofFullBlockMat A)‖ *
        ‖HilbertBlockVec.ofBlockVec v‖ :=
          (HilbertBlockVec.applyBlockMat (ofFullBlockMat A)).le_opNorm _
    _ = ‖HilbertBlockVec.applyBlockMat (ofFullBlockMat A)‖ * ‖x‖ := by
          rw [← hilbertBlockVec_euclidean_norm_eq x]

/-- The concrete source physical shear is the block operator represented by
the source constant-skew full matrix, with its actual sign convention. -/
theorem physical_shear_eq_constantSkewMatrix (σ η : ℝ) :
    ASDExplicitGamma.Gaussian.missingWaveShearOperator σ η =
      HilbertBlockVec.applyBlockMat
        (ofFullBlockMat (ASDExplicitGamma.Variational.constantSkewMatrix (-(η/σ)))) := by
  apply ContinuousLinearMap.ext
  intro X
  apply HilbertBlockVec.ext
  · apply HilbertVec.ext
    intro i
    fin_cases i <;> simp [ASDExplicitGamma.Gaussian.missingWaveShearOperator,
      Response.responseShearPointwiseOperator_apply,
      HilbertBlockVec.applyBlockMat_apply, ASDExplicitGamma.Variational.constantSkewMatrix,
      Homogenization.ofFullBlockMat, Homogenization.blockMatVecMul,
      Homogenization.toFullBlockMat, Homogenization.matVecMul,
      HilbertBlockVec.potential, HilbertBlockVec.flux, HilbertVec.toVec,
      Response.responsePlanarJ, Fin.sum_univ_two] <;> ring_nf
  · ext i
    fin_cases i <;> simp [ASDExplicitGamma.Gaussian.missingWaveShearOperator,
      Response.responseShearPointwiseOperator_apply,
      HilbertBlockVec.applyBlockMat_apply, ASDExplicitGamma.Variational.constantSkewMatrix,
      Homogenization.ofFullBlockMat, Homogenization.blockMatVecMul,
      Homogenization.toFullBlockMat, Homogenization.matVecMul,
      HilbertBlockVec.potential, HilbertBlockVec.flux, HilbertVec.toVec,
      Response.responsePlanarJ, Fin.sum_univ_two] <;> ring_nf

/-- Full-matrix representative of the actual later-shell physical shear on a
translated square. -/
def physicalShearMatrix (A : ABKModel 2) (j n N : ℤ) (a c : ℝ)
    (weights : ℤ → ℝ) (ω : Cutoff.CutoffSample 2) : FullBlockMat 2 :=
  ASDExplicitGamma.Variational.constantSkewMatrix
    (-(physicalMissingWaveAverage A j n N a c weights ω / Annealed.sigmaBar A j))

/-- The full-matrix representative of the physical shear is ambient measurable. -/
theorem physical_shear_matrix_measurable (A : ABKModel 2)
    (j n N : ℤ) (a c : ℝ) (weights : ℤ → ℝ) :
    Measurable (physicalShearMatrix A j n N a c weights) := by
  let K := ASDExplicitGamma.Gaussian.closedRectangle
    a (a+(3:ℝ)^n) c (c+(3:ℝ)^n)
  have havg : Measurable (physicalMissingWaveAverage A j n N a c weights) := by
    exact (ASDExplicitGamma.Gaussian.q3SpatialAverageCLM
      (by rw [ASDExplicitGamma.Gaussian.spatialVolume_square_real
        (R := (3:ℝ)^n) (by positivity)]; positivity)).continuous.measurable.comp
      (ASDExplicitGamma.Gaussian.measurable_modelWeightedBand K
        (ASDExplicitGamma.Gaussian.wholeRootShellLabel j N)
        (ASDExplicitGamma.Gaussian.wholeRootWeights j N weights))
  change Measurable (fun ω =>
    ASDExplicitGamma.Variational.constantSkewMatrix
      (-(physicalMissingWaveAverage A j n N a c weights ω / Annealed.sigmaBar A j)))
  apply Measurable.of_eval_matrix
  intro α β
  fin_cases α <;> fin_cases β <;>
    simp [ASDExplicitGamma.Variational.constantSkewMatrix,
      Homogenization.toFullBlockMat, Response.responsePlanarJ] <;> fun_prop

/-- The all-order shear moment controls the full-matrix representative as
well, with no change to its source moment budget. -/
theorem physical_shear_matrix_sq_Lp (A : ABKModel 2) (h : ℝ)
    (hA : PlanarQ3Gaussian A h) (j n N : ℤ) (hstrict : j < N)
    (hstate : nativeInductionState A h j) (a c : ℝ) (weights : ℤ → ℝ)
    (hw : ∀ k ∈ Finset.Ioc j N, 0 ≤ weights k ∧ weights k ≤ 1)
    (p : ℝ) (hp : 1 ≤ p) :
    eLpNorm (fun ω => ‖Matrix.toEuclideanCLM (n := BlockCoord 2) (𝕜 := ℝ)
      (physicalShearMatrix A j n N a c weights ω)‖^2) (ENNReal.ofReal p)
      (Cutoff.cutoffSampleLaw A).toMeasure ≤
      ENNReal.ofReal (2+80*(p+2)*(A.gamma*(N-j:ℝ)*(3:ℝ)^(2*A.gamma*(N-j:ℝ)))) := by
  let K := ASDExplicitGamma.Gaussian.closedRectangle
    a (a+(3:ℝ)^n) c (c+(3:ℝ)^n)
  let μ := (Cutoff.cutoffSampleLaw A).toMeasure
  let avg := physicalMissingWaveAverage A j n N a c weights
  let T := Matrix.toEuclideanCLM (n := BlockCoord 2) (𝕜 := ℝ)
  let R := physicalShearMatrix A j n N a c weights
  have havg : Measurable avg := by
    dsimp [avg, physicalMissingWaveAverage, K,
      ASDExplicitGamma.Gaussian.wholeRootModelBand]
    exact (ASDExplicitGamma.Gaussian.q3SpatialAverageCLM
      (by rw [ASDExplicitGamma.Gaussian.spatialVolume_square_real
        (R := (3:ℝ)^n) (by positivity)]; positivity)).continuous.measurable.comp
        (ASDExplicitGamma.Gaussian.measurable_modelWeightedBand _ _ _)
  have hR : Measurable R := by
    change Measurable (fun ω =>
      ASDExplicitGamma.Variational.constantSkewMatrix (-(avg ω/Annealed.sigmaBar A j)))
    apply Measurable.of_eval_matrix
    intro α β
    fin_cases α <;> fin_cases β <;>
      simp [ASDExplicitGamma.Variational.constantSkewMatrix,
        Homogenization.toFullBlockMat, Response.responsePlanarJ] <;> fun_prop
  let L : FullBlockMat 2 →ₗ[ℝ]
      (EuclideanSpace ℝ (BlockCoord 2) →L[ℝ] EuclideanSpace ℝ (BlockCoord 2)) :=
    { toFun := T
      map_add' := fun B C => map_add T B C
      map_smul' := fun r B => map_smul T r B }
  have hnormMeas : Measurable (fun ω => ‖T (R ω)‖) :=
    L.continuous_of_finiteDimensional.norm.measurable.comp hR
  have hsqMeas : Measurable (fun ω => ‖T (R ω)‖^2) := hnormMeas.pow_const 2
  have hdom (ω : Cutoff.CutoffSample 2) :
      ‖T (R ω)‖^2 ≤ ‖physicalMissingWaveShear A j n N a c weights ω‖^2 := by
    have hnorm := fullMatrix_opNorm_le_hilbertBlockMat
      (ASDExplicitGamma.Variational.constantSkewMatrix
        (-(avg ω / Annealed.sigmaBar A j)))
    have hsame : physicalMissingWaveShear A j n N a c weights ω =
        ASDExplicitGamma.Gaussian.missingWaveShearOperator
          (Annealed.sigmaBar A j) (avg ω) := by
      rfl
    rw [← physical_shear_eq_constantSkewMatrix] at hnorm
    rw [hsame]
    exact pow_le_pow_left₀ (norm_nonneg _) (by simpa [T, R, physicalShearMatrix] using hnorm) 2
  have hmono : eLpNorm (fun ω => ‖T (R ω)‖^2) (ENNReal.ofReal p) μ ≤
      eLpNorm (fun ω => ‖physicalMissingWaveShear A j n N a c weights ω‖^2)
        (ENNReal.ofReal p) μ :=
    eLpNorm_mono_ae_real hsqMeas.aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => by
        exact (Real.norm_of_nonneg (sq_nonneg _)).symm ▸ hdom ω)
  exact hmono.trans (physical_missing_wave_shear_sq_Lp A h hA j n N hstrict hstate
    a c weights hw p hp)

/-- A complete physical later-shell shear on a deterministic square is
measurable with respect to the entire later-shell sigma field. -/
theorem physical_shear_matrix_later_measurable (A : ABKModel 2)
    (j n N : ℤ) (hjn : j ≤ N) (a c : ℝ) (weights : ℤ → ℝ) :
    @Measurable (Cutoff.CutoffSample 2) (FullBlockMat 2)
      (Model.cutoffLaterSigma (Set.Ioi j)) _
      (physicalShearMatrix A j n N a c weights) := by
  let K := ASDExplicitGamma.Gaussian.closedRectangle
    a (a+(3:ℝ)^n) c (c+(3:ℝ)^n)
  letI : MeasurableSpace (Cutoff.CutoffSample 2) :=
    Model.cutoffLaterSigma (Set.Ioi j)
  have hlabel (i : Fin (ASDExplicitGamma.Gaussian.wholeRootBandLength j N)) :
      ASDExplicitGamma.Gaussian.wholeRootShellLabel j N i ∈ Set.Ioi j := by
    change j < ASDExplicitGamma.Gaussian.wholeRootShellLabel j N i
    simp [ASDExplicitGamma.Gaussian.wholeRootShellLabel]
    omega
  have hcoord (i : Fin (ASDExplicitGamma.Gaussian.wholeRootBandLength j N)) :
      Measurable (fun ω : Cutoff.CutoffSample 2 =>
        ω.1 (ASDExplicitGamma.Gaussian.wholeRootShellLabel j N i)) := by
    exact (Cutoff.measurable_shellCoordinate_shellIndexSigma
      (I := Set.Ioi j) (k := ASDExplicitGamma.Gaussian.wholeRootShellLabel j N i)
      (hlabel i)).comp
        (Measurable.of_comap_le le_rfl)
  have hband : Measurable (fun ω : Cutoff.CutoffSample 2 =>
      ASDExplicitGamma.Gaussian.wholeRootModelBand
        (a := a) (b := a+(3:ℝ)^n) (c := c) (d := c+(3:ℝ)^n) j N weights ω) := by
    change Measurable (fun ω : Cutoff.CutoffSample 2 =>
      ∑ i : Fin (ASDExplicitGamma.Gaussian.wholeRootBandLength j N),
        ASDExplicitGamma.Gaussian.wholeRootWeights j N weights i •
          ASDExplicitGamma.Gaussian.shellFieldScalarRestriction K
            (ω.1 (ASDExplicitGamma.Gaussian.wholeRootShellLabel j N i)))
    apply Finset.measurable_sum
    intro i hi
    exact ((ASDExplicitGamma.Gaussian.measurable_shellFieldScalarRestriction K).comp
      (hcoord i)).const_smul (ASDExplicitGamma.Gaussian.wholeRootWeights j N weights i)
  have havg : Measurable (physicalMissingWaveAverage A j n N a c weights) := by
    change Measurable (fun ω : Cutoff.CutoffSample 2 =>
      ASDExplicitGamma.Gaussian.q3SpatialAverageCLM
      (by rw [ASDExplicitGamma.Gaussian.spatialVolume_square_real
        (R := (3:ℝ)^n) (by positivity)]; positivity)
        (ASDExplicitGamma.Gaussian.wholeRootModelBand
          (a := a) (b := a+(3:ℝ)^n) (c := c) (d := c+(3:ℝ)^n) j N weights ω))
    exact ((ASDExplicitGamma.Gaussian.q3SpatialAverageCLM
      (by rw [ASDExplicitGamma.Gaussian.spatialVolume_square_real
        (R := (3:ℝ)^n) (by positivity)]; positivity)).continuous.measurable).comp hband
  change Measurable (fun ω =>
    ASDExplicitGamma.Variational.constantSkewMatrix
      (-(physicalMissingWaveAverage A j n N a c weights ω /
        Annealed.sigmaBar A j)))
  apply Measurable.of_eval_matrix
  intro α β
  fin_cases α <;> fin_cases β <;>
    simp [ASDExplicitGamma.Variational.constantSkewMatrix,
      Homogenization.toFullBlockMat, Response.responsePlanarJ] <;> fun_prop

/-- Fixed conjugators preserve colored independence and insert their fourth
operator-norm moments as the individual Hoeffding radii. -/
theorem fixed_shear_matrix_concentration_Lp {β I K : Type*} [MeasurableSpace β]
    [Fintype I] [Fintype K] [DecidableEq K]
    (ν : Measure β) [IsProbabilityMeasure ν] (Y : I → β → FullBlockMat 2)
    (color : I → K)
    (hind : ∀ k, iIndepFun (fun i : {i // color i=k} => Y i.1) ν)
    (hm : ∀ i, Measurable (Y i)) (R : I → FullBlockMat 2)
    (G : ℝ) (hG : 0 ≤ G)
    (hY : ∀ i, ∀ᵐ y ∂ν,
      ‖Matrix.toEuclideanCLM (n := BlockCoord 2) (𝕜 := ℝ) (Y i y)‖ ≤ G)
    (hYint : ∀ i, Integrable (Y i) ν)
    (w : I → ℝ) (p : ℝ) (hp : 1 ≤ p) :
    eLpNorm (fun y => ‖Matrix.toEuclideanCLM (n := BlockCoord 2) (𝕜 := ℝ)
      (∑ i, w i • ((R i).transpose*(Y i y-∫ z, Y i z ∂ν)*R i))‖)
      (ENNReal.ofReal p) ν ≤ ENNReal.ofReal (4*4^2*G*Real.sqrt p*
        Real.sqrt (Fintype.card K:ℝ)*
        Real.sqrt (∑ i, w i^2*‖Matrix.toEuclideanCLM (n := BlockCoord 2)
          (𝕜 := ℝ) (R i)‖^4)) := by
  let Y' : I → β → FullBlockMat 2 := fun i y => (R i).transpose*Y i y*R i
  let G' : I → ℝ := fun i => G*‖Matrix.toEuclideanCLM (n := BlockCoord 2)
    (𝕜 := ℝ) (R i)‖^2
  have hG' (i : I) : 0 ≤ G' i := by dsimp [G']; positivity
  have hind' (k : K) :
      iIndepFun (fun i : {i // color i=k} => Y' i.1) ν := by
    exact (hind k).comp (fun i A => (R i).transpose*A*R i)
      (fun i => ((continuous_const.mul continuous_id).mul continuous_const).measurable)
  have hm' (i : I) : Measurable (Y' i) := by
    dsimp [Y']
    exact (((continuous_const.mul continuous_id).mul continuous_const).measurable).comp (hm i)
  have hb' (i : I) (a b : BlockCoord 2) :
      ∀ᵐ y ∂ν, |Y' i y a b| ≤ G' i := by
    filter_upwards [hY i] with y hYi
    have hnorm := matrix_congruence_opNorm_le (R i) (Y i y) G hG hYi
    exact (clipped_matrix_entry_abs_le_norm _ a b).trans hnorm
  have hInt (i : I) :
      ∫ z, Y' i z ∂ν = (R i).transpose*(∫ z, Y i z ∂ν)*R i := by
    let L : FullBlockMat 2 →ₗ[ℝ] FullBlockMat 2 :=
      { toFun := fun A => (R i).transpose*A*R i
        map_add' := by intro A B; simp [Matrix.mul_add, Matrix.add_mul]
        map_smul' := by intro c A; simp }
    let E : FullBlockMat 2 →L[ℝ] FullBlockMat 2 := ⟨L,L.continuous_of_finiteDimensional⟩
    change ∫ z, E (Y i z) ∂ν = E (∫ z, Y i z ∂ν)
    exact E.integral_comp_comm (hYint i)
  let mean : I → FullBlockMat 2 := fun i => ∫ z, Y i z ∂ν
  let mean' : I → FullBlockMat 2 := fun i => ∫ z, Y' i z ∂ν
  have hYint' (i : I) : Integrable (Y' i) ν := by
    let L : FullBlockMat 2 →ₗ[ℝ] FullBlockMat 2 :=
      { toFun := fun A => (R i).transpose*A*R i
        map_add' := by intro A B; simp [Matrix.mul_add, Matrix.add_mul]
        map_smul' := by intro c A; simp }
    let E : FullBlockMat 2 →L[ℝ] FullBlockMat 2 := ⟨L,L.continuous_of_finiteDimensional⟩
    change Integrable (fun z => E (Y i z)) ν
    exact E.integrable_comp (hYint i)
  have hmean (i : I) (a b : BlockCoord 2) :
      mean i a b = ∫ z, Y i z a b ∂ν :=
    integral_matrix_entry_eq ν (Y i) (hYint i) a b
  have hmean' (i : I) (a b : BlockCoord 2) :
      mean' i a b = ∫ z, Y' i z a b ∂ν :=
    integral_matrix_entry_eq ν (Y' i) (hYint' i) a b
  have he (y : β) :
      (∑ i, w i • (Y' i y-mean' i)) =
        ∑ i, w i • ((R i).transpose*(Y i y-mean i)*R i) := by
    apply Finset.sum_congr rfl
    intro i hi
    dsimp only [Y', mean', mean]
    rw [hInt i, Matrix.mul_sub, Matrix.sub_mul]
  have hefun :
      (fun y => ‖Matrix.toEuclideanCLM (n := BlockCoord 2) (𝕜 := ℝ)
        (∑ i, w i • (Y' i y-mean' i))‖) =
      fun y => ‖Matrix.toEuclideanCLM (n := BlockCoord 2) (𝕜 := ℝ)
        (∑ i, w i • ((R i).transpose*(Y i y-mean i)*R i))‖ := by
    funext y
    exact congrArg (fun A : FullBlockMat 2 =>
      ‖Matrix.toEuclideanCLM (n := BlockCoord 2) (𝕜 := ℝ) A‖) (he y)
  have hconc := colored_matrix_variable_radius_Lp ν Y' mean' hmean' color hind' hm' G' hG'
    hb' w p hp
  have hconc' := hconc
  rw [hefun] at hconc'
  apply hconc'.trans
  have hroot :
      Real.sqrt (∑ i, (w i*G' i)^2) = G*Real.sqrt (∑ i,
        w i^2*‖Matrix.toEuclideanCLM (n := BlockCoord 2) (𝕜 := ℝ) (R i)‖^4) := by
    dsimp [G']
    have hsq : (∑ i, (w i*(G*‖Matrix.toEuclideanCLM (n := BlockCoord 2)
        (𝕜 := ℝ) (R i)‖^2))^2) = G^2*(∑ i, w i^2*‖Matrix.toEuclideanCLM
          (n := BlockCoord 2) (𝕜 := ℝ) (R i)‖^4) := by
      calc
        _ = ∑ i, G^2*(w i^2*‖Matrix.toEuclideanCLM
            (n := BlockCoord 2) (𝕜 := ℝ) (R i)‖^4) := by
          apply Finset.sum_congr rfl
          intro i hi
          ring
        _ = _ := by rw [← Finset.mul_sum]
    rw [hsq]
    rw [Real.sqrt_mul (sq_nonneg G), Real.sqrt_sq hG]
  apply ENNReal.ofReal_le_ofReal
  have hcard : (Fintype.card (BlockCoord 2):ℝ)=4 := by norm_num [BlockCoord]
  rw [hroot, hcard]
  have hbase : 0 ≤ G*Real.sqrt p*Real.sqrt (Fintype.card K:ℝ)*
      Real.sqrt (∑ i, w i^2*‖Matrix.toEuclideanCLM
        (n := BlockCoord 2) (𝕜 := ℝ) (R i)‖^4) := by positivity
  nlinarith only [hbase]

/-- Integrating the fixed-shear estimate over an independent shear family
preserves the colored matrix bound. The product-law hypothesis is discharged
from the old/later shell sigma-field independence in the application. -/
theorem independent_random_shear_matrix_concentration_Lp
    {Ω I K : Type*} [MeasurableSpace Ω] [Fintype I] [Fintype K] [DecidableEq K]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (η : Measure (I → FullBlockMat 2)) [IsProbabilityMeasure η]
    (ρ : Measure (I → FullBlockMat 2)) [IsProbabilityMeasure ρ]
    (X R : Ω → I → FullBlockMat 2)
    (hjoint : μ.map (fun ω => (R ω, X ω)) = ρ.prod η)
    (hX : Measurable X) (hR : Measurable R)
    (color : I → K)
    (hcolor : ∀ k, iIndepFun (fun i : {i // color i=k} => fun a => a i.1) η)
    (G : ℝ) (hG0 : 0 ≤ G)
    (hY : ∀ i, ∀ᵐ a ∂η,
      ‖Matrix.toEuclideanCLM (n := BlockCoord 2) (𝕜 := ℝ) (a i)‖ ≤ G)
    (hYint : ∀ i, Integrable (fun a => a i) η)
    (w : I → ℝ) (p : ℝ) (hp : 2 ≤ p)
    (S : ℝ)
    (hRadius : eLpNorm (fun r => Real.sqrt (∑ i, w i^2 *
        ‖Matrix.toEuclideanCLM (n := BlockCoord 2) (𝕜 := ℝ) (r i)‖^4))
        (ENNReal.ofReal p) ρ ≤ ENNReal.ofReal S) :
    eLpNorm (fun ω => ‖Matrix.toEuclideanCLM (n := BlockCoord 2) (𝕜 := ℝ)
      (∑ i, w i • ((R ω i).transpose*((X ω i)-∫ a, a i ∂η)*(R ω i)))‖)
      (ENNReal.ofReal p) μ ≤ ENNReal.ofReal
        (4*4^2*G*Real.sqrt p*Real.sqrt (Fintype.card K:ℝ)*S) := by
  let T := Matrix.toEuclideanCLM (n := BlockCoord 2) (𝕜 := ℝ)
  let mean : I → FullBlockMat 2 := fun i => ∫ a, a i ∂η
  let F : (I → FullBlockMat 2) × (I → FullBlockMat 2) → ℝ := fun z =>
    ‖T (∑ i, w i • ((z.1 i).transpose*(z.2 i-mean i)*(z.1 i)))‖
  let rad : (I → FullBlockMat 2) → ℝ := fun r =>
    Real.sqrt (∑ i, w i^2*‖T (r i)‖^4)
  let C : ℝ := 4*4^2*G*Real.sqrt p*Real.sqrt (Fintype.card K:ℝ)
  let g : (I → FullBlockMat 2) → ℝ := fun r => C*rad r
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hmean (i : I) (a b : BlockCoord 2) :
      mean i a b = ∫ z, z i a b ∂η :=
    integral_matrix_entry_eq η (fun z => z i) (hYint i) a b
  have hsec (r : I → FullBlockMat 2) :
      eLpNorm (fun a => F (r,a)) (ENNReal.ofReal p) η ≤ ENNReal.ofReal (g r) := by
    have hfixed := fixed_shear_matrix_concentration_Lp η
      (fun i a => a i) color hcolor (fun _ => measurable_pi_apply _) r G hG0
      hY hYint w p (by linarith)
    simpa only [F, g, rad, C, T, mean, hmean, smul_eq_mul] using hfixed
  have hF : Measurable F := by
    have hmat : Measurable (fun z : (I → FullBlockMat 2) × (I → FullBlockMat 2) =>
        ∑ i, w i • ((z.1 i).transpose*(z.2 i-mean i)*(z.1 i))) := by
      apply Measurable.of_eval_matrix
      intro a b
      simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul,
        Matrix.mul_apply, Matrix.transpose_apply]
      apply Finset.measurable_sum
      intro i hi
      measurability
    let L : Matrix (BlockCoord 2) (BlockCoord 2) ℝ →ₗ[ℝ]
        (EuclideanSpace ℝ (BlockCoord 2) →L[ℝ] EuclideanSpace ℝ (BlockCoord 2)) :=
      { toFun := T
        map_add' := fun A B => map_add T A B
        map_smul' := fun r A => map_smul T r A }
    exact L.continuous_of_finiteDimensional.norm.measurable.comp hmat
  have hg : Measurable g := by
    let L : Matrix (BlockCoord 2) (BlockCoord 2) ℝ →ₗ[ℝ]
        (EuclideanSpace ℝ (BlockCoord 2) →L[ℝ] EuclideanSpace ℝ (BlockCoord 2)) :=
      { toFun := T
        map_add' := fun A B => map_add T A B
        map_smul' := fun r A => map_smul T r A }
    have hn (i : I) : Measurable (fun r : I → FullBlockMat 2 => ‖T (r i)‖) :=
      L.continuous_of_finiteDimensional.norm.measurable.comp (measurable_pi_apply i)
    have hterm (i : I) : Measurable (fun r : I → FullBlockMat 2 =>
        w i^2*‖T (r i)‖^4) := measurable_const.mul ((hn i).pow_const 4)
    have hsum : Measurable (fun r : I → FullBlockMat 2 =>
        ∑ i, w i^2*‖T (r i)‖^4) :=
      Finset.measurable_sum _ (fun i _ => hterm i)
    have hrad : Measurable rad := by
      dsimp only [rad]
      exact hsum.sqrt
    exact measurable_const.mul hrad
  have hg0 (r : I → FullBlockMat 2) : 0 ≤ g r := by
    dsimp [g, rad, C]
    positivity
  have hprod := eLpNorm_product_sections_le ρ η p (by linarith) F g hF hg hg0 hsec
  have hgLp : eLpNorm g (ENNReal.ofReal p) ρ ≤ ENNReal.ofReal (C*S) := by
    calc
      eLpNorm g (ENNReal.ofReal p) ρ = ENNReal.ofReal C *
          eLpNorm rad (ENNReal.ofReal p) ρ := by
        have hmul : g = C • rad := by
          funext r
          change C*rad r = C • rad r
          symm
          exact smul_eq_mul C (rad r)
        rw [hmul, eLpNorm_const_smul]
        rw [Real.enorm_eq_ofReal hC]
      _ ≤ ENNReal.ofReal C * ENNReal.ofReal S :=
        mul_le_mul_of_nonneg_left hRadius bot_le
      _ = ENNReal.ofReal (C*S) := by rw [ENNReal.ofReal_mul hC]
  have hprod' := hprod.trans hgLp
  let pair : Ω → (I → FullBlockMat 2) × (I → FullBlockMat 2) := fun ω => (R ω,X ω)
  have hpair : Measurable pair := hR.prodMk hX
  have hmap := eLpNorm_map_measure (μ := μ) (p := ENNReal.ofReal p)
    (f := pair) (g := F) hF.aestronglyMeasurable hpair.aemeasurable
  calc
    eLpNorm (fun ω => ‖T (∑ i, w i • ((R ω i).transpose*(X ω i-∫ a, a i ∂η)*(R ω i)))‖)
        (ENNReal.ofReal p) μ
      = eLpNorm (fun z => F z) (ENNReal.ofReal p) (μ.map pair) := by
          rw [hmap]
          rfl
    _ = eLpNorm F (ENNReal.ofReal p) (ρ.prod η) := by rw [hjoint]
    _ ≤ ENNReal.ofReal (C*S) := hprod'

/-- Congruence transforms the full quadratic form by acting on its vector. -/
theorem fullMatrixQuadratic_congruence (v : BlockCoord 2 → ℝ)
    (C R : FullBlockMat 2) :
    fullMatrixQuadratic v (R.transpose * C * R) =
      fullMatrixQuadratic (R.mulVec v) C := by
  change dotProduct v ((R.transpose * C * R).mulVec v) =
    dotProduct (R.mulVec v) (C.mulVec (R.mulVec v))
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  calc
    dotProduct v (R.transpose.mulVec (C.mulVec (R.mulVec v))) =
        dotProduct (C.mulVec (R.mulVec v)) (R.mulVec v) :=
      Matrix.dotProduct_transpose_mulVec R v (C.mulVec (R.mulVec v))
    _ = dotProduct (R.mulVec v) (C.mulVec (R.mulVec v)) := dotProduct_comm _ _

theorem fullMatrixQuadratic_shear_metric (v : BlockCoord 2 → ℝ)
    (R : FullBlockMat 2) :
    fullMatrixQuadratic v (R.transpose * R) = dotProduct (R.mulVec v) (R.mulVec v) := by
  calc
    fullMatrixQuadratic v (R.transpose * R) = fullMatrixQuadratic (R.mulVec v) (1 : FullBlockMat 2) := by
      simpa only [Matrix.mul_one] using
        fullMatrixQuadratic_congruence v (1 : FullBlockMat 2) R
    _ = dotProduct (R.mulVec v) (R.mulVec v) := by
      change dotProduct (R.mulVec v) ((1 : FullBlockMat 2).mulVec (R.mulVec v)) = _
      simp

end
end ASDExplicitGamma.Inverse
