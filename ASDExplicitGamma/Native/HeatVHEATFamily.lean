module

public import ASDExplicitGamma.Native.HeatVHEATChild
public import ASDExplicitGamma.Native.HeatVHEATCurvature

/-! Center covariance is retained across a heterogeneous finite family of
true-frame child traces. -/

@[expose] public section

open MeasureTheory Homogenization
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Response ASDExplicitGamma.Variational
open scoped ENNReal

namespace ASDExplicitGamma.Native

/-- The directional derivative of the heterogeneous child mean is the
normalized sum of the individual child derivatives. -/
theorem nativeHeat_childMeanTrace_fderiv_apply
    {n : ℕ} [NeZero n] (Q : Fin n → TriadicCube 2)
    [∀ i, IsFiniteMeasure (volumeMeasureOn (cubeSet (Q i)))]
    [∀ i, CompactSpace (closure (cubeSet (Q i)))]
    (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (k v : ∀ i, C(closure (cubeSet (Q i)), ℝ)) :
    fderiv ℝ
        (childMeanTrace (fun i => cubeSet (Q i))
          (fun i => measurableSet_cubeSet (Q i))
          (fun i => volume_cubeSet_toReal_pos (Q i)) ν σ hν hσ)
        k v =
      (n : ℝ)⁻¹ * ∑ i : Fin n,
        fderiv ℝ (childTraceObservable
          (measurableSet_cubeSet (Q i))
          (volume_cubeSet_toReal_pos (Q i)) ν σ hν hσ) (k i) (v i) := by
  classical
  let E : Fin n → Type := fun i => C(closure (cubeSet (Q i)), ℝ)
  let f : Fin n → (∀ i, E i) → ℝ := fun i y =>
    childTraceObservable (measurableSet_cubeSet (Q i))
      (volume_cubeSet_toReal_pos (Q i)) ν σ hν hσ (y i)
  have htermDiff (i : Fin n) : DifferentiableAt ℝ (f i) k := by
    let π : (∀ i, E i) →L[ℝ] E i :=
      ContinuousLinearMap.proj (R := ℝ) (φ := E) i
    have htrace : DifferentiableAt ℝ
        (childTraceObservable (measurableSet_cubeSet (Q i))
          (volume_cubeSet_toReal_pos (Q i)) ν σ hν hσ) (k i) :=
      (childTraceObservable_polynomial
        (measurableSet_cubeSet (Q i))
        (volume_cubeSet_toReal_pos (Q i)) ν σ hν hσ).1.differentiable
          (by norm_num : (2 : WithTop ℕ∞) ≠ 0) _
    have hchain := htrace.hasFDerivAt.comp k π.hasFDerivAt
    have hfun : f i =
        childTraceObservable (measurableSet_cubeSet (Q i))
          (volume_cubeSet_toReal_pos (Q i)) ν σ hν hσ ∘ π := by
      funext y
      rfl
    rw [hfun]
    exact hchain.differentiableAt
  have hsumDiff : DifferentiableAt ℝ
      (fun y : ∀ i, E i => ∑ i : Fin n, f i y) k :=
    DifferentiableAt.fun_sum fun i hi => htermDiff i
  have hsumFDeriv :
      fderiv ℝ (fun y : ∀ i, E i => ∑ i : Fin n, f i y) k =
        ∑ i : Fin n, fderiv ℝ (f i) k := by
    apply fderiv_fun_sum
    intro i hi
    exact htermDiff i
  have htermApply (i : Fin n) :
      fderiv ℝ (f i) k v =
        fderiv ℝ (childTraceObservable
          (measurableSet_cubeSet (Q i))
          (volume_cubeSet_toReal_pos (Q i)) ν σ hν hσ)
          (k i) (v i) := by
    let π : (∀ i, E i) →L[ℝ] E i :=
      ContinuousLinearMap.proj (R := ℝ) (φ := E) i
    have htrace : DifferentiableAt ℝ
        (childTraceObservable (measurableSet_cubeSet (Q i))
          (volume_cubeSet_toReal_pos (Q i)) ν σ hν hσ) (k i) :=
      (childTraceObservable_polynomial
        (measurableSet_cubeSet (Q i))
        (volume_cubeSet_toReal_pos (Q i)) ν σ hν hσ).1.differentiable
          (by norm_num : (2 : WithTop ℕ∞) ≠ 0) _
    have hchain := htrace.hasFDerivAt.comp k π.hasFDerivAt
    have hfun : f i =
        childTraceObservable (measurableSet_cubeSet (Q i))
          (volume_cubeSet_toReal_pos (Q i)) ν σ hν hσ ∘ π := by
      funext y
      rfl
    have hchainderiv : fderiv ℝ (f i) k =
        (fderiv ℝ (childTraceObservable
          (measurableSet_cubeSet (Q i))
          (volume_cubeSet_toReal_pos (Q i)) ν σ hν hσ) (k i)).comp π := by
      simpa only [hfun] using hchain.fderiv
    have happly := congrArg (fun D : (∀ i, E i) →L[ℝ] ℝ => D v) hchainderiv
    simpa [π, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.proj_apply] using happly
  unfold childMeanTrace
  change fderiv ℝ
      (fun y : ∀ i, E i => (n : ℝ)⁻¹ • ∑ i : Fin n, f i y) k v = _
  rw [fderiv_fun_const_smul hsumDiff (n : ℝ)⁻¹, hsumFDeriv]
  simp only [smul_apply, sum_apply, smul_eq_mul]
  simp_rw [htermApply]

/-- The covariance trace of the heterogeneous child mean is the normalized
sum of the physical covariance traces of its children. Correlations between
the child directions are retained in each direction before projection. -/
theorem nativeHeat_childMeanTrace_covarianceTrace
    {n : ℕ} [NeZero n] (Q : Fin n → TriadicCube 2)
    [∀ i, IsFiniteMeasure (volumeMeasureOn (cubeSet (Q i)))]
    [∀ i, CompactSpace (closure (cubeSet (Q i)))]
    (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {v : ℕ → V} (hv : Summable (fun j => ‖v j‖ ^ 2))
    (P : V →L[ℝ] (∀ i, C(closure (cubeSet (Q i)), ℝ)))
    (k : ∀ i, C(closure (cubeSet (Q i)), ℝ)) :
    modelCovarianceTrace
        (childMeanTrace (fun i => cubeSet (Q i))
          (fun i => measurableSet_cubeSet (Q i))
          (fun i => volume_cubeSet_toReal_pos (Q i)) ν σ hν hσ)
        (fun j => P (v j)) k =
      (n : ℝ)⁻¹ * ∑ i : Fin n,
        modelCovarianceTrace
          (childTraceObservable (measurableSet_cubeSet (Q i))
            (volume_cubeSet_toReal_pos (Q i)) ν σ hν hσ)
          (fun j => (P (v j)) i) (k i) := by
  classical
  let E : Fin n → Type := fun i => C(closure (cubeSet (Q i)), ℝ)
  let μ : (∀ i, E i) → ℝ := childMeanTrace
    (fun i => cubeSet (Q i))
    (fun i => measurableSet_cubeSet (Q i))
    (fun i => volume_cubeSet_toReal_pos (Q i)) ν σ hν hσ
  let c : ℝ := (n : ℝ)⁻¹
  have hμpoly : HasPolynomiallyBoundedC2Derivatives μ := by
    simpa [μ] using childMeanTrace_polynomial
      (fun i => cubeSet (Q i))
      (fun i => measurableSet_cubeSet (Q i))
      (fun i => volume_cubeSet_toReal_pos (Q i)) ν σ hν hσ
  have hsecond (w : ∀ i, E i) :
      secondDirectionalDerivative μ k w = c * ∑ i : Fin n,
        secondDirectionalDerivative
          (childTraceObservable (measurableSet_cubeSet (Q i))
            (volume_cubeSet_toReal_pos (Q i)) ν σ hν hσ)
          (k i) (w i) := by
    let g : Fin n → (∀ i, E i) → ℝ := fun i y =>
      fderiv ℝ (childTraceObservable
        (measurableSet_cubeSet (Q i))
        (volume_cubeSet_toReal_pos (Q i)) ν σ hν hσ) (y i) (w i)
    have htermDiff (i : Fin n) : DifferentiableAt ℝ (g i) k := by
      let π : (∀ i, E i) →L[ℝ] E i :=
        ContinuousLinearMap.proj (R := ℝ) (φ := E) i
      let G : E i → ℝ := fun z => fderiv ℝ
        (childTraceObservable
          (measurableSet_cubeSet (Q i))
          (volume_cubeSet_toReal_pos (Q i)) ν σ hν hσ) z (w i)
      have htrace := childTraceObservable_polynomial
        (measurableSet_cubeSet (Q i))
        (volume_cubeSet_toReal_pos (Q i)) ν σ hν hσ
      have hG : ContDiff ℝ 1 G := by
        have h := htrace.1.contDiff_fderiv_apply (m := 1)
          (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)
        have hp : ContDiff ℝ 1 (fun z : E i => (z, w i)) :=
          contDiff_id.prodMk contDiff_const
        simpa [G, Function.comp_def] using h.comp hp
      have hGdiff : DifferentiableAt ℝ G (k i) :=
        hG.differentiable (by norm_num : (1 : WithTop ℕ∞) ≠ 0) _
      have hchain := hGdiff.hasFDerivAt.comp k π.hasFDerivAt
      have hfun : g i = G ∘ π := by
        funext y
        rfl
      rw [hfun]
      exact hchain.differentiableAt
    have hsumDiff : DifferentiableAt ℝ
        (fun y : ∀ i, E i => ∑ i : Fin n, g i y) k :=
      DifferentiableAt.fun_sum fun i hi => htermDiff i
    have hsumFDeriv :
        fderiv ℝ (fun y : ∀ i, E i => ∑ i : Fin n, g i y) k =
          ∑ i : Fin n, fderiv ℝ (g i) k := by
      apply fderiv_fun_sum
      intro i hi
      exact htermDiff i
    have htermApply (i : Fin n) :
        fderiv ℝ (g i) k w =
          secondDirectionalDerivative
            (childTraceObservable
              (measurableSet_cubeSet (Q i))
              (volume_cubeSet_toReal_pos (Q i)) ν σ hν hσ)
            (k i) (w i) := by
      let π : (∀ i, E i) →L[ℝ] E i :=
        ContinuousLinearMap.proj (R := ℝ) (φ := E) i
      let G : E i → ℝ := fun z => fderiv ℝ
        (childTraceObservable
          (measurableSet_cubeSet (Q i))
          (volume_cubeSet_toReal_pos (Q i)) ν σ hν hσ) z (w i)
      have htrace := childTraceObservable_polynomial
        (measurableSet_cubeSet (Q i))
        (volume_cubeSet_toReal_pos (Q i)) ν σ hν hσ
      have hG : ContDiff ℝ 1 G := by
        have h := htrace.1.contDiff_fderiv_apply (m := 1)
          (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)
        have hp : ContDiff ℝ 1 (fun z : E i => (z, w i)) :=
          contDiff_id.prodMk contDiff_const
        simpa [G, Function.comp_def] using h.comp hp
      have hGdiff : DifferentiableAt ℝ G (k i) :=
        hG.differentiable (by norm_num : (1 : WithTop ℕ∞) ≠ 0) _
      have hchain := hGdiff.hasFDerivAt.comp k π.hasFDerivAt
      have hfun : g i = G ∘ π := by
        funext y
        rfl
      have hchainDeriv : fderiv ℝ (g i) k =
          (fderiv ℝ G (k i)).comp π := by
        simpa only [hfun] using hchain.fderiv
      have happly := congrArg (fun D : (∀ i, E i) →L[ℝ] ℝ => D w) hchainDeriv
      simpa [G, π, secondDirectionalDerivative,
        ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.proj_apply] using happly
    have hfirst : (fun y : ∀ i, E i => fderiv ℝ μ y w) =
        fun y => c * ∑ i : Fin n,
          fderiv ℝ (childTraceObservable
            (measurableSet_cubeSet (Q i))
            (volume_cubeSet_toReal_pos (Q i)) ν σ hν hσ) (y i) (w i) := by
      funext y
      simpa [μ, c] using nativeHeat_childMeanTrace_fderiv_apply
        Q ν σ hν hσ y w
    change fderiv ℝ (fun y => fderiv ℝ μ y w) k w = _
    rw [hfirst]
    change fderiv ℝ
      (fun y : ∀ i, E i => c • ∑ i : Fin n, g i y) k w = _
    rw [fderiv_fun_const_smul hsumDiff c, hsumFDeriv]
    simp only [smul_apply, sum_apply, smul_eq_mul]
    simp_rw [htermApply]
  have hμsum : Summable (fun j => secondDirectionalDerivative μ k (P (v j))) := by
    let B : (∀ i, E i) →L[ℝ] (∀ i, E i) →L[ℝ] ℝ :=
      fderiv ℝ (fderiv ℝ μ) k
    have hs := summable_bilinear_images hv B P P
    apply hs.congr
    intro j
    exact (second_fderiv_eq hμpoly.1 k (P (v j)) (P (v j))).symm
  have hchildSum (i : Fin n) :
      Summable (fun j => secondDirectionalDerivative
        (childTraceObservable (measurableSet_cubeSet (Q i))
          (volume_cubeSet_toReal_pos (Q i)) ν σ hν hσ)
        (k i) ((P (v j)) i)) := by
    let π : (∀ i, E i) →L[ℝ] E i :=
      ContinuousLinearMap.proj (R := ℝ) (φ := E) i
    let B : E i →L[ℝ] E i →L[ℝ] ℝ := fderiv ℝ
      (fderiv ℝ (childTraceObservable
        (measurableSet_cubeSet (Q i))
        (volume_cubeSet_toReal_pos (Q i)) ν σ hν hσ)) (k i)
    have hs := summable_bilinear_images hv B (π.comp P) (π.comp P)
    apply hs.congr
    intro j
    change B ((π.comp P) (v j)) ((π.comp P) (v j)) = _
    simpa [B, π, secondDirectionalDerivative,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply] using
        (second_fderiv_eq
          (childTraceObservable_polynomial
            (measurableSet_cubeSet (Q i))
            (volume_cubeSet_toReal_pos (Q i)) ν σ hν hσ).1
          (k i) ((P (v j)) i) ((P (v j)) i)).symm
  unfold modelCovarianceTrace
  rw [tsum_congr fun j => hsecond (P (v j)), tsum_mul_left]
  rw [Summable.tsum_finsetSum (fun i _ => hchildSum i)]

/-- On a probability space, an L128 cap controls every positive natural
moment through order 128 of a nonnegative observable. -/
theorem nativeHeat_integral_natPow_le_of_eLpNorm128
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (hprob : IsProbabilityMeasure μ)
    {f : Ω → ℝ} (hf : AEStronglyMeasurable f μ)
    (hf0 : ∀ ω, 0 ≤ f ω) (C : ℝ) (hC : 0 ≤ C)
    (hcap : eLpNorm f 128 μ ≤ ENNReal.ofReal C)
    (r : ℕ) (hr1 : 1 ≤ r) (hr128 : r ≤ 128) :
    ∫ ω, f ω ^ r ∂μ ≤ C ^ r := by
  have hrpos : 0 < (r : ℝ) := by exact_mod_cast (by omega : 0 < r)
  have hrle : (r : ℝ) ≤ 128 := by exact_mod_cast hr128
  have hpq : ENNReal.ofReal (r : ℝ) ≤ (128 : ℝ≥0∞) := by
    calc
      ENNReal.ofReal (r : ℝ) ≤ ENNReal.ofReal 128 :=
        (ENNReal.ofReal_le_ofReal_iff (by norm_num : (0 : ℝ) ≤ 128)).mpr hrle
      _ = 128 := by norm_num
  have hmonoLp : eLpNorm f (ENNReal.ofReal (r : ℝ)) μ ≤ eLpNorm f 128 μ := by
    have h := eLpNorm_le_eLpNorm_mul_rpow_measure_univ hpq hf
    simpa [hprob.measure_univ] using h
  have h128 : eLpNorm f 128 μ = eLpNorm' f 128 μ := by
    simpa using (eLpNorm_eq_eLpNorm' (p := (128 : ℝ≥0∞))
      (by norm_num) (by norm_num) hf)
  have hsmall_eq :
      eLpNorm f (ENNReal.ofReal (r : ℝ)) μ = eLpNorm' f (r : ℝ) μ := by
    rw [eLpNorm_eq_eLpNorm' (p := ENNReal.ofReal (r : ℝ))
      (ne_of_gt (ENNReal.ofReal_pos.mpr hrpos)) ENNReal.ofReal_ne_top hf]
    simp only [ENNReal.toReal_ofReal hrpos.le]
  have hmono : eLpNorm' f (r : ℝ) μ ≤ eLpNorm' f 128 μ := by
    rw [← hsmall_eq, ← h128]
    exact hmonoLp
  have hsmall : eLpNorm f (ENNReal.ofReal (r : ℝ)) μ ≤ ENNReal.ofReal C := by
    exact hmonoLp.trans hcap
  have hmem : MemLp f (ENNReal.ofReal (r : ℝ)) μ :=
    memLp_iff.mpr (hsmall.trans_lt (ENNReal.ofReal_lt_top))
  have hmemNat : MemLp f r μ := by simpa using hmem
  have hpowIntegrable : Integrable (fun ω => f ω ^ r) μ := by
    have h := hmemNat.integrable_norm_pow (p := r) (by omega : r ≠ 0)
    convert h using 1
    ext ω
    rw [Real.norm_eq_abs, abs_of_nonneg (hf0 ω)]
  have hlintegral :
      ∫⁻ ω, ‖f ω‖ₑ ^ (r : ℝ) ∂μ ≤ eLpNorm f 128 μ ^ r := by
    calc
      ∫⁻ ω, ‖f ω‖ₑ ^ (r : ℝ) ∂μ = eLpNorm' f (r : ℝ) μ ^ (r : ℝ) :=
        lintegral_rpow_enorm_eq_rpow_eLpNorm' hrpos
      _ ≤ eLpNorm' f 128 μ ^ (r : ℝ) :=
        ENNReal.rpow_le_rpow hmono (by positivity)
      _ = eLpNorm f 128 μ ^ r := by rw [← h128, ENNReal.rpow_natCast]
  have htoENN :
      ENNReal.ofReal (∫ ω, f ω ^ r ∂μ) =
        ∫⁻ ω, ‖f ω‖ₑ ^ (r : ℝ) ∂μ := by
    symm
    calc
      ∫⁻ ω, ‖f ω‖ₑ ^ (r : ℝ) ∂μ =
          ∫⁻ ω, ENNReal.ofReal (f ω ^ r) ∂μ := by
            apply lintegral_congr
            intro ω
            simp [Real.enorm_eq_ofReal_abs, abs_of_nonneg (hf0 ω),
              ENNReal.rpow_natCast, ENNReal.ofReal_pow (hf0 ω)]
      _ = ENNReal.ofReal (∫ ω, f ω ^ r ∂μ) :=
        (ofReal_integral_eq_lintegral_ofReal hpowIntegrable
          (Filter.Eventually.of_forall fun ω => pow_nonneg (hf0 ω) r)).symm
  have hbound :
      ENNReal.ofReal (∫ ω, f ω ^ r ∂μ) ≤ ENNReal.ofReal (C ^ r) := by
    rw [htoENN]
    calc
      ∫⁻ ω, ‖f ω‖ₑ ^ (r : ℝ) ∂μ ≤ eLpNorm f 128 μ ^ r := hlintegral
      _ ≤ ENNReal.ofReal C ^ r := by
        exact pow_le_pow_left₀ (by simp) hcap r
      _ = ENNReal.ofReal (C ^ r) := by rw [ENNReal.ofReal_pow hC]
  exact (ENNReal.ofReal_le_ofReal_iff (pow_nonneg hC r)).mp hbound

/-- The mean of finitely many child traces is convex along any joint constant
center direction. The covariance of the centers is unrestricted. -/
theorem nativeHeat_childMeanTrace_secondDirectional_nonneg
    {n : ℕ} [NeZero n] (Q : Fin n → TriadicCube 2)
    [∀ i, IsFiniteMeasure (volumeMeasureOn (cubeSet (Q i)))]
    [∀ i, CompactSpace (closure (cubeSet (Q i)))]
    (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (k : ∀ i, C(closure (cubeSet (Q i)), ℝ))
    (x v : Fin n → ℝ) :
    let U := fun i : Fin n => cubeSet (Q i)
    let hU := fun i : Fin n => measurableSet_cubeSet (Q i)
    let hvol := fun i : Fin n => volume_cubeSet_toReal_pos (Q i)
    let I := childConstantMap (fun i : Fin n => closure (cubeSet (Q i)))
    0 ≤ secondDirectionalDerivative
      (childMeanTrace U hU hvol ν σ hν hσ)
      (k + I x) (I v) := by
  classical
  let U : Fin n → Set (Vec 2) := fun i => cubeSet (Q i)
  let hU : ∀ i, MeasurableSet (U i) := fun i => measurableSet_cubeSet (Q i)
  let hvol : ∀ i, 0 < (volume (U i)).toReal :=
    fun i => volume_cubeSet_toReal_pos (Q i)
  let I : (Fin n → ℝ) →L[ℝ] (∀ i, C(closure (U i), ℝ)) :=
    childConstantMap (fun i => closure (U i))
  let Φ : (∀ i, C(closure (U i), ℝ)) → ℝ :=
    childMeanTrace U hU hvol ν σ hν hσ
  let κ : ∀ i, C(closure (U i), ℝ) := fun i =>
    k i + BoundedContinuousFunction.const (closure (U i)) (x i)
  let R : ∀ i, ResponseCoefficient (cubeSet (Q i)) := fun i =>
    ContinuousMap.linearIsometryBoundedOfCompact
      (closure (cubeSet (Q i))) ℝ ℝ (κ i)
  let A : ∀ i, BlockMat 2 := fun i =>
    coarseBlockMatrix (cubeSet (Q i)) (responsePlanarCoefficientField ν (R i))
  let T : ∀ i, ℝ := fun i =>
    traceDefect (cubeSet (Q i)) (responsePlanarCoefficientField ν (R i)) σ
  let Z : ∀ i, ℝ := fun i => Variational.shearTraceLinear (A i) / σ
  let D : ∀ i, ℝ := fun i => Matrix.trace (frameMatrix σ (A i)).lowerRight / σ ^ 2
  let cN : ℝ := (n : ℝ)⁻¹
  let a : ℝ := cN * ∑ i : Fin n, T i
  let b : ℝ := cN * ∑ i : Fin n, 2 * v i * Z i
  let c : ℝ := cN * ∑ i : Fin n, (v i) ^ 2 * D i
  have hΦpoly : HasPolynomiallyBoundedC2Derivatives Φ := by
    simpa [Φ] using childMeanTrace_polynomial U hU hvol ν σ hν hσ
  have hDpos (i : Fin n) : 0 < D i := by
    have hrows := nativeHeat_childTrace_shear_rows
      (measurableSet_cubeSet (Q i)) (volume_cubeSet_toReal_pos (Q i))
      ν σ hν hσ (κ i)
    simpa [D, A, R, κ] using hrows.2.1
  have hshear (i : Fin n) (g : ℝ) :
      childTraceObservable (measurableSet_cubeSet (Q i))
        (volume_cubeSet_toReal_pos (Q i)) ν σ hν hσ
          (κ i + BoundedContinuousFunction.const (closure (U i)) g) =
        T i + 2 * g * Z i + g ^ 2 * D i := by
    have hrows := nativeHeat_childTrace_shear_rows
      (measurableSet_cubeSet (Q i)) (volume_cubeSet_toReal_pos (Q i))
      ν σ hν hσ (κ i)
    simpa [T, Z, D, A, R, κ] using hrows.2.2.2 g
  have harg (t : ℝ) : k + I x + t • I v = k + I (x + t • v) := by
    ext i y
    simp [I, childConstantMap]
    abel_nf
  have hterm (t : ℝ) (i : Fin n) :
      childTraceObservable (measurableSet_cubeSet (Q i))
        (volume_cubeSet_toReal_pos (Q i)) ν σ hν hσ
          (k i + BoundedContinuousFunction.const (closure (U i))
            ((x + t • v) i)) =
        T i + 2 * (t * v i) * Z i + (t * v i) ^ 2 * D i := by
    have hcoord : (x + t • v) i = x i + t * v i := by simp
    rw [hcoord]
    have hfield :
        k i + BoundedContinuousFunction.const (closure (U i)) (x i + t * v i) =
          κ i + BoundedContinuousFunction.const (closure (U i)) (t * v i) := by
      ext y
      change (k i) y + (x i + t * v i) =
        ((k i) y + x i) + t * v i
      ring
    rw [hfield]
    exact hshear i (t * v i)
  have hsum (t : ℝ) :
      (∑ i : Fin n, (T i + 2 * (t * v i) * Z i + (t * v i) ^ 2 * D i)) =
        (∑ i : Fin n, T i) + t * (∑ i : Fin n, 2 * v i * Z i) +
          t ^ 2 * (∑ i : Fin n, (v i) ^ 2 * D i) := by
    have hB : (∑ i : Fin n, 2 * (t * v i) * Z i) =
        t * (∑ i : Fin n, 2 * v i * Z i) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    have hC : (∑ i : Fin n, (t * v i) ^ 2 * D i) =
        t ^ 2 * (∑ i : Fin n, (v i) ^ 2 * D i) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    calc
      _ = (∑ i : Fin n, T i) + (∑ i : Fin n, 2 * (t * v i) * Z i) +
          (∑ i : Fin n, (t * v i) ^ 2 * D i) := by
            rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
      _ = _ := by rw [hB, hC]
  have hline (t : ℝ) : Φ (k + I x + t • I v) = a + b * t + c * t ^ 2 := by
    calc
      Φ (k + I x + t • I v) = Φ (k + I (x + t • v)) := by rw [harg]
      _ = cN * ∑ i : Fin n,
          childTraceObservable (measurableSet_cubeSet (Q i))
            (volume_cubeSet_toReal_pos (Q i)) ν σ hν hσ
            (k i + BoundedContinuousFunction.const (closure (U i))
              ((x + t • v) i)) := by
              simpa [Φ, U, hU, hvol, I] using
                nativeHeat_childMeanTrace_constantShift_sum Q ν σ hν hσ k
                  (x + t • v)
      _ = cN * ∑ i : Fin n,
          (T i + 2 * (t * v i) * Z i + (t * v i) ^ 2 * D i) := by
            congr 1
            apply Finset.sum_congr rfl
            intro i hi
            exact hterm t i
      _ = a + b * t + c * t ^ 2 := by
            rw [hsum]
            simp [a, b, c]
            ring
  have hcN : 0 ≤ cN := by positivity
  have hc : 0 ≤ c := by
    apply mul_nonneg hcN
    apply Finset.sum_nonneg
    intro i hi
    exact mul_nonneg (sq_nonneg _) (le_of_lt (hDpos i))
  have hsecond := nativeHeat_secondDirectionalDerivative_eq_two_mul_of_quadratic_line
    hΦpoly.1 (k + I x) (I v) a b c hline
  change 0 ≤ secondDirectionalDerivative Φ (k + I x) (I v)
  rw [hsecond]
  exact mul_nonneg (by norm_num) hc

end ASDExplicitGamma.Native
