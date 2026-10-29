module

public import ASDExplicitGamma.Native.HeatCenterCovariance
public import ASDExplicitGamma.Gaussian.BandModelLaw
public import ASDExplicitGamma.Model.CutoffGaussian
public import ASDExplicitGamma.Main.ShellClock

/-! Actual finite independent shell bands sampled on the q3 child-center grid. -/

@[expose] public section

namespace ASDExplicitGamma.Native

open MeasureTheory ProbabilityTheory Homogenization ASDExplicitGamma.Gaussian
open Filter
open Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3
open scoped BigOperators RealInnerProductSpace Topology

/-- The finite set of q3 grid centers, used as one common compact carrier for
all child evaluations. -/
def nativeHeatQ3GridCenterSet (s : ℕ) : Set (Vec 2) :=
  Set.range (q3GridCenterVector s)

/-- The compact topology on the finite grid-center carrier. -/
noncomputable instance nativeHeatQ3GridCenterCompactSpace (s : ℕ) :
    CompactSpace (nativeHeatQ3GridCenterSet s) := by
  apply isCompact_iff_compactSpace.mp
  exact Set.Finite.isCompact (Set.finite_range (q3GridCenterVector s))

/-- The second moment of a finite linear combination of a centered Gaussian
family is its covariance Gram form. -/
theorem nativeHeat_integral_sum_sq_eq_gram {Ω I : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [Fintype I] {X : I → Ω → ℝ}
    (hX : IsCenteredGaussianFamily μ X) (t : I → ℝ) :
    (∫ ω, (∑ i, t i * X i ω) ^ 2 ∂μ) =
      ∑ i, ∑ j, t i * t j * (∫ ω, X i ω * X j ω ∂μ) := by
  have hXi (i : I) : MemLp (X i) 2 μ := hX.memLp i 2 (by norm_num)
  have hprod (i j : I) : Integrable
      (fun ω => (t i * t j) * (X i ω * X j ω)) μ :=
    ((hXi i).integrable_mul (hXi j)).const_mul _
  have hsum : (fun ω => (∑ i, t i * X i ω) ^ 2) =
      fun ω => ∑ i, ∑ j, (t i * t j) * (X i ω * X j ω) := by
    funext ω
    rw [pow_two, Finset.sum_mul]
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hsum, integral_finsetSum Finset.univ
    (fun i _ => integrable_finsetSum Finset.univ (fun j _ => hprod i j))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum Finset.univ (fun j _ => hprod i j)]
  simp only [integral_const_mul]

/-- A grid center viewed as a point of the common finite carrier. -/
noncomputable def nativeHeatQ3GridCenterPoint (s : ℕ)
    (ij : Fin (3^s) × Fin (3^s)) : nativeHeatQ3GridCenterSet s :=
  ⟨q3GridCenterVector s ij, ⟨ij, rfl⟩⟩

/-- Actual finite shell bands form a centered Gaussian family on all child
centers simultaneously. The law is the physical finite-band law on the
completed cutoff probability space. -/
theorem nativeHeat_q3FiniteBand_gridValues_gaussian
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    {b : ℕ} [NeZero b] (k : Fin b → ℤ) (hk : Function.Injective k)
    (s : ℕ) :
    IsCenteredGaussianFamily (Cutoff.cutoffSampleLaw M).toMeasure
      (fun ij ω =>
        modelBand (nativeHeatQ3GridCenterSet s) k ω
          (nativeHeatQ3GridCenterPoint s ij)) := by
  classical
  let K := nativeHeatQ3GridCenterSet s
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  obtain ⟨T, v, hA, hlaw⟩ :=
    exists_modelBand_realization K M h hM k hk
  refine ⟨?_, ?_⟩
  · intro ij
    have hm : Measurable (fun f : C(K, ℝ) => f (nativeHeatQ3GridCenterPoint s ij)) :=
      (ContinuousMap.evalCLM ℝ (nativeHeatQ3GridCenterPoint s ij)).continuous.measurable
    exact (hm.comp (measurable_modelBand K k)).aemeasurable
  · intro J _ x t
    let Lobs : J → C(K, ℝ) →L[ℝ] ℝ :=
      fun j => ContinuousMap.evalCLM ℝ (nativeHeatQ3GridCenterPoint s (x j))
    let Lsum : C(K, ℝ) →L[ℝ] ℝ := ∑ j, t j • Lobs j
    have hsum (f : C(K, ℝ)) : (∑ j, t j * Lobs j f) = Lsum f := by
      simp [Lsum, Lobs]
    refine ⟨Real.toNNReal (∑' j, (Lsum (T (v j))) ^ 2), ?_⟩
    calc
      μ.map (fun ω => ∑ j, t j *
          modelBand K k ω (nativeHeatQ3GridCenterPoint s (x j)))
          = μ.map (fun ω => Lsum (modelBand K k ω)) := by
              congr 1
              funext ω
              exact hsum (modelBand K k ω)
      _ = (μ.map (modelBand K k)).map Lsum := by
            calc
              _ = μ.map (Lsum ∘ modelBand K k) := rfl
              _ = (μ.map (modelBand K k)).map Lsum :=
                (Measure.map_map Lsum.continuous.measurable (measurable_modelBand K k)).symm
      _ = (standardGaussianInfinitePi.map (gaussianSeriesLimitE hA T)).map Lsum := by
            rw [hlaw]
      _ = standardGaussianInfinitePi.map
          (Lsum ∘ gaussianSeriesLimitE hA T) :=
            Measure.map_map Lsum.continuous.measurable
              (stronglyMeasurable_gaussianSeriesLimitE hA T).measurable
      _ = gaussianReal 0 (Real.toNNReal
          (∑' j, (Lsum (T (v j))) ^ 2)) := by
            simpa only [Function.comp_def] using
            map_gaussianSeriesLimitE_linear hA T Lsum

/-- Exact covariance-form law for every finite linear combination of the
actual finite-band grid values. Independence is used only across physical
shell levels; the grid observations within one shell retain their q3 joint
law. -/
theorem nativeHeat_q3FiniteBand_gridCombination_law
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    {b : ℕ} [NeZero b] (k : Fin b → ℤ) (hk : Function.Injective k)
    (s : ℕ) {J : Type} [Fintype J]
    (x : J → Fin (3^s) × Fin (3^s)) (t : J → ℝ) :
    (Cutoff.cutoffSampleLaw M).toMeasure.map
      (fun ω => ∑ i, t i *
        modelBand (nativeHeatQ3GridCenterSet s) k ω
          (nativeHeatQ3GridCenterPoint s (x i))) =
      gaussianReal 0 (∑ d : Fin b, Real.toNNReal
        (∑ i, ∑ j, t i * t j * q3ShellCovariance M h (k d)
          (q3GridCenterVector s (x i)) (q3GridCenterVector s (x j)))) := by
  classical
  let K := nativeHeatQ3GridCenterSet s
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let L : C(K, ℝ) →L[ℝ] ℝ := ∑ i, t i •
    ContinuousMap.evalCLM ℝ (nativeHeatQ3GridCenterPoint s (x i))
  let Y : Fin b → Cutoff.CutoffSample 2 → ℝ := fun d ω =>
    L (shellFieldScalarRestriction K (ω.1 (k d)))
  have hL (f : C(K, ℝ)) : L f = ∑ i, t i * f (nativeHeatQ3GridCenterPoint s (x i)) := by
    simp [L]
  have hYmeas (d : Fin b) : Measurable (Y d) := by
    dsimp [Y]
    exact L.continuous.measurable.comp ((measurable_shellFieldScalarRestriction K).comp
      ((measurable_pi_apply (k d)).comp measurable_subtype_coe))
  have hYind : iIndepFun Y μ := by
    simpa only [Y, Function.comp_def] using
      (iIndepFun_shellRestrictions K M k hk).comp
        (fun _ => L) (fun _ => L.continuous.measurable)
  have hYlaw (d : Fin b) : μ.map (Y d) = gaussianReal 0 (Real.toNNReal
      (∑ i, ∑ j, t i * t j * q3ShellCovariance M h (k d)
        (q3GridCenterVector s (x i)) (q3GridCenterVector s (x j)))) := by
    let ν := (ShellField.shellMarginalLaw M.P (k d)).toMeasure
    let coord : Cutoff.CutoffSample 2 → ShellField 2 := fun ω => ω.1 (k d)
    let obs : ShellField 2 → ℝ := fun ξ =>
      ∑ i, t i * shellScalarValue ξ (q3GridCenterVector s (x i))
    have hcoord : Measurable coord := (measurable_pi_apply (k d)).comp measurable_subtype_coe
    have hobs : Measurable obs := by
      dsimp [obs]
      exact Finset.measurable_sum _ fun i _ =>
        (measurable_const.mul
          ((shellDerivativeEval_continuous (.value (q3GridCenterVector s (x i)))).measurable))
    have hmap : μ.map coord = ν := by
      simpa [coord, μ, ν] using Model.map_freshShell_eq_shellMarginalLaw M (k d - 1)
    have hq3 := (q3Shell_values_gaussian M h hM (k d)).map_linearCombination_covariance
      (x := fun i => q3GridCenterVector s (x i)) t
    have hcompose : (fun ξ : ShellField 2 => obs ξ) = fun ξ =>
        ∑ i, t i * shellScalarValue ξ (q3GridCenterVector s (x i)) := rfl
    have hcov (i j : J) :
        (∫ ξ, shellScalarValue ξ (q3GridCenterVector s (x i)) *
          shellScalarValue ξ (q3GridCenterVector s (x j)) ∂ν) =
        q3ShellCovariance M h (k d) (q3GridCenterVector s (x i))
          (q3GridCenterVector s (x j)) := by
      dsimp [ν]
      exact q3Shell_value_covariance M h hM (k d)
        (q3GridCenterVector s (x i)) (q3GridCenterVector s (x j))
    have hobsLaw : ν.map obs = gaussianReal 0 (Real.toNNReal
        (∑ i, ∑ j, t i * t j * q3ShellCovariance M h (k d)
          (q3GridCenterVector s (x i)) (q3GridCenterVector s (x j)))) := by
      simpa only [ν, hcompose, hcov] using hq3
    have hYeq : Y d = obs ∘ coord := by
      funext ω
      dsimp [Y, obs, coord]
      rw [hL]
      apply Finset.sum_congr rfl
      intro i _
      congr 1
    calc
      μ.map (Y d) = μ.map (obs ∘ coord) := by rw [hYeq]
      _ = (μ.map coord).map obs := by
        rw [Measure.map_map hobs hcoord]
      _ = ν.map obs := by rw [hmap]
      _ = _ := hobsLaw
  have hsumlaw := independent_gaussian_sum_law μ Y
    (fun d => Real.toNNReal
      (∑ i, ∑ j, t i * t j * q3ShellCovariance M h (k d)
        (q3GridCenterVector s (x i)) (q3GridCenterVector s (x j))))
    hYmeas hYind hYlaw
  have hsumEq : (fun ω => ∑ d : Fin b, Y d ω) = fun ω =>
      ∑ i, t i * modelBand K k ω (nativeHeatQ3GridCenterPoint s (x i)) := by
    funext ω
    have hrestriction (d : Fin b) (i : J) :
        shellFieldScalarRestriction K (ω.1 (k d))
          (nativeHeatQ3GridCenterPoint s (x i)) =
        shellScalarValue (ω.1 (k d)) (q3GridCenterVector s (x i)) := by
      rfl
    have hband (i : J) : modelBand K k ω
        (nativeHeatQ3GridCenterPoint s (x i)) =
        ∑ d : Fin b, shellScalarValue (ω.1 (k d)) (q3GridCenterVector s (x i)) := by
      simp only [Gaussian.modelBand, ContinuousMap.sum_apply]
      apply Finset.sum_congr rfl
      intro d _
      exact hrestriction d i
    calc
      ∑ d : Fin b, Y d ω =
          ∑ d : Fin b, ∑ i, t i * shellScalarValue (ω.1 (k d))
            (q3GridCenterVector s (x i)) := by
            apply Finset.sum_congr rfl
            intro d _
            dsimp [Y]
            rw [hL]
            apply Finset.sum_congr rfl
            intro i _
            exact congrArg (fun z : ℝ => t i * z) (hrestriction d i)
      _ = ∑ i, t i * ∑ d : Fin b,
            shellScalarValue (ω.1 (k d)) (q3GridCenterVector s (x i)) := by
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro i _
            rw [Finset.mul_sum]
      _ = ∑ i, t i * modelBand K k ω
            (nativeHeatQ3GridCenterPoint s (x i)) := by
            apply Finset.sum_congr rfl
            intro i _
            rw [hband i]
  simpa only [hsumEq] using hsumlaw

/-- The source's support-reduced Gaussian quadratic-moment recurrence for a
finite band of actual q3 shells on one child-center grid. Each shell is paired
with its physical grid scale; the band trace and operator caps are derived
from the shell variances and support overlaps. -/
theorem nativeHeat_q3FiniteBand_gridCenterMoment_step_scaled
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    {b : ℕ} [NeZero b] (n : Fin b → ℕ) (hninj : Function.Injective n)
    (s : ℕ) (hn : ∀ d, 1 ≤ n d)
    (r : ℕ) (hr : 1 ≤ r) (c : ℝ) (hc : 0 ≤ c) :
    let k : Fin b → ℤ := fun d => (n d : ℤ) - (s : ℤ)
    let β : Fin b → ℝ := fun d => h * (3 : ℝ)^(M.gamma * (k d : ℝ))
    let K := nativeHeatQ3GridCenterSet s
    let I := Fin (3^s) × Fin (3^s)
    let N := Fintype.card I
    (∫ ω, (c * ((N : ℝ)⁻¹ * ∑ ij : I,
      (modelBand K k ω (nativeHeatQ3GridCenterPoint s ij)) ^ 2)) ^ (r + 1)
      ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
      (c * (∑ d, β d ^ 2) + 2 * (r : ℝ) *
        (c * (∑ d, q3GridOverlapFactor s (n d) * β d ^ 2))) *
        ∫ ω, (c * ((N : ℝ)⁻¹ * ∑ ij : I,
          (modelBand K k ω (nativeHeatQ3GridCenterPoint s ij)) ^ 2)) ^ r
          ∂(Cutoff.cutoffSampleLaw M).toMeasure := by
  classical
  dsimp only
  let k : Fin b → ℤ := fun d => (n d : ℤ) - (s : ℤ)
  let β : Fin b → ℝ := fun d => h * (3 : ℝ)^(M.gamma * (k d : ℝ))
  let K := nativeHeatQ3GridCenterSet s
  let I := Fin (3^s) × Fin (3^s)
  let N : ℕ := Fintype.card I
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let X : I → Cutoff.CutoffSample 2 → ℝ := fun ij ω =>
    modelBand K k ω (nativeHeatQ3GridCenterPoint s ij)
  let Vcap : ℝ := ∑ d, β d ^ 2
  let Lcap : ℝ := ∑ d, q3GridOverlapFactor s (n d) * β d ^ 2
  have hk : Function.Injective k := by
    intro d e hde
    apply hninj
    have hh : (n d : ℤ) = n e := by
      dsimp [k] at hde
      omega
    exact_mod_cast hh
  have hX : IsCenteredGaussianFamily μ X := by
    simpa [X, μ, K] using
      nativeHeat_q3FiniteBand_gridValues_gaussian M h hM k hk s
  have hNpos : 0 < N := by
    dsimp [N, I]
    simp only [Fintype.card_prod, Fintype.card_fin]
    positivity
  have hNrealpos : 0 < (N : ℝ) := by exact_mod_cast hNpos
  have hcardReal : ((Finset.univ : Finset I).card : ℝ) = (N : ℝ) := by
    simp [N, I, Fintype.card_prod, Fintype.card_fin]
  have hScale (d : Fin b) :
      (q3GridKernelScale s (n d)).1 = (3 : ℝ)^(k d) := by
    simpa [k] using nativeHeat_q3GridKernelScale_eq_zpow_any s (n d)
  have hAmp (d : Fin b) :
      β d ^ 2 = h ^ 2 * (3 : ℝ)^(2 * M.gamma * (k d : ℝ)) := by
    exact nativeHeat_q3ShellAmplitude_sq h M.gamma (k d)
  have hSectionCov (d : Fin b) (ij jl : I) :
      q3ShellCovariance M h (k d) (q3GridCenterVector s ij)
          (q3GridCenterVector s jl) =
        ⟪q3Section (β d) (q3GridKernelScale s (n d)) h3Zero
            (q3GridCenterVector s ij),
          q3Section (β d) (q3GridKernelScale s (n d)) h3Zero
            (q3GridCenterVector s jl)⟫ := by
    have hcoord (a : Fin 2) :
        ((3 : ℝ)^(k d))⁻¹ *
            (q3GridCenterVector s ij - q3GridCenterVector s jl) a =
          (q3GridCenterVector s ij - q3GridCenterVector s jl) a /
            (q3GridKernelScale s (n d)).1 := by
      rw [hScale d]
      simp only [Pi.sub_apply]
      rw [div_eq_mul_inv]
      ring
    rw [Gaussian.q3ShellCovariance, ← hAmp d, hcoord 0, hcoord 1]
    exact (Gaussian.q3Section_covariance (β d) (q3GridKernelScale s (n d))
      (q3GridCenterVector s ij) (q3GridCenterVector s jl)).symm
  have hVar (ij : I) : ∫ ω, (X ij ω) ^ 2 ∂μ = Vcap := by
    have hlaw := nativeHeat_q3FiniteBand_gridCombination_law M h hM k hk s
      (J := Unit) (x := fun _ => ij) (t := fun _ => 1)
    have hdiag (d : Fin b) :
        (∑ i : Unit, ∑ j : Unit, (1 : ℝ) * 1 *
          q3ShellCovariance M h (k d) (q3GridCenterVector s ij)
            (q3GridCenterVector s ij)) = β d ^ 2 := by
      simp only [Fintype.sum_unique, one_mul]
      rw [Gaussian.q3ShellCovariance_diagonal, hAmp d]
    have hlaw' : μ.map (X ij) = gaussianReal 0
        (∑ d, Real.toNNReal (β d ^ 2)) := by
      have hfun : (fun ω => ∑ i : Unit, (1 : ℝ) *
          modelBand K k ω (nativeHeatQ3GridCenterPoint s ij)) = X ij := by
        funext ω
        simp [X, K]
      rw [hfun] at hlaw
      simpa only [μ, K, hdiag] using hlaw
    have hsecond := integral_sq_of_map_gaussianReal_zero (hX.1 ij) hlaw'
    rw [NNReal.coe_sum] at hsecond
    simp_rw [Real.coe_toNNReal _ (sq_nonneg _)] at hsecond
    simpa [X, μ, Vcap] using hsecond
  have hV : (N : ℝ)⁻¹ * ∑ ij : I,
      ∫ ω, (X ij ω) ^ 2 ∂μ ≤ Vcap := by
    have hsum : ∑ ij : I, ∫ ω, (X ij ω) ^ 2 ∂μ = (N : ℝ) * Vcap := by
      calc
        _ = ∑ _ij : I, Vcap := by
          apply Finset.sum_congr rfl
          intro ij _
          exact hVar ij
        _ = (N : ℝ) * Vcap := by simp [N]
    rw [hsum]
    field_simp [ne_of_gt hNrealpos]
    exact le_rfl
  let u : Fin b → I → Gaussian.WhiteNoise := fun d ij =>
    Gaussian.q3Section (β d) (q3GridKernelScale s (n d)) Gaussian.h3Zero
      (q3GridCenterVector s ij)
  let Q (d : Fin b) (t : I → ℝ) : ℝ :=
    ∑ ij : I, ∑ jl : I, t ij * t jl *
      q3ShellCovariance M h (k d) (q3GridCenterVector s ij)
        (q3GridCenterVector s jl)
  have hGram (d : Fin b) (t : I → ℝ) :
      ‖∑ ij : I, t ij • u d ij‖ ^ 2 = Q d t := by
    rw [nativeHeat_norm_sum_smul_sq]
    dsimp [Q, u]
    apply Finset.sum_congr rfl
    intro ij _
    apply Finset.sum_congr rfl
    intro jl _
    rw [hSectionCov]
  have hQnonneg (d : Fin b) (t : I → ℝ) : 0 ≤ Q d t := by
    rw [← hGram]
    positivity
  have hComboLaw (t : I → ℝ) :
      μ.map (fun ω => ∑ ij : I, t ij * X ij ω) =
        gaussianReal 0 (∑ d, Real.toNNReal (Q d t)) := by
    simpa [X, K, Q, μ] using
      nativeHeat_q3FiniteBand_gridCombination_law M h hM k hk s
        (J := I) (x := fun ij => ij) t
  have hComboMeas (t : I → ℝ) :
      AEMeasurable (fun ω => ∑ ij : I, t ij * X ij ω) μ :=
    Finset.aemeasurable_fun_sum Finset.univ fun ij _ =>
      aemeasurable_const.mul (hX.1 ij)
  have hComboSecond (t : I → ℝ) :
      (∫ ω, (∑ ij : I, t ij * X ij ω) ^ 2 ∂μ) = ∑ d, Q d t := by
    have hsecond := integral_sq_of_map_gaussianReal_zero (hComboMeas t) (hComboLaw t)
    rw [NNReal.coe_sum] at hsecond
    simp_rw [Real.coe_toNNReal _ (hQnonneg _ t)] at hsecond
    exact hsecond
  have hActualGram (t : I → ℝ) :
      ∑ ij : I, ∑ jl : I, t ij * t jl *
        (∫ ω, X ij ω * X jl ω ∂μ) = ∑ d, Q d t := by
    calc
      _ = ∫ ω, (∑ ij : I, t ij * X ij ω) ^ 2 ∂μ :=
        (nativeHeat_integral_sum_sq_eq_gram hX t).symm
      _ = ∑ d, Q d t := hComboSecond t
  have hL : ∀ t : I → ℝ,
      (N : ℝ)⁻¹ * ∑ ij : I, ∑ jl : I,
        t ij * t jl * (∫ ω, X ij ω * X jl ω ∂μ) ≤
      Lcap * ∑ ij : I, t ij ^ 2 := by
    intro t
    have hweight (d : Fin b) :
        ∑ ij : I, t ij ^ 2 * β d ^ 2 = β d ^ 2 * ∑ ij : I, t ij ^ 2 := by
      rw [← Finset.sum_mul]
      ring
    have hsection (d : Fin b) :
        ‖((Finset.univ : Finset I).card : ℝ)⁻¹ •
          ∑ ij : I, t ij • u d ij‖ ^ 2 ≤
        q3GridOverlapFactor s (n d) *
          (((Finset.univ : Finset I).card : ℝ)⁻¹) *
            ∑ ij : I, t ij ^ 2 * β d ^ 2 := by
      exact nativeHeat_q3GridSectionAverage_sq_le_support_overlap s (n d)
        (hn d) (β d) t
    rw [hcardReal] at hsection
    have hsection' (d : Fin b) :
        ‖(N : ℝ)⁻¹ • ∑ ij : I, t ij • u d ij‖ ^ 2 ≤
          q3GridOverlapFactor s (n d) * (N : ℝ)⁻¹ *
            (β d ^ 2 * ∑ ij : I, t ij ^ 2) := by
      have hh := hsection d
      rw [hweight d] at hh
      exact hh
    have hper (d : Fin b) :
        (N : ℝ)⁻¹ * Q d t ≤
          (q3GridOverlapFactor s (n d) * β d ^ 2) * ∑ ij : I, t ij ^ 2 := by
      calc
        _ = (N : ℝ) *
            ‖(N : ℝ)⁻¹ • ∑ ij : I, t ij • u d ij‖ ^ 2 := by
              rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, hGram]
              field_simp [ne_of_gt hNrealpos]
        _ ≤ (N : ℝ) * (q3GridOverlapFactor s (n d) * (N : ℝ)⁻¹ *
            (β d ^ 2 * ∑ ij : I, t ij ^ 2)) :=
              mul_le_mul_of_nonneg_left (hsection' d) (le_of_lt hNrealpos)
        _ = (q3GridOverlapFactor s (n d) * β d ^ 2) *
            ∑ ij : I, t ij ^ 2 := by
              field_simp [ne_of_gt hNrealpos]
    calc
      _ = (N : ℝ)⁻¹ * ∑ d : Fin b, Q d t := by rw [hActualGram t]
      _ = ∑ d : Fin b, (N : ℝ)⁻¹ * Q d t := by rw [Finset.mul_sum]
      _ ≤ ∑ d : Fin b,
          (q3GridOverlapFactor s (n d) * β d ^ 2) * ∑ ij : I, t ij ^ 2 :=
            Finset.sum_le_sum fun d _ => hper d
      _ = Lcap * ∑ ij : I, t ij ^ 2 := by
            rw [← Finset.sum_mul]
  let e : Fin N ≃ I := (Fintype.equivFin I).symm
  let Xfin : Fin N → Cutoff.CutoffSample 2 → ℝ := fun i ω => X (e i) ω
  have hXfin : IsCenteredGaussianFamily μ Xfin := by
    simpa [Xfin] using hX.comp e
  have hVfin : (N : ℝ)⁻¹ * ∑ i : Fin N,
      ∫ ω, (Xfin i ω) ^ 2 ∂μ ≤ Vcap := by
    have hsumReindex : ∑ i : Fin N, ∫ ω, (Xfin i ω) ^ 2 ∂μ =
        ∑ ij : I, ∫ ω, (X ij ω) ^ 2 ∂μ := by
      exact Equiv.sum_comp e (fun ij => ∫ ω, (X ij ω) ^ 2 ∂μ)
    rw [hsumReindex]
    exact hV
  have hLfin : ∀ t : Fin N → ℝ,
      (N : ℝ)⁻¹ * ∑ i : Fin N, ∑ j : Fin N,
        t i * t j * (∫ ω, Xfin i ω * Xfin j ω ∂μ) ≤
      Lcap * ∑ i : Fin N, t i ^ 2 := by
    intro t
    let tI : I → ℝ := fun ij => t (e.symm ij)
    have hGramReindex :
        ∑ i : Fin N, ∑ j : Fin N,
          t i * t j * (∫ ω, Xfin i ω * Xfin j ω ∂μ) =
        ∑ ij : I, ∑ jl : I,
          tI ij * tI jl * (∫ ω, X ij ω * X jl ω ∂μ) := by
      calc
        _ = ∑ ij : I, ∑ j : Fin N,
            tI ij * t j * (∫ ω, X ij ω * X (e j) ω ∂μ) := by
              simpa [Xfin, tI] using Equiv.sum_comp e (fun ij =>
                ∑ j : Fin N, tI ij * t j * (∫ ω, X ij ω * X (e j) ω ∂μ))
        _ = ∑ ij : I, ∑ jl : I,
            tI ij * tI jl * (∫ ω, X ij ω * X jl ω ∂μ) := by
              apply Finset.sum_congr rfl
              intro ij _
              simpa [tI] using Equiv.sum_comp e (fun jl =>
                tI ij * tI jl * (∫ ω, X ij ω * X jl ω ∂μ))
    have hWeights : ∑ ij : I, tI ij ^ 2 = ∑ i : Fin N, t i ^ 2 := by
      calc
        _ = ∑ i : Fin N, tI (e i) ^ 2 :=
          (Equiv.sum_comp e (fun ij => tI ij ^ 2)).symm
        _ = _ := by simp [tI]
    have hlocal := hL tI
    calc
      _ = (N : ℝ)⁻¹ * ∑ ij : I, ∑ jl : I,
          tI ij * tI jl * (∫ ω, X ij ω * X jl ω ∂μ) := by rw [hGramReindex]
      _ ≤ Lcap * ∑ ij : I, tI ij ^ 2 := hlocal
      _ = Lcap * ∑ i : Fin N, t i ^ 2 := by rw [hWeights]
  let Xscaled : Fin N → Cutoff.CutoffSample 2 → ℝ := fun i ω =>
    Real.sqrt c * Xfin i ω
  have hXscaled : IsCenteredGaussianFamily μ Xscaled := by
    simpa [Xscaled] using hXfin.finite_linear_image
      (fun i (_ : Unit) => i) (fun _ _ => Real.sqrt c)
  have hvarScaled (i : Fin N) :
      (∫ ω, (Xscaled i ω) ^ 2 ∂μ) = c * ∫ ω, (Xfin i ω) ^ 2 ∂μ := by
    have hmem : MemLp (Xfin i) 2 μ := hXfin.memLp i 2 (by norm_num)
    have hint : Integrable (fun ω => (Xfin i ω) ^ 2) μ := by
      simpa only [Real.norm_eq_abs, sq_abs] using
        hmem.integrable_norm_pow (by norm_num : 2 ≠ 0)
    calc
      _ = ∫ ω, c * (Xfin i ω) ^ 2 ∂μ := by
        apply integral_congr_ae
        filter_upwards [] with ω
        dsimp [Xscaled]
        rw [mul_pow, Real.sq_sqrt hc]
      _ = c * ∫ ω, (Xfin i ω) ^ 2 ∂μ := by rw [integral_const_mul]
  have hsumVarScaled : ∑ i : Fin N, ∫ ω, (Xscaled i ω) ^ 2 ∂μ =
      c * ∑ i : Fin N, ∫ ω, (Xfin i ω) ^ 2 ∂μ := by
    calc
      _ = ∑ i : Fin N, c * ∫ ω, (Xfin i ω) ^ 2 ∂μ := by
        apply Finset.sum_congr rfl
        intro i _
        exact hvarScaled i
      _ = _ := by rw [Finset.mul_sum]
  have hVscaled : (N : ℝ)⁻¹ * ∑ i : Fin N,
      ∫ ω, (Xscaled i ω) ^ 2 ∂μ ≤ c * Vcap := by
    calc
      _ = c * ((N : ℝ)⁻¹ * ∑ i : Fin N,
          ∫ ω, (Xfin i ω) ^ 2 ∂μ) := by rw [hsumVarScaled]; ring
      _ ≤ c * Vcap := mul_le_mul_of_nonneg_left hVfin hc
  have hcovScaled (i j : Fin N) :
      (∫ ω, Xscaled i ω * Xscaled j ω ∂μ) =
        c * ∫ ω, Xfin i ω * Xfin j ω ∂μ := by
    have hmemi : MemLp (Xfin i) 2 μ := hXfin.memLp i 2 (by norm_num)
    have hmemj : MemLp (Xfin j) 2 μ := hXfin.memLp j 2 (by norm_num)
    have hint : Integrable (fun ω => Xfin i ω * Xfin j ω) μ :=
      hmemi.integrable_mul hmemj
    calc
      _ = ∫ ω, c * (Xfin i ω * Xfin j ω) ∂μ := by
        apply integral_congr_ae
        filter_upwards [] with ω
        dsimp [Xscaled]
        calc
          Real.sqrt c * Xfin i ω * (Real.sqrt c * Xfin j ω) =
              (Real.sqrt c * Real.sqrt c) * (Xfin i ω * Xfin j ω) := by ring
          _ = c * (Xfin i ω * Xfin j ω) := by
            have hroot : Real.sqrt c * Real.sqrt c = c := by
              simpa [pow_two] using Real.sq_sqrt hc
            rw [hroot]
      _ = c * ∫ ω, Xfin i ω * Xfin j ω ∂μ := by rw [integral_const_mul]
  have hsumCovScaled (t : Fin N → ℝ) :
      ∑ i : Fin N, ∑ j : Fin N,
        t i * t j * (∫ ω, Xscaled i ω * Xscaled j ω ∂μ) =
      c * ∑ i : Fin N, ∑ j : Fin N,
        t i * t j * (∫ ω, Xfin i ω * Xfin j ω ∂μ) := by
    calc
      _ = ∑ i : Fin N, ∑ j : Fin N,
          c * (t i * t j * (∫ ω, Xfin i ω * Xfin j ω ∂μ)) := by
            apply Finset.sum_congr rfl
            intro i _
            apply Finset.sum_congr rfl
            intro j _
            rw [hcovScaled i j]
            ring
      _ = c * ∑ i : Fin N, ∑ j : Fin N,
          t i * t j * (∫ ω, Xfin i ω * Xfin j ω ∂μ) := by
            calc
              _ = ∑ i : Fin N, c * ∑ j : Fin N,
                  t i * t j * (∫ ω, Xfin i ω * Xfin j ω ∂μ) := by
                    apply Finset.sum_congr rfl
                    intro i _
                    rw [Finset.mul_sum]
              _ = _ := by rw [Finset.mul_sum]
  have hLscaled : ∀ t : Fin N → ℝ,
      (N : ℝ)⁻¹ * ∑ i : Fin N, ∑ j : Fin N,
        t i * t j * (∫ ω, Xscaled i ω * Xscaled j ω ∂μ) ≤
      (c * Lcap) * ∑ i : Fin N, t i ^ 2 := by
    intro t
    calc
      _ = c * ((N : ℝ)⁻¹ * ∑ i : Fin N, ∑ j : Fin N,
          t i * t j * (∫ ω, Xfin i ω * Xfin j ω ∂μ)) := by
            rw [hsumCovScaled t]
            ring
      _ ≤ c * (Lcap * ∑ i : Fin N, t i ^ 2) :=
            mul_le_mul_of_nonneg_left (hLfin t) hc
      _ = (c * Lcap) * ∑ i : Fin N, t i ^ 2 := by ring
  have hstep := nativeHeatGaussianFamily_moment_step hNpos Xscaled hXscaled
    (c * Vcap) (c * Lcap) hVscaled hLscaled r hr
  have hQ (ω : Cutoff.CutoffSample 2) :
      (N : ℝ)⁻¹ * ∑ i : Fin N, (Xfin i ω) ^ 2 =
        (N : ℝ)⁻¹ * ∑ ij : I, (X ij ω) ^ 2 := by
    congr 1
    exact Equiv.sum_comp e (fun ij => (X ij ω) ^ 2)
  have hQscaled (ω : Cutoff.CutoffSample 2) :
      (N : ℝ)⁻¹ * ∑ i : Fin N, (Xscaled i ω) ^ 2 =
        c * ((N : ℝ)⁻¹ * ∑ ij : I, (X ij ω) ^ 2) := by
    have hsum : ∑ i : Fin N, (Xscaled i ω) ^ 2 =
        c * ∑ i : Fin N, (Xfin i ω) ^ 2 := by
      calc
        _ = ∑ i : Fin N, c * (Xfin i ω) ^ 2 := by
          apply Finset.sum_congr rfl
          intro i _
          dsimp [Xscaled]
          rw [mul_pow, Real.sq_sqrt hc]
        _ = _ := by rw [Finset.mul_sum]
    calc
      _ = c * ((N : ℝ)⁻¹ * ∑ i : Fin N, (Xfin i ω) ^ 2) := by
        rw [hsum]
        ring
      _ = _ := by rw [hQ]
  have hleft :
      (∫ ω, (c * ((N : ℝ)⁻¹ * ∑ ij : I, (X ij ω) ^ 2)) ^ (r + 1) ∂μ) =
        ∫ ω, ((N : ℝ)⁻¹ * ∑ i : Fin N, (Xscaled i ω) ^ 2) ^ (r + 1) ∂μ := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun ω =>
      congrArg (fun z : ℝ => z ^ (r + 1)) (hQscaled ω).symm
  have hright :
      (∫ ω, (c * ((N : ℝ)⁻¹ * ∑ ij : I, (X ij ω) ^ 2)) ^ r ∂μ) =
        ∫ ω, ((N : ℝ)⁻¹ * ∑ i : Fin N, (Xscaled i ω) ^ 2) ^ r ∂μ := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun ω =>
      congrArg (fun z : ℝ => z ^ r) (hQscaled ω).symm
  rw [← hleft, ← hright] at hstep
  simpa [X, K, I, N, μ, Vcap, Lcap, β, k] using hstep

private noncomputable def nativeHeatQ3PrefixOverlapMajorant (d : ℕ) : ℝ :=
  if d < 8 then (25 / 9 : ℝ) * (1 / 9 : ℝ) ^ (8 - d) else 1

private theorem nativeHeat_q3Prefix_factor_le_majorant (d : ℕ) :
    q3GridOverlapFactor 9 (d + 1) ≤ nativeHeatQ3PrefixOverlapMajorant d := by
  by_cases hd : d < 8
  · have hidx : 9 - (d + 1) = 8 - d := by omega
    have hsq : ((3 : ℝ) ^ (8 - d)) ^ 2 = (9 : ℝ) ^ (8 - d) := by
      rw [← pow_mul, show (8 - d) * 2 = 2 * (8 - d) by omega, pow_mul]
      norm_num
    have hinv : (((3 : ℝ) ^ (8 - d)) ^ 2)⁻¹ = (1 / 9 : ℝ) ^ (8 - d) := by
      rw [hsq, ← inv_pow]
      norm_num
    unfold nativeHeatQ3PrefixOverlapMajorant q3GridOverlapFactor
    rw [ite_eq_left hd, hidx, hinv]
    exact min_le_right _ _
  · have hle : q3GridOverlapFactor 9 (d + 1) ≤ 1 := by
      dsimp [q3GridOverlapFactor]
      exact min_le_left _ _
    simpa [nativeHeatQ3PrefixOverlapMajorant, hd] using hle

/-- The first eight shell levels contribute at most the source's exact
`25/72` overlap reserve; every later level contributes at most one. -/
theorem nativeHeat_q3Prefix_overlap_sum_le (b : ℕ) :
    (∑ d : Fin b, q3GridOverlapFactor 9 (d.val + 1)) ≤
      ((max (b - 8) 0 : ℕ) : ℝ) + 25 / 72 := by
  rw [Fin.sum_univ_eq_sum_range (fun d : ℕ => q3GridOverlapFactor 9 (d + 1))]
  have hterm : ∀ d ∈ Finset.range b,
      q3GridOverlapFactor 9 (d + 1) ≤ nativeHeatQ3PrefixOverlapMajorant d := by
    intro d hd
    exact nativeHeat_q3Prefix_factor_le_majorant d
  calc
    (∑ d ∈ Finset.range b, q3GridOverlapFactor 9 (d + 1)) ≤
        ∑ d ∈ Finset.range b, nativeHeatQ3PrefixOverlapMajorant d := by
          apply Finset.sum_le_sum
          intro d hd
          exact hterm d hd
    _ ≤ ((max (b - 8) 0 : ℕ) : ℝ) + 25 / 72 := by
      have hgeom :
          (∑ d ∈ Finset.range 8, (25 / 9 : ℝ) * (1 / 9 : ℝ) ^ (8 - d)) ≤
            25 / 72 := by
        norm_num [Finset.sum_range_succ]
      by_cases hb : b ≤ 8
      · have hsubset : Finset.range b ⊆ Finset.range 8 := Finset.range_mono hb
        have hEarly :
            (∑ d ∈ Finset.range b, nativeHeatQ3PrefixOverlapMajorant d) =
              ∑ d ∈ Finset.range b, (25 / 9 : ℝ) * (1 / 9 : ℝ) ^ (8 - d) := by
          apply Finset.sum_congr rfl
          intro d hd
          have hd8 : d < 8 := by
            have := Finset.mem_range.mp hd
            omega
          simp [nativeHeatQ3PrefixOverlapMajorant, hd8]
        rw [hEarly]
        have hsmall :
            (∑ d ∈ Finset.range b, (25 / 9 : ℝ) * (1 / 9 : ℝ) ^ (8 - d)) ≤
              ∑ d ∈ Finset.range 8, (25 / 9 : ℝ) * (1 / 9 : ℝ) ^ (8 - d) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
          intro d hd hnot
          positivity
        have hzero : max (b - 8) 0 = 0 := by omega
        rw [hzero]
        linarith
      · have hsplit : b = 8 + (b - 8) := by omega
        rw [hsplit, Finset.sum_range_add]
        have hcast : ((b - 8 : ℕ) : ℝ) = (b : ℝ) - 8 := by
          rw [Nat.cast_sub (by omega : 8 ≤ b)]
          norm_num
        have hEarly :
            (∑ d ∈ Finset.range 8, nativeHeatQ3PrefixOverlapMajorant d) =
              ∑ d ∈ Finset.range 8, (25 / 9 : ℝ) * (1 / 9 : ℝ) ^ (8 - d) := by
          apply Finset.sum_congr rfl
          intro d hd
          have hd8 : d < 8 := Finset.mem_range.mp hd
          simp [nativeHeatQ3PrefixOverlapMajorant, hd8]
        have hLate :
            (∑ d ∈ Finset.range (b - 8),
              nativeHeatQ3PrefixOverlapMajorant (8 + d)) = (b - 8 : ℝ) := by
          simp [nativeHeatQ3PrefixOverlapMajorant, hcast]
        rw [hEarly, hLate]
        have hmax : max (8 + (b - 8) - 8) 0 = b - 8 := by omega
        rw [hmax, hcast]
        linarith

/-- The native OLD-label shell clock controls every shell in a future block
after normalization by the old frame.  This is the source's per-shell
variance cap `(9/2) γ 3^(2 γ b)` for a block of `b` inserted shells. -/
theorem nativeHeat_futureShellVariance_le_of_state
    (M : ABKModel 2) (h : ℝ) (m : ℤ) (j b : ℕ)
    (hj : 1 ≤ j) (hjb : j ≤ b)
    (hstate : nativeInductionState M h m) :
    h ^ 2 * (3 : ℝ) ^ (2 * M.gamma * ((m + (j : ℤ) : ℤ) : ℝ)) /
        (Annealed.sigmaBar M m : ℝ) ^ 2 ≤
      (9 / 2 : ℝ) * M.gamma * (3 : ℝ) ^ (2 * M.gamma * (b : ℝ)) := by
  have hγ : 0 < M.gamma := M.shellPrefix.gamma_pos
  have hσ : 0 < (Annealed.sigmaBar M m : ℝ) := (Annealed.sigmaBar M m).2
  have hclock := Main.shellClock_le M h m hγ hstate
  have hjz : (1 : ℤ) ≤ (j : ℤ) := by exact_mod_cast hj
  have hindex : ((m + (j : ℤ) : ℤ) : ℝ) =
      ((m + 1 : ℤ) : ℝ) + ((j - 1 : ℕ) : ℝ) := by
    have hnatCast : (1 : ℝ) + ((j - 1 : ℕ) : ℝ) = (j : ℝ) := by
      exact_mod_cast Nat.add_sub_of_le hj
    push_cast
    rw [← hnatCast]
    ring_nf
  have hfactor_nonneg : 0 ≤ (3 : ℝ) ^ (2 * M.gamma * ((j - 1 : ℕ) : ℝ)) := by
    positivity
  have hid :
      h ^ 2 * (3 : ℝ) ^ (2 * M.gamma * ((m + (j : ℤ) : ℤ) : ℝ)) /
          (Annealed.sigmaBar M m : ℝ) ^ 2 =
        Main.shellClock M h m * (3 : ℝ) ^ (2 * M.gamma * ((j - 1 : ℕ) : ℝ)) := by
    rw [hindex, mul_add, Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    unfold Main.shellClock
    field_simp [ne_of_gt hσ]
  have hgap : (443 / 125 : ℝ) * M.gamma ≤ (9 / 2 : ℝ) * M.gamma := by
    nlinarith [hγ]
  have hpowSmall :
      (3 : ℝ) ^ (2 * M.gamma * (j : ℝ)) ≤
        (3 : ℝ) ^ (2 * M.gamma * (b : ℝ)) := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3)
    have hjb' : (j : ℝ) ≤ (b : ℝ) := by exact_mod_cast hjb
    exact mul_le_mul_of_nonneg_left hjb' (by positivity)
  have hpowEq :
      (3 : ℝ) ^ (2 * M.gamma) *
          (3 : ℝ) ^ (2 * M.gamma * ((j - 1 : ℕ) : ℝ)) =
        (3 : ℝ) ^ (2 * M.gamma * (j : ℝ)) := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    congr 1
    have hjcast : (1 : ℝ) + ((j - 1 : ℕ) : ℝ) = (j : ℝ) := by
      exact_mod_cast Nat.add_sub_of_le hj
    rw [← hjcast]
    ring
  calc
    _ = Main.shellClock M h m *
        (3 : ℝ) ^ (2 * M.gamma * ((j - 1 : ℕ) : ℝ)) := hid
    _ ≤ ((443 / 125 : ℝ) * M.gamma * (3 : ℝ) ^ (2 * M.gamma)) *
        (3 : ℝ) ^ (2 * M.gamma * ((j - 1 : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_right hclock hfactor_nonneg
    _ = (443 / 125 : ℝ) * M.gamma *
        (3 : ℝ) ^ (2 * M.gamma * (j : ℝ)) := by
          calc
            _ = (443 / 125 : ℝ) * M.gamma *
                ((3 : ℝ) ^ (2 * M.gamma) *
                  (3 : ℝ) ^ (2 * M.gamma * ((j - 1 : ℕ) : ℝ))) := by ring
            _ = _ := by rw [hpowEq]
    _ ≤ (9 / 2 : ℝ) * M.gamma *
        (3 : ℝ) ^ (2 * M.gamma * (j : ℝ)) :=
          mul_le_mul_of_nonneg_right hgap (by positivity)
    _ ≤ (9 / 2 : ℝ) * M.gamma *
        (3 : ℝ) ^ (2 * M.gamma * (b : ℝ)) :=
          mul_le_mul_of_nonneg_left hpowSmall (by positivity)

end ASDExplicitGamma.Native
