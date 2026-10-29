module

public import ASDExplicitGamma.Native.HeatInitialRefinedGaussian
public import ASDExplicitGamma.Native.HeatInitialRefinedCoordGen
public import ASDExplicitGamma.Native.HeatInitialNumericsStructGen
public import ASDExplicitGamma.Native.HeatInitialRefinedIndepGen

/-! The Gaussian center-quadratic row for `ns` shells. -/

@[expose] public section

namespace ASDExplicitGamma.Native

open MeasureTheory ProbabilityTheory Homogenization Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Numerics.Native
open scoped ENNReal BigOperators
set_option linter.constructorNameAsVariable false


/-- The first moment of the scaled depth-ten grid quadratic is its trace. -/
theorem nativeHeatRefined_gridMean_eqGen (ns : ℕ) [NeZero ns]
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (c : ℝ) :
    let k : Fin ns → ℤ := fun d => ((d.val + 2 : ℕ) : ℤ) - ((10 : ℕ) : ℤ)
    let K := nativeHeatQ3GridCenterSet 10
    let I := Fin (3^10) × Fin (3^10)
    let N := Fintype.card I
    ∫ ω, c * ((N : ℝ)⁻¹ * ∑ ij : I,
      (modelBand K k ω (nativeHeatQ3GridCenterPoint 10 ij)) ^ 2)
      ∂(Cutoff.cutoffSampleLaw M).toMeasure =
      c * ∑ d : Fin ns, (h * (3 : ℝ) ^ (M.gamma * (k d : ℝ))) ^ 2 := by
  classical
  dsimp only
  let s : ℕ := 10
  let k : Fin ns → ℤ := fun d => ((d.val + 2 : ℕ) : ℤ) - ((10 : ℕ) : ℤ)
  let β : Fin ns → ℝ := fun d => h * (3 : ℝ)^(M.gamma * (k d : ℝ))
  let K := nativeHeatQ3GridCenterSet 10
  let I := Fin (3^10) × Fin (3^10)
  let N : ℕ := Fintype.card I
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let X : I → Cutoff.CutoffSample 2 → ℝ := fun ij ω =>
    modelBand K k ω (nativeHeatQ3GridCenterPoint 10 ij)
  let Vcap : ℝ := ∑ d, β d ^ 2
  have hk : Function.Injective k := by
    intro d e hde
    apply Fin.ext
    dsimp [k] at hde
    omega
  have hX : IsCenteredGaussianFamily μ X := by
    simpa [X, μ, K, I] using nativeHeat_q3FiniteBand_gridValues_gaussian M h hM k hk 10
  have hNpos : 0 < N := by
    dsimp [N, I]
    simp only [Fintype.card_prod, Fintype.card_fin]
    positivity
  have hNrealpos : 0 < (N : ℝ) := by exact_mod_cast hNpos
  have hAmp (d : Fin ns) : β d ^ 2 =
      h ^ 2 * (3 : ℝ) ^ (2 * M.gamma * (k d : ℝ)) :=
    nativeHeat_q3ShellAmplitude_sq h M.gamma (k d)
  have hVar (ij : I) : ∫ ω, (X ij ω) ^ 2 ∂μ = Vcap := by
    have hlaw := nativeHeat_q3FiniteBand_gridCombination_law M h hM k hk 10
      (J := Unit) (x := fun _ => ij) (t := fun _ => 1)
    have hdiag (d : Fin ns) :
        (∑ i : Unit, ∑ j : Unit, (1 : ℝ) * 1 *
          q3ShellCovariance M h (k d) (q3GridCenterVector 10 ij)
            (q3GridCenterVector 10 ij)) = β d ^ 2 := by
      simp only [Fintype.sum_unique, one_mul]
      rw [Gaussian.q3ShellCovariance_diagonal, hAmp d]
    have hlaw' : μ.map (X ij) = gaussianReal 0
        (∑ d, Real.toNNReal (β d ^ 2)) := by
      have hfun : (fun ω => ∑ i : Unit, (1 : ℝ) *
          modelBand K k ω (nativeHeatQ3GridCenterPoint 10 ij)) = X ij := by
        funext ω
        simp [X, K]
      rw [hfun] at hlaw
      simpa only [μ, K, hdiag] using hlaw
    have hsecond := integral_sq_of_map_gaussianReal_zero (hX.1 ij) hlaw'
    rw [NNReal.coe_sum] at hsecond
    simp_rw [Real.coe_toNNReal _ (sq_nonneg _)] at hsecond
    simpa [X, μ, Vcap] using hsecond
  have hInt (ij : I) : Integrable (fun ω => (X ij ω) ^ 2) μ := by
    have hmem : MemLp (X ij) 2 μ := hX.memLp ij 2 (by norm_num)
    simpa only [Real.norm_eq_abs, sq_abs] using
      hmem.integrable_norm_pow (by norm_num : 2 ≠ 0)
  have hsumVar : ∑ ij : I, ∫ ω, (X ij ω) ^ 2 ∂μ = (N : ℝ) * Vcap := by
    calc
      _ = ∑ _ij : I, Vcap := by
        apply Finset.sum_congr rfl
        intro ij _
        exact hVar ij
      _ = (N : ℝ) * Vcap := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  calc
    _ = c * ((N : ℝ)⁻¹ * ∫ ω, ∑ ij : I, (X ij ω) ^ 2 ∂μ) := by
      rw [integral_const_mul, integral_const_mul]
    _ = c * ((N : ℝ)⁻¹ * ∑ ij : I, ∫ ω, (X ij ω) ^ 2 ∂μ) := by
      rw [integral_finsetSum Finset.univ (fun ij _ => hInt ij)]
    _ = c * Vcap := by rw [hsumVar]; field_simp [ne_of_gt hNrealpos]

private theorem nativeHeatRefined_overlap_eqGen (d : ℕ) :
    q3GridOverlapFactor 10 (d + 2) = q3GridOverlapFactor 9 (d + 1) := by
  unfold q3GridOverlapFactor
  have : 10 - (d + 2) = 9 - (d + 1) := by omega
  rw [this]

private theorem nativeHeatRefined_overlap_sum_leGen (ns : ℕ) [NeZero ns] :
    (∑ d : Fin ns, q3GridOverlapFactor 10 ((d : ℕ) + 2)) ≤
      min (ns : ℝ) (((max (ns - 8) 0 : ℕ) : ℝ) + 25 / 72) := by
  apply le_min
  · calc
      _ ≤ ∑ _d : Fin ns, (1 : ℝ) := Finset.sum_le_sum fun d _ => by
          unfold q3GridOverlapFactor; exact min_le_left _ _
      _ = (ns : ℝ) := by simp
  · have := nativeHeat_q3Prefix_overlap_sum_le ns
    simpa [nativeHeatRefined_overlap_eqGen] using this

/-- The state at the frame label `m` caps every normalized shell variance at the
depth-ten grid centres. -/
theorem nativeHeatRefined_shellCapGen (ns : ℕ) [NeZero ns]
    (M : ABKModel 2) (h : ℝ) (m : ℤ) (scale : ℝ) (hscale : 0 ≤ scale)
    (d : Fin ns) (hstate : nativeInductionState M h m) :
    scale * ((3 : ℝ) ^ (2 * M.gamma * ((m + 9 : ℤ) : ℝ)) /
        (Annealed.sigmaBar M m : ℝ) ^ 2) *
      (h * (3 : ℝ) ^ (M.gamma *
        ((((d.val + 2 : ℕ) : ℤ) - ((10 : ℕ) : ℤ) : ℤ) : ℝ))) ^ 2 ≤
    scale * ((9 / 2 : ℝ) * M.gamma * (3 : ℝ) ^ (2 * M.gamma * (ns : ℝ))) := by
  let c : ℝ := scale *
    ((3 : ℝ) ^ (2 * M.gamma * ((m + 9 : ℤ) : ℝ)) /
      (Annealed.sigmaBar M m : ℝ) ^ 2)
  let e : ℝ := scale *
    ((9 / 2 : ℝ) * M.gamma * (3 : ℝ) ^ (2 * M.gamma * (ns : ℝ)))
  let k : Fin ns → ℤ := fun d => ((d.val + 2 : ℕ) : ℤ) - ((10 : ℕ) : ℤ)
  let β : Fin ns → ℝ := fun d => h * (3 : ℝ)^(M.gamma * (k d : ℝ))
  show c * β d ^ 2 ≤ e
  have hcapAux : c * β d ^ 2 ≤ e := by
    have hfuture := nativeHeat_futureShellVariance_le_of_state M h m
      (d.val + 1) ns (by omega) (by omega) hstate
    have hAmp : β d ^ 2 = h ^ 2 * (3 : ℝ) ^ (2 * M.gamma * (k d : ℝ)) :=
      nativeHeat_q3ShellAmplitude_sq h M.gamma (k d)
    have hindex : ((m + 9 : ℤ) : ℝ) + (k d : ℝ) =
        ((m + ((d.val + 1 : ℕ) : ℤ) : ℤ) : ℝ) := by
      dsimp [k]
      have hz : (m + 9 : ℤ) + (((d.val + 2 : ℕ) : ℤ) - ((10 : ℕ) : ℤ)) =
          m + ((d.val + 1 : ℕ) : ℤ) := by push_cast; ring
      exact_mod_cast hz
    have hpow :
        (3 : ℝ) ^ (2 * M.gamma * ((m + 9 : ℤ) : ℝ)) *
            (3 : ℝ) ^ (2 * M.gamma * (k d : ℝ)) =
          (3 : ℝ) ^ (2 * M.gamma *
            ((m + ((d.val + 1 : ℕ) : ℤ) : ℤ) : ℝ)) := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
      congr 1
      rw [← hindex]
      ring
    have hid : c * β d ^ 2 =
        scale * (h ^ 2 * ((3 : ℝ) ^ (2 * M.gamma * ((m + 9 : ℤ) : ℝ)) *
          (3 : ℝ) ^ (2 * M.gamma * (k d : ℝ))) /
          (Annealed.sigmaBar M m : ℝ) ^ 2) := by
      dsimp [c]
      rw [hAmp]
      ring
    rw [hid, hpow]
    calc
      _ ≤ scale * ((9 / 2 : ℝ) * M.gamma * (3 : ℝ) ^ (2 * M.gamma * (ns : ℝ))) :=
        mul_le_mul_of_nonneg_left hfuture hscale
      _ = e := by simp [e]
  exact hcapAux

/-- All moments of the scaled depth-ten grid quadratic, under the native state at the
frame label `m'` (shells `m'+1,…,m'+9` above parent scale `m'+9`). -/
theorem nativeHeatRefined_gridMoment_product_of_stateGen (ns : ℕ) [NeZero ns]
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (m : ℤ)
    (scale : ℝ) (hscale : 0 ≤ scale) (r : ℕ)
    (hstate : nativeInductionState M h m) :
    let c : ℝ := scale *
      ((3 : ℝ) ^ (2 * M.gamma * ((m + 9 : ℤ) : ℝ)) /
        (Annealed.sigmaBar M m : ℝ) ^ 2)
    let e : ℝ := scale *
      ((9 / 2 : ℝ) * M.gamma * (3 : ℝ) ^ (2 * M.gamma * (ns : ℝ)))
    let k : Fin ns → ℤ := fun d => ((d.val + 2 : ℕ) : ℤ) - ((10 : ℕ) : ℤ)
    let K := nativeHeatQ3GridCenterSet 10
    let I := Fin (3^10) × Fin (3^10)
    let N := Fintype.card I
    ∫ ω, (c * ((N : ℝ)⁻¹ * ∑ ij : I,
      (modelBand K k ω (nativeHeatQ3GridCenterPoint 10 ij)) ^ 2)) ^ r
      ∂(Cutoff.cutoffSampleLaw M).toMeasure ≤
      ∏ i ∈ Finset.range r,
        ((ns : ℝ) * e + 2 * (i : ℝ) * e *
          min (ns : ℝ) (((max (ns - 8) 0 : ℕ) : ℝ) + 25 / 72)) := by
  classical
  dsimp only
  let c : ℝ := scale *
    ((3 : ℝ) ^ (2 * M.gamma * ((m + 9 : ℤ) : ℝ)) /
      (Annealed.sigmaBar M m : ℝ) ^ 2)
  let e : ℝ := scale *
    ((9 / 2 : ℝ) * M.gamma * (3 : ℝ) ^ (2 * M.gamma * (ns : ℝ)))
  let n : Fin ns → ℕ := fun d => d.val + 2
  let k : Fin ns → ℤ := fun d => ((d.val + 2 : ℕ) : ℤ) - ((10 : ℕ) : ℤ)
  let β : Fin ns → ℝ := fun d => h * (3 : ℝ)^(M.gamma * (k d : ℝ))
  let K := nativeHeatQ3GridCenterSet 10
  let I := Fin (3^10) × Fin (3^10)
  let N : ℕ := Fintype.card I
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let Q (ω : Cutoff.CutoffSample 2) : ℝ :=
    (N : ℝ)⁻¹ * ∑ ij : I,
      (modelBand K k ω (nativeHeatQ3GridCenterPoint 10 ij)) ^ 2
  let L : ℝ := min (ns : ℝ) (((max (ns - 8) 0 : ℕ) : ℝ) + 25 / 72)
  let factor (i : ℕ) : ℝ := (ns : ℝ) * e + 2 * (i : ℝ) * e * L
  let moment (j : ℕ) : ℝ := ∫ ω, (c * Q ω) ^ j ∂μ
  letI : IsProbabilityMeasure μ := (Cutoff.cutoffSampleLaw M).property
  have hγ : 0 < M.gamma := M.shellPrefix.gamma_pos
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have he : 0 ≤ e := by dsimp [e]; positivity
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hcap (d : Fin ns) : c * β d ^ 2 ≤ e :=
    nativeHeatRefined_shellCapGen ns M h m scale hscale d hstate
  have hninj : Function.Injective n := by
    intro d d' hde
    apply Fin.ext
    dsimp [n] at hde
    omega
  have hn (d : Fin ns) : 1 ≤ n d := by dsimp [n]; omega
  have hmean : moment 1 ≤ (ns : ℝ) * e := by
    have hh := nativeHeatRefined_gridMean_eqGen ns M h hM c
    have hh' : moment 1 = c * ∑ d : Fin ns, β d ^ 2 := by
      simpa [moment, Q, μ, K, I, N, k, β] using hh
    rw [hh', Finset.mul_sum]
    calc
      _ ≤ ∑ _d : Fin ns, e := Finset.sum_le_sum fun d _ => hcap d
      _ = (ns : ℝ) * e := by simp
  have hstep (j : ℕ) (hj : 1 ≤ j) :
      moment (j + 1) ≤ factor j * moment j := by
    have hh := nativeHeat_q3FiniteBand_gridCenterMoment_step_scaled M h hM
      n hninj 10 hn j hj c hc
    dsimp only at hh
    have hcoeff : c * (∑ d, β d ^ 2) + 2 * (j : ℝ) *
        (c * (∑ d, q3GridOverlapFactor 10 (n d) * β d ^ 2)) ≤ factor j := by
      have hV : c * (∑ d, β d ^ 2) ≤ (ns : ℝ) * e := by
        rw [Finset.mul_sum]
        calc
          _ ≤ ∑ _d : Fin ns, e := Finset.sum_le_sum fun d _ => hcap d
          _ = (ns : ℝ) * e := by simp
      have hLs : c * (∑ d, q3GridOverlapFactor 10 (n d) * β d ^ 2) ≤ e * L := by
        calc
          _ = ∑ d, q3GridOverlapFactor 10 (n d) * (c * β d ^ 2) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro d _
            ring
          _ ≤ ∑ d, q3GridOverlapFactor 10 (n d) * e :=
            Finset.sum_le_sum fun d _ => mul_le_mul_of_nonneg_left (hcap d)
              (by unfold q3GridOverlapFactor; positivity)
          _ = e * ∑ d, q3GridOverlapFactor 10 (n d) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro d _
            ring
          _ ≤ e * L := mul_le_mul_of_nonneg_left
            (by simpa [n, L] using nativeHeatRefined_overlap_sum_leGen ns) he
      have hj0 : (0 : ℝ) ≤ 2 * (j : ℝ) := by positivity
      dsimp only [factor]
      nlinarith [mul_le_mul_of_nonneg_left hLs hj0]
    have hI : 0 ≤ moment j := by
      apply integral_nonneg
      intro ω
      apply pow_nonneg
      apply mul_nonneg hc
      apply mul_nonneg
      · positivity
      · exact Finset.sum_nonneg fun ij _ => sq_nonneg _
    calc
      moment (j + 1) ≤ (c * (∑ d, β d ^ 2) + 2 * (j : ℝ) *
          (c * (∑ d, q3GridOverlapFactor 10 (n d) * β d ^ 2))) * moment j := by
        simpa [moment, Q, μ, K, I, N, k, β, n] using hh
      _ ≤ factor j * moment j := mul_le_mul_of_nonneg_right hcoeff hI
  have hfactor (j : ℕ) : 0 ≤ factor j := by
    dsimp [factor]
    positivity
  have hzero : moment 0 = 1 := by simp [moment, μ]
  have hprod : ∀ j : ℕ, moment j ≤ ∏ i ∈ Finset.range j, factor i := by
    intro j
    induction j with
    | zero => simp [hzero]
    | succ j ih =>
        by_cases hj : j = 0
        · subst j
          simpa [factor, L, Finset.prod_range_succ] using hmean
        · have hj' : 1 ≤ j := Nat.one_le_iff_ne_zero.mpr hj
          calc
            moment (j + 1) ≤ factor j * moment j := hstep j hj'
            _ ≤ factor j * (∏ i ∈ Finset.range j, factor i) :=
              mul_le_mul_of_nonneg_left ih (hfactor j)
            _ = ∏ i ∈ Finset.range (j + 1), factor i := by
              rw [Finset.prod_range_succ]
              ring
  exact hprod r

private theorem nativeHeat009_q3Factor_le_oldVariance_for_heatGen (ns : ℕ) [NeZero ns] (hnum : NativeHeatGenNum ns)
    (M : ABKModel 2) (hgamma : M.gamma ≤ gammaZero) :
    (9 / 2 : ℝ) * M.gamma *
        (3 : ℝ) ^ (2 * M.gamma * (ns : ℝ)) ≤
      ((nativeHeatOldRowGen ns).e : ℝ) :=
  hnum.efactor M.gamma M.shellPrefix.gamma_pos.le hgamma

theorem nativeHeat009_scaledVariance_capGen (ns : ℕ) [NeZero ns] (hnum : NativeHeatGenNum ns)
    (M : ABKModel 2) (hgamma : M.gamma ≤ gammaZero) :
    (ns : ℝ) * ((1 + (nativeHeatTheta : ℝ)) *
        ((9 / 2 : ℝ) * M.gamma * (3 : ℝ) ^
          (2 * M.gamma * (ns : ℝ)))) ≤
      ((nativeHeatGenVariance ns) : ℝ) := by
  have hfactor := nativeHeat009_q3Factor_le_oldVariance_for_heatGen ns hnum M hgamma
  have hdataQ : (1 + nativeHeatTheta) * (nativeHeatOldRowGen ns).e * (ns : ℚ) ≤
      (nativeHeatGenVariance ns) := by
    rw [nativeHeatGenVariance_eq]
    exact nativeUp_ge _
  have hdata : (1 + (nativeHeatTheta : ℝ)) *
      (ns : ℝ) * ((nativeHeatOldRowGen ns).e : ℝ) ≤
        ((nativeHeatGenVariance ns) : ℝ) := by
    have hdataCast :
        (((1 + nativeHeatTheta) * (nativeHeatOldRowGen ns).e * (ns : ℚ) : ℚ) : ℝ) ≤
          ((nativeHeatGenVariance ns) : ℝ) := by
      exact_mod_cast hdataQ
    calc
      _ = (((1 + nativeHeatTheta) * (nativeHeatOldRowGen ns).e * (ns : ℚ) : ℚ) : ℝ) := by
        simp only [Rat.cast_mul, Rat.cast_add, Rat.cast_one, Rat.cast_natCast]
        ring
      _ ≤ _ := hdataCast
  have hscale0 : 0 ≤ (1 + (nativeHeatTheta : ℝ)) := by
    norm_num [nativeHeatTheta]
  calc
    _ = (ns : ℝ) * (1 + (nativeHeatTheta : ℝ)) *
        ((9 / 2 : ℝ) * M.gamma *
          (3 : ℝ) ^ (2 * M.gamma * (ns : ℝ))) := by ring
    _ ≤ (ns : ℝ) * (1 + (nativeHeatTheta : ℝ)) *
        ((nativeHeatOldRowGen ns).e : ℝ) :=
      mul_le_mul_of_nonneg_left hfactor (mul_nonneg (by positivity) hscale0)
    _ ≤ ((nativeHeatGenVariance ns) : ℝ) := by
      calc
        _ = (1 + (nativeHeatTheta : ℝ)) * (ns : ℝ) *
            ((nativeHeatOldRowGen ns).e : ℝ) := by ring
        _ ≤ _ := hdata

theorem nativeHeat009_scaledSpectral_capGen (ns : ℕ) [NeZero ns] (hnum : NativeHeatGenNum ns)
    (M : ABKModel 2) (hgamma : M.gamma ≤ gammaZero) :
    ((1 + (nativeHeatTheta : ℝ)) *
      ((9 / 2 : ℝ) * M.gamma * (3 : ℝ) ^
        (2 * M.gamma * (ns : ℝ)))) *
      min (ns : ℝ) (((max (ns - 8) 0 : ℕ) : ℝ) + 25 / 72) ≤
        ((nativeHeatGenSpectral ns) : ℝ) := by
  have hfactor := nativeHeat009_q3Factor_le_oldVariance_for_heatGen ns hnum M hgamma
  have hdataQ : (1 + nativeHeatTheta) * (nativeHeatOldRowGen ns).e *
        min (ns : ℚ) (((max (ns - 8) 0 : ℕ) : ℚ) + 25 / 72) ≤
      (nativeHeatGenSpectral ns) := by
    rw [nativeHeatGenSpectral_eq]
    exact nativeUp_ge _
  have hdata : (1 + (nativeHeatTheta : ℝ)) *
      ((nativeHeatOldRowGen ns).e : ℝ) *
        min (ns : ℝ) (((max (ns - 8) 0 : ℕ) : ℝ) + 25 / 72) ≤
        ((nativeHeatGenSpectral ns) : ℝ) := by
    have hdataCast :
        (((1 + nativeHeatTheta) * (nativeHeatOldRowGen ns).e *
          min (ns : ℚ) (((max (ns - 8) 0 : ℕ) : ℚ) + 25 / 72) : ℚ) : ℝ) ≤
        ((nativeHeatGenSpectral ns) : ℝ) := by
      exact_mod_cast hdataQ
    calc
      _ = (((1 + nativeHeatTheta) * (nativeHeatOldRowGen ns).e *
          min (ns : ℚ) (((max (ns - 8) 0 : ℕ) : ℚ) + 25 / 72) : ℚ) : ℝ) := by
        push_cast
        ring
      _ ≤ _ := hdataCast
  have hscale0 : 0 ≤ (1 + (nativeHeatTheta : ℝ)) := by
    norm_num [nativeHeatTheta]
  have hL : 0 ≤ min (ns : ℝ) (((max (ns - 8) 0 : ℕ) : ℝ) + 25 / 72) := by
    positivity
  calc
    _ = (1 + (nativeHeatTheta : ℝ)) *
        min (ns : ℝ) (((max (ns - 8) 0 : ℕ) : ℝ) + 25 / 72) *
        ((9 / 2 : ℝ) * M.gamma *
          (3 : ℝ) ^ (2 * M.gamma * (ns : ℝ))) := by ring
    _ ≤ (1 + (nativeHeatTheta : ℝ)) *
        min (ns : ℝ) (((max (ns - 8) 0 : ℕ) : ℝ) + 25 / 72) *
        ((nativeHeatOldRowGen ns).e : ℝ) :=
      mul_le_mul_of_nonneg_left hfactor (mul_nonneg hscale0 hL)
    _ = (1 + (nativeHeatTheta : ℝ)) *
        ((nativeHeatOldRowGen ns).e : ℝ) *
        min (ns : ℝ) (((max (ns - 8) 0 : ℕ) : ℝ) + 25 / 72) := by ring
    _ ≤ _ := hdata

/-- The canonical depth-ten grid quadratic, heat-inflated, in the frame label `n`. -/
noncomputable def nativeHeatRefinedGridQuadraticGen (ns : ℕ) [NeZero ns]
    (M : ABKModel 2) (n : ℤ) (ω : Cutoff.CutoffSample 2) : ℝ :=
  (1 + (nativeHeatTheta : ℝ)) *
    ((3 : ℝ) ^ (2 * M.gamma * ((n + 9 : ℤ) : ℝ)) /
      (Annealed.sigmaBar M n : ℝ) ^ 2 *
      ((Fintype.card (Fin (3^10) × Fin (3^10)) : ℝ)⁻¹ *
        ∑ ij : Fin (3^10) × Fin (3^10),
          (modelBand (nativeHeatQ3GridCenterSet 10)
            (fun d : Fin ns => ((d.val + 2 : ℕ) : ℤ) - ((10 : ℕ) : ℤ))
            ω (nativeHeatQ3GridCenterPoint 10 ij)) ^ 2))

theorem nativeHeatRefined_gridMoment_le_009_of_stateGen (ns : ℕ) [NeZero ns] (hnum : NativeHeatGenNum ns)
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (n : ℤ)
    (hgamma : M.gamma ≤ gammaZero) (hstate : nativeInductionState M h n)
    (r : ℕ) (hr : r ≤ 20) :
    ∫ ω, nativeHeatRefinedGridQuadraticGen ns M n ω ^ r
      ∂(Cutoff.cutoffSampleLaw M).toMeasure ≤
        (((nativeHeatGenQm ns).getD r 0 : ℚ) : ℝ) := by
  have hscale : 0 ≤ (1 + (nativeHeatTheta : ℝ)) := by norm_num [nativeHeatTheta]
  have hprod := nativeHeatRefined_gridMoment_product_of_stateGen ns M h hM n
    (1 + (nativeHeatTheta : ℝ)) hscale r hstate
  dsimp only at hprod
  have hγ : 0 ≤ M.gamma := M.shellPrefix.gamma_pos.le
  have hV : 0 ≤ ((nativeHeatGenVariance ns) : ℚ) := hnum.variance_nonneg
  have hS : 0 ≤ ((nativeHeatGenSpectral ns) : ℚ) := hnum.spectral_nonneg
  have hvar := nativeHeat009_scaledVariance_capGen ns hnum M hgamma
  have hspec := nativeHeat009_scaledSpectral_capGen ns hnum M hgamma
  have htable := nativeGaussianMoments_product_le (nativeHeatGenVariance ns)
    (nativeHeatGenSpectral ns) hV hS r hr
  rw [← nativeHeatGenQm_eq] at htable
  have htableR : ∏ i ∈ Finset.range r, (((nativeHeatGenVariance ns) : ℝ) +
      2 * (i : ℝ) * ((nativeHeatGenSpectral ns) : ℝ)) ≤
        (((nativeHeatGenQm ns).getD r 0 : ℚ) : ℝ) := by
    exact_mod_cast htable
  have hprod2 : ∏ i ∈ Finset.range r,
      ((ns : ℝ) * ((1 + (nativeHeatTheta : ℝ)) *
          ((9 / 2 : ℝ) * M.gamma * (3 : ℝ) ^ (2 * M.gamma * (ns : ℝ)))) +
        2 * (i : ℝ) * ((1 + (nativeHeatTheta : ℝ)) *
          ((9 / 2 : ℝ) * M.gamma * (3 : ℝ) ^ (2 * M.gamma * (ns : ℝ)))) *
          min (ns : ℝ) (((max (ns - 8) 0 : ℕ) : ℝ) + 25 / 72)) ≤
      ∏ i ∈ Finset.range r, (((nativeHeatGenVariance ns) : ℝ) +
        2 * (i : ℝ) * ((nativeHeatGenSpectral ns) : ℝ)) := by
    apply Finset.prod_le_prod₀
    · intro i _
      have : 0 ≤ (1 + (nativeHeatTheta : ℝ)) *
          ((9 / 2 : ℝ) * M.gamma * (3 : ℝ) ^ (2 * M.gamma * (ns : ℝ))) := by
        positivity
      positivity
    · intro i _
      have hi : (0 : ℝ) ≤ 2 * (i : ℝ) := by positivity
      have := mul_le_mul_of_nonneg_left hspec hi
      nlinarith [hvar, this]
  have hmoment := hprod.trans (hprod2.trans htableR)
  refine (integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)).trans_le hmoment
  simp only [nativeHeatRefinedGridQuadraticGen, mul_assoc]

theorem nativeHeatRefined_gridQuadratic_nonnegGen (ns : ℕ) [NeZero ns] (M : ABKModel 2) (n : ℤ)
    (ω : Cutoff.CutoffSample 2) : 0 ≤ nativeHeatRefinedGridQuadraticGen ns M n ω := by
  unfold nativeHeatRefinedGridQuadraticGen
  have hheat : 0 ≤ 1 + (nativeHeatTheta : ℝ) := by norm_num [nativeHeatTheta]
  exact mul_nonneg hheat (mul_nonneg
    (div_nonneg (Real.rpow_nonneg (by norm_num) _) (sq_nonneg _))
    (mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
      (Finset.sum_nonneg fun ij _ => sq_nonneg _)))

theorem nativeHeatRefined_gridQuadratic_measurableGen (ns : ℕ) [NeZero ns] (M : ABKModel 2) (n : ℤ) :
    Measurable (nativeHeatRefinedGridQuadraticGen ns M n) := by
  unfold nativeHeatRefinedGridQuadraticGen
  apply measurable_const.mul
  apply measurable_const.mul
  apply measurable_const.mul
  apply Finset.measurable_sum
  intro ij _
  exact ((ContinuousMap.evalCLM ℝ (nativeHeatQ3GridCenterPoint 10 ij)).continuous.measurable.comp
    (measurable_modelBand (nativeHeatQ3GridCenterSet 10)
      (fun d : Fin ns => ((d.val + 2 : ℕ) : ℤ) - ((10 : ℕ) : ℤ)))).pow_const 2

theorem nativeHeatRefined_gridMoment_lintegral_le_009_of_stateGen (ns : ℕ) [NeZero ns] (hnum : NativeHeatGenNum ns)
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (n : ℤ)
    (hgamma : M.gamma ≤ gammaZero) (hstate : nativeInductionState M h n)
    (j : ℕ) (hj20 : j ≤ 20) :
    ∫⁻ ω, ENNReal.ofReal (nativeHeatRefinedGridQuadraticGen ns M n ω ^ j)
      ∂(Cutoff.cutoffSampleLaw M).toMeasure ≤
        ENNReal.ofReal (((nativeHeatGenQm ns).getD j 0 : ℚ) : ℝ) := by
  classical
  let I := Fin (3^10) × Fin (3^10)
  let K := nativeHeatQ3GridCenterSet 10
  let shells : Fin ns → ℤ := fun d => ((d.val + 2 : ℕ) : ℤ) - ((10 : ℕ) : ℤ)
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let X : I → Cutoff.CutoffSample 2 → ℝ := fun ij ω =>
    modelBand K shells ω (nativeHeatQ3GridCenterPoint 10 ij)
  let F := nativeHeatRefinedGridQuadraticGen ns M n
  letI : IsProbabilityMeasure μ := (Cutoff.cutoffSampleLaw M).property
  have hshells : Function.Injective shells := by
    intro d₁ d₂ hh
    apply Fin.ext
    dsimp [shells] at hh
    omega
  have hXgauss : IsCenteredGaussianFamily μ X := by
    dsimp [X, K, μ]
    exact nativeHeat_q3FiniteBand_gridValues_gaussian M h hM shells hshells 10
  have hXmem (ij : I) : MemLp (X ij) (ENNReal.ofReal (2 * (j : ℝ))) μ :=
    hXgauss.memLp ij (ENNReal.ofReal (2 * (j : ℝ))) ENNReal.ofReal_ne_top
  have hXsqmem (ij : I) : MemLp (fun ω => (X ij ω) ^ 2)
      (ENNReal.ofReal (j : ℝ)) μ := by
    have hh := (hXmem ij).norm_rpow_div (ENNReal.ofReal 2)
    rw [← ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)] at hh
    have hdiv : (2 * (j : ℝ)) / 2 = (j : ℝ) := by ring
    rw [hdiv] at hh
    simpa [Real.norm_eq_abs, sq_abs] using hh
  have hFmem : MemLp F (ENNReal.ofReal (j : ℝ)) μ := by
    have hsum : MemLp (fun ω => ∑ ij : I, (X ij ω) ^ 2)
        (ENNReal.ofReal (j : ℝ)) μ :=
      memLp_finsetSum Finset.univ (fun ij _ => hXsqmem ij)
    have := (hsum.const_mul ((Fintype.card I : ℝ)⁻¹)).const_mul
      ((3 : ℝ) ^ (2 * M.gamma * ((n + 9 : ℤ) : ℝ)) / (Annealed.sigmaBar M n : ℝ) ^ 2)
    exact (this.const_mul (1 + (nativeHeatTheta : ℝ)))
  have hFnonneg (ω : Cutoff.CutoffSample 2) : 0 ≤ F ω :=
    nativeHeatRefined_gridQuadratic_nonnegGen ns M n ω
  have hMoment : ∫ ω, F ω ^ j ∂μ ≤ (((nativeHeatGenQm ns).getD j 0 : ℚ) : ℝ) :=
    nativeHeatRefined_gridMoment_le_009_of_stateGen ns hnum M h hM n hgamma hstate j hj20
  have hFmem' : MemLp F j μ := by simpa using hFmem
  have hInt : Integrable (fun ω => F ω ^ j) μ := by
    have hh := hFmem'.integrable_norm_pow'
    have heq : (fun ω => ‖F ω‖ ^ j) = fun ω => F ω ^ j := by
      funext ω
      rw [Real.norm_eq_abs, abs_of_nonneg (hFnonneg ω)]
    exact heq ▸ hh
  have hlin : ∫⁻ ω, ENNReal.ofReal (F ω ^ j) ∂μ =
      ENNReal.ofReal (∫ ω, F ω ^ j ∂μ) := by
    rw [← ofReal_integral_eq_lintegral_ofReal hInt
      (Filter.Eventually.of_forall fun ω => pow_nonneg (hFnonneg ω) j)]
  rw [hlin]
  exact ENNReal.ofReal_le_ofReal hMoment

/-- The physical depth-ten centre quadratic is the canonical grid quadratic after the
exact translate/scale shift, with frame label `m+1`. -/
theorem nativeHeatRefined_centerQuadratic_eq_gridGen (ns : ℕ) [NeZero ns] (M : ABKModel 2) (m : ℤ)
    (ω : Cutoff.CutoffSample 2) :
    nativeHeatQ3RefinedCarrierSourceCenterQuadraticGen ns M m ω =
      nativeHeatRefinedGridQuadraticGen ns M (m + 1)
        (ASDExplicitGamma.Scalar.cutoffScaleShift M.gamma (m + 10)
          (Cutoff.translateCutoffSample
            (nativeHeatQ3ParentOrigin (originCube 2 (m + 10))) ω)) := by
  classical
  let Q0 := originCube 2 (m + 10)
  have hscale : Q0.scale = m + 10 := by simp [Q0, originCube]
  let B : ℝ := Real.rpow 3 (M.gamma * ((m + 10 : ℤ) : ℝ))
  let A : ℝ := Real.rpow 3 (M.gamma * (-((m + 10 : ℤ) : ℝ)))
  let σ : ℝ := (Annealed.sigmaBar M (m + 1) : ℝ)
  have hAB : A * B = 1 := by
    dsimp [A, B]
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    have hzero : M.gamma * (-((m + 10 : ℤ) : ℝ)) +
        M.gamma * ((m + 10 : ℤ) : ℝ) = 0 := by ring
    rw [hzero]
    simp
  have hBsq : B ^ 2 = (3 : ℝ) ^ (2 * M.gamma * ((m + 10 : ℤ) : ℝ)) := by
    dsimp [B]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    congr 1
    ring
  have hcard : (Fintype.card nativeHeatQ3RefinedCarrierIndex : ℝ) =
      (Fintype.card (Fin (3^10) × Fin (3^10)) : ℝ) := by
    rw [Fintype.card_congr (finProdFinEquiv.symm :
      nativeHeatQ3RefinedCarrierIndex ≃ Fin (3^10) × Fin (3^10))]
  have hraw (ij : Fin (3^10) × Fin (3^10)) := nativeHeatQ3RefinedFreshRaw_eq_scaled_bandGen ns M m ω ij
  unfold nativeHeatQ3RefinedCarrierSourceCenterQuadraticGen
    nativeHeatRefinedGridQuadraticGen
  rw [hcard]
  rw [← Equiv.sum_comp finProdFinEquiv]
  have hz (ij : Fin (3^10) × Fin (3^10)) :
      (nativeHeatQ3RefinedCarrierSourceZGen ns M m ω (finProdFinEquiv ij)) ^ 2 =
        (1 + (nativeHeatTheta : ℝ)) * ((B ^ 2 / σ ^ 2) *
          (modelBand (nativeHeatQ3GridCenterSet 10)
            (fun d : Fin ns => ((d.val + 2 : ℕ) : ℤ) - ((10 : ℕ) : ℤ))
            (ASDExplicitGamma.Scalar.cutoffScaleShift M.gamma (m + 10)
              (Cutoff.translateCutoffSample (nativeHeatQ3ParentOrigin Q0) ω))
            (nativeHeatQ3GridCenterPoint 10 ij)) ^ 2) := by
    unfold nativeHeatQ3RefinedCarrierSourceZGen
    rw [hraw ij, div_pow, mul_pow, Real.sq_sqrt (by norm_num [nativeHeatTheta])]
    ring
  simp_rw [hz]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  rw [show (m + 1 + 9 : ℤ) = m + 10 by ring, hBsq]
  ring

/-- The depth-ten source centre quadratic obeys the configured 009 Gaussian row. -/
theorem nativeHeatQ3RefinedCarrierSourceCenterQuadraticMoment_le_009_Gen (ns : ℕ) [NeZero ns] (hnum : NativeHeatGenNum ns)
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hgamma : M.gamma ≤ gammaZero)
    (m : ℤ) (hstate : nativeInductionState M h (m + 1))
    (k : ℕ) (hk1 : 1 ≤ k) (hk20 : k ≤ 20) :
    ∫⁻ ω, ENNReal.ofReal
      (nativeHeatQ3RefinedCarrierSourceCenterQuadraticGen ns M m ω ^ k)
      ∂(Cutoff.cutoffSampleLaw M).toMeasure ≤
      ENNReal.ofReal (((nativeHeatGenQm ns).getD k 0 : ℚ) : ℝ) := by
  let f : Cutoff.CutoffSample 2 → ℝ≥0∞ := fun ω =>
    ENNReal.ofReal (nativeHeatRefinedGridQuadraticGen ns M (m + 1) ω ^ k)
  have hf : Measurable f :=
    ENNReal.measurable_ofReal.comp
      ((nativeHeatRefined_gridQuadratic_measurableGen ns M (m + 1)).pow_const k)
  have htransfer := nativeHeat_cutoff_lintegral_translate_scale_shift M
    (nativeHeatQ3ParentOrigin (originCube 2 (m + 10))) (m + 10) f hf
  calc
    _ = ∫⁻ ω, f (ASDExplicitGamma.Scalar.cutoffScaleShift M.gamma (m + 10)
        (Cutoff.translateCutoffSample
          (nativeHeatQ3ParentOrigin (originCube 2 (m + 10))) ω))
        ∂(Cutoff.cutoffSampleLaw M).toMeasure := by
      apply lintegral_congr
      intro ω
      simp only [f, nativeHeatRefined_centerQuadratic_eq_gridGen]
    _ = ∫⁻ ω, f ω ∂(Cutoff.cutoffSampleLaw M).toMeasure := htransfer
    _ ≤ _ := nativeHeatRefined_gridMoment_lintegral_le_009_of_stateGen ns hnum M h hM (m + 1)
      hgamma hstate k hk20

end ASDExplicitGamma.Native
