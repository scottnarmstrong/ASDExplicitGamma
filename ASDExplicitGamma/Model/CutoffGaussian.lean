module

public import ASDExplicitGamma.Model.Cutoff
public import ASDExplicitGamma.Model.SpectralModel
public import Algsuperdiff.Section3.Provider.Stream.CutoffSecondMoment
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic

@[expose] public section

namespace ASDExplicitGamma.Model

open Homogenization MeasureTheory ProbabilityTheory Filter
open scoped NNReal
open Algsuperdiff.Section3 Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3.Cutoff

/-- The actual finite lower-tail scalar stream at a fixed spatial point. -/
def cutoffPartialStream (m : ℤ) (x : Vec 2) (N : ℕ) (ω : ShellSeq 2) : ℝ :=
  ∑ r ∈ Finset.range N, ω (m - (r : ℤ)) x 1 0

private theorem measurable_shellPoint (k : ℤ) (x : Vec 2) :
    Measurable (fun ω : ShellSeq 2 => ω k x 1 0) :=
  (ShellField.measurable_eval_entry x 1 0).comp (measurable_pi_apply k)

/-- Exact Gaussian law of each scaled shell stream at a point. -/
theorem shellPoint_gaussian (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (k : ℤ) (x : Vec 2) :
    HasLaw (fun ω : ShellSeq 2 => ω k x 1 0)
      (gaussianReal 0 (Real.toNNReal (h ^ 2 * (3 : ℝ) ^ (2 * M.gamma * (k : ℝ))))) M.P.toMeasure := by
  refine ⟨(measurable_shellPoint k x).aemeasurable, ?_⟩
  have hs := shellStream_linearCombination_law M h hM k 1
    (fun _ : Fin 1 => x) (fun _ : Fin 1 => (1 : ℝ))
  have he : Measure.map (fun ω : ShellSeq 2 => ω k x 1 0) M.P.toMeasure =
      Measure.map (fun j : ShellField 2 => j x 1 0) (ShellField.shellMarginalLaw M.P k).toMeasure := by
    change Measure.map ((fun j : ShellField 2 => j x 1 0) ∘ (fun ω : ShellSeq 2 => ω k)) _ = _
    rw [← Measure.map_map (ShellField.measurable_eval_entry x 1 0) (measurable_pi_apply k)]
    rfl
  rw [he]
  have ho : shellStreamObservable 1 (fun _ : Fin 1 => x) (fun _ : Fin 1 => (1 : ℝ)) =
      (fun j : ShellField 2 => j x 1 0) := by
    funext j
    simp [shellStreamObservable]
  rw [ho] at hs
  simpa only [sub_self, Pi.zero_apply, mul_zero, q3Cov_zero_eq_one,
    Fintype.sum_unique, one_mul, mul_one] using hs

private theorem shellPoint_tail_independent (M : ABKModel 2) (m : ℤ) (x : Vec 2) :
    iIndepFun (fun r : ℕ => fun ω : ShellSeq 2 => ω (m - (r : ℤ)) x 1 0) M.P.toMeasure := by
  have hi := (shellLevels_independent M).comp
    (fun _ : ℤ => fun j : ShellField 2 => j x 1 0)
    (fun _ => ShellField.measurable_eval_entry x 1 0)
  have hinj : Function.Injective (fun r : ℕ => m - (r : ℤ)) := by
    intro a b hab
    change m - (a : ℤ) = m - (b : ℤ) at hab
    have hh : (a : ℤ) = b := by omega
    exact_mod_cast hh
  exact hi.precomp (g := fun r : ℕ => m - (r : ℤ)) hinj

/-- Every finite lower-tail partial stream is centered Gaussian with its
actual accumulated marginal variance. -/
theorem cutoffPartialStream_gaussian (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (m : ℤ) (x : Vec 2) (N : ℕ) :
    HasLaw (cutoffPartialStream m x N)
      (gaussianReal 0 (∑ r ∈ Finset.range N,
        Real.toNNReal (h ^ 2 * (3 : ℝ) ^ (2 * M.gamma * ((m - (r : ℤ) : ℤ) : ℝ)))))
      M.P.toMeasure := by
  have hm (N : ℕ) : Measurable (cutoffPartialStream m x N) := by
    change Measurable (fun ω : ShellSeq 2 => ∑ r ∈ Finset.range N, ω (m - (r : ℤ)) x 1 0)
    exact Finset.measurable_sum _ (fun r _ => measurable_shellPoint (m - (r : ℤ)) x)
  refine ⟨(hm N).aemeasurable, ?_⟩
  induction N with
  | zero =>
    have hz : cutoffPartialStream m x 0 = (fun _ : ShellSeq 2 => (0 : ℝ)) := by
      funext ω; simp [cutoffPartialStream]
    rw [hz]
    simp
  | succ N ih =>
    have hi := (shellPoint_tail_independent M m x).indepFun_finsetSum_of_notMem
      (fun r => measurable_shellPoint (m - (r : ℤ)) x) (Finset.notMem_range_self (n := N))
    have hsum : (∑ j ∈ Finset.range N, fun ω : ShellSeq 2 => ω (m - (j : ℤ)) x 1 0) =
        cutoffPartialStream m x N := by
      funext ω
      simp [cutoffPartialStream, Finset.sum_apply]
    rw [hsum] at hi
    have hx : HasLaw (cutoffPartialStream m x N)
        (gaussianReal 0 (∑ r ∈ Finset.range N,
          Real.toNNReal (h ^ 2 * (3 : ℝ) ^ (2 * M.gamma * ((m - (r : ℤ) : ℤ) : ℝ))))) M.P.toMeasure :=
      ⟨(hm N).aemeasurable, ih⟩
    have hs := gaussianReal_add_gaussianReal_of_indepFun hi hx (shellPoint_gaussian M h hM (m - (N : ℤ)) x)
    have hstep : cutoffPartialStream m x (N + 1) =
        cutoffPartialStream m x N + (fun ω : ShellSeq 2 => ω (m - (N : ℤ)) x 1 0) := by
      funext ω
      simp [cutoffPartialStream, Finset.sum_range_succ]
    rw [hstep, Finset.sum_range_succ]
    simpa only [zero_add] using hs

/-- Partial-stream Gaussian laws on the actual completed-sample carrier. -/
theorem cutoffPartialStream_sample_gaussian (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (m : ℤ) (x : Vec 2) (N : ℕ) :
    HasLaw (fun ω : CutoffSample 2 => cutoffPartialStream m x N ω.1)
      (gaussianReal 0 (∑ r ∈ Finset.range N,
        Real.toNNReal (h ^ 2 * (3 : ℝ) ^ (2 * M.gamma * ((m - (r : ℤ) : ℤ) : ℝ)))))
      (cutoffSampleLaw M).toMeasure := by
  exact (cutoffPartialStream_gaussian M h hM m x N).comp
    ⟨measurable_subtype_coe.aemeasurable, map_cutoffSampleLaw_val M⟩

/-- The literal cutoff series converges at every point of every source sample. -/
theorem cutoffPartialStream_tendsto (m : ℤ) (x : Vec 2) (ω : CutoffSample 2) :
    Tendsto (fun N => cutoffPartialStream m x N ω.1) atTop
      (nhds (cutoffValue m ω x 1 0)) := by
  obtain ⟨ell, hx⟩ := Algsuperdiff.Section3.Provider.Stream.exists_mem_openCubeSet_originCube x
  have hs : Summable (fun r : ℕ => ω.1 (m - (r : ℤ)) x 1 0) := by
    refine (lowerTailGood_summable ω.2 ell m).of_norm_bounded fun r => ?_
    exact abs_entry_le_localCubeControl ell _ hx 1 0
  exact hs.hasSum.tendsto_sum_nat

private theorem shellVarianceSeries_hasSum (h γ : ℝ) (m : ℤ) (hγ : 0 < γ) :
    HasSum (shellVarianceSeries h γ m) (shellVarianceSum h γ m) := by
  let q : ℝ := (3 : ℝ) ^ (-(2 * γ))
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have he (r : ℕ) : shellVarianceSeries h γ m r =
      (h ^ 2 * (3 : ℝ) ^ (2 * γ * (m : ℝ))) * q ^ r := by
    dsimp [shellVarianceSeries, q]
    rw [show 2 * γ * ((m : ℝ) - (r : ℝ)) =
      2 * γ * (m : ℝ) + (-(2 * γ)) * (r : ℝ) by ring,
      Real.rpow_add (by norm_num : (0 : ℝ) < 3),
      Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 3)]
    ring
  have hs : Summable (shellVarianceSeries h γ m) := by
    exact ((summable_geometric_of_lt_one hq0 hq1).mul_left
      (h ^ 2 * (3 : ℝ) ^ (2 * γ * (m : ℝ)))).congr (fun r => (he r).symm)
  rw [← shellVarianceSeries_eq_shellVarianceSum h γ m hγ]
  exact hs.hasSum

/-- The literal accumulated finite Gaussian variance parameter. -/
noncomputable def cutoffPartialVariance (M : ABKModel 2) (h : ℝ) (m : ℤ) (N : ℕ) : ℝ≥0 :=
  ∑ r ∈ Finset.range N,
    Real.toNNReal (h ^ 2 * (3 : ℝ) ^ (2 * M.gamma * ((m - (r : ℤ) : ℤ) : ℝ)))

/-- The actual finite Gaussian variance parameters converge to the actual B_m. -/
theorem cutoffPartialStream_variance_tendsto (M : ABKModel 2) (h : ℝ) (m : ℤ) :
    Tendsto (fun N : ℕ => (cutoffPartialVariance M h m N : ℝ))
      atTop (nhds (shellVarianceSum h M.gamma m)) := by
  have he (N : ℕ) : (cutoffPartialVariance M h m N : ℝ) =
      ∑ r ∈ Finset.range N, shellVarianceSeries h M.gamma m r := by
    simp only [cutoffPartialVariance, NNReal.coe_sum]
    apply Finset.sum_congr rfl
    intro r hr
    change ((Real.toNNReal (h ^ 2 * (3 : ℝ) ^
      (2 * M.gamma * ((m - (r : ℤ) : ℤ) : ℝ))) : ℝ≥0) : ℝ) = _
    rw [Real.coe_toNNReal _ (by positivity : 0 ≤ h ^ 2 * (3 : ℝ) ^
      (2 * M.gamma * ((m - (r : ℤ) : ℤ) : ℝ)))]
    simp [shellVarianceSeries]
  simpa only [he] using (shellVarianceSeries_hasSum h M.gamma m M.shellPrefix.gamma_pos).tendsto_sum_nat

/-- The completed stream has its exact Gaussian law with variance B_m.
The proof passes characteristic functions of the actual finite shell sums. -/
theorem cutoffStream_gaussian (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (m : ℤ) (x : Vec 2) :
    HasLaw (fun ω : CutoffSample 2 => cutoffValue m ω x 1 0)
      (gaussianReal 0 (Real.toNNReal (shellVarianceSum h M.gamma m)))
      (cutoffSampleLaw M).toMeasure := by
  let μ := (cutoffSampleLaw M).toMeasure
  let f : CutoffSample 2 → ℝ := fun ω => cutoffValue m ω x 1 0
  have hf : Measurable f := measurable_cutoff_apply_entry m x 1 0
  refine ⟨hf.aemeasurable, ?_⟩
  have hv := cutoffPartialStream_variance_tendsto M h m
  have hB : 0 ≤ shellVarianceSum h M.gamma m :=
    ge_of_tendsto hv (Filter.Eventually.of_forall fun N => (cutoffPartialVariance M h m N).coe_nonneg)
  apply Measure.ext_of_charFun
  funext t
  let F (N : ℕ) (ω : CutoffSample 2) : ℂ :=
    Complex.exp (((t * cutoffPartialStream m x N ω.1 : ℝ) : ℂ) * Complex.I)
  let G (ω : CutoffSample 2) : ℂ := Complex.exp (((t * f ω : ℝ) : ℂ) * Complex.I)
  have hFN (N : ℕ) : AEStronglyMeasurable (F N) μ := by
    have hm : AEMeasurable (fun ω : CutoffSample 2 => cutoffPartialStream m x N ω.1) μ :=
      (cutoffPartialStream_sample_gaussian M h hM m x N).aemeasurable
    have hc : Continuous (fun y : ℝ => Complex.exp (((t * y : ℝ) : ℂ) * Complex.I)) := by fun_prop
    exact (hc.measurable.comp_aemeasurable hm).aestronglyMeasurable
  have hb (N : ℕ) : ∀ᵐ ω ∂μ, ‖F N ω‖ ≤ (1 : ℝ) := by
    exact Filter.Eventually.of_forall fun ω => by
      dsimp [F]
      rw [Complex.norm_exp_ofReal_mul_I]
  have hl : ∀ᵐ ω ∂μ, Tendsto (fun N => F N ω) atTop (nhds (G ω)) := by
    apply Filter.Eventually.of_forall
    intro ω
    have hc : Continuous (fun y : ℝ => Complex.exp (((t * y : ℝ) : ℂ) * Complex.I)) := by fun_prop
    exact hc.continuousAt.tendsto.comp (cutoffPartialStream_tendsto m x ω)
  have hi := tendsto_integral_filter_of_dominated_convergence (fun _ : CutoffSample 2 => (1 : ℝ))
    (Filter.Eventually.of_forall hFN) (Filter.Eventually.of_forall hb) (integrable_const 1) hl
  have he (N : ℕ) : (∫ ω, F N ω ∂μ) =
      charFun (gaussianReal 0 (cutoffPartialVariance M h m N)) t := by
    have hn := cutoffPartialStream_sample_gaussian M h hM m x N
    change HasLaw (fun ω : CutoffSample 2 => cutoffPartialStream m x N ω.1)
      (gaussianReal 0 (cutoffPartialVariance M h m N)) μ at hn
    rw [← hn.map_eq, charFun_apply_real,
      integral_map hn.aemeasurable (by fun_prop)]
    simp only [F, Complex.ofReal_mul]
  simp_rw [he] at hi
  let H : ℝ → ℂ := fun v => Complex.exp (-((v : ℂ) * (t : ℂ) ^ 2) / 2)
  have hc : Continuous H := by dsimp [H]; fun_prop
  have hv' := hc.continuousAt.tendsto.comp hv
  have heq (v : ℝ≥0) : charFun (gaussianReal 0 v) t = H (v : ℝ) := by
    simp [H, charFun_gaussianReal, neg_div]
  have hchar : Tendsto (fun N => charFun (gaussianReal 0 (cutoffPartialVariance M h m N)) t)
      atTop (nhds (charFun (gaussianReal 0 (Real.toNNReal (shellVarianceSum h M.gamma m))) t)) := by
    simp_rw [heq, Real.coe_toNNReal _ hB]
    exact hv'
  have hlimit := tendsto_nhds_unique hi hchar
  rw [charFun_apply_real, integral_map hf.aemeasurable (by fun_prop)]
  simpa only [G, μ, Complex.ofReal_mul] using hlimit

end ASDExplicitGamma.Model
