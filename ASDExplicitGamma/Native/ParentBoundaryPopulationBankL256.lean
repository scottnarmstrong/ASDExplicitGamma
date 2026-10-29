module

public import ASDExplicitGamma.Inverse.BankInverse
public import ASDExplicitGamma.Inverse.BankOnePassMeanActual

/-! Actual L256 total local-bank estimate for every admissible finite root population. -/

@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Inverse Algsuperdiff.Section3
open scoped ENNReal
noncomputable section

/-- The original pretruncation local bank has its total L256 cap on every
admissible actual root population. All causal mean inputs are discharged;
only the source geometric root/population data and model states remain. -/
theorem parent_boundary_population_bank_L256
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (hg : M.gamma ≤ gammaZero)
    (roots : Finset (TriadicCube 2)) (m J : ℤ) (hmJ : m ≤ J) (weights : ℤ → ℝ)
    (hw : ∀ k ∈ Finset.Ioc m J,0 ≤ weights k ∧ weights k ≤ 1)
    (hscale : ∀ Q ∈ roots,Q.scale ≤ m ∧ m-Q.scale ≤ 5)
    (hcard : roots.card ≤ 6*9^45) (hpast : ∀ k<m,nativeInductionState M h k) :
    eLpNorm (fun ω : Cutoff.CutoffSample 2 => (bankFiniteRootHistoryMax roots M m J weights ω).toReal)
      256 (Cutoff.cutoffSampleLaw M).toMeasure ≤ ENNReal.ofReal (3683/2500:ℝ) := by
  classical
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let Y := bankFiniteRootHistoryMax roots M m J
    weights
  let R := bankFiniteRootRemainderHistoryMax roots M m (inverseBankRootRow .localInverse)
  let A : ℝ := inverseBankA .localInverse
  let E : ℝ := inverseBankE .localInverse
  have hmean := (bank_inverse_mean_inputs_of_states M h hM hg m hpast).2
  obtain ⟨hY,hR,hSplit,hR256⟩ := inverse_bank_population_pretruncation M h hM hg .localInverse
    roots m J hmJ weights hw hscale hcard hpast hmean
  have hmono : eLpNorm Y 256 μ ≤ eLpNorm (fun ω => ENNReal.ofReal A+R ω) 256 μ := by
    apply eLpNorm_mono_enorm_ae hY.aestronglyMeasurable
    filter_upwards [hSplit] with ω hω
    simpa only [enorm_eq_self] using hω
  have haff := bank_ennreal_affine_Lp_bound μ 256 1 (ENNReal.ofReal A) (fun _ => 1) R
    (by simp) ENNReal.ofReal_ne_top measurable_const hR (by norm_num)
  have hone : eLpNorm (fun _ : Cutoff.CutoffSample 2 => (1:ℝ≥0∞)) 256 μ=1 := by
    rw [eLpNorm_const' _ (by norm_num) (by norm_num)]
    simp only [enorm_eq_self,measure_univ,ENNReal.one_rpow,mul_one]
  simp only [one_mul,mul_one,hone] at haff
  have htotal : eLpNorm Y 256 μ ≤ ENNReal.ofReal (3683/2500:ℝ) := by
    apply (hmono.trans haff).trans
    apply (add_le_add_right hR256 (ENNReal.ofReal A)).trans
    have hA0 := (inverse_bank_profile_nonneg .localInverse).1
    have hE0 := (inverse_bank_profile_nonneg .localInverse).2.1
    rw [←ENNReal.ofReal_add hA0 hE0]
    apply ENNReal.ofReal_le_ofReal
    have hn := (inverse_bank_numeric_bounds .localInverse).1
    simpa only [A,E,inverseBankCap,Rat.cast_div,Rat.cast_ofNat] using hn.le
  have hb := local_inverse_bank M h hM hg roots m J hmJ weights hw hscale hcard hpast hmean
  have hr : eLpNorm ((fun ω => (Y ω).toReal)) 256 μ=eLpNorm Y 256 μ := by
    calc
      _ = eLpNorm (fun ω => ENNReal.ofReal ((fun ω => (Y ω).toReal) ω)) 256 μ :=
        (eLpNorm_ofReal _ (Filter.Eventually.of_forall fun _ => ENNReal.toReal_nonneg)).symm
      _ = _ := eLpNorm_congr_ae (ofReal_toReal_ae_eq hb.history_finite)
  exact hr.trans_le htotal

end
end ASDExplicitGamma.Native
