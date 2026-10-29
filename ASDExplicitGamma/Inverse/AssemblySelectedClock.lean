module

public import ASDExplicitGamma.Inverse.AllOrderPlanarInterpolation
public import ASDExplicitGamma.Inverse.SelectedTail
public import ASDExplicitGamma.Inverse.StoppedSelectedFamilyIdentity

/-! Exact complete root-clock moment at every order band. -/

@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian
open scoped ENNReal
noncomputable section

/-- Root clock expressed in the selected index, retaining the five-generation
shift between the selected and full stopping indices. -/
def assemblySelectedClock (γ : ℝ) (H : ℕ) : ℝ :=
  (3:ℝ)^(2*γ*((H:ℝ)+5-38))

/-- Exact finite-candidate maximum plus the complete infinite root tail. -/
def assemblySelectedClockBudget (γ p : ℝ) (H0 : ℕ) : ℝ :=
  (3:ℝ)^(10*γ)*((3:ℝ)^(2*γ*((H0:ℝ)-27))+
    selectedWaveExactTail (γ/2) (p/2) H0 0)

/-- A deterministic clock pays the maximum of the twelve bounded candidates,
while every later height atom is retained with its actual probability. -/
theorem assembly_selected_clock_Lp_of_atoms {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (H : Ω → ℕ) (hH : Measurable H)
    (H0 : ℕ) (hH0 : 333 ≤ H0) (hge : ∀ ω, H0 ≤ H ω)
    (γ : ℝ) (hγ : 0 ≤ γ) (p : ℝ) (hp : 2 ≤ p)
    (hprob : ∀ n, μ {ω | H ω=H0+12+n} ≤ ENNReal.ofReal (selectedTailProbability H0 n)) :
    eLpNorm (fun ω => assemblySelectedClock γ (H ω)) (ENNReal.ofReal p) μ ≤
      ENNReal.ofReal (assemblySelectedClockBudget γ p H0) := by
  let f := fun n : ℕ => fun _ : Ω => assemblySelectedClock γ n
  let F := fun n : ℕ => ({ω | H ω=H0+12+n} : Set Ω).indicator (f (H0+12+n))
  let b := fun n : ℕ => assemblySelectedClock γ (H0+12+n)*
    (selectedTailProbability H0 n)^(1/p:ℝ)
  have hp0 : 0 < p := by linarith only [hp]
  have hpne : ENNReal.ofReal p ≠ 0 := (ENNReal.ofReal_pos.mpr hp0).ne'
  have hE (n : ℕ) : MeasurableSet {ω | H ω=H0+12+n} := hH (measurableSet_singleton _)
  have hFm (n : ℕ) : Measurable (F n) := measurable_const.indicator (hE n)
  have hb0 (n : ℕ) : 0 ≤ b n := by dsimp only [b,assemblySelectedClock]; unfold selectedTailProbability; positivity
  have hF (n : ℕ) : eLpNorm (F n) (ENNReal.ofReal p) μ ≤ ENNReal.ofReal (b n) := by
    rw [eLpNorm_indicator_const (hE n).nullMeasurableSet hpne ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal hp0.le,Real.enorm_eq_ofReal (by unfold assemblySelectedClock; positivity)]
    apply (mul_le_mul_right (ENNReal.rpow_le_rpow (hprob n) (by positivity : (0:ℝ) ≤ 1/p)) _).trans_eq
    rw [ENNReal.ofReal_rpow_of_pos (by unfold selectedTailProbability; positivity),
      ← ENNReal.ofReal_mul (by unfold assemblySelectedClock; positivity)]
  have he (n : ℕ) : b n = (3:ℝ)^(10*γ)*
      ((3:ℝ)^(4*(γ/2)*(selectedFirstClock H0+(n:ℝ)))*
        (selectedTailProbability H0 n)^(1/(2*(p/2)):ℝ)) := by
    dsimp only [b,assemblySelectedClock,selectedFirstClock]
    push_cast
    rw [← mul_assoc,← Real.rpow_add (by norm_num : (0:ℝ)<3)]
    congr 2 <;> ring
  have hs := physical_selected_exact_tail_summable (γ/2) (p/2) H0 (by positivity) hH0 0
  simp only [Fin.val_zero,pow_zero,one_mul] at hs
  have hbs : HasSum b ((3:ℝ)^(10*γ)*selectedWaveExactTail (γ/2) (p/2) H0 0) := by
    convert hs.hasSum.mul_left ((3:ℝ)^(10*γ)) using 1
    · funext n
      exact he n
    · simp only [selectedWaveExactTail,Fin.val_zero,pow_zero,one_mul]
  have htail := countable_density_series_Lp μ (ENNReal.ofReal p)
    (ENNReal.one_le_ofReal.mpr (by linarith only [hp])) F hFm b hb0 _ hbs hF
  let B := selectedBoundedFamily H (selectedCandidateHeights H0) f
  have hB : Measurable B := Finset.measurable_sum _ (fun n _ =>
    measurable_const.indicator (hH (measurableSet_singleton n)))
  have hfinite : eLpNorm B (ENNReal.ofReal p) μ ≤
      ENNReal.ofReal (assemblySelectedClock γ (H0+11)) := by
    have hpoint (ω : Ω) : ‖B ω‖ ≤ assemblySelectedClock γ (H0+11) := by
      change ‖selectedBoundedFamily H (selectedCandidateHeights H0) f ω‖ ≤ _
      rw [selected_bounded_family_eq]
      split_ifs with hm
      · rw [Real.norm_eq_abs,abs_of_nonneg (by unfold f assemblySelectedClock; positivity)]
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 3)
        apply mul_le_mul_of_nonneg_left _ (mul_nonneg (by norm_num) hγ)
        have hh := (selected_candidate_mem H0 (H ω)).mp hm
        have hh' : (H ω:ℝ) ≤ (H0+11:ℕ) := by exact_mod_cast hh.2
        linarith only [hh']
      · rw [norm_zero]
        unfold assemblySelectedClock
        positivity
    apply (eLpNorm_mono_real hB.aestronglyMeasurable hpoint).trans_eq
    rw [eLpNorm_const' _ hpne ENNReal.ofReal_ne_top,measure_univ,ENNReal.one_rpow,mul_one,
      Real.enorm_eq_ofReal (by unfold assemblySelectedClock; positivity)]
  change eLpNorm (fun ω => f (H ω) ω) (ENNReal.ofReal p) μ ≤ _
  rw [selected_real_family_eq H H0 hge f]
  apply (eLpNorm_add_le (ENNReal.one_le_ofReal.mpr (by linarith only [hp]))).trans
  apply (add_le_add hfinite htail.2).trans_eq
  rw [← ENNReal.ofReal_add (by unfold assemblySelectedClock; positivity) (by
    have ht0 : 0 ≤ selectedWaveExactTail (γ/2) (p/2) H0 0 := by
      unfold selectedWaveExactTail
      exact tsum_nonneg fun n => by
        simp only [Fin.val_zero,pow_zero,one_mul]
        unfold selectedTailProbability
        positivity
    positivity)]
  congr 1
  unfold assemblySelectedClock assemblySelectedClockBudget
  rw [mul_add,← Real.rpow_add (by norm_num : (0:ℝ)<3)]
  congr 2
  push_cast
  ring

/-- The actual selected clock has the complete norm bound at all finite
orders, without any independence assumption between geometry and fields. -/
theorem assembly_q3_selected_clock_Lp (M : ABKModel 2) (h : ℝ)
    (hM : PlanarQ3Gaussian M h) (hγ : M.gamma ≤ gammaZero)
    (Q : TriadicCube 2) (p : ℝ) (hp : 2 ≤ p)
    (hpast : ∀ n : ℤ, n ≤ Q.scale-342-12*orderBand p → nativeInductionState M h n) :
    eLpNorm (fun ω => (3:ℝ)^(2*M.gamma*((resetQ3StoppedHeight M Q (orderBand p) ω:ℝ)-38)))
      (ENNReal.ofReal p) (Cutoff.cutoffSampleLaw M).toMeasure ≤
        ENNReal.ofReal (assemblySelectedClockBudget M.gamma p (heightEntrance (orderBand p))) := by
  have he (ω : Cutoff.CutoffSample 2) :
      resetQ3StoppedHeight M Q (orderBand p) ω = q3SelectedHeight M Q (orderBand p) ω+5 := by
    have hh := (reset_q3_planar_geometry M h hM hγ Q p hp hpast).2.1 ω
    change heightEntrance (orderBand p)+5 ≤ resetQ3StoppedHeight M Q (orderBand p) ω at hh
    unfold q3SelectedHeight
    omega
  simp_rw [he,Nat.cast_add,Nat.cast_ofNat]
  exact assembly_selected_clock_Lp_of_atoms (Cutoff.cutoffSampleLaw M).toMeasure _
    (selected_height_measurable M Q _) _ (by unfold heightEntrance; omega)
    (q3_selected_height_ge M Q _) M.gamma M.shellPrefix.gamma_pos.le p hp (fun n => by
      rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
      exact ENNReal.ofReal_le_ofReal (selected_height_atom M h hM hγ Q p hp hpast n))

end
end ASDExplicitGamma.Inverse
