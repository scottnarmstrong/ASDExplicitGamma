module

public import ASDExplicitGamma.Inverse.BankOnePassGenerator
public import ASDExplicitGamma.Inverse.BankOnePassClock
public import ASDExplicitGamma.Inverse.BankOnePassMeanAdapter
public import ASDExplicitGamma.Inverse.BankOnePassArithmetic

/-! One-pass inverse means conditional only on the named physical signed generator. -/
@[expose] public section

namespace ASDExplicitGamma.Inverse

open Homogenization MeasureTheory Set Algsuperdiff.Section3 ASDExplicitGamma.Gaussian
open scoped Matrix.Norms.Elementwise

noncomputable def bankOnePassShellAllowance (M : ABKModel 2) (h : ℝ) (k : ℤ) (i : ℕ) : ℝ :=
  2*((q3ModelAmplitude M h (k+(i:ℤ)+1))^2/(Annealed.sigmaBar M k:ℝ)^2)*
    pureFluxCovarianceMu (pureFluxCovarianceA 0 i) (pureFluxCovarianceB 0 i)*(159/100:ℝ)^3

theorem bank_one_pass_physical_shell_increment
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (hg : M.gamma ≤ gammaZero)
    (k : ℤ) (hpast : ∀ n < k, nativeInductionState M h n)
    (hgen : BankPureFluxGeneratorInput M h k) (i : ℕ) (hi : i < 40) :
    bankCompletedInverseTraceMean k M (k+(i:ℤ)+1) (Annealed.sigmaBar M k:ℝ) ≤
      bankCompletedInverseTraceMean k M (k+(i:ℤ)) (Annealed.sigmaBar M k:ℝ)+
        bankOnePassShellAllowance M h k i := by
  apply bank_inverse_trace_heat_increment_of_generator k M h hM (k+(i:ℤ)) _
    (Annealed.sigmaBar_characterization M k).1
  intro T v hA hlaw t ht
  have he : k+((i+1:ℕ):ℤ)-1=k+(i:ℤ) := by omega
  have hlaw' : (Cutoff.cutoffSampleLaw M).toMeasure.map
      (fun ω : Cutoff.CutoffSample 2 => shellFieldScalarRestriction
        (closure (cubeSet (originCube 2 k))) (ω.1 (k+((i+1:ℕ):ℤ)))) =
      standardGaussianInfinitePi.map (gaussianSeriesLimitE hA T) := by
    simpa only [Nat.cast_add,Nat.cast_one,add_assoc] using hlaw
  have hh := bank_one_pass_generator_mean_of_source M h hM hg k hpast hgen
    (i+1) (by omega) t ⟨ht.1.le,ht.2.le⟩ T v hA hlaw'
  rw [he] at hh
  simpa only [Nat.add_sub_cancel,Nat.cast_add,Nat.cast_one,bankOnePassShellAllowance,add_assoc] using hh

theorem bank_one_pass_fixed_frame_mean
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (hg : M.gamma ≤ gammaZero)
    (k : ℤ) (hpast : ∀ n < k, nativeInductionState M h n)
    (hstate : nativeInductionState M h k) (hgen : BankPureFluxGeneratorInput M h k) :
    bankCompletedInverseTraceMean k M (k+40) (Annealed.sigmaBar M k:ℝ) ≤
      2+(3/50:ℝ)*theta M+(711/40:ℝ)*M.gamma*(159/100:ℝ)^3*bankOnePassFrame M := by
  have hsteps (j : ℕ) (hj : j ≤ 40) :
      bankCompletedInverseTraceMean k M (k+(j:ℤ)) (Annealed.sigmaBar M k:ℝ) ≤
        bankCompletedInverseTraceMean k M k (Annealed.sigmaBar M k:ℝ)+
          ∑ i ∈ Finset.range j, bankOnePassShellAllowance M h k i := by
    induction j with
    | zero => simp
    | succ j ih =>
        have hh := bank_one_pass_physical_shell_increment M h hM hg k hpast hgen j (by omega)
        have hi := ih (by omega)
        rw [Finset.sum_range_succ]
        have he : k+((j+1:ℕ):ℤ)=k+(j:ℤ)+1 := by omega
        rw [he]
        linarith only [hh,hi]
  let C := 2*((9/2:ℝ)*M.gamma*bankOnePassFrame M)*(159/100:ℝ)^3
  have hC : 0 ≤ C := by
    have hγ := M.shellPrefix.gamma_pos
    have hR := bank_one_pass_frame_pos M hg
    dsimp [C]
    positivity
  have hterm (i : ℕ) (hi : i ∈ Finset.range 40) : bankOnePassShellAllowance M h k i ≤
      C*pureFluxCovarianceMu (pureFluxCovarianceA 0 i) (pureFluxCovarianceB 0 i) := by
    have hv := bank_one_pass_native_shell_clock M h hg k (k+(i:ℤ)+1)
      (by have := Finset.mem_range.mp hi; omega) hstate
    have hmu := (pureFlux_covariance_mu_lower (pureFluxCovarianceA 0 i) (pureFluxCovarianceB 0 i)).1
    calc
      _ ≤ 2*((9/2:ℝ)*M.gamma*bankOnePassFrame M)*
          pureFluxCovarianceMu (pureFluxCovarianceA 0 i) (pureFluxCovarianceB 0 i)*(159/100:ℝ)^3 :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hv (by norm_num)) hmu)
            (by positivity)
      _ = _ := by dsimp [C]; ring
  have hsum : (∑ i ∈ Finset.range 40, bankOnePassShellAllowance M h k i) ≤
      (711/40:ℝ)*M.gamma*(159/100:ℝ)^3*bankOnePassFrame M := by
    calc
      _ ≤ ∑ i ∈ Finset.range 40, C*pureFluxCovarianceMu
          (pureFluxCovarianceA 0 i) (pureFluxCovarianceB 0 i) := Finset.sum_le_sum hterm
      _ = C*(∑ i ∈ Finset.range 40, pureFluxCovarianceMu
          (pureFluxCovarianceA 0 i) (pureFluxCovarianceB 0 i)) := (Finset.mul_sum _ _ _).symm
      _ ≤ C*(79/40) := mul_le_mul_of_nonneg_left (bank_covariance_plain_partial_sum _) hC
      _ = _ := by dsimp [C]; ring
  have hh := hsteps 40 le_rfl
  have hs := bank_completed_inverse_trace_mean_start M h k hstate
  norm_num only [Nat.cast_ofNat] at hh
  linarith only [hh,hs,hsum]


/-- The final true frame appears only after the fixed-frame forty-shell insertion. -/
theorem bank_one_pass_true_frame_mean_of_generator
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (hg : M.gamma ≤ gammaZero)
    (k : ℤ) (hpast : ∀ n < k, nativeInductionState M h n)
    (hstate : nativeInductionState M h k) (hgen : BankPureFluxGeneratorInput M h k) :
    bankCompletedInverseTraceMean k M (k+40) (Annealed.sigmaBar M (k+40):ℝ) < 2+747/5000 := by
  let A := 2+(3/50:ℝ)*theta M+(711/40:ℝ)*M.gamma*(159/100:ℝ)^3*bankOnePassFrame M
  have hA : 0 ≤ A := by
    have hγ := M.shellPrefix.gamma_pos
    have hR := bank_one_pass_frame_pos M hg
    have ht : 0 ≤ theta M := div_nonneg hγ.le (by norm_num [gammaZero])
    dsimp [A]
    positivity
  have hfixed := bank_one_pass_fixed_frame_mean M h hM hg k hpast hstate hgen
  have hratio := bank_one_pass_frame_restoration M hg k
  have hratio0 : 0 ≤ (Annealed.sigmaBar M (k+40):ℝ)/(Annealed.sigmaBar M k:ℝ) :=
    div_nonneg (Annealed.sigmaBar_characterization M (k+40)).1.le
      (Annealed.sigmaBar_characterization M k).1.le
  have hscalar : bankOnePassFrame M*A < 2+747/5000 := by
    have hh := bank_one_pass_scalar_bound M.gamma (by simpa only [gammaZero] using hg)
    change bankOnePassFrame M*A-2 < 747/5000 at hh
    linarith only [hh]
  rw [bank_completed_inverse_trace_mean_rescale k M (k+40) (Annealed.sigmaBar M k:ℝ)
    (Annealed.sigmaBar M (k+40):ℝ) (Annealed.sigmaBar_characterization M k).1.ne']
  exact ((mul_le_mul_of_nonneg_left hfixed hratio0).trans
    (mul_le_mul_of_nonneg_right hratio hA)).trans_lt hscalar

/-- The exact one-pass inverse-only mean on every physical cell at label n-40.
The only additional source input is the named physical pure-flux generator. -/
theorem bank_one_pass_clipped_inverse_mean_of_generator
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (hg : M.gamma ≤ gammaZero)
    (n : ℤ) (hpast : ∀ j < n, nativeInductionState M h j)
    (hgen : BankPureFluxGeneratorInput M h (n-40))
    (U : TriadicCube 2) (hU : U.scale=n-40) (tau : ℝ) (v : Vec 2) :
    fullMatrixQuadratic (toFullBlockVec (0,v))
      (∫ ω, clippedCellMatrix M n U tau ω ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
        (10747/10000:ℝ)*dotProduct v v := by
  have hh := bank_one_pass_true_frame_mean_of_generator M h hM hg (n-40)
    (fun j hj => hpast j (by omega)) (hpast (n-40) (by omega)) hgen
  have hn : n-40+40=n := by omega
  rw [hn] at hh
  apply bank_clipped_inverse_mean_of_trace M n (10747/10000) _ U hU tau v
  linarith only [hh]

/-- Causal H3 inputs for both sharpened inverse rows, derived at strictly earlier
labels. No result of either sharpened bank supplies its own mean premise. -/
theorem bank_inverse_mean_inputs_of_generator
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (hg : M.gamma ≤ gammaZero)
    (m : ℤ) (hpast : ∀ n < m, nativeInductionState M h n)
    (hgen : ∀ n < m, BankPureFluxGeneratorInput M h (n-40)) :
    ClippedInverseMeanInput M m .globalInverse ∧ ClippedInverseMeanInput M m .localInverse := by
  have hh (n : ℤ) (hn : n < m) (U : TriadicCube 2) (hU : U.scale=n-40) (tau : ℝ) (v : Vec 2) :=
    bank_one_pass_clipped_inverse_mean_of_generator M h hM hg n
      (fun j hj => hpast j (hj.trans hn)) (hgen n hn) U hU tau v
  exact ⟨fun n hn U hU v => hh n hn U hU (rootTau .globalInverse) v,
    fun n hn U hU v => hh n hn U hU (rootTau .localInverse) v⟩

end ASDExplicitGamma.Inverse
