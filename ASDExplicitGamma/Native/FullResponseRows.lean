module

public import ASDExplicitGamma.Native.FullResponseRowsClocks
public import ASDExplicitGamma.Inverse.FullResponseExports

/-! NA-FULL-RESPONSE-ROWS: the full64 response and complete future-history
profiles at a completed output, using only strictly earlier native states. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Inverse ASDExplicitGamma.Numerics.Inverse ASDExplicitGamma.Gaussian
open ASDExplicitGamma.Variational
open scoped ENNReal
noncomputable section

/-- The full64 physical response in any true frame, from the completed past.
The largest source roots have scale at most n+40; all reset inputs remain
strictly below n even when the terminal cutoff is far in the future. -/
theorem native_full_response_rows64
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (n : ℤ)
    (hpast : ∀ k < n, nativeInductionState M h k)
    (Q : TriadicCube 2) (hQ : Q.scale ≤ n+40) (N K : ℤ) (hN : Q.scale-1 ≤ N) :
    let D := (N:ℝ)-(Q.scale:ℝ)+1
    eLpNorm (fun ω => Matrix.trace (toFullBlockMat (frameMatrix (Annealed.sigmaBar M K:ℝ)
      (coarseBlockMatrix (cubeSet Q) (Cutoff.coefficientCutoff M.nu N ω))))/4)
      (ENNReal.ofReal 64) (Cutoff.cutoffSampleLaw M).toMeasure ≤ ENNReal.ofReal
        ((1009309/500000+M.gamma*(16684*D+5899542))*
          (3:ℝ)^(2*M.gamma*D+2*M.gamma*|((K-Q.scale+1:ℤ):ℝ)|)) := by
  have hh := full_response_bank64_outward M h hM hg Q
    (fun k hk => hpast k (by omega)) N K hN (fun _ => 1) (by intros; norm_num)
  have he : (fun ω => rootTraceObservable M Q (Q.scale-342) N K (fun _ => 1) ω/4) =
      (fun ω => Matrix.trace (toFullBlockMat (frameMatrix (Annealed.sigmaBar M K:ℝ)
        (coarseBlockMatrix (cubeSet Q) (Cutoff.coefficientCutoff M.nu N ω))))/4) := by
    funext ω
    unfold rootTraceObservable
    rw [full_response_coefficient_unit M _ N (by omega)]
  rw [he] at hh
  simpa only [show (2018618:ℝ)/1000000=1009309/500000 by norm_num] using hh

/-- The full64 future-depth envelope with the exact dimension-two p64
population root and both depth-dependent physical clocks. -/
def nativeFullResponse64FutureTerm (γ D f : ℝ) (j : ℕ) : ℝ :=
  (1-(3:ℝ)^(-(1/4:ℝ)))*((3:ℝ)^(-(7/32:ℝ)+4*γ))^j*
    (1009309/500000+γ*(16684*(D+(j:ℝ))+5899542))*(3:ℝ)^(2*γ*D+2*γ*f)

/-- Explicit convergence of the entire future profile, before taking its
real tsum. This rules out the default-zero convention for divergent series. -/
theorem native_full_response_rows64_future_summable (γ D f : ℝ) (J : ℕ)
    (hγ : 0 ≤ γ) (hg : γ ≤ 17/50000) :
    Summable (fun j : ℕ => nativeFullResponse64FutureTerm γ D f (J+j)) := by
  have hs := (native_full_response_physical_history_tail_summable γ
    (1009309/500000+γ*(16684*D+5899542)) (γ*16684) J hγ hg).mul_right
      ((3:ℝ)^(2*γ*D+2*γ*f))
  apply hs.congr
  intro j
  dsimp only [nativeFullResponse64FutureTerm]
  ring

/-- Every complete full64 future tail is retained. S0 pays the constant
part and S1 pays the first future-depth moment; J=0 is the entire history. -/
theorem native_full_response_rows64_future_tail (γ D f : ℝ) (J : ℕ)
    (hγ : 0 ≤ γ) (hg : γ ≤ 17/50000) (hD : 0 ≤ D) :
    (∑' j : ℕ, nativeFullResponse64FutureTerm γ D f (J+j)) ≤
      nativeFullResponseHistoryRatio^J*
        ((1009309/500000+γ*(16684*(D+(J:ℝ))+5899542))*(invS0:ℝ)+
          γ*16684*(invS1:ℝ))*(3:ℝ)^(2*γ*D+2*γ*f) := by
  let A : ℝ := 1009309/500000+γ*(16684*D+5899542)
  let B : ℝ := γ*16684
  have ht := native_full_response_physical_history_tail_le γ A B J hγ hg
    (by dsimp only [A]; positivity) (by dsimp only [B]; positivity)
  calc
    _ = (∑' j : ℕ, (1-(3:ℝ)^(-(1/4:ℝ)))*
        ((3:ℝ)^(-(7/32:ℝ)+4*γ))^(J+j)*(A+B*((J+j:ℕ):ℝ)))*
          (3:ℝ)^(2*γ*D+2*γ*f) := by
      rw [← tsum_mul_right]
      congr 1
      funext j
      dsimp only [nativeFullResponse64FutureTerm,A,B]
      ring
    _ ≤ (nativeFullResponseHistoryRatio^J*((A+B*(J:ℝ))*(invS0:ℝ)+B*(invS1:ℝ)))*
        (3:ℝ)^(2*γ*D+2*γ*f) :=
      mul_le_mul_of_nonneg_right ht (Real.rpow_nonneg (by norm_num) _)
    _ = _ := by dsimp only [A,B]; ring

/-- The separate full64 outward tuple, including the complete-history
factors. No full128 slope is substituted into this interface. -/
theorem native_full_response_rows64_coefficients :
    (invFull64Bt:ℝ) < 1009309/500000 ∧ (invFull64KD:ℝ) < 16684 ∧
      (invFull64K0:ℝ) < 5899542 ∧ (invS0:ℝ) < 1130469/1000000 ∧
        (invS1:ℝ) < 838143/200000 := by
  have hc := bank_full_response_64_caps
  have hs := full_response_history_factor_caps
  norm_num at hc hs ⊢
  exact ⟨hc.1,hc.2.1,hc.2.2,hs.2.2.1,hs.2.2.2⟩

end
end ASDExplicitGamma.Native
