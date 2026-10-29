module

public import ASDExplicitGamma.Inverse.AssemblyTraceMatrixBudget
public import ASDExplicitGamma.Inverse.FullResponseRetainedResetBounds
public import ASDExplicitGamma.Inverse.FullResponseDecayNumerics

/-! Explicit reset-series caps for the all-height matrix budget. -/

@[expose] public section
namespace ASDExplicitGamma.Inverse
noncomputable section

/-- The reset power and first moment decay uniformly at the entrance, with
the exact source abscissa and a band exponent that leaves room for all order
coefficients. -/
theorem assembly_trace_reset_profile_bounds (γ : ℝ) (hγ : γ ≤ gammaZero)
    (k : ℕ) :
    let C := 344+12*k
    let N := 336+11*k
    densityResetPowerSum (2*γ) 1 C ≤
        (3:ℝ)^(-1:ℝ)*(3:ℝ)^(-(N:ℝ))*(1/(1-34/100))^2 ∧
      densityResetPowerSum (4*γ) 1 C ≤
        (3:ℝ)^(-1:ℝ)*(3:ℝ)^(-(N:ℝ))*(1/(1-34/100))^2 ∧
      densityResetFirstPowerSum (4*γ) 1 C ≤
        (3:ℝ)^(-1:ℝ)*(3:ℝ)^(-(N:ℝ))*
          (((C:ℝ)+2)*(1/(1-34/100))^2+
            3*(34/100)/(1-34/100)^3) := by
  let C := 344+12*k
  let N := 336+11*k
  let β : ℝ := 99/100
  let c : ℝ := 34/100
  have hγ' : γ ≤ 17/50000 := by simpa [gammaZero] using hγ
  have hrate : (0:ℝ) ≤ β := by norm_num [β]
  have hc : 0 ≤ c := by norm_num [c]
  have hc1 : c < 1 := by norm_num [c]
  have hq : (3:ℝ)^(-β) ≤ c := by
    dsimp [β,c]
    exact full_response_three_neg_99_le
  have hN : (N:ℝ) ≤ β*((C+1:ℕ):ℝ) := by
    dsimp [N,β,C]
    push_cast
    nlinarith
  have hβ2 : β ≤ 1-2*γ := by dsimp [β]; nlinarith [hγ']
  have hβ4 : β ≤ 1-4*γ := by dsimp [β]; nlinarith [hγ']
  have h2 := full_response_retained_reset_bounds (2*γ) 1 β c C N
    (by linarith) hβ2 hrate hN hc hc1 hq
  have h4 := full_response_retained_reset_bounds (4*γ) 1 β c C N
    (by linarith) hβ4 hrate hN hc hc1 hq
  refine ⟨?_,?_,?_⟩
  · simpa [C,N,c] using h2.1
  · simpa [C,N,c] using h4.1
  · simpa [C,N,c] using h4.2

end
end ASDExplicitGamma.Inverse
