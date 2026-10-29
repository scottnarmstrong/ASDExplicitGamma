module

public import ASDExplicitGamma.Inverse.FullResponseLeadingEndpoint
public import ASDExplicitGamma.Inverse.FullResponseErrorEndpoint

/-! The two literal finite-order endpoint rows of the full response bank. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open ASDExplicitGamma.Numerics.Inverse
noncomputable section

/-- The literal order-64 leading-component endpoint row. -/
def fullResponseLeadingRow64 (γ D : ℝ) : Fin 3 → ℝ :=
  fullResponseLeadingEndpoint γ D (invFull64Ed:ℝ) (invFull64c0:ℝ) (invFull64c1:ℝ)
    (invFull64M4root:ℝ) (invFull64J:ℝ) (invFull64W0:ℝ) (invFull64W1:ℝ)

/-- The literal order-64 complete error-component endpoint row. -/
def fullResponseErrorRow64 (γ D : ℝ) : Fin 4 → ℝ :=
  fullResponseErrorEndpoint γ 64 D (invFull64Ed:ℝ) (invFull64c0:ℝ) (invFull64c1:ℝ)
    (invFull64MC:ℝ) (invFull64M0:ℝ) (invFull64Z0:ℝ) (invFull64D4:ℝ)

/-- Actual order-64 leading components consume the certified source row. -/
theorem full_response_leading_row64_le (γ D : ℝ) (hγ : 0 ≤ γ)
    (hg : γ ≤ gammaZero) (hD : 0 ≤ D) (a : Fin 3) :
    fullResponseTraceLeadingBudget γ 64 D a ≤ fullResponseLeadingRow64 γ D a := by
  have hE : rootEdelta .full ≤ (invFull64Ed:ℝ) := by
    simpa only [invFull128Ed,invFull64Ed,invFull128Delta,invFull64Delta] using full_response_Edelta_endpoint
  have hc0 : fullResponseTraceC0 ≤ (invFull64c0:ℝ) := by
    simpa only [invFull128c0,invFull64c0,invFull128Delta,invFull64Delta] using full_response_c0_endpoint
  have hc1 : fullResponseTraceC1=(invFull64c1:ℝ) := by
    simpa only [invFull128c1,invFull64c1] using full_response_c1_endpoint
  have hm4 : Real.sqrt (densityMomentBudget (rootQ .full) 4 1232) ≤ (invFull64M4root:ℝ) := by
    simpa only [invFull128M4root,invFull64M4root] using full_response_m4root_endpoint
  have hrow := full_response_selected_row64 γ hγ hg
  have hcomb : (invFull64W0:ℝ)*(invL1plus:ℝ)+(invFull64W1:ℝ)*(invL0plus:ℝ) ≤
      (invFull64W0:ℝ)*(invL1:ℝ)+(invFull64W1:ℝ)*(invL0:ℝ) := by
    have hh := (Rat.cast_lt (K := ℝ)).mpr invFull64_layer_combination.2
    simpa only [Rat.cast_add,Rat.cast_mul] using hh.le
  exact full_response_leading_endpoint_le γ 64 D (invFull64Ed:ℝ) (invFull64c0:ℝ) (invFull64c1:ℝ)
    (invFull64M4root:ℝ) (invFull64J:ℝ) (invFull64W0:ℝ) (invFull64W1:ℝ)
    hγ hg (by norm_num) hD hE hc0 hc1 hm4 hrow.1 hrow.2.1 hrow.2.2 hcomb a

/-- Actual order-64 errors consume the certified source row. -/
theorem full_response_error_row64_le (γ D : ℝ) (hγ : 0 ≤ γ)
    (hg : γ ≤ gammaZero) (hD : 0 ≤ D) (b : Fin 4) :
    fullResponseTraceErrorBudget γ 64 D b ≤ fullResponseErrorRow64 γ D b := by
  have hE : rootEdelta .full ≤ (invFull64Ed:ℝ) := by
    simpa only [invFull128Ed,invFull64Ed,invFull128Delta,invFull64Delta] using full_response_Edelta_endpoint
  have hc0 : fullResponseTraceC0 ≤ (invFull64c0:ℝ) := by
    simpa only [invFull128c0,invFull64c0,invFull128Delta,invFull64Delta] using full_response_c0_endpoint
  have hc1 : fullResponseTraceC1=(invFull64c1:ℝ) := by
    simpa only [invFull128c1,invFull64c1] using full_response_c1_endpoint
  have hZ : densityEZ γ (planarGradientCharge 40) 339 ≤
      9*(planarGradientCharge 40+1)*(invFull64Z0:ℝ) := by
    simpa only [invFull128Z0,invFull64Z0] using full_response_density_EZ_endpoint γ hg
      (planarGradientCharge 40) (by unfold planarGradientCharge; positivity)
  have hD4 := full_response_D4_endpoint64 γ hg
  exact full_response_error_endpoint_le γ 64 D (invFull64Ed:ℝ) (invFull64c0:ℝ) (invFull64c1:ℝ)
    (invFull64MC:ℝ) (invFull64M0:ℝ) (invFull64Z0:ℝ) (invFull64D4:ℝ)
    hγ hg (by norm_num) hD hE hc0 hc1 (full_response_matrix_budget64 γ D hγ hg hD)
    hZ hD4.1 hD4.2 b

/-- The literal order-128 leading-component endpoint row. -/
def fullResponseLeadingRow128 (γ D : ℝ) : Fin 3 → ℝ :=
  fullResponseLeadingEndpoint γ D (invFull128Ed:ℝ) (invFull128c0:ℝ) (invFull128c1:ℝ)
    (invFull128M4root:ℝ) (invFull128J:ℝ) (invFull128W0:ℝ) (invFull128W1:ℝ)

/-- The literal order-128 complete error-component endpoint row. -/
def fullResponseErrorRow128 (γ D : ℝ) : Fin 4 → ℝ :=
  fullResponseErrorEndpoint γ 128 D (invFull128Ed:ℝ) (invFull128c0:ℝ) (invFull128c1:ℝ)
    (invFull128MC:ℝ) (invFull128M0:ℝ) (invFull128Z0:ℝ) (invFull128D4:ℝ)

/-- Actual order-128 leading components consume the certified source row. -/
theorem full_response_leading_row128_le (γ D : ℝ) (hγ : 0 ≤ γ)
    (hg : γ ≤ gammaZero) (hD : 0 ≤ D) (a : Fin 3) :
    fullResponseTraceLeadingBudget γ 128 D a ≤ fullResponseLeadingRow128 γ D a := by
  have hE : rootEdelta .full ≤ (invFull128Ed:ℝ) := by
    simpa only [] using full_response_Edelta_endpoint
  have hc0 : fullResponseTraceC0 ≤ (invFull128c0:ℝ) := by
    simpa only [] using full_response_c0_endpoint
  have hc1 : fullResponseTraceC1=(invFull128c1:ℝ) := by
    simpa only [] using full_response_c1_endpoint
  have hm4 : Real.sqrt (densityMomentBudget (rootQ .full) 4 1232) ≤ (invFull128M4root:ℝ) := by
    simpa only [] using full_response_m4root_endpoint
  have hrow := full_response_selected_row128 γ hγ hg
  have hcomb : (invFull128W0:ℝ)*(invL1plus:ℝ)+(invFull128W1:ℝ)*(invL0plus:ℝ) ≤
      (invFull128W0:ℝ)*(invL1:ℝ)+(invFull128W1:ℝ)*(invL0:ℝ) := by
    have hh := (Rat.cast_lt (K := ℝ)).mpr invFull128_layer_combination.2
    simpa only [Rat.cast_add,Rat.cast_mul] using hh.le
  exact full_response_leading_endpoint_le γ 128 D (invFull128Ed:ℝ) (invFull128c0:ℝ) (invFull128c1:ℝ)
    (invFull128M4root:ℝ) (invFull128J:ℝ) (invFull128W0:ℝ) (invFull128W1:ℝ)
    hγ hg (by norm_num) hD hE hc0 hc1 hm4 hrow.1 hrow.2.1 hrow.2.2 hcomb a

/-- Actual order-128 errors consume the certified source row. -/
theorem full_response_error_row128_le (γ D : ℝ) (hγ : 0 ≤ γ)
    (hg : γ ≤ gammaZero) (hD : 0 ≤ D) (b : Fin 4) :
    fullResponseTraceErrorBudget γ 128 D b ≤ fullResponseErrorRow128 γ D b := by
  have hE : rootEdelta .full ≤ (invFull128Ed:ℝ) := by
    simpa only [] using full_response_Edelta_endpoint
  have hc0 : fullResponseTraceC0 ≤ (invFull128c0:ℝ) := by
    simpa only [] using full_response_c0_endpoint
  have hc1 : fullResponseTraceC1=(invFull128c1:ℝ) := by
    simpa only [] using full_response_c1_endpoint
  have hZ : densityEZ γ (planarGradientCharge 40) 339 ≤
      9*(planarGradientCharge 40+1)*(invFull128Z0:ℝ) := by
    simpa only [] using full_response_density_EZ_endpoint γ hg
      (planarGradientCharge 40) (by unfold planarGradientCharge; positivity)
  have hD4 := full_response_D4_endpoint128 γ hg
  exact full_response_error_endpoint_le γ 128 D (invFull128Ed:ℝ) (invFull128c0:ℝ) (invFull128c1:ℝ)
    (invFull128MC:ℝ) (invFull128M0:ℝ) (invFull128Z0:ℝ) (invFull128D4:ℝ)
    hγ hg (by norm_num) hD hE hc0 hc1 (full_response_matrix_budget128 γ D hγ hg hD)
    hZ hD4.1 hD4.2 b

end
end ASDExplicitGamma.Inverse
