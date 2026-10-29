module

public import ASDExplicitGamma.Inverse.FullResponseParameterEndpoint

/-! The two actual selected-height profile rows consume the exact root certificates. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open ASDExplicitGamma.Numerics.Inverse
noncomputable section

/-- Literal Jp/W₀/W₁ endpoint row at order 64. -/
theorem full_response_selected_row64 (γ : ℝ) (hγ : 0 ≤ γ) (hg : γ ≤ gammaZero) :
    selectedJp γ 64 377 ≤ (invFull64J:ℝ) ∧
      physicalSelectedWaveBudget γ 64 377 0 ≤ (invFull64W0:ℝ) ∧
        physicalSelectedWaveBudget γ 64 377 1 ≤ (invFull64W1:ℝ) := by
  have hroot : (12:ℝ)^(1/(64:ℝ)) ≤ (invFull64SelectedRoot:ℝ) := by
    have hh := inv_root_upper (x := 12) (u := invFull64SelectedRoot) (n := 64)
      (by norm_num) (by norm_num [invFull64SelectedRoot]) (by decide) invFull64_selected_root
    simpa only [one_div,Nat.cast_ofNat,Rat.cast_ofNat] using hh.le
  have hJ := full_response_selected_Jp_endpoint γ 64 hγ hg (by norm_num) (by norm_num)
  have hW := full_response_selected_wave_endpoint γ 64 (invFull64SelectedRoot:ℝ) hγ hg
    (by norm_num) (by norm_num) hroot
  refine ⟨?_,?_,?_⟩
  · convert hJ using 1
    unfold invFull64J
    push_cast
    ring
  · convert hW.1 using 1
    unfold fullResponseSelectedBase invFull64W0 invFull64W
    push_cast
    ring
  · convert hW.2 using 1
    unfold fullResponseSelectedBase invFull64W1 invFull64W
    push_cast
    ring

/-- Literal Jp/W₀/W₁ endpoint row at order 128. -/
theorem full_response_selected_row128 (γ : ℝ) (hγ : 0 ≤ γ) (hg : γ ≤ gammaZero) :
    selectedJp γ 128 377 ≤ (invFull128J:ℝ) ∧
      physicalSelectedWaveBudget γ 128 377 0 ≤ (invFull128W0:ℝ) ∧
        physicalSelectedWaveBudget γ 128 377 1 ≤ (invFull128W1:ℝ) := by
  have hroot : (12:ℝ)^(1/(128:ℝ)) ≤ (invFull128SelectedRoot:ℝ) := by
    have hh := inv_root_upper (x := 12) (u := invFull128SelectedRoot) (n := 128)
      (by norm_num) (by norm_num [invFull128SelectedRoot]) (by decide) invFull128_selected_root
    simpa only [one_div,Nat.cast_ofNat,Rat.cast_ofNat] using hh.le
  have hJ := full_response_selected_Jp_endpoint γ 128 hγ hg (by norm_num) (by norm_num)
  have hW := full_response_selected_wave_endpoint γ 128 (invFull128SelectedRoot:ℝ) hγ hg
    (by norm_num) (by norm_num) hroot
  refine ⟨?_,?_,?_⟩
  · convert hJ using 1
    unfold invFull128J
    push_cast
    ring
  · convert hW.1 using 1
    unfold fullResponseSelectedBase invFull128W0 invFull128W
    push_cast
    ring
  · convert hW.2 using 1
    unfold fullResponseSelectedBase invFull128W1 invFull128W
    push_cast
    ring

end
end ASDExplicitGamma.Inverse
