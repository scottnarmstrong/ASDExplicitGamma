module

public import ASDExplicitGamma.Cold.ColdGraphScaling

/-! # Exact real-valued source graph candidates -/

@[expose] public section
noncomputable section
namespace ASDExplicitGamma.Cold

/-- The old source graph cap, including the global spectral branch. -/
def coldOldGraphCap (a L : ℝ) (ell : ℕ) : ℝ :=
  min (2*(2*a+2*(Real.sqrt (2*a+L^2)+L)*(3:ℝ)^(-(ell:ℝ)))^2) (4*(a+L^2))

/-- The exact five-sixths source candidate at separation d. -/
def coldFiveSixthsGraphCap (D L : ℝ) (d : ℕ) : ℝ :=
  let c := 2*(3:ℝ)^(-(d:ℝ))
  2*(c*Real.sqrt (2*D+L^2)+Real.sqrt ((5/6:ℝ)*D^2+c^2*L^2))^2

/-- The exact half-floor sandwich candidate at separation d. -/
def coldSandwichGraphCap (D L : ℝ) (d : ℕ) : ℝ :=
  let e := 2*(3:ℝ)^(-(d:ℝ))*Real.sqrt (2*D+L^2)
  2*(e+Real.sqrt (D^2/2+2*e^2))^2

/-- Exact old graph caps scale by at most theta. -/
theorem coldOldGraphCap_scale {θ a L : ℝ} (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (ha : 0 ≤ a) (hL : 0 ≤ L) (ell : ℕ) :
    coldOldGraphCap (θ*a) (θ*L) ell ≤ θ*coldOldGraphCap a L ell := by
  exact cold_old_graph_scale hθ hθ1 ha hL (Real.rpow_nonneg (by norm_num) _)

/-- Exact five-sixths graph caps scale by at most theta. -/
theorem coldFiveSixthsGraphCap_scale {θ D L : ℝ} (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) (d : ℕ) :
    coldFiveSixthsGraphCap (θ*D) (θ*L) d ≤ θ*coldFiveSixthsGraphCap D L d := by
  exact cold_five_sixths_scale hθ hθ1 (by positivity)

/-- Exact sandwich graph caps scale by at most theta. -/
theorem coldSandwichGraphCap_scale {θ D L : ℝ} (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hD : 0 ≤ D) (d : ℕ) :
    coldSandwichGraphCap (θ*D) (θ*L) d ≤ θ*coldSandwichGraphCap D L d := by
  exact cold_sandwich_scale hθ hθ1 hD (by positivity)

end ASDExplicitGamma.Cold
