module

public import ASDExplicitGamma.Native.OldSignedFiniteMinkowski
public import Homogenization.Besov.Basic

/-! Exact Euclidean aggregation under the actual finite descendant weights. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization
noncomputable section

/-- Finite descendant averaging preserves the joint two-energy Minkowski
bill, without replacing averages by maxima. -/
theorem old_signed_descendant_sqrt_energy_bound (Q : TriadicCube 2) (j : ℕ)
    (E G c : TriadicCube 2 → ℝ) {A B : ℝ} (hA : 0≤A) (hB : 0≤B)
    (hE : ∀ U ∈ descendantsAtDepth Q j,0≤E U)
    (hG : ∀ U ∈ descendantsAtDepth Q j,0≤G U)
    (hc : ∀ U ∈ descendantsAtDepth Q j,0≤c U)
    (h : ∀ U ∈ descendantsAtDepth Q j,c U≤A*Real.sqrt (E U)+B*Real.sqrt (G U)) :
    Real.sqrt (descendantsAverage Q j (fun U => c U^2))≤
      A*Real.sqrt (descendantsAverage Q j E)+B*Real.sqrt (descendantsAverage Q j G) := by
  classical
  let S := descendantsAtDepth Q j
  have hh := old_signed_finite_weighted_sqrt_energy_bound
    (fun _ : {U // U ∈ S} => ((S.card : ℝ)⁻¹))
    (fun U => E U.1) (fun U => G U.1) (fun U => c U.1)
    (fun _ => inv_nonneg.mpr (Nat.cast_nonneg _)) hA hB
    (fun U => hE U.1 U.2) (fun U => hG U.1 U.2) (fun U => hc U.1 U.2)
    (fun U => h U.1 U.2)
  simp only [←Finset.mul_sum] at hh
  have hsum (f : TriadicCube 2 → ℝ) :
      (∑ U : {U // U ∈ S},f U.1)=∑ U ∈ S,f U := S.sum_coe_sort f
  rw [hsum (fun U => c U^2),hsum E,hsum G] at hh
  exact hh

end
end ASDExplicitGamma.Native
