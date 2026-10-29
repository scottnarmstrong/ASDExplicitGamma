module

public import ASDExplicitGamma.Native.HeatRefinedOverlapProfile

/-! Complete positive-shell sum for the refined depth-ten child grid. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open ASDExplicitGamma.Variational ASDExplicitGamma.Numerics.Native
open scoped BigOperators
noncomputable section

/-- Beyond the eight-shell prefix the mesh and radius agree, and the
squared coefficient is a sum of three positive geometric sequences. -/
theorem heat_refined_profile_tail_formula (n : ℕ) :
    heatRefinedProfileMajorant (n+8) =
      heatRefinedTailA^2*(1/3)^20*(1/9)^n +
      (2*heatRefinedTailA*heatRefinedTailC)*(1/3)^30*(1/27)^n +
      heatRefinedTailC^2*(1/3)^40*(1/81)^n := by
  have hmax : max (n+8+2) 5=n+8+2 := max_eq_left (by omega)
  have hsub : 8-(n+8)=0 := by omega
  have hp : (1/3:ℚ)^(n+8+2)=(1/3)^10*(1/3)^n := by
    rw [show n+8+2=10+n by omega,pow_add]
  have h2 : ((1/3:ℚ)^n)^2=(1/9)^n := by
    rw [←pow_mul,mul_comm n 2,pow_mul]; norm_num
  have h3 : ((1/3:ℚ)^n)^3=(1/27)^n := by
    rw [←pow_mul,mul_comm n 3,pow_mul]; norm_num
  have h4 : ((1/3:ℚ)^n)^4=(1/81)^n := by
    rw [←pow_mul,mul_comm n 4,pow_mul]; norm_num
  unfold heatRefinedProfileMajorant heatRefinedOverlap heatRefinedBnMajorant
    heatRefinedRho heatRefinedDelta heatRefinedTailA heatRefinedTailC
  rw [hmax,hsub,hp,←h2,←h3,←h4]
  norm_num only [pow_zero,mul_one,min_eq_left (by norm_num : (1:ℚ) ≤ 25/9),one_mul]
  ring

/-- The infinite tail has the exact rational sum used in the finite certificate. -/
theorem heat_refined_profile_tail_hasSum :
    HasSum (fun n : ℕ => (heatRefinedProfileMajorant (n+8):ℝ)) (heatRefinedTailSum:ℝ) := by
  have h9 := (hasSum_geometric_of_norm_lt_one (by norm_num : ‖(1/9:ℝ)‖<1)).mul_left
    ((heatRefinedTailA:ℝ)^2*(1/3)^20)
  have h27 := (hasSum_geometric_of_norm_lt_one (by norm_num : ‖(1/27:ℝ)‖<1)).mul_left
    ((2*(heatRefinedTailA:ℝ)*heatRefinedTailC)*(1/3)^30)
  have h81 := (hasSum_geometric_of_norm_lt_one (by norm_num : ‖(1/81:ℝ)‖<1)).mul_left
    ((heatRefinedTailC:ℝ)^2*(1/3)^40)
  convert (h9.add h27).add h81 using 1
  · funext n
    rw [heat_refined_profile_tail_formula]
    push_cast
    rfl
  · unfold heatRefinedTailSum
    push_cast
    ring

/-- The rational positive profile is summable. -/
theorem heat_refined_profile_summable :
    Summable (fun n : ℕ => (heatRefinedProfileMajorant n:ℝ)) :=
  (summable_nat_add_iff 8).mp heat_refined_profile_tail_hasSum.summable

/-- The complete refined profile, including its infinite tail, fits the
literal configured S_B. -/
theorem heat_refined_profile_tsum_le :
    (∑' n : ℕ,(heatRefinedProfileMajorant n:ℝ)) ≤ (nativeHeatSB:ℝ) := by
  rw [←heat_refined_profile_summable.sum_add_tsum_nat_add 8,
    heat_refined_profile_tail_hasSum.tsum_eq]
  exact_mod_cast heat_refined_overlap_rational_budget

/-- The actual positive Lemma V profile is summable and fits the same
complete rational certificate. -/
theorem heat_refined_Bn_profile_control :
    Summable (fun n : ℕ => (heatRefinedOverlap n:ℝ)*
      (lemmaVH2Bn (heatRefinedRho n:ℝ) (heatRefinedDelta n:ℝ))^2) ∧
    (∑' n : ℕ,(heatRefinedOverlap n:ℝ)*
      (lemmaVH2Bn (heatRefinedRho n:ℝ) (heatRefinedDelta n:ℝ))^2) ≤ (nativeHeatSB:ℝ) := by
  have hw (n : ℕ) : (0:ℝ) ≤ heatRefinedOverlap n := by unfold heatRefinedOverlap; positivity
  have hb (n : ℕ) : 0 ≤ lemmaVH2Bn (heatRefinedRho n:ℝ) (heatRefinedDelta n:ℝ) := by
    unfold lemmaVH2Bn heatRefinedRho heatRefinedDelta lemmaVH2C1 lemmaVH2C2
    positivity
  have hdom (n : ℕ) : (heatRefinedOverlap n:ℝ)*
      (lemmaVH2Bn (heatRefinedRho n:ℝ) (heatRefinedDelta n:ℝ))^2 ≤
        (heatRefinedProfileMajorant n:ℝ) := by
    unfold heatRefinedProfileMajorant
    push_cast
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (hb n) (heat_refined_Bn_le_majorant n) 2) (hw n)
  have hs := Summable.of_nonneg_of_le (fun n => mul_nonneg (hw n) (sq_nonneg _)) hdom
    heat_refined_profile_summable
  exact ⟨hs,(hs.tsum_le_tsum hdom heat_refined_profile_summable).trans heat_refined_profile_tsum_le⟩

/-- Complete actual square-root profile bound. -/
theorem heat_refined_Bn_profile_tsum_le :
    (∑' n : ℕ,(heatRefinedOverlap n:ℝ)*
      (lemmaVH2Bn (heatRefinedRho n:ℝ) (heatRefinedDelta n:ℝ))^2) ≤ (nativeHeatSB:ℝ) :=
  heat_refined_Bn_profile_control.2

end
end ASDExplicitGamma.Native
