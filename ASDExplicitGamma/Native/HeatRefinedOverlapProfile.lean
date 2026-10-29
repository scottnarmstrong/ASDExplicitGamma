module

public import ASDExplicitGamma.Variational.LemmaVH2Constants
public import ASDExplicitGamma.Numerics.Native.Heat
public import Mathlib.Analysis.SpecificLimits.Normed

/-! Rational majorants for the actual refined depth-ten overlap profile.
Index `n` here denotes source shell `n+1`: the relative offset is `n+2`
and the refined mesh depth is `max (3-n) 0`. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open ASDExplicitGamma.Variational ASDExplicitGamma.Numerics.Native
open scoped BigOperators
noncomputable section

def heatRefinedRootOne : ℚ := 279284800875379/100000000000000
def heatRefinedRootTwo : ℚ := 394968353162630/100000000000000
def heatRefinedRootThree : ℚ := 3049196615503829/100000000000000

def heatRefinedRho (n : ℕ) : ℚ := (1/3)^(n+2)
def heatRefinedDelta (n : ℕ) : ℚ := (1/3)^(max (n+2) 5)
def heatRefinedOverlap (n : ℕ) : ℚ := min 1 ((25/9)*(1/9)^(8-n))
def heatRefinedBnMajorant (n : ℕ) : ℚ :=
  heatRefinedRootOne*heatRefinedRho n +
    (36/25)*heatRefinedRootTwo*heatRefinedDelta n +
    (57/200)*heatRefinedRootThree*(heatRefinedDelta n)^2

def heatRefinedProfileMajorant (n : ℕ) : ℚ :=
  heatRefinedOverlap n*(heatRefinedBnMajorant n)^2

def heatRefinedTailA : ℚ := heatRefinedRootOne+(36/25)*heatRefinedRootTwo
def heatRefinedTailC : ℚ := (57/200)*heatRefinedRootThree

def heatRefinedTailSum : ℚ :=
  heatRefinedTailA^2*(1/3)^20/(1-1/9) +
    (2*heatRefinedTailA*heatRefinedTailC)*(1/3)^30/(1-1/27) +
    heatRefinedTailC^2*(1/3)^40/(1-1/81)

/-- All three square-root enclosures are kernel-checked rational inequalities. -/
theorem heat_refined_overlap_root_bounds :
    Real.sqrt (lemmaVH2R1/2) ≤ (heatRefinedRootOne:ℝ) ∧
    Real.sqrt lemmaVH2R1 ≤ (heatRefinedRootTwo:ℝ) ∧
    Real.sqrt lemmaVH2A2 ≤ (heatRefinedRootThree:ℝ) := by
  constructor
  · apply Real.sqrt_le_iff.mpr
    norm_num [lemmaVH2R1,heatRefinedRootOne]
  constructor
  · apply Real.sqrt_le_iff.mpr
    norm_num [lemmaVH2R1,heatRefinedRootTwo]
  · apply Real.sqrt_le_iff.mpr
    norm_num [lemmaVH2A2,lemmaVH2R1,heatRefinedRootThree]

/-- The refined mesh keeps rho and delta separate in the Lemma V coefficient. -/
theorem heat_refined_Bn_le_majorant (n : ℕ) :
    lemmaVH2Bn (heatRefinedRho n:ℝ) (heatRefinedDelta n:ℝ) ≤
      (heatRefinedBnMajorant n:ℝ) := by
  obtain ⟨h1,h2,h3⟩ := heat_refined_overlap_root_bounds
  have hρ : (0:ℝ) ≤ heatRefinedRho n := by unfold heatRefinedRho; positivity
  have hδ : (0:ℝ) ≤ heatRefinedDelta n := by unfold heatRefinedDelta; positivity
  unfold lemmaVH2Bn heatRefinedBnMajorant
  push_cast
  apply add_le_add
  · exact add_le_add (mul_le_mul_of_nonneg_right h1 hρ)
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 (by norm_num [lemmaVH2C1])) hδ)
  · exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left h3 (by norm_num [lemmaVH2C2])) (sq_nonneg _)

/-- Eight finite shells plus the exact positive geometric tail fit the
configured refined-child shell coefficient, with no decimal rounding trusted. -/
theorem heat_refined_overlap_rational_budget :
    (∑ n ∈ Finset.range 8,heatRefinedProfileMajorant n)+heatRefinedTailSum ≤ nativeHeatSB := by
  norm_num [heatRefinedProfileMajorant,heatRefinedOverlap,heatRefinedBnMajorant,
    heatRefinedRho,heatRefinedDelta,heatRefinedTailSum,heatRefinedTailA,heatRefinedTailC,
    heatRefinedRootOne,heatRefinedRootTwo,heatRefinedRootThree,nativeHeatSB,Finset.sum_range_succ]

end
end ASDExplicitGamma.Native
