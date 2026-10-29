module

public import ASDExplicitGamma.Native.ParentWeakLeadingMean

/-! The sharp half-trace budget with the theta-scaled original rare payment. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Variational Gaussian Inverse Main Triadic Cold Algsuperdiff.Section3
noncomputable section

/-- Exact directional leading mean and a correlated depth reserve paid
against the actual physical history, rather than a full-response norm. -/
def parentWeakDirectionalBudget (M : ABKModel 2) (n : ℤ) (height : ℕ)
    (U : TriadicCube 2) (t : ℝ) (j : ℕ) : ℝ :=
  (inverseBankCap .localInverse:ℝ)*bankDepthFrame M j/2*
    (∫ ω,parentBoundaryBandCellTrace M n height t U j ω ∂(Cutoff.cutoffSampleLaw M).toMeasure)+
      inverseBankDepthReserve .localInverse M j*parentWeakRareTraceCap M j

/-- Complete directional budget, with its exact half and one theta on the
entire reserve. The infinite mean series is proved summable first. -/
theorem parent_weak_directional_budget_return
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (hg : M.gamma ≤ gammaZero)
    (n : ℤ) (height : ℕ) (hheight : 1 ≤ height)
    (hpast : ∀ k<n,nativeInductionState M h k) (hstate : nativeInductionState M h n)
    (depth : ℕ) (hdepth : depth=5) (U : TriadicCube 2)
    (hU : U∈descendantsAtDepth (originCube 2 n) depth) (t : ℝ) (ht : 0 ≤ t ∧ t ≤ 1) :
    Summable (fun j : ℕ => inverseHistoryDiscount^(2*j)*parentWeakDirectionalBudget M n height U t j) ∧
    (1-inverseHistoryDiscount^2)*(∑' j : ℕ,inverseHistoryDiscount^(2*j)*
      parentWeakDirectionalBudget M n height U t j) ≤
        (theta M/2)*((23/100:ℝ)+t*parentBoundaryWeakMeanSlope gammaZero height+1/10^12) := by
  let f := fun j : ℕ => (3683/2500:ℝ)*inverseHistoryDiscount^(2*j)*bankDepthFrame M j*
    (∫ ω,parentBoundaryBandCellTrace M n height t U j ω ∂(Cutoff.cutoffSampleLaw M).toMeasure)
  let r := fun j : ℕ => inverseHistoryDiscount^(2*j)*inverseBankDepthReserve .localInverse M j*
    parentWeakRareTraceCap M j
  have hf := parent_weak_leading_mean_return M h hM hg n height hheight hpast hstate depth hdepth U hU t ht
  have hr := parent_weak_rare_series_payment M hg
  have he : (fun j : ℕ => inverseHistoryDiscount^(2*j)*parentWeakDirectionalBudget M n height U t j)=
      (fun j => (1/2:ℝ)*f j+r j) := by
    funext j
    dsimp only [f,r,parentWeakDirectionalBudget]
    norm_num only [inverseBankCap,Rat.cast_div,Rat.cast_ofNat]
    ring
  rw [he]
  have hs := (hf.1.mul_left (1/2:ℝ)).add hr.1
  refine ⟨hs,?_⟩
  rw [(hf.1.mul_left (1/2:ℝ)).tsum_add hr.1,tsum_mul_left]
  calc
    _ = (1/2:ℝ)*((1-inverseHistoryDiscount^2)*(∑' j : ℕ,f j))+
      (1-inverseHistoryDiscount^2)*(∑' j : ℕ,r j) := by ring
    _ ≤ (1/2:ℝ)*(theta M*((23/100:ℝ)+t*parentBoundaryWeakMeanSlope gammaZero height))+
      theta M*(1/(2*10^12):ℝ) :=
      add_le_add (mul_le_mul_of_nonneg_left hf.2 (by norm_num)) hr.2
    _ = _ := by ring

end
end ASDExplicitGamma.Native
