module

public import ASDExplicitGamma.Native.ParentBoundaryCommonHistoryGeometric

/-! Exact full-depth sums of the source quartic covariance profile. -/

@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Cold Algsuperdiff.Section3
noncomputable section

/-- Closed source sum of the five quartic degrees, with the affine raw
response allowance inside each literal geometric ratio. -/
def parentBoundaryCommonKernelGeometric (A2 A4 gamma growth U V : ℝ) : ℝ :=
  ∑ i : Fin 5,parentBoundaryCommonKernelCoefficients A2 A4 i*
    (U/(1-parentBoundaryCommonHistoryRatio gamma growth i)+
      V*parentBoundaryCommonHistoryRatio gamma growth i/
        (1-parentBoundaryCommonHistoryRatio gamma growth i)^2)

/-- The complete source quartic depth budget is summable and equals the
literal source rational-geometric program. No finite-depth truncation or
unproved geometric estimate is a premise. -/
theorem parent_boundary_common_kernel_geometric_sum
    (A2 A4 gamma growth U V : ℝ) (hg0 : 0 ≤ gamma) (hg : gamma ≤ gammaZero) (hgrowth : growth ≤ 8) :
    Summable (fun j : ℕ => coldHistoryBeta^j*parentBoundaryCommonKernelProfile A2 A4 ((1/3:ℝ)^j)*
      (3:ℝ)^(growth*gamma*(j:ℝ))*(U+V*(j:ℝ))) ∧
      (∑' j : ℕ,coldHistoryBeta^j*parentBoundaryCommonKernelProfile A2 A4 ((1/3:ℝ)^j)*
        (3:ℝ)^(growth*gamma*(j:ℝ))*(U+V*(j:ℝ)))=
          parentBoundaryCommonKernelGeometric A2 A4 gamma growth U V := by
  let c := parentBoundaryCommonKernelCoefficients A2 A4
  let q := parentBoundaryCommonHistoryRatio gamma growth
  let F := fun (i : Fin 5) (j : ℕ) => c i*(q i^j*(U+V*(j:ℝ)))
  have hq (i : Fin 5) : 0 ≤ q i ∧ q i < 1 :=
    parent_boundary_common_history_ratio_range hg0 hg growth hgrowth i
  have hF (i : Fin 5) : Summable (F i) :=
    (parent_boundary_common_affine_geometric (q i) U V (hq i).1 (hq i).2).1.mul_left (c i)
  have hpoint (j : ℕ) : coldHistoryBeta^j*parentBoundaryCommonKernelProfile A2 A4 ((1/3:ℝ)^j)*
      (3:ℝ)^(growth*gamma*(j:ℝ))*(U+V*(j:ℝ))=∑ i : Fin 5,F i j := by
    rw [parent_boundary_common_kernel_profile_polynomial]
    calc
      _ = ∑ i : Fin 5,c i*(coldHistoryBeta^j*((1/3:ℝ)^j)^i.val*(3:ℝ)^(growth*gamma*(j:ℝ)))*(U+V*(j:ℝ)) := by
        rw [Finset.mul_sum,Finset.sum_mul,Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i _
        dsimp only [c]
        ring
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i _
        rw [parent_boundary_common_history_ratio_power]
        dsimp only [F,q]
        ring
  have he : (fun j : ℕ => coldHistoryBeta^j*parentBoundaryCommonKernelProfile A2 A4 ((1/3:ℝ)^j)*
      (3:ℝ)^(growth*gamma*(j:ℝ))*(U+V*(j:ℝ)))=(fun j : ℕ => ∑ i : Fin 5,F i j) := funext hpoint
  rw [he]
  refine ⟨summable_sum (fun i _ => hF i),?_⟩
  rw [Summable.tsum_finsetSum (fun i _ => hF i)]
  apply Finset.sum_congr rfl
  intro i _
  dsimp only [F]
  rw [tsum_mul_left,(parent_boundary_common_affine_geometric (q i) U V (hq i).1 (hq i).2).2]

end
end ASDExplicitGamma.Native
