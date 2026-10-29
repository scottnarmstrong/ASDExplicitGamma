module

public import ASDExplicitGamma.Scalar.QuarterHaarDuality
public import ASDExplicitGamma.Triadic.VectorHaar

/-! Constant-one joint vector weak/positive pairing at OLD's actual
quarter-order Haar weight sqrt3, including the root coefficient. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ASDExplicitGamma.Triadic
noncomputable section

/-- The actual vector pairing at the OLD weight, with convergence proved
from L2 rather than supplied as a limit estimate. -/
theorem old_signed_vector_haar_pairing_bound (Q : TriadicCube 2) (r f : Vec 2 → Vec 2)
    (hr : ∀ i,MemLp (fun x => r x i) 2 (normalizedCubeMeasure Q))
    (hf : ∀ i,MemLp (fun x => f x i) 2 (normalizedCubeMeasure Q))
    (hs : ∀ i,Summable (fun j => (Real.sqrt 3)^(j+1)*energy Q
      (cubeIncrement Q (j+1) (fun x => f x i)))) :
    |∑ i,pairing Q (fun x => r x i) (fun x => f x i)|≤
      vectorWeakHaarNorm Q r*vectorPositiveHaarNorm Q f := by
  have hq : 1<Real.sqrt 3 := by
    nlinarith only [Real.sq_sqrt (by norm_num : (0:ℝ)≤3),Real.sqrt_nonneg (3:ℝ)]
  have hqinv : 0≤(Real.sqrt 3)⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg _)
  calc
    _ ≤ ∑ i,|pairing Q (fun x => r x i) (fun x => f x i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i,Real.sqrt (dualEnergy Q (Real.sqrt 3) (fun x => r x i))*
        Real.sqrt (primalEnergy Q (Real.sqrt 3) (fun x => f x i)) := by
      apply Finset.sum_le_sum
      intro i _
      exact weak_positive_duality_of_weight Q hq (hr i) (hf i) (hs i)
        (Scalar.haar_pairing_projection_limit Q (hr i) (hf i))
    _ ≤ _ := Real.sum_sqrt_mul_sqrt_le Finset.univ
      (fun i => primalEnergy_nonneg Q _ hqinv _)
      (fun i => primalEnergy_nonneg Q _ (Real.sqrt_nonneg _) _)

end
end ASDExplicitGamma.Native
