module

public import ASDExplicitGamma.Native.OldSignedRowProductBounds

/-! Actual L2 and positive-Haar membership of row contractions, supplied
by genuine C1 coefficient and Hilbert H1 field data. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ASDExplicitGamma.Triadic
noncomputable section

/-- No unproved norm-membership premise is needed for a smooth row acting
on a genuine Hilbert H1 function. -/
theorem old_signed_row_h1_product_membership {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (Q : TriadicCube 2) (b : Vec 2 → E) (hb : ContDiff ℝ 1 b)
    (u : HilbertH1Function (openCubeSet Q) E) :
    MemLp (fun x => inner ℝ (b x) (u.toFun x)) 2 (normalizedCubeMeasure Q) ∧
    Summable (fun k => (Real.sqrt 3)^(k+1)*energy Q
      (cubeIncrement Q (k+1) (fun x => inner ℝ (b x) (u.toFun x)))) := by
  let B := oldSignedRowMultiplier Q b hb
  have hq : 1<Real.sqrt 3 := by
    nlinarith only [Real.sq_sqrt (by norm_num : (0:ℝ)≤3),Real.sqrt_nonneg (3:ℝ)]
  have hq9 : Real.sqrt 3<9 := by
    nlinarith only [Real.sq_sqrt (by norm_num : (0:ℝ)≤3),Real.sqrt_nonneg (3:ℝ)]
  have hp := (old_signed_hilbert_h1_positive_bound Q u).1
  have ht := hilbert_positive_product_of_bounds B hq hq9 (u.memL2_normalized Q) hp
    lpNorm_nonneg lpNorm_nonneg B.ae_value_le B.ae_gradient_sq_le
  refine ⟨B.product_memLp (u.memL2_normalized Q),?_⟩
  simpa only [B,oldSignedRowMultiplier,innerSL_apply_apply,
    hilbertCubeIncrement_real,hilbertEnergy_real] using ht.1

end
end ASDExplicitGamma.Native
