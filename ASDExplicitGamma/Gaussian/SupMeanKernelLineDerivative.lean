module

public import ASDExplicitGamma.Gaussian.SupMeanKernelSuccessor

/-! Genuine scalar weak derivatives of tensor kernel sections along every spatial line. -/
@[expose] public section
namespace ASDExplicitGamma.Gaussian
open Homogenization ASDExplicitGamma.Model
open scoped RealInnerProductSpace
noncomputable section

/-- The actual Hilbert kernel line has the two successor kernels as its weak
derivative; a third derivative of the frozen random shell is never assumed. -/
theorem supMean_kernel_line_hasDerivAt (β : ℝ) (L : {l : ℝ // 0 < l})
    (o : Q3SpatialJet) (u : WhiteNoise) (x v : Vec 2) (t : ℝ) :
    HasDerivAt (fun s : ℝ => ⟪u,Real.sqrt 2 • q3Section β L
      (supMeanKernelJetIndex o) (x+s • v)⟫)
      ⟪u,v 0 • (Real.sqrt 2 • q3Section β L (supMeanKernelJetSuccessor o 0) (x+t • v))+
        v 1 • (Real.sqrt 2 • q3Section β L (supMeanKernelJetSuccessor o 1) (x+t • v))⟫ t := by
  have ha : (supMeanKernelJetIndex o).val.1.val+(supMeanKernelJetIndex o).val.2.val ≤ 2 := by
    cases o with
    | value => norm_num [supMeanKernelJetIndex, Q3SpatialJet.count]
    | first i => fin_cases i <;> norm_num [supMeanKernelJetIndex, Q3SpatialJet.count]
    | second i j => fin_cases i <;> fin_cases j <;> norm_num [supMeanKernelJetIndex, Q3SpatialJet.count]
  have hl : HasDerivAt (fun s : ℝ => x+s • v) v t := by
    simpa only [id_eq, one_smul] using ((hasDerivAt_id t).smul_const v).const_add x
  have hd := ((q3Convolution_hasFDerivAt β L (supMeanKernelJetIndex o) ha u
    (x+t • v)).comp_hasDerivAt t hl).const_mul (Real.sqrt 2)
  simp only [Function.comp_def, add_apply, smul_apply, ContinuousLinearMap.proj_apply] at hd
  have hf : (fun s : ℝ => ⟪u,Real.sqrt 2 • q3Section β L (supMeanKernelJetIndex o) (x+s • v)⟫) =
      (fun s => Real.sqrt 2*q3Convolution β L (supMeanKernelJetIndex o) u (x+s • v)) := by
    funext s
    exact real_inner_smul_right _ _ _
  have he : ⟪u,v 0 • (Real.sqrt 2 • q3Section β L (supMeanKernelJetSuccessor o 0) (x+t • v))+
      v 1 • (Real.sqrt 2 • q3Section β L (supMeanKernelJetSuccessor o 1) (x+t • v))⟫ =
      Real.sqrt 2*(q3Convolution β L (h3Next (supMeanKernelJetIndex o) 0 ha) u (x+t • v)*v 0+
        q3Convolution β L (h3Next (supMeanKernelJetIndex o) 1 ha) u (x+t • v)*v 1) := by
    simp only [inner_add_right, real_inner_smul_right, supMeanKernelJetSuccessor, q3Convolution]
    ring
  rw [hf,he]
  exact hd

end
end ASDExplicitGamma.Gaussian
