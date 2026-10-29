module

public import ASDExplicitGamma.Native.ParentBoundaryBandProfiles

/-! Actual simultaneous-band broken weak budgets on the common physical
tiling, with complete bank-weighted trace convergence proved internally. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Algsuperdiff.Section3 Response Scalar Gaussian Main Triadic Variational Inverse
noncomputable section

/-- Literal complete shifted inverse-weighted trace on the actual band. -/
def parentBoundaryBandWeakProxy (M : ABKModel 2) (n : ℤ) (height depth : ℕ)
    (t : ℝ) (omega : Cutoff.CutoffSample 2) : ℝ :=
  rawWeakTraceProxy (fun j => parentBoundaryBandInverseDepth M n height t omega (depth+j))
    (fun j => parentBoundaryBandTraceDepth M n height t omega (depth+j))

/-- The normalized parent-field proxy is the SAME complete physical
bank/trace proxy on every common descendant, before estimating it. -/
theorem parent_boundary_band_proxy_eq (M : ABKModel 2) (n : ℤ) (height depth : ℕ)
    (t : ℝ) (omega : Cutoff.CutoffSample 2) :
    rawWeakTraceProxy (fun j => lemmaVInverseDepthMax (originCube 2 n)
      (parentBoundaryBandFrameField M n height t omega) (depth+j))
      (fun j => descendantsAverage (originCube 2 n) (depth+j) (fun U => traceDefect (openCubeSet U)
        (parentBoundaryBandFrameField M n height t omega) 1))=
      parentBoundaryBandWeakProxy M n height depth t omega := by
  unfold rawWeakTraceProxy parentBoundaryBandWeakProxy
  apply congrArg (fun z : ℝ => (1-inverseHistoryDiscount^2)*z)
  apply tsum_congr
  intro j
  dsimp only
  rw [←parent_boundary_band_inverse_depth M n height t omega (depth+j),
    parent_boundary_band_trace_depth]

/-- Both actual parent-error moments obey the corrected one/two proxy
budgets on the simultaneous physical band, including convergence of the
entire inverse-weighted trace history. There is no estimate premise. -/
theorem parent_boundary_actual_band_weak_budget (M : ABKModel 2) (n : ℤ)
    (height depth : ℕ) (t : ℝ) (omega : Cutoff.CutoffSample 2) :
    let Q := originCube 2 n
    let sigma : ℝ := Annealed.sigmaBar M n
    let hsigma := (Annealed.sigmaBar_characterization M n).1
    let k := pureFluxOpenResponseRestriction n (nativeSourceBandScalar n height t omega)
    let V := fun U => oldSignedPrimalErrorSize Q U M.nu sigma M.nu_pos hsigma k
    let G := fun U => oldSignedReciprocalErrorSize Q U M.nu sigma M.nu_pos hsigma k
    let xi := parentBoundaryBandWeakProxy M n height depth t omega
    descendantsAverage Q depth (fun U => V U^2)≤xi ∧
    descendantsAverage Q depth (fun U => V U^2+G U^2)≤2*xi ∧
    Summable (fun j : ℕ => inverseHistoryDiscount^(2*j)*
      parentBoundaryBandInverseDepth M n height t omega (depth+j)*
      parentBoundaryBandTraceDepth M n height t omega (depth+j)) := by
  intro Q sigma hsigma k V G xi
  have hV := parent_boundary_primal_broken_weak_bound Q depth M.nu sigma M.nu_pos hsigma k
  have hVG := parent_boundary_joint_broken_weak_bound Q depth M.nu sigma M.nu_pos hsigma k
  change descendantsAverage Q depth (fun U => V U^2)≤rawWeakTraceProxy
    (fun j => lemmaVInverseDepthMax Q (parentBoundaryBandFrameField M n height t omega) (depth+j))
    (fun j => descendantsAverage Q (depth+j) (fun U => traceDefect (openCubeSet U)
      (parentBoundaryBandFrameField M n height t omega) 1)) at hV
  change descendantsAverage Q depth (fun U => V U^2+G U^2)≤2*rawWeakTraceProxy
    (fun j => lemmaVInverseDepthMax Q (parentBoundaryBandFrameField M n height t omega) (depth+j))
    (fun j => descendantsAverage Q (depth+j) (fun U => traceDefect (openCubeSet U)
      (parentBoundaryBandFrameField M n height t omega) 1)) at hVG
  rw [parent_boundary_band_proxy_eq] at hV hVG
  refine ⟨hV,hVG,?_⟩
  have hs := parent_boundary_broken_trace_summable Q depth
    (parentBoundaryBandFrameField M n height t omega)
    (responseFramePlanarCoefficientField_isElliptic (measurableSet_openCubeSet Q) M.nu sigma M.nu_pos hsigma k)
  apply hs.congr
  intro j
  rw [←parent_boundary_band_inverse_depth M n height t omega (depth+j),
    parent_boundary_band_trace_depth]

end
end ASDExplicitGamma.Native
