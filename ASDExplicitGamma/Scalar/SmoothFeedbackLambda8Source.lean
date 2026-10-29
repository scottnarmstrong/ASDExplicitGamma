module

public import ASDExplicitGamma.Scalar.SmoothFeedbackGapSourceForce
public import ASDExplicitGamma.Scalar.Lambda8Q3ParentOscillation
public import ASDExplicitGamma.Native.OldSignedFlatAdmissibility

/-! Actual q3 projected shell loads have the H¹ regularity needed by the
smooth-feedback cell source estimate. -/

@[expose] public section

namespace ASDExplicitGamma.Scalar

open Homogenization MeasureTheory
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Response ASDExplicitGamma.Triadic
open Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3

noncomputable section

/-- Restricting an H² potential to a cell makes its projected load H¹ there,
with both the quarter-order pairing admissibility and the source-energy
admissibility used by the actual OLD estimates. -/
theorem smooth_feedback_h2_projected_source_admissible
    (Q R : TriadicCube 2) (hRQ : openCubeSet R ⊆ openCubeSet Q)
    (u : H10Function (openCubeSet Q))
    (H : HasWeakHessianOn (openCubeSet Q) u.toH1Function) :
    ScalarQuarterHaarAdmissible R (fun x i => u.toH1Function.grad x i) ∧
      ScalarPositiveHaarAdmissible R (fun x i => u.toH1Function.grad x i) ∧
      ScalarQuarterHaarAdmissible R
        (fun x i => u.toH1Function.grad x i -
          cubeAverage R (fun y => u.toH1Function.grad y i)) ∧
      ScalarPositiveHaarAdmissible R
        (fun x i => u.toH1Function.grad x i -
          cubeAverage R (fun y => u.toH1Function.grad y i)) := by
  let uR := u.toH1Function.restrict (isOpen_openCubeSet R) hRQ
  let HR := H.restrict (isOpen_openCubeSet R) hRQ
  let g : Fin 2 → H1Function (openCubeSet R) := fun i => HR.gradCoordH1Function i
  have hfg : ∀ x i, u.toH1Function.grad x i = (g i).toFun x := by
    intro x i
    simp [g, HR, HasWeakHessianOn.restrict, H1Function.restrict]
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact smooth_feedback_quarter_haar_admissible_of_h1 R _ g hfg
  · have hpos := ASDExplicitGamma.Native.old_signed_h1_vector_positive_admissible R g
    have heq : (fun x i => (g i).toFun x) =
        (fun x i => u.toH1Function.grad x i) := by
      funext x i
      exact (hfg x i).symm
    rw [heq] at hpos
    exact hpos
  · exact smooth_feedback_centered_quarter_haar_admissible_of_h1 R
      (fun x i => u.toH1Function.grad x i) g hfg
  · let mean : Vec 2 := fun i => cubeAverage R
      (fun x => u.toH1Function.grad x i)
    have hpos := ASDExplicitGamma.Native.old_signed_centered_h1_vector_positive_admissible
      R g mean 1
    have heq : (fun x i => (1 : ℝ) * (g i).toFun x - mean i) =
        (fun x i => u.toH1Function.grad x i -
          cubeAverage R (fun y => u.toH1Function.grad y i)) := by
      funext x i
      simp [mean, hfg x i]
    rw [heq] at hpos
    exact hpos

end

end ASDExplicitGamma.Scalar
