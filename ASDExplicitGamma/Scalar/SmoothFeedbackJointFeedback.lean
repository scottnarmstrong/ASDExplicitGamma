module

public import ASDExplicitGamma.Scalar.SmoothFeedbackGapIdentity
public import ASDExplicitGamma.Scalar.SmoothFeedbackSourcePatchEnergy
public import ASDExplicitGamma.Native.OldSignedCellHistories
public import ASDExplicitGamma.Native.OldSignedResidualReciprocalEnergy

/-! Actual-maximizer preliminaries for the joint smooth-feedback row. -/

@[expose] public section

namespace ASDExplicitGamma.Scalar

open MeasureTheory Homogenization Response Triadic Variational
open ASDExplicitGamma.Native
open Algsuperdiff.Section3
open scoped BigOperators

noncomputable section

/-- Centering the gradient of a genuine parent H10 potential by the mean on
an actual child still gives a compatible source on the parent. The witness
is the parent H1 potential minus the affine H1 function with that child mean. -/
theorem smooth_feedback_centered_h10_source_compatible
    (Q R : TriadicCube 2) (u : H10Function (openCubeSet Q)) :
    let f : Vec 2 → Vec 2 := u.toH1Function.grad
    let mean : Vec 2 := fun j => cubeAverage R (fun x => f x j)
    let C : Vec 2 → BlockVec 2 := fun x => (fun j => f x j - mean j, 0)
    ScalarCompatible (openCubeSet Q) C := by
  classical
  dsimp only
  let f : Vec 2 → Vec 2 := u.toH1Function.grad
  let mean : Vec 2 := fun j => cubeAverage R (fun x => f x j)
  let C : Vec 2 → BlockVec 2 := fun x => (fun j => f x j - mean j, 0)
  let F : Vec 2 → BlockVec 2 := fun x => (f x, 0)
  let hF : MemBlockL2 (openCubeSet Q) F :=
    memBlockL2_blockField u.toH1Function.grad_memVectorL2 MemLp.zero
  let hC : MemBlockL2 (openCubeSet Q) C := by
    have hsub : MemLp (fun x => F x - (mean, 0)) 2
        (volumeMeasureOn (openCubeSet Q)) := hF.sub (memLp_const (mean, 0))
    convert hsub using 1
    ext x j
    · simp [C, F, f]
    · change (0 : Vec 2) j = (0 - 0 : Vec 2) j
      simp
  let affine : H1Function (openCubeSet Q) :=
    H1Function.affineOnIsSobolevRegularDomain
      (isOpenBoundedConvexDomain_openCubeSet Q).isSobolevRegularDomain mean
  let centeredPotential : H1Function (openCubeSet Q) := u.toH1Function - affine
  refine ⟨hC, ⟨centeredPotential, ?_⟩, isSolenoidalOn_zero⟩
  funext x
  simp [centeredPotential, affine, H1Function.sub_grad,
    H1Function.affineOnIsSobolevRegularDomain_grad]
  ext j
  rfl

end

end ASDExplicitGamma.Scalar
