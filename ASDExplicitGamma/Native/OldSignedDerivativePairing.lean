module

public import ASDExplicitGamma.Variational.LocalizedShearWeak

/-! AN (3.4): zero-boundary cell potentials remove every constant fresh
gauge from the actual localized-shear feedback against reciprocal gradients. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ASDExplicitGamma.Response ASDExplicitGamma.Variational
noncomputable section

private instance oldSignedDerivativePairingFiniteMeasure (Q : TriadicCube 2) :
    IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
  (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume

/-- Exact column-divergence feedback on a zero-boundary cell potential.
The reciprocal test may have nonzero boundary data. -/
theorem old_signed_zero_trace_derivative_pairing (Q : TriadicCube 2)
    (eta : H1Function (openCubeSet Q)) (phi : H10Function (openCubeSet Q))
    (g : H1Function (openCubeSet Q))
    (heta : MemLp eta.toFun ⊤ (volume.restrict (openCubeSet Q)))
    (hdeta : ∀ i,MemLp (fun x => eta.grad x i) ⊤ (volume.restrict (openCubeSet Q))) :
    volumeAverage (openCubeSet Q) (fun x => vecDot
      (eta x • matVecMul responsePlanarJ (phi.toH1Function.grad x)) (g.grad x))=
      volumeAverage (openCubeSet Q) (fun x => vecDot
        (phi.toH1Function x • lemmaVPlanarWeakColumnDivergence eta x) (g.grad x)) := by
  let I : H1Function (openCubeSet Q) →ₗ[ℝ] H1Function (openCubeSet Q) := 0
  have hr : MemH10 (openCubeSet Q) (phi.toH1Function-I phi.toH1Function).toFun := by
    simp only [I,LinearMap.zero_apply,sub_zero]
    exact ⟨phi,rfl⟩
  have ht := lemmaV_pairing_lift_of_interpolant (isOpenBoundedConvexDomain_openCubeSet Q)
    I phi.toH1Function eta g hr heta hdeta
  simpa only [I,lemmaVPlanarRowField,LinearMap.zero_apply,H1Function.zero_grad,
    H1Function.sub_toFun,sub_zero,H1Function.zero_toFun,Pi.zero_apply,matVecMul_zero,
    smul_zero,zero_add] using ht

end
end ASDExplicitGamma.Native
