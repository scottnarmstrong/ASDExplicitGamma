module

public import ASDExplicitGamma.Triadic.DiagEnergyCongr
public import ASDExplicitGamma.Triadic.VectorHaar

/-! Null-set invariance of the OLD vector norms, needed to identify the
actual patched fields with the cell minimizers in projection estimates. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ASDExplicitGamma.Triadic
noncomputable section

/-- Coordinate positive energies depend only on the actual cell class. -/
theorem old_signed_coordinate_primal_sum_congr {m : ℕ} (Q : TriadicCube 2) (q : ℝ)
    {F G : Vec 2 → Fin m → ℝ} (hFG : F =ᵐ[volumeMeasureOn (openCubeSet Q)] G) :
    (∑ i,primalEnergy Q q (fun x => F x i))=∑ i,primalEnergy Q q (fun x => G x i) := by
  apply Finset.sum_congr rfl
  intro i _
  apply diagPrimalEnergy_congr_ae
  rw [volume_restrict_cubeSet_eq_volume_restrict_openCubeSet]
  filter_upwards [hFG] with x hx
  exact congrFun hx i

/-- The actual reciprocal weak norm is invariant under cell null sets. -/
theorem old_signed_vector_weak_congr {m : ℕ} (Q : TriadicCube 2)
    {F G : Vec 2 → Fin m → ℝ} (hFG : F =ᵐ[volumeMeasureOn (openCubeSet Q)] G) :
    vectorWeakHaarNorm Q F=vectorWeakHaarNorm Q G :=
  congrArg Real.sqrt (old_signed_coordinate_primal_sum_congr Q (Real.sqrt 3)⁻¹ hFG)

end
end ASDExplicitGamma.Native
