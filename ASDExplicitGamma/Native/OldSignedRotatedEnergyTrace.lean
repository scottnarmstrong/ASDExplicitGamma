module

public import ASDExplicitGamma.Native.OldSignedWhiteEnergyTrace
public import ASDExplicitGamma.Native.OldSignedRotatedProjectedField
public import ASDExplicitGamma.Triadic.VectorHaarSymmetry

/-! Rotating the two physical input loads preserves their complete
whole-plane projected spatial energy trace. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ASDExplicitGamma.Model ASDExplicitGamma.Gaussian
open ASDExplicitGamma.Triadic ASDExplicitGamma.Response
noncomputable section

/-- The quarter turn is an exact signed permutation of the two actual
projected inputs, so their normalized spatial energy sum is unchanged. -/
theorem old_signed_rotated_projected_energy_sum (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0 < l}) (n : whiteBasisIndex) :
    (∑ i : Fin 2,∑ k : Fin 2,energy Q (fun x => oldSignedRotatedProjectedField b L (whiteBasis n) i x k)) =
      ∑ i : Fin 2,∑ j : Fin 2,energy Q (fun x =>
        inner ℝ (whiteBasis n) (oldSignedProjectedWhiteKernel b L (L.1⁻¹ • x) i j)) := by
  have h0 (k : Fin 2) : (fun x => oldSignedRotatedProjectedField b L (whiteBasis n) 0 x k)=
      fun x => inner ℝ (whiteBasis n) (oldSignedProjectedWhiteKernel b L (L.1⁻¹ • x) k 1) := by
    funext x
    simp [oldSignedRotatedProjectedField,responsePlanarJ,oldSignedPhysicalProjectedField]
  have h1 (k : Fin 2) : (fun x => oldSignedRotatedProjectedField b L (whiteBasis n) 1 x k)=
      fun x => -inner ℝ (whiteBasis n) (oldSignedProjectedWhiteKernel b L (L.1⁻¹ • x) k 0) := by
    funext x
    simp [oldSignedRotatedProjectedField,responsePlanarJ,oldSignedPhysicalProjectedField]
  simp only [Fin.sum_univ_two,h0,h1,energy_neg]
  ring

/-- The complete rotated physical whole-plane family has exactly one
shell variance of normalized spatial energy. -/
theorem old_signed_rotated_projected_energy_trace (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0 < l}) :
    HasSum (fun n : whiteBasisIndex => ∑ i : Fin 2,∑ k : Fin 2,
      energy Q (fun x => oldSignedRotatedProjectedField b L (whiteBasis n) i x k)) (b^2) :=
  (old_signed_projected_total_spatial_energy_trace Q b L).congr_fun
    (fun n => old_signed_rotated_projected_energy_sum Q b L n)

end
end ASDExplicitGamma.Native
