module

public import ASDExplicitGamma.Native.ParentBoundaryCovarianceRotation
public import ASDExplicitGamma.Triadic.HilbertHaarAlgebra

/-! Centering commutes with the actual signed coordinate permutation;
the complete centered plus and minus beta norms are identical. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ASDExplicitGamma.Scalar ASDExplicitGamma.Gaussian
open ASDExplicitGamma.Triadic ASDExplicitGamma.Main
noncomputable section

private theorem center_congr (Q : TriadicCube 2) {f g : Vec 2 → ℝ}
    (hh : f =ᵐ[normalizedCubeMeasure Q] g) :
    (fun x => f x-∫ y,f y ∂normalizedCubeMeasure Q) =ᵐ[normalizedCubeMeasure Q]
      fun x => g x-∫ y,g y ∂normalizedCubeMeasure Q := by
  filter_upwards [hh] with x hx
  rw [hx,integral_congr_ae hh]

private theorem center_neg (Q : TriadicCube 2) {f g : Vec 2 → ℝ}
    (hh : f =ᵐ[normalizedCubeMeasure Q] fun x => -g x) :
    (fun x => f x-∫ y,f y ∂normalizedCubeMeasure Q) =ᵐ[normalizedCubeMeasure Q]
      fun x => -(g x-∫ y,g y ∂normalizedCubeMeasure Q) := by
  filter_upwards [center_congr Q hh] with x hx
  rw [hx,integral_neg]
  ring

/-- The centered actual covariance entries retain the signed permutation,
including their actual deterministic parent means. -/
theorem parent_boundary_centered_covariance_entries (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0<l}) :
    (fun x => parentBoundaryCenteredCovariance Q b L true 0 x 0) =ᵐ[normalizedCubeMeasure Q]
      (fun x => -parentBoundaryCenteredCovariance Q b L false 1 x 1) ∧
    (fun x => parentBoundaryCenteredCovariance Q b L true 0 x 1) =ᵐ[normalizedCubeMeasure Q]
      (fun x => parentBoundaryCenteredCovariance Q b L false 1 x 0) ∧
    (fun x => parentBoundaryCenteredCovariance Q b L true 1 x 0) =ᵐ[normalizedCubeMeasure Q]
      (fun x => parentBoundaryCenteredCovariance Q b L false 0 x 1) ∧
    (fun x => parentBoundaryCenteredCovariance Q b L true 1 x 1) =ᵐ[normalizedCubeMeasure Q]
      (fun x => -parentBoundaryCenteredCovariance Q b L false 0 x 0) := by
  have hh := parent_boundary_remainder_covariance_entries Q b L
  exact ⟨center_neg Q hh.1,center_congr Q hh.2.1,
    center_congr Q hh.2.2.1,center_neg Q hh.2.2.2⟩

private theorem primal_congr (U : TriadicCube 2) {f g : Vec 2 → ℝ}
    (hh : f =ᵐ[normalizedCubeMeasure U] g) :
    primalEnergy U (Real.sqrt 3) f=primalEnergy U (Real.sqrt 3) g := by
  rw [←hilbertPrimalEnergy_real,←hilbertPrimalEnergy_real]
  simp only [hilbertPrimalEnergy,hilbertCubeIncrement_congr_ae U _ hh]

/-- The ACTUAL complete centered plus and minus covariance sizes agree
on each fine cell. The same common-noise contraction controls both. -/
theorem parent_boundary_centered_beta_rotation (Q U : TriadicCube 2) (depth : ℕ)
    (hU : U ∈ descendantsAtDepth Q depth) (b : ℝ) (L : {l : ℝ // 0<l}) :
    parentBoundaryCenteredBeta Q U b L true =
      parentBoundaryCenteredBeta Q U b L false := by
  have hh := parent_boundary_centered_covariance_entries Q b L
  have h00 := primal_congr U (hilbert_ae_descendant hU hh.1)
  have h01 := primal_congr U (hilbert_ae_descendant hU hh.2.1)
  have h10 := primal_congr U (hilbert_ae_descendant hU hh.2.2.1)
  have h11 := primal_congr U (hilbert_ae_descendant hU hh.2.2.2)
  unfold parentBoundaryCenteredBeta
  apply congrArg Real.sqrt
  simp only [vectorPositiveHaarNorm_sq,Fin.sum_univ_two]
  have hpos (f : Vec 2 → ℝ) : positiveHaarNorm U f^2=primalEnergy U (Real.sqrt 3) f :=
    Real.sq_sqrt (primalEnergy_nonneg U (Real.sqrt 3) (Real.sqrt_nonneg _) f)
  simp only [hpos]
  rw [h00,h01,h10,h11,primalEnergy_neg,primalEnergy_neg]
  ring

end
end ASDExplicitGamma.Native
