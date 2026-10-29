module

public import ASDExplicitGamma.Native.OldSignedCoordinateGradientEnergy

/-! Both physical input and output quarter turns preserve the exact
complete sigma² gradient trace of the whole-plane projected family. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ASDExplicitGamma.Model ASDExplicitGamma.Gaussian
open ASDExplicitGamma.Triadic ASDExplicitGamma.Main ASDExplicitGamma.Response
noncomputable section

/-- The actual H1 input quarter turn is a signed permutation. -/
theorem old_signed_rotated_projected_coordinate_zero (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0 < l}) (w : WhiteNoise) (c : Fin 2) :
    oldSignedRotatedProjectedCoordinateH1 Q b L w (0,c)=oldSignedProjectedPhysicalCoordinateH1 Q b L w c 1 := by
  simp [oldSignedRotatedProjectedCoordinateH1,responsePlanarJ]

theorem old_signed_rotated_projected_coordinate_one (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0 < l}) (w : WhiteNoise) (c : Fin 2) :
    oldSignedRotatedProjectedCoordinateH1 Q b L w (1,c)= -oldSignedProjectedPhysicalCoordinateH1 Q b L w c 0 := by
  simp [oldSignedRotatedProjectedCoordinateH1,responsePlanarJ]

/-- The actual H1 output quarter turn is a signed permutation. -/
theorem old_signed_complementary_coordinate_zero (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0 < l}) (w : WhiteNoise) (i : Fin 2) :
    oldSignedComplementaryCoordinateH1 Q b L w (i,0)= -oldSignedProjectedPhysicalCoordinateH1 Q b L w 1 i := by
  simp [oldSignedComplementaryCoordinateH1,responsePlanarJ]

theorem old_signed_complementary_coordinate_one (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0 < l}) (w : WhiteNoise) (i : Fin 2) :
    oldSignedComplementaryCoordinateH1 Q b L w (i,1)=oldSignedProjectedPhysicalCoordinateH1 Q b L w 0 i := by
  simp [oldSignedComplementaryCoordinateH1,responsePlanarJ]

/-- Input rotation preserves the actual mode's Frobenius gradient energy. -/
theorem old_signed_rotated_projected_gradient_mode (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0 < l}) (n : whiteBasisIndex) :
    oldSignedCoordinateGradientEnergy Q (oldSignedRotatedProjectedCoordinateH1 Q b L (whiteBasis n))=
      ∑ k : Fin 2,∑ i : Fin 2,∑ j : Fin 2,energy Q (fun x =>
        (oldSignedProjectedPhysicalCoordinateH1 Q b L (whiteBasis n) i j).grad x k) := by
  unfold oldSignedCoordinateGradientEnergy
  apply Finset.sum_congr rfl
  intro k _
  simp only [Fintype.sum_prod_type,Fin.sum_univ_two,old_signed_rotated_projected_coordinate_zero,
    old_signed_rotated_projected_coordinate_one,H1Function.neg_grad,Pi.neg_apply,energy_neg]
  ring

/-- Output rotation preserves the actual mode's Frobenius gradient energy. -/
theorem old_signed_complementary_gradient_mode (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0 < l}) (n : whiteBasisIndex) :
    oldSignedCoordinateGradientEnergy Q (oldSignedComplementaryCoordinateH1 Q b L (whiteBasis n))=
      ∑ k : Fin 2,∑ i : Fin 2,∑ j : Fin 2,energy Q (fun x =>
        (oldSignedProjectedPhysicalCoordinateH1 Q b L (whiteBasis n) i j).grad x k) := by
  unfold oldSignedCoordinateGradientEnergy
  apply Finset.sum_congr rfl
  intro k _
  simp only [Fintype.sum_prod_type,Fin.sum_univ_two,old_signed_complementary_coordinate_zero,
    old_signed_complementary_coordinate_one,H1Function.neg_grad,Pi.neg_apply,energy_neg]
  ring

/-- Exact complete derivative trace for the physical input rotation. -/
theorem old_signed_rotated_projected_gradient_trace (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0 < l}) :
    HasSum (fun n : whiteBasisIndex => oldSignedCoordinateGradientEnergy Q
      (oldSignedRotatedProjectedCoordinateH1 Q b L (whiteBasis n))) (mainFlatSigmaSq b L) :=
  (old_signed_projected_gradient_energy_trace Q b L).congr_fun
    (fun n => old_signed_rotated_projected_gradient_mode Q b L n)

/-- Exact complete derivative trace for the physical complementary family. -/
theorem old_signed_complementary_gradient_trace (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0 < l}) :
    HasSum (fun n : whiteBasisIndex => oldSignedCoordinateGradientEnergy Q
      (oldSignedComplementaryCoordinateH1 Q b L (whiteBasis n))) (mainFlatSigmaSq b L) :=
  (old_signed_projected_gradient_energy_trace Q b L).congr_fun
    (fun n => old_signed_complementary_gradient_mode Q b L n)

end
end ASDExplicitGamma.Native
