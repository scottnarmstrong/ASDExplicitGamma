module

public import ASDExplicitGamma.Native.OldSignedComplementaryKernel
public import ASDExplicitGamma.Native.OldSignedWhiteEnergyTrace

/-! Complete normalized spatial energy of the actual whole-plane
complementary fields. The trace is one shell variance. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ASDExplicitGamma.Model ASDExplicitGamma.Gaussian ASDExplicitGamma.Triadic
noncomputable section

/-- The actual complementary white spatial kernel is L2 on every source
square, with its integrability witness supplied from the amplitude bound. -/
theorem old_signed_complementary_spatial_memLp (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0 < l}) (i j : Fin 2) :
    MemLp (fun x : Vec 2 => oldSignedComplementaryWhiteKernel b L (L.1⁻¹ • x) i j)
      2 (normalizedCubeMeasure Q) := by
  have hx : Continuous (fun x : Vec 2 => L.1⁻¹ • x) := continuous_id.const_smul (L.1⁻¹)
  apply MemLp.of_bound ((old_signed_complementary_white_continuous b L i j).comp hx).aestronglyMeasurable
    (C := 2*|b|)
  exact Filter.Eventually.of_forall (fun x => old_signed_complementary_white_norm_le b L (L.1⁻¹ • x) i j)

/-- Exact complete white-mode trace for one complementary coordinate. -/
theorem old_signed_complementary_coordinate_energy_trace (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0 < l}) (i j : Fin 2) :
    HasSum (fun n : whiteBasisIndex => energy Q (fun x => inner ℝ (whiteBasis n)
      (oldSignedComplementaryWhiteKernel b L (L.1⁻¹ • x) i j)))
      (∫ x,‖oldSignedComplementaryWhiteKernel b L (L.1⁻¹ • x) i j‖^2 ∂normalizedCubeMeasure Q) := by
  have hA := old_signed_complementary_spatial_memLp Q b L i j
  have hs := old_signed_white_energy_trace (normalizedCubeMeasure Q) whiteBasis _
    hA.aestronglyMeasurable (hA.integrable_norm_pow (by norm_num))
  simpa only [energy_eq_integral_sq,Real.norm_eq_abs,sq_abs] using hs

/-- Both complementary loads and both components have exactly one shell
variance of complete normalized physical energy. -/
theorem old_signed_complementary_total_spatial_energy_trace (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0 < l}) :
    HasSum (fun n : whiteBasisIndex => ∑ i : Fin 2,∑ j : Fin 2,energy Q (fun x =>
      inner ℝ (whiteBasis n) (oldSignedComplementaryWhiteKernel b L (L.1⁻¹ • x) i j))) (b^2) := by
  have hs := hasSum_sum (s := Finset.univ) (fun i _ =>
    hasSum_sum (s := Finset.univ) (fun j _ => old_signed_complementary_coordinate_energy_trace Q b L i j))
  have hi (i j : Fin 2) : Integrable (fun x : Vec 2 =>
      ‖oldSignedComplementaryWhiteKernel b L (L.1⁻¹ • x) i j‖^2) (normalizedCubeMeasure Q) :=
    (old_signed_complementary_spatial_memLp Q b L i j).integrable_norm_pow (by norm_num)
  have hin (i : Fin 2) : (∑ j : Fin 2,∫ x,‖oldSignedComplementaryWhiteKernel b L (L.1⁻¹ • x) i j‖^2
      ∂normalizedCubeMeasure Q) = ∫ x,∑ j : Fin 2,‖oldSignedComplementaryWhiteKernel b L (L.1⁻¹ • x) i j‖^2
        ∂normalizedCubeMeasure Q := (integral_finsetSum _ (fun j _ => hi i j)).symm
  have he : (∑ i : Fin 2,∑ j : Fin 2,∫ x,‖oldSignedComplementaryWhiteKernel b L (L.1⁻¹ • x) i j‖^2
      ∂normalizedCubeMeasure Q)=b^2 := by
    simp_rw [hin]
    rw [←integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hi i j))]
    simp_rw [old_signed_complementary_white_total_energy]
    simp only [integral_const,Measure.real_def,normalizedCubeMeasure_apply_univ,ENNReal.toReal_one,one_smul]
  rw [he] at hs
  exact hs

end
end ASDExplicitGamma.Native
