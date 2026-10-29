module

public import ASDExplicitGamma.Native.OldSignedProjectedPhysicalH1
public import ASDExplicitGamma.Native.OldSignedWhiteEnergyTrace
public import ASDExplicitGamma.Main.FlatFieldH1Bounds

/-! Exact complete physical derivative-energy trace of the whole-plane
projection; all inverse shell-length factors are explicit. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ASDExplicitGamma.Model ASDExplicitGamma.Gaussian
open ASDExplicitGamma.Triadic ASDExplicitGamma.Main
noncomputable section

/-- A derivative entry is bounded by its proved covariance trace. -/
theorem old_signed_projected_derivative_white_norm_le (b : ℝ) (L : {l : ℝ // 0 < l})
    (x : Vec 2) (i j k : Fin 2) :
    ‖oldSignedProjectedDerivativeWhiteKernel b L x i j k‖≤Real.sqrt (b^2*(78/5:ℝ)) := by
  have ht := old_signed_projected_derivative_white_total_energy b L x k
  have hle : ‖oldSignedProjectedDerivativeWhiteKernel b L x i j k‖^2≤b^2*(78/5:ℝ) := by
    rw [←ht]
    calc
      _ ≤ ∑ a : Fin 2,‖oldSignedProjectedDerivativeWhiteKernel b L x i a k‖^2 :=
        Finset.single_le_sum (fun a _ => sq_nonneg _) (Finset.mem_univ j)
      _ ≤ _ := Finset.single_le_sum
        (f := fun a : Fin 2 => ∑ c : Fin 2,‖oldSignedProjectedDerivativeWhiteKernel b L x a c k‖^2)
        (fun a _ => Finset.sum_nonneg (fun c _ => sq_nonneg _)) (Finset.mem_univ i)
  nlinarith only [hle,Real.sq_sqrt (by positivity : 0≤b^2*(78/5:ℝ)),
    Real.sqrt_nonneg (b^2*(78/5:ℝ)),norm_nonneg (oldSignedProjectedDerivativeWhiteKernel b L x i j k)]

/-- The actual derivative kernel is square integrable on the physical
square, with its witness supplied by the covariance bound. -/
theorem old_signed_projected_derivative_spatial_memLp (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0 < l}) (i j k : Fin 2) :
    MemLp (fun x : Vec 2 => oldSignedProjectedDerivativeWhiteKernel b L (L.1⁻¹ • x) i j k)
      2 (normalizedCubeMeasure Q) := by
  have hx : Continuous (fun x : Vec 2 => L.1⁻¹ • x) := continuous_id.const_smul (L.1⁻¹)
  have hD : Continuous (fun x => oldSignedProjectedDerivativeWhiteKernel b L x i j k) :=
    (oldSignedPotentialWhiteMap b L).continuous.comp (old_signed_projected_derivative_continuous b i j k)
  apply MemLp.of_bound (hD.comp hx).aestronglyMeasurable (C := Real.sqrt (b^2*(78/5:ℝ)))
  exact Filter.Eventually.of_forall (fun x => old_signed_projected_derivative_white_norm_le b L (L.1⁻¹ • x) i j k)

/-- Exact scaling of normalized scalar spatial energy. -/
theorem old_signed_energy_const_mul (Q : TriadicCube 2) (c : ℝ) (f : Vec 2 → ℝ) :
    energy Q (fun x => c*f x)=c^2*energy Q f := by
  rw [energy_eq_integral_sq,energy_eq_integral_sq]
  simp_rw [mul_pow]
  exact integral_const_mul _ _

/-- Every actual projected H1 derivative coordinate has its full physical
white-mode energy trace. -/
theorem old_signed_projected_gradient_coordinate_trace (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0 < l}) (i j k : Fin 2) :
    HasSum (fun n : whiteBasisIndex => energy Q (fun x =>
      (oldSignedProjectedPhysicalCoordinateH1 Q b L (whiteBasis n) i j).grad x k))
      (L.1⁻¹^2*(∫ x,‖oldSignedProjectedDerivativeWhiteKernel b L (L.1⁻¹ • x) i j k‖^2
        ∂normalizedCubeMeasure Q)) := by
  have hA := old_signed_projected_derivative_spatial_memLp Q b L i j k
  have hs := (old_signed_white_energy_trace (normalizedCubeMeasure Q) whiteBasis _
    hA.aestronglyMeasurable (hA.integrable_norm_pow (by norm_num))).mul_left (L.1⁻¹^2)
  simp_rw [old_signed_projected_physical_coordinate_grad,old_signed_energy_const_mul]
  simpa only [energy_eq_integral_sq] using hs

/-- The complete actual whole-plane projected physical H1 family has
exactly sigma² derivative energy. -/
theorem old_signed_projected_gradient_energy_trace (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0 < l}) :
    HasSum (fun n : whiteBasisIndex => ∑ k : Fin 2,∑ i : Fin 2,∑ j : Fin 2,energy Q (fun x =>
      (oldSignedProjectedPhysicalCoordinateH1 Q b L (whiteBasis n) i j).grad x k)) (mainFlatSigmaSq b L) := by
  have hs := hasSum_sum (s := Finset.univ) (fun k _ => hasSum_sum (s := Finset.univ)
    (fun i _ => hasSum_sum (s := Finset.univ) (fun j _ => old_signed_projected_gradient_coordinate_trace Q b L i j k)))
  have hi (i j k : Fin 2) : Integrable (fun x : Vec 2 =>
      ‖oldSignedProjectedDerivativeWhiteKernel b L (L.1⁻¹ • x) i j k‖^2) (normalizedCubeMeasure Q) :=
    (old_signed_projected_derivative_spatial_memLp Q b L i j k).integrable_norm_pow (by norm_num)
  have hsum (k : Fin 2) : (∑ i : Fin 2,∑ j : Fin 2,L.1⁻¹^2*(∫ x,
      ‖oldSignedProjectedDerivativeWhiteKernel b L (L.1⁻¹ • x) i j k‖^2 ∂normalizedCubeMeasure Q))=
      L.1⁻¹^2*(b^2*(78/5:ℝ)) := by
    simp_rw [←Finset.mul_sum]
    congr 1
    have hin (i : Fin 2) : (∑ j : Fin 2,∫ x,
        ‖oldSignedProjectedDerivativeWhiteKernel b L (L.1⁻¹ • x) i j k‖^2 ∂normalizedCubeMeasure Q)=
        ∫ x,∑ j : Fin 2,‖oldSignedProjectedDerivativeWhiteKernel b L (L.1⁻¹ • x) i j k‖^2
          ∂normalizedCubeMeasure Q := (integral_finsetSum _ (fun j _ => hi i j k)).symm
    simp_rw [hin]
    rw [←integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hi i j k))]
    simp_rw [old_signed_projected_derivative_white_total_energy]
    simp only [integral_const,Measure.real_def,normalizedCubeMeasure_apply_univ,ENNReal.toReal_one,one_smul]
  simp_rw [hsum] at hs
  convert hs using 1
  simp only [Fin.sum_univ_two,mainFlatSigmaSq,div_eq_mul_inv,inv_pow]
  ring

end
end ASDExplicitGamma.Native
