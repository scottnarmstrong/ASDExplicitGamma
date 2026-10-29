module

public import ASDExplicitGamma.Native.ParentBoundaryMinusKernel
public import ASDExplicitGamma.Native.ParentBoundaryRowEnergy
public import ASDExplicitGamma.Triadic.VectorPositiveMultiplier

/-! Sharp complete-Hilbert covariance derivative budget, with all spatial
and load coordinates aggregated before estimating. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ASDExplicitGamma.Scalar ASDExplicitGamma.Gaussian
open ASDExplicitGamma.Triadic ASDExplicitGamma.Main
noncomputable section

/-- The actual full-minus covariance gradient costs
sqrt(b² sigma²)+sqrt((sigma²/2)Y), with no coordinate-count loss. -/
theorem parent_boundary_minus_covariance_gradient (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0<l}) :
    Real.sqrt (∑ a : Fin 2 × Fin 2,∑ i : Fin 2,
      energy Q (fun x => (parentBoundaryMinusCovarianceH1 Q b L a).grad x i)) ≤
      Real.sqrt (b^2*mainFlatSigmaSq b L) +
        Real.sqrt ((mainFlatSigmaSq b L/2)*parentBoundaryDirichletEnergy Q b L) := by
  let F := fun (p : (Fin 2 × Fin 2) × Fin 2) (x : Vec 2) =>
    inner ℝ (q3Section b L h3Zero x) ((parentBoundaryMinusKernel Q b L p.1).grad x p.2)
  let G := fun (p : (Fin 2 × Fin 2) × Fin 2) (x : Vec 2) =>
    inner ℝ ((fderiv ℝ (q3Section b L h3Zero) x) (basisVec p.2))
      ((parentBoundaryMinusKernel Q b L p.1).toFun x)
  have hF (p : (Fin 2 × Fin 2) × Fin 2) : MemLp (F p) 2 (normalizedCubeMeasure Q) :=
    (innerSL ℝ).memLp_of_bilin 2
      (main_continuous_memLp_top Q (q3Section_continuous b L h3Zero))
      ((parentBoundaryMinusKernel Q b L p.1).gradMemL2_normalized Q p.2)
  have hG (p : (Fin 2 × Fin 2) × Fin 2) : MemLp (G p) 2 (normalizedCubeMeasure Q) :=
    parent_boundary_derivative_row_memLp Q b L _
      ((parentBoundaryMinusKernel Q b L p.1).memL2_normalized Q) p.2
  have hpoint (p : (Fin 2 × Fin 2) × Fin 2) :
      Real.sqrt (energy Q (fun x => (parentBoundaryMinusCovarianceH1 Q b L p.1).grad x p.2)) ≤
        Real.sqrt (energy Q (F p))+Real.sqrt (energy Q (G p)) := by
    have he : (fun x => (parentBoundaryMinusCovarianceH1 Q b L p.1).grad x p.2) =
        (fun x => F p x+G p x) := rfl
    rw [he]
    have hh := hilbertL2Norm_add_le Q (hF p) (hG p)
    simpa only [hilbertL2Norm,hilbertEnergy_real] using hh
  have hh := sqrt_finset_energy_bound Finset.univ
    (fun p : (Fin 2 × Fin 2) × Fin 2 => energy Q (fun x =>
      (parentBoundaryMinusCovarianceH1 Q b L p.1).grad x p.2))
    (fun p => energy Q (F p)) (fun p => energy Q (G p))
    (M := 1) (N := 1) (by norm_num) (by norm_num)
    (fun _ _ => energy_nonneg Q _) (fun _ _ => energy_nonneg Q _)
    (fun _ _ => energy_nonneg Q _) (fun p _ => by simpa only [one_mul] using hpoint p)
  simp only [Fintype.sum_prod_type,one_mul] at hh
  have hFE : (∑ a : Fin 2 × Fin 2,∑ i : Fin 2,energy Q (F (a,i))) ≤ b^2*mainFlatSigmaSq b L := by
    calc
      _ ≤ ∑ a : Fin 2 × Fin 2,∑ i : Fin 2,b^2*hilbertEnergy Q
          (fun x => (parentBoundaryMinusKernel Q b L a).grad x i) :=
        Finset.sum_le_sum (fun a _ => Finset.sum_le_sum (fun i _ =>
          parent_boundary_white_row_energy Q b L _
            ((parentBoundaryMinusKernel Q b L a).gradMemL2_normalized Q i)))
      _ = b^2*∑ a : Fin 2 × Fin 2,hilbertGradientEnergy Q (parentBoundaryMinusKernel Q b L a).grad := by
        simp only [hilbertGradientEnergy,Finset.mul_sum]
      _ = _ := by rw [parent_boundary_minus_kernel_gradient_energy]
  have hGE : (∑ a : Fin 2 × Fin 2,∑ i : Fin 2,energy Q (G (a,i))) ≤
      (mainFlatSigmaSq b L/2)*parentBoundaryDirichletEnergy Q b L := by
    calc
      _ ≤ ∑ a : Fin 2 × Fin 2,(mainFlatSigmaSq b L/2)*
          hilbertEnergy Q (parentBoundaryMinusKernel Q b L a).toFun :=
        Finset.sum_le_sum (fun a _ => parent_boundary_derivative_row_energy Q b L _
          ((parentBoundaryMinusKernel Q b L a).memL2_normalized Q))
      _ = _ := by rw [←Finset.mul_sum,parent_boundary_minus_kernel_energy]
  simp only [Fintype.sum_prod_type] at hFE hGE ⊢
  exact hh.trans (add_le_add (Real.sqrt_le_sqrt hFE) (Real.sqrt_le_sqrt hGE))

end
end ASDExplicitGamma.Native
