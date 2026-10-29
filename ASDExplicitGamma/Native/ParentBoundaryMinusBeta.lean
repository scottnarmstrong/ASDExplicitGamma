module

public import ASDExplicitGamma.Native.ParentBoundaryCenteredH1
public import ASDExplicitGamma.Native.ParentBoundaryPositiveEnergy
public import ASDExplicitGamma.Triadic.HilbertHaarAlgebra

/-! The actual centered minus beta clock on an independent fine partition. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ASDExplicitGamma.Scalar ASDExplicitGamma.Gaussian
open ASDExplicitGamma.Triadic ASDExplicitGamma.Main
noncomputable section

private theorem primal_congr_normalized (Q : TriadicCube 2) (q : ℝ)
    {f g : Vec 2 → ℝ} (hfg : f =ᵐ[normalizedCubeMeasure Q] g) :
    primalEnergy Q q f=primalEnergy Q q g := by
  rw [←hilbertPrimalEnergy_real,←hilbertPrimalEnergy_real]
  simp only [hilbertPrimalEnergy,hilbertCubeIncrement_congr_ae Q _ hfg]

/-- The centered beta is the exact two-load positive-Haar norm of the
actual centered H1 representatives on every genuine fine cell. -/
theorem parent_boundary_centered_beta_h1 (Q U : TriadicCube 2) (depth : ℕ)
    (hU : U ∈ descendantsAtDepth Q depth) (b : ℝ) (L : {l : ℝ // 0<l}) :
    parentBoundaryCenteredBeta Q U b L false^2 =
      ∑ i : Fin 2,∑ k : Fin 2,positiveHaarNorm U (parentBoundaryCenteredMinusH1 Q b L i k).toFun^2 := by
  unfold parentBoundaryCenteredBeta
  rw [Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg _))]
  simp_rw [vectorPositiveHaarNorm_sq]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro k _
  unfold positiveHaarNorm
  rw [←primal_congr_normalized U (Real.sqrt 3)
    (hilbert_ae_descendant hU (parent_boundary_centered_h1_ae Q b L i k))]

/-- The source's signed centered value variance and sharp derivative
operator budget control the ACTUAL complete minus beta on fine cells.
The comparison mesh remains independent of the parent boundary potential. -/
theorem parent_boundary_minus_beta_squared (m : ℤ) (depth : ℕ) (b : ℝ)
    (L : {l : ℝ // 0<l}) :
    descendantsAverage (originCube 2 m) depth (fun U =>
      parentBoundaryCenteredBeta (originCube 2 m) U b L false^2) ≤
      b^2*parentBoundaryDirichletEnergy (originCube 2 m) b L -
        (parentBoundaryDirichletEnergy (originCube 2 m) b L)^2/2 +
      (cubeScaleFactor (originCube 2 m)/3^depth)^2*planarC1^2*
        (Real.sqrt (b^2*mainFlatSigmaSq b L)+
          Real.sqrt ((mainFlatSigmaSq b L/2)*parentBoundaryDirichletEnergy (originCube 2 m) b L))^2 := by
  let Q := originCube 2 m
  have hrepr : descendantsAverage Q depth (fun U => parentBoundaryCenteredBeta Q U b L false^2) =
      ∑ i : Fin 2,∑ k : Fin 2,descendantsAverage Q depth
        (fun U => positiveHaarNorm U (parentBoundaryCenteredMinusH1 Q b L i k).toFun^2) := by
    calc
      _ = descendantsAverage Q depth (fun U => ∑ i : Fin 2,∑ k : Fin 2,
          positiveHaarNorm U (parentBoundaryCenteredMinusH1 Q b L i k).toFun^2) :=
        congrArg (fun z : ℝ => ((descendantsAtDepth Q depth).card : ℝ)⁻¹*z)
          (Finset.sum_congr rfl (fun U hU => parent_boundary_centered_beta_h1 Q U depth hU b L))
      _ = _ := by simp_rw [Homogenization.descendantsAverage_sum]
  rw [hrepr]
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    Finset.sum_le_sum (s := Finset.univ) (fun k _ =>
      parent_boundary_broken_positive_energy Q depth (parentBoundaryCenteredMinusH1 Q b L i k)))
  simp only [Finset.sum_add_distrib,←Finset.mul_sum] at hs
  have hv : (∑ i : Fin 2,∑ k : Fin 2,energy Q (parentBoundaryCenteredMinusH1 Q b L i k).toFun) ≤
      b^2*parentBoundaryDirichletEnergy Q b L-(parentBoundaryDirichletEnergy Q b L)^2/2 := by
    have he (i k : Fin 2) : energy Q (parentBoundaryCenteredMinusH1 Q b L i k).toFun =
        energy Q (fun x => parentBoundaryCenteredCovariance Q b L false i x k) := by
      simpa only [hilbertEnergy_real] using hilbertEnergy_congr_ae Q
        (parent_boundary_centered_h1_ae Q b L i k)
    simp_rw [he]
    exact parent_boundary_centered_value_variance m b L
  exact hs.trans (add_le_add hv (mul_le_mul_of_nonneg_left
    (parent_boundary_centered_gradient_bound Q b L) (by positivity)))

end
end ASDExplicitGamma.Native
