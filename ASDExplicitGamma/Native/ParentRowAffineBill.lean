module

public import ASDExplicitGamma.Native.ParentBoundaryBandAffineBill
public import ASDExplicitGamma.Native.ParentRowAffineUpper
public import ASDExplicitGamma.Native.ParentBoundaryBandEnergy

/-! The complete finite-shell affine bill on the actual simultaneous law. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Variational Gaussian Inverse Main Triadic Algsuperdiff.Section3
noncomputable section

/-- The actual whole-band affine term is integrable and obeys the complete
own-native Y/v/derivative-variance bill, with no moment or generator premise. -/
theorem parent_row_affine_bill
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma≤gammaZero) (n : ℤ) (height : ℕ) (hheight : 1≤height) (r : ℕ) (hr : r≤5)
    (U0 : TriadicCube 2) (hU0 : U0∈descendantsAtDepth (originCube 2 n) r)
    (t : ℝ) (ht : t≤1) (hpast : ∀ k<n,nativeInductionState M h k) :
    Integrable (parentBoundaryBandAffineBill M h n height r t) (Cutoff.cutoffSampleLaw M).toMeasure ∧
    (∫ omega,parentBoundaryBandAffineBill M h n height r t omega ∂(Cutoff.cutoffSampleLaw M).toMeasure)≤
      (parentBoundaryBandDirichletEnergy M h n height/2)*
        (∫ omega,traceDefect (cubeSet U0)
          (attenuatedCoefficient M n (n+(height:ℤ)) (fun _ => Real.sqrt t) omega)
          (Annealed.sigmaBar M n) ∂(Cutoff.cutoffSampleLaw M).toMeasure)+
      2*parentBoundaryBandVariance M h n height*
        ((3683/2500:ℝ)-1)+
      (4+2*Real.sqrt 2)*(cubeScaleFactor (originCube 2 n)/(Real.pi*(3:ℝ)^r))^2*
        parentBoundaryBandDerivativeVariance M h n height := by
  let b := fun i : Fin height => q3ModelAmplitude M h (n+((i.val+1:ℕ):ℤ))/(Annealed.sigmaBar M n:ℝ)
  let L := fun i : Fin height => q3ModelLength (n+((i.val+1:ℕ):ℤ))
  have hi (i : Fin height) :=
    (parent_boundary_band_affine_expectation M h hM n height hheight r t (b i) (L i)).1
  have hb (i : Fin height) := parent_row_affine_upper M h hM hg n height hheight r hr
    U0 hU0 t ht hpast (b i) (L i)
  have hint : Integrable (parentBoundaryBandAffineBill M h n height r t)
      (Cutoff.cutoffSampleLaw M).toMeasure := integrable_finsetSum _ (fun i _ => hi i)
  refine ⟨hint,?_⟩
  unfold parentBoundaryBandAffineBill
  rw [integral_finsetSum _ (fun i _ => hi i)]
  apply (Finset.sum_le_sum (fun i _ => hb i)).trans_eq
  simp only [Finset.sum_add_distrib]
  unfold parentBoundaryBandDirichletEnergy parentBoundaryBandVariance parentBoundaryBandDerivativeVariance
  simp only [Finset.sum_div,Finset.sum_mul,Finset.mul_sum,b,L]

end
end ASDExplicitGamma.Native
