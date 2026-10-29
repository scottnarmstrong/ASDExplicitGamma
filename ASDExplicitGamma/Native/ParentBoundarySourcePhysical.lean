module

public import ASDExplicitGamma.Native.ParentBoundarySourceTrace
public import ASDExplicitGamma.Native.ParentBoundaryTrial

/-! The sharp complete source trace applies to the literal canonical
parent source used in the physical signed Hessian trials. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ASDExplicitGamma.Scalar ASDExplicitGamma.Gaussian
open ASDExplicitGamma.Triadic ASDExplicitGamma.Main ASDExplicitGamma.Response ASDExplicitGamma.Variational
noncomputable section

/-- The physical source's quarter turn preserves the entire positive
Haar norm, including the zero mode on an arbitrary comparison cell. -/
theorem parent_boundary_source_column_rotation (Q U : TriadicCube 2)
    (u : H10Function (openCubeSet Q)) (b : ℝ) (L : {l : ℝ // 0<l}) (n : whiteBasisIndex) :
    vectorPositiveHaarNorm U (fun x => -u.toH1Function x •
      lemmaVPlanarWeakColumnDivergence (mainQ3DirectionW2 Q b L (whiteBasis n)).value x) =
    vectorPositiveHaarNorm U (fun x i => u.toH1Function x*
      (fderiv ℝ (q3Convolution b L h3Zero (whiteBasis n)) x) (basisVec i)) := by
  have hf : (fun x => -u.toH1Function x •
      lemmaVPlanarWeakColumnDivergence (mainQ3DirectionW2 Q b L (whiteBasis n)).value x) =
      (fun x => planarQuarterTurn (fun i => u.toH1Function x*
        (fderiv ℝ (q3Convolution b L h3Zero (whiteBasis n)) x) (basisVec i))) := by
    funext x i
    fin_cases i <;> simp [lemmaVPlanarWeakColumnDivergence,matVecMul,responsePlanarJ,
      Fin.sum_univ_two,planarQuarterTurn]
    all_goals exact Or.inl rfl
  rw [hf,vectorPositiveHaarNorm_quarterTurn]

/-- Actual canonical parent source complete energy estimate, with no
projection, regularity, convergence or source-norm estimate premise. -/
theorem parent_boundary_actual_source_trace (Q : TriadicCube 2) (depth : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (P : BlockVec 2)
    (b : ℝ) (L : {l : ℝ // 0<l}) :
    let u := oldSignedCanonicalFirstCorrector Q (responseFramePlanarCoefficientField nu sigma k)
      (responseFramePlanarCoefficientField_isElliptic (measurableSet_openCubeSet Q) nu sigma hnu hsigma k) P
    let f := fun n : whiteBasisIndex => descendantsAverage Q depth (fun U =>
      vectorPositiveHaarNorm U (fun x => (parentBoundaryOldSource Q nu sigma hnu hsigma k b L n P x).2)^2)
    Summable f ∧ (∑' n,f n)≤parentBoundaryPotentialSourceClock Q depth b L^2*
      lemmaVTiledWeakEnergy Q depth u.toH1Function.grad := by
  intro u f
  have he : f=parentBoundaryPotentialSourceMode whiteBasis Q depth u b L := by
    funext n
    dsimp only [f,parentBoundaryPotentialSourceMode]
    rw [parent_boundary_old_source_formula]
    simp only [←neg_smul,parent_boundary_source_column_rotation]
    rfl
  rw [he]
  exact parent_boundary_potential_source_trace whiteBasis Q depth u b L

end
end ASDExplicitGamma.Native
