module

public import ASDExplicitGamma.Scalar.OldHessianTrialCenteredSource
public import ASDExplicitGamma.Scalar.OldHessianTrialBrokenPositiveTriangle
public import ASDExplicitGamma.Scalar.OldHessianTrialPatchedProduct
public import ASDExplicitGamma.Scalar.OldHessianTrialPrincipalContraction

/-! Complete actual mixed residual-source energy, with the unchanged fine
interpolant and the retained coarse potential product summed jointly. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Native Response Triadic Variational Gaussian Inverse Main
noncomputable section
attribute [local irreducible] Homogenization.descendantsAtDepth

/-- The literal coarse-cell product bill, before any stochastic history cap. -/
def oldHessianCoarseColumnBill (Q : TriadicCube 2) (coarse : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (e : Vec 2) (b : ℝ) (L : {l : ℝ // 0<l}) : ℝ :=
  oldSignedCellAverage Q coarse (fun D =>
    (Real.sqrt 2*((503/200:ℝ)*(cubeScaleFactor D.val/L.1)+
      (2031/500:ℝ)*(cubeScaleFactor D.val/L.1)^2)*|b|)^2*
    vectorWeakHaarEnergy D.val
      (oldHessianCoarseCellPotential Q coarse nu sigma hnu hsigma k e D).toH1Function.grad)

/-- The actual centered mixed residual is a complete positive-energy
column. Its norm costs exactly the centered row plus genuine coarse product
bills, with no truncation or source-energy premise. -/
theorem old_hessian_actual_centered_mixed_energy (Q : TriadicCube 2) (coarse : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (b : ℝ) (L : {l : ℝ // 0<l}) (i : Fin 2) :
    let a := responseFramePlanarCoefficientField nu sigma k
    let ha := responseFramePlanarCoefficientField_isElliptic (measurableSet_openCubeSet Q) nu sigma hnu hsigma k
    let v := oldSignedCanonicalFirstCorrector Q a ha (0,basisVec i)
    let phi := oldHessianCoarsePotential Q coarse nu sigma hnu hsigma k (basisVec i)
    let u := v-phi
    let E := fun j => oldHessianBrokenColumnEnergy Q (coarse+1)
      (fun U => oldHessianCenteredMixedSource Q (coarse+1) b L v phi U j)
    Summable E ∧ Real.sqrt (∑' j,E j) ≤
      mainQ3RemainderExact (diagMeshRadius Q (coarse+1)) b L.val*
        Real.sqrt (lemmaVTiledWeakEnergy Q (coarse+1) u.toH1Function.grad)+
      Real.sqrt (oldHessianCoarseColumnBill Q coarse nu sigma hnu hsigma k (basisVec i) b L) := by
  intro a ha v phi u E
  let F := fun (j : whiteBasisIndex) (U : TriadicCube 2) (x : Vec 2) =>
    planarQuarterTurn (mainQ3ResidualCoordinate whiteBasis b L Q (coarse+1) u.toH1Function U j x)
  let G := fun (j : whiteBasisIndex) (_U : TriadicCube 2) =>
    oldHessianCoarseProduct Q b L phi (whiteBasis j)
  have hFm (j : whiteBasisIndex) (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth Q (coarse+1))
      (r : Fin 2) : MemLp (fun x => F j U x r) 2 (normalizedCubeMeasure U) := by
    fin_cases r
    · exact (main_q3_residual_coordinate_memLp whiteBasis b L Q (coarse+1) u.toH1Function U hU j 1).neg
    · exact main_q3_residual_coordinate_memLp whiteBasis b L Q (coarse+1) u.toH1Function U hU j 0
  have hFp (j : whiteBasisIndex) (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth Q (coarse+1)) :=
    positive_series_quarterTurn U (mainQ3ResidualCoordinate whiteBasis b L Q (coarse+1) u.toH1Function U j)
      (old_hessian_centered_row_positive Q (coarse+1) b L u U hU j)
  have hGm (j : whiteBasisIndex) (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth Q (coarse+1))
      (r : Fin 2) := (old_hessian_coarse_product_regular Q (coarse+1) b L phi j U hU r).1
  have hGp (j : whiteBasisIndex) (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth Q (coarse+1))
      (r : Fin 2) := (old_hessian_coarse_product_regular Q (coarse+1) b L phi j U hU r).2
  have hrow := old_hessian_centered_row_energy Q (coarse+1) b L u
  have hprod := old_hessian_patched_product_energy Q coarse nu sigma hnu hsigma k (basisVec i) b L
  have hFs : Summable (fun j => oldHessianBrokenColumnEnergy Q (coarse+1) (F j)) := hrow.1
  have hGs : Summable (fun j => oldHessianBrokenColumnEnergy Q (coarse+1) (G j)) := hprod.1
  have ht := old_hessian_broken_cell_positive_triangle Q (coarse+1) F G hFm hGm hFp hGp hFs hGs
  have he (j : whiteBasisIndex) : E j=oldHessianBrokenColumnEnergy Q (coarse+1)
      (fun U x r => F j U x r+G j U x r) := by
    unfold oldHessianBrokenColumnEnergy
    apply congrArg (descendantsAverage Q (coarse+1))
    funext U
    dsimp only
    rw [old_hessian_centered_mixed_source_split]
    rfl
  simp_rw [←he] at ht
  exact ⟨ht.1,ht.2.trans (add_le_add hrow.2 (Real.sqrt_le_sqrt hprod.2))⟩

end
end ASDExplicitGamma.Scalar
