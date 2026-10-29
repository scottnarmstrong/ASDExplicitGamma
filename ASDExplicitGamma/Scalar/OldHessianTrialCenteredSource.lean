module

public import ASDExplicitGamma.Scalar.OldHessianTrialSourceRegularity
public import ASDExplicitGamma.Main.LocalizedHessianQ3Residual
public import ASDExplicitGamma.Main.Q3ResidualHilbertSchmidt

/-! Literal mixed source minus its frozen coefficient-mean nodal row.
The residual contains the actual centered DIAG row and retained coarse product. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Native Response Triadic Variational Gaussian Inverse Main
noncomputable section

/-- The exact frozen residual of the actual mixed vector source. -/
def oldHessianCenteredMixedSource (Q : TriadicCube 2) (fine : ℕ) (b : ℝ)
    (L : {l : ℝ // 0<l}) (v phi : H10Function (openCubeSet Q))
    (U : TriadicCube 2) (j : whiteBasisIndex) : Vec 2 → Vec 2 :=
  fun x => -(oldHessianMixedSource (diagInterpolant Q fine)
      (mainQ3DirectionW2 Q b L (whiteBasis j)).value v.toH1Function phi.toH1Function x).2-
    cubeAverage U (q3Convolution b L h3Zero (whiteBasis j)) •
      matVecMul responsePlanarJ ((diagInterpolant Q fine (v-phi).toH1Function).grad x)

/-- Exact actual-source decomposition, before any positive-norm estimate.
Only the coefficient is frozen; the nodal interpolant remains the same. -/
theorem old_hessian_centered_mixed_source_split (Q : TriadicCube 2) (fine : ℕ) (b : ℝ)
    (L : {l : ℝ // 0<l}) (v phi : H10Function (openCubeSet Q))
    (U : TriadicCube 2) (j : whiteBasisIndex) :
    oldHessianCenteredMixedSource Q fine b L v phi U j=
      fun x => planarQuarterTurn (mainQ3ResidualCoordinate whiteBasis b L Q fine
        (v-phi).toH1Function U j x)+oldHessianCoarseProduct Q b L phi (whiteBasis j) x := by
  let eta := (mainQ3DirectionW2 Q b L (whiteBasis j)).value
  have hw : (v-phi).toH1Function=v.toH1Function-phi.toH1Function := rfl
  have hs (x : Vec 2) : -(oldHessianMixedSource (diagInterpolant Q fine) eta
      v.toH1Function phi.toH1Function x).2=
      lemmaVPlanarRowField (diagInterpolant Q fine) eta (v-phi).toH1Function x+
        oldHessianCoarseProduct Q b L phi (whiteBasis j) x := by
    rw [hw]
    change -(-lemmaVPlanarRowField (diagInterpolant Q fine) eta
      (v.toH1Function-phi.toH1Function) x + -oldHessianCoarseProduct Q b L phi (whiteBasis j) x)=_
    abel
  have hJ (p : Vec 2) : matVecMul responsePlanarJ p=planarQuarterTurn p := by
    funext i
    fin_cases i <;> simp [matVecMul,responsePlanarJ,planarQuarterTurn,Fin.sum_univ_two]
  funext x
  unfold oldHessianCenteredMixedSource
  rw [hs,main_q3_localized_row_centered_residual_split,hJ]
  funext k
  fin_cases k <;> norm_num [planarQuarterTurn,Pi.add_apply,Pi.sub_apply,Pi.smul_apply,smul_eq_mul] <;> ring

/-- The actual centered row's complete positive series on every fine tile,
proved from the same finite Hilbert-column product estimate. -/
theorem old_hessian_centered_row_positive (Q : TriadicCube 2) (fine : ℕ) (b : ℝ)
    (L : {l : ℝ // 0<l}) (u : H10Function (openCubeSet Q))
    (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth Q fine)
    (j : whiteBasisIndex) (k : Fin 2) :
    Summable (fun d => (Real.sqrt 3)^(d+1)*energy U (cubeIncrement U (d+1)
      (fun x => mainQ3ResidualCoordinate whiteBasis b L Q fine u.toH1Function U j x k))) := by
  let s : Finset whiteBasisIndex := {j}
  let F := mainQ3DiagResidualColumn whiteBasis s b L Q fine u.toH1Function U
  have hm : MemLp F 2 (normalizedCubeMeasure U) := by
    apply memLp_piLp_iff.mpr
    rintro ⟨l,i⟩
    simpa only [F,mainQ3DiagResidualColumn_coordinate] using
      main_q3_residual_coordinate_memLp whiteBasis b L Q fine u.toH1Function U hU l.val i
  have hp := (main_q3_diag_residual_local whiteBasis s b L Q fine 0 u U hU).1
  rw [old_signed_zero_affine_potential] at hp
  let li : s := ⟨j,Finset.mem_singleton_self j⟩
  simpa only [F,mainQ3DiagResidualColumn_coordinate,li,s] using
    main_hilbert_coordinate_summable U hm hp (li,k)

/-- The complete centered row has its exact physical covariance residual
coefficient times the actual fine weak energy. -/
theorem old_hessian_centered_row_energy (Q : TriadicCube 2) (fine : ℕ) (b : ℝ)
    (L : {l : ℝ // 0<l}) (u : H10Function (openCubeSet Q)) :
    Summable (mainQ3ResidualEnergy whiteBasis b L Q fine u.toH1Function) ∧
      Real.sqrt (∑' j,mainQ3ResidualEnergy whiteBasis b L Q fine u.toH1Function j) ≤
        mainQ3RemainderExact (diagMeshRadius Q fine) b L.val*
          Real.sqrt (lemmaVTiledWeakEnergy Q fine u.toH1Function.grad) := by
  have hh := main_q3_residual_hilbert_schmidt whiteBasis b L Q fine 0 u
  dsimp only at hh
  rw [old_signed_zero_affine_potential] at hh
  exact hh

end
end ASDExplicitGamma.Scalar
