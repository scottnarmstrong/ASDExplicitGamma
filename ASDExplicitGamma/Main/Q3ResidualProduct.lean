module

public import ASDExplicitGamma.Main.Q3CenteredProduct
public import ASDExplicitGamma.Main.Q3ColumnH1Product
public import ASDExplicitGamma.Main.HilbertPositiveTriangle
public import ASDExplicitGamma.Main.HilbertCoordinateMembership

/-! Actual frozen-source residual columns before applying the DIAG estimates. -/

@[expose] public section
namespace ASDExplicitGamma.Main
open Homogenization MeasureTheory ASDExplicitGamma.Gaussian ASDExplicitGamma.Triadic
open scoped BigOperators

/-- The two actual terms in the centered covariance receiver residual.
The final spatial quarter turn is an isometry and is applied separately. -/
noncomputable def mainQ3ResidualColumn {ι : Type*} (e : HilbertBasis ι ℝ WhiteNoise)
    (s : Finset ι) (b : ℝ) (L : {l : ℝ // 0 < l}) (Q : TriadicCube 2)
    (F : Vec 2 → EuclideanSpace ℝ (Fin 2)) (r : H1Function (openCubeSet Q)) (x : Vec 2) :
    EuclideanSpace ℝ (s × Fin 2) :=
  mainEuclideanTensor
    (mainQ3FiniteValue e s b L x-hilbertCubeAverage Q (mainQ3FiniteValue e s b L)) (F x)+
      (-r.toFun x) • mainQ3FiniteColumn e s b L x

/-- The centered residual product bound for arbitrary genuine source data.
Only the vector input's actual L2/positive-Haar membership is required;
all covariance caps, tensor norms and product membership are internal. -/
theorem main_q3_residual_product {ι : Type*} (e : HilbertBasis ι ℝ WhiteNoise)
    (s : Finset ι) (b : ℝ) (L : {l : ℝ // 0 < l}) (Q : TriadicCube 2)
    {F : Vec 2 → EuclideanSpace ℝ (Fin 2)} (hF : MemLp F 2 (normalizedCubeMeasure Q))
    (hP : Summable (fun k => (Real.sqrt 3)^(k+1)*hilbertEnergy Q (hilbertCubeIncrement Q (k+1) F)))
    (r : H1Function (openCubeSet Q)) :
    Summable (fun k => (Real.sqrt 3)^(k+1)*hilbertEnergy Q
      (hilbertCubeIncrement Q (k+1) (mainQ3ResidualColumn e s b L Q F r))) ∧
    hilbertPositiveHaarNorm Q (Real.sqrt 3) (mainQ3ResidualColumn e s b L Q F r) ≤
      (cubeScaleFactor Q*(1/Real.sqrt 3+planarC1)*Real.sqrt ((156/5)*b^2/L.1^2))*
        hilbertPositiveHaarNorm Q (Real.sqrt 3) F+
      Real.sqrt ((156/5)*b^2/L.1^2)*positiveHaarNorm Q r.toFun+
      cubeScaleFactor Q*planarC1*Real.sqrt ((46488/25)*b^2/L.1^4)*Real.sqrt (energy Q r.toFun) := by
  let ψ := mainQ3FiniteValue e s b L
  let a := fun x => mainEuclideanTensor (ψ x-hilbertCubeAverage Q ψ) (F x)
  let d := fun x => (-r.toFun x) • mainQ3FiniteColumn e s b L x
  have ha := main_q3_centered_tensor_product e s b L Q hF hP
  have hd := main_q3_negative_column_h1_product e s b L Q r
  let T := mainEuclideanTensorMap (κ := s) (ρ := Fin 2)
  let B := mainSmoothHilbertOperator Q (fun x => T (ψ x-hilbertCubeAverage Q ψ))
    (T.contDiff.comp ((mainQ3FiniteValue_contDiff e s b L).sub contDiff_const))
  have ham : MemLp a 2 (normalizedCubeMeasure Q) := B.product_memLp hF
  have hdm : MemLp d 2 (normalizedCubeMeasure Q) :=
    (mainRankOneMultiplier Q _ (mainQ3FiniteColumn_contDiff e s b L)).product_memLp
      r.memL2_normalizedCubeMeasure.neg
  have ht := main_hilbert_positive_add Q ham hdm ha.1 hd.1
  refine ⟨ht.1, ht.2.trans ?_⟩
  have hL := main_hilbertL2_le_positive Q hF hP
  have hR := ASDExplicitGamma.Triadic.cubeScaleFactor_pos' Q
  have hc : 0 ≤ cubeScaleFactor Q*planarC1*Real.sqrt ((156/5)*b^2/L.1^2) := by
    unfold planarC1
    positivity
  have hae := ha.2.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hL hc))
  calc
    hilbertPositiveHaarNorm Q (Real.sqrt 3) a+hilbertPositiveHaarNorm Q (Real.sqrt 3) d ≤
      ((cubeScaleFactor Q/Real.sqrt 3*Real.sqrt ((156/5)*b^2/L.1^2))*
        hilbertPositiveHaarNorm Q (Real.sqrt 3) F+
        cubeScaleFactor Q*planarC1*Real.sqrt ((156/5)*b^2/L.1^2)*
          hilbertPositiveHaarNorm Q (Real.sqrt 3) F)+
      (Real.sqrt ((156/5)*b^2/L.1^2)*positiveHaarNorm Q r.toFun+
        cubeScaleFactor Q*planarC1*Real.sqrt ((46488/25)*b^2/L.1^4)*Real.sqrt (energy Q r.toFun)) :=
      add_le_add hae hd.2
    _ = _ := by ring

end ASDExplicitGamma.Main
