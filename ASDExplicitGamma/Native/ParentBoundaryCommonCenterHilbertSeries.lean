module

public import ASDExplicitGamma.Native.ParentBoundaryCommonCenterHilbertTrace
public import ASDExplicitGamma.Inverse.PureFluxGeneratorCenteredSource

/-! Complete common-center covariance-row traces, in the physical frame. -/

@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Gaussian Main Model Response Triadic Variational Scalar Inverse
open scoped BigOperators
noncomputable section

/-- Every covariance mode has its genuine positive Haar series, with the
same parent source center throughout the observed descendant. -/
theorem parent_boundary_common_row_positive_series_unit
    (P Q : TriadicCube 2) (hQP : cubeSet Q ⊆ cubeSet P) (b : ℝ) (L : {l : ℝ // 0 < l}) (m : ℕ)
    (p : Vec 2) (u : H10Function (openCubeSet Q))
    (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth Q m)
    (l0 : whiteBasisIndex) :
    ∀ i : Fin 2, Summable (fun k => (Real.sqrt 3)^(k+1)*energy U
      (cubeIncrement U (k+1) (fun x => lemmaVPlanarRowField
        (diagInterpolant Q m)
        (parentBoundaryCommonBasisMultiplier P Q b 1 L l0)
        (lemmaVAffinePotential (isOpenBoundedConvexDomain_openCubeSet Q) p u) x i))) := by
  classical
  let v := lemmaVAffinePotential (isOpenBoundedConvexDomain_openCubeSet Q) p u
  let I := diagInterpolant Q m
  let s : Finset whiteBasisIndex := {l0}
  let l : s := ⟨l0, Finset.mem_singleton_self _⟩
  let C := parentBoundaryCommonFiniteRawRow whiteBasis s b L P Q m v
  have hd := parent_boundary_common_center_hilbert_tile P Q hQP m p u s U hU b L
  have hmem : MemLp C 2 (normalizedCubeMeasure U) := hd.1
  have hsum : Summable (fun k => (Real.sqrt 3)^(k+1)*hilbertEnergy U
      (hilbertCubeIncrement U (k+1) C)) := hd.2.1
  let η := parentBoundaryCommonBasisMultiplier P Q b 1 L l
  let f := fun x i => η.toFun x * (I v).grad x i - η.grad x i * (v-I v).toFun x
  have heta : η = (parentBoundaryCommonQ3Direction P Q b L (whiteBasis l)).value := by
    simp [η, parentBoundaryCommonBasisMultiplier]
  have hvalue (x : Vec 2) : η.toFun x =
      q3Convolution b L h3Zero (whiteBasis l) x -
        q3Convolution b L h3Zero (whiteBasis l) (cubeCenter P) := by
    rw [heta, parent_boundary_common_q3_direction_value]
  have hgrad (x : Vec 2) (i : Fin 2) : η.grad x i =
      (fderiv ℝ (q3Convolution b L h3Zero (whiteBasis l)) x)
        (basisVec i) := by
    have hj := parent_boundary_common_q3_direction_grad P Q b L (whiteBasis l) x i
    have hderiv : (fderiv ℝ (q3Convolution b L h3Zero
        (whiteBasis l)) x) (basisVec i) =
        q3Convolution b L (mainQ3JetIndex (.first i))
          (whiteBasis l) x := by
      rw [q3Convolution_fderiv_basis b L h3Zero (by decide)]
      fin_cases i <;> norm_num [mainQ3JetIndex, h3Next, h3Zero,
        Model.Q3SpatialJet.count]
    rw [heta]
    exact hj.trans hderiv.symm
  have hcoord (x : Vec 2) (i : Fin 2) :
      (C x).ofLp (l,i) = f x i := by
    rw [parent_boundary_common_finite_row_coordinate]
    simp only [f]
    rw [hvalue, hgrad]
    ring
  have hfield : (fun x => lemmaVPlanarRowField I η v x) =
      (fun x => planarQuarterTurn (f x)) := by
    rw [lemmaVH2_rowField_eq]
  have hp (i : Fin 2) : Summable (fun k => (Real.sqrt 3)^(k+1)*energy U
      (cubeIncrement U (k+1) (fun x => f x i))) := by
    have hc := main_hilbert_coordinate_summable U hmem hsum (l,i)
    have hf : (fun x => f x i) = fun x => (C x).ofLp (l,i) :=
      funext fun x => (hcoord x i).symm
    rw [hf]
    exact hc
  intro i
  change Summable (fun k => (Real.sqrt 3)^(k+1)*energy U
    (cubeIncrement U (k+1) (fun x => lemmaVPlanarRowField I η v x i)))
  have hfi : (fun x => lemmaVPlanarRowField I η v x i) =
      fun x => planarQuarterTurn (f x) i := by
    funext x
    exact congrFun (congrFun hfield x) i
  rw [hfi]
  exact positive_series_quarterTurn U f hp i

end
end ASDExplicitGamma.Native
