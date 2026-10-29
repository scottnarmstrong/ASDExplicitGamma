module

public import ASDExplicitGamma.Inverse.PureFluxGeneratorRowOperator
public import ASDExplicitGamma.Main.Q3ValueColumns
public import ASDExplicitGamma.Main.CubeDirections
public import ASDExplicitGamma.Variational.LemmaVH2RemainderKernel

/-! The actual q3 direction with the one fixed parent center removed. -/

@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory ASDExplicitGamma.Gaussian ASDExplicitGamma.Main
  ASDExplicitGamma.Triadic ASDExplicitGamma.Variational
open scoped BigOperators
noncomputable section

local instance pureFluxCenteredFiniteMeasure (Q : TriadicCube 2) :
    IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
  (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume

def pureFluxH1Constant (Q : TriadicCube 2) (c : ℝ) : H1Function (openCubeSet Q) :=
  H1Function.ofContDiffOnIsOpenBoundedConvexDomain
    (isOpenBoundedConvexDomain_openCubeSet Q) (f := fun _ => c) contDiff_const

theorem pureFluxH1Constant_toFun (Q : TriadicCube 2) (c : ℝ) :
    (pureFluxH1Constant Q c).toFun = fun _ => c := by
  simp [pureFluxH1Constant, H1Function.ofContDiffOnIsOpenBoundedConvexDomain,
    H1Function.ofContDiffOnIsSobolevRegularDomain]

theorem pureFluxH1Constant_grad (Q : TriadicCube 2) (c : ℝ) :
    (pureFluxH1Constant Q c).grad = 0 := by
  funext x i
  simp [pureFluxH1Constant, H1Function.ofContDiffOnIsOpenBoundedConvexDomain,
    H1Function.ofContDiffOnIsSobolevRegularDomain]

/-- Centering at one parent point preserves every actual derivative. -/
def pureFluxQ3CenteredDirection (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0 < l}) (w : WhiteNoise) : PlanarW2Infinity Q where
  value := (mainQ3DirectionW2 Q b L w).value - pureFluxH1Constant Q
    (q3Convolution b L h3Zero w (cubeCenter Q))
  value_memLp_top := by
    have h := (mainQ3DirectionW2 Q b L w).value_memLp_top.sub
      (memLp_const (q3Convolution b L h3Zero w (cubeCenter Q)))
    convert h using 1
    funext x
    simp only [H1Function.sub_toFun, pureFluxH1Constant_toFun, Pi.sub_apply]
  gradient := (mainQ3DirectionW2 Q b L w).gradient
  gradient_eq i := by
    simp only [H1Function.sub_grad, pureFluxH1Constant_grad, Pi.sub_apply,
      Pi.zero_apply, sub_zero]
    exact (mainQ3DirectionW2 Q b L w).gradient_eq i

theorem pureFluxQ3CenteredDirection_value (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0 < l}) (w : WhiteNoise) (x : Vec 2) :
    (pureFluxQ3CenteredDirection Q b L w).value.toFun x =
      q3Convolution b L h3Zero w x -
        q3Convolution b L h3Zero w (cubeCenter Q) := by
  simp only [pureFluxQ3CenteredDirection, H1Function.sub_toFun,
    pureFluxH1Constant_toFun, mainQ3DirectionW2_value]

theorem pureFluxQ3CenteredDirection_grad (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0 < l}) (w : WhiteNoise) (x : Vec 2) (i : Fin 2) :
    (pureFluxQ3CenteredDirection Q b L w).value.grad x i =
      q3Convolution b L (mainQ3JetIndex (.first i)) w x := by
  rw [← congrFun ((pureFluxQ3CenteredDirection Q b L w).gradient_eq i) x]
  change ((mainQ3DirectionW2 Q b L w).gradient.component i).toFun x = _
  rw [congrFun ((mainQ3DirectionW2 Q b L w).gradient_eq i) x]
  exact mainQ3DirectionW2_jet Q b L w (.first i) x

/-- The centered response multiplier in the physical scalar frame. -/
def pureFluxMainQ3CenteredBasisMultiplier (n : ℤ) (b σ : ℝ)
    (L : {l : ℝ // 0 < l}) (l : whiteBasisIndex) :
    H1Function (openCubeSet (originCube 2 n)) :=
  (σ⁻¹ : ℝ) • (pureFluxQ3CenteredDirection (originCube 2 n) b L (whiteBasis l)).value

/-- The full finite value covariance column has the parent-center cap. -/
theorem pureFluxQ3CenteredFiniteValue_norm_sq_le {ι : Type*}
    (e : HilbertBasis ι ℝ WhiteNoise) (s : Finset ι) (b : ℝ)
    (L : {l : ℝ // 0 < l}) (Q : TriadicCube 2) {x : Vec 2} (hx : x ∈ cubeSet Q) :
    ‖mainQ3FiniteValue e s b L x - mainQ3FiniteValue e s b L (cubeCenter Q)‖^2 ≤
      b^2*((78/5:ℝ)/2)*(cubeScaleFactor Q/L.1)^2 := by
  have hd : mainSpatialDistanceSq x (cubeCenter Q) ≤ (cubeScaleFactor Q)^2/2 := by
    simpa only [mainSpatialDistanceSq, Fin.sum_univ_two] using planar_cube_center_distance_sq Q hx
  have h := (main_q3_value_difference_sq e s b L x (cubeCenter Q)).trans
    (mul_le_mul_of_nonneg_left hd (by positivity : 0 ≤ (78/5:ℝ)*b^2/L.1^2))
  exact h.trans_eq (by ring)

end
end ASDExplicitGamma.Inverse
