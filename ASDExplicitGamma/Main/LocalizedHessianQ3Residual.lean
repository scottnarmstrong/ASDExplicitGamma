module

public import ASDExplicitGamma.Main.Q3ResidualCoordinates
public import ASDExplicitGamma.Gaussian.CovarianceRow
public import ASDExplicitGamma.Variational.LemmaVH2Row

import ASDExplicitGamma.Main.CMCovariance

/-! The actual localized q3 row split into its cell-mean flat part and
centered source residual. -/

@[expose] public section

namespace ASDExplicitGamma.Main

open Homogenization ASDExplicitGamma.Gaussian ASDExplicitGamma.Model ASDExplicitGamma.Triadic
  ASDExplicitGamma.Variational

/-- The q3 DIAG row is exactly the centered receiver residual plus the
cell-mean flat row. This is the modewise split used before the signed
covariance contraction. -/
theorem main_q3_localized_row_centered_residual_split
    {ι : Type*} (e : HilbertBasis ι ℝ WhiteNoise)
    (b : ℝ) (L : {l : ℝ // 0 < l}) (Q : TriadicCube 2) (m : ℕ)
    (φ : H1Function (openCubeSet Q)) (U : TriadicCube 2) (l : ι)
    (x : Vec 2) :
    lemmaVPlanarRowField (diagInterpolant Q m)
        (mainQ3DirectionW2 Q b L (e l)).value φ x =
      planarQuarterTurn (fun i =>
        mainQ3ResidualCoordinate e b L Q m φ U l x i +
          cubeAverage U (q3Convolution b L h3Zero (e l)) *
            (diagInterpolant Q m φ).grad x i) := by
  let η := (mainQ3DirectionW2 Q b L (e l)).value
  let f := q3Convolution b L h3Zero (e l)
  let I := diagInterpolant Q m
  have hηfun : η.toFun = f := by
    funext y
    exact mainQ3DirectionW2_value Q b L (e l) y
  have hindex (i : Fin 2) : mainQ3JetIndex (.first i) =
      h3Next h3Zero i (by decide) := by
    fin_cases i <;> norm_num [mainQ3JetIndex, Q3SpatialJet.count,
      h3Next, h3Zero]
  have hηgrad (i : Fin 2) : η.grad x i =
      (fderiv ℝ f x) (basisVec i) := by
    have hjet := mainQ3DirectionW2_jet Q b L (e l) (.first i) x
    change η.grad x i = q3Convolution b L
      (mainQ3JetIndex (.first i)) (e l) x at hjet
    rw [hindex] at hjet
    have hderiv := q3Convolution_fderiv_basis b L h3Zero
      (by decide) (e l) x i
    exact hjet.trans hderiv.symm
  rw [lemmaVH2_rowField_eq]
  apply congrArg planarQuarterTurn
  funext i
  simp only [mainQ3ResidualCoordinate, H1Function.sub_toFun]
  rw [hηfun, hηgrad]
  ring

end ASDExplicitGamma.Main

end
