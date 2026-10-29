module

public import ASDExplicitGamma.Main.HotPatchRow
public import ASDExplicitGamma.Main.HotCovPairedDrop

/-! MA-E-COVARIANCE, step 2: the hot source on a tile.  On the open source
cell `U`, `(f')_n` is `-J(ψ ∇Iw - ∇ψ (w - Iw + φ_U))`, where `ψ = ψ_n` is the
`n`-th Gaussian mode of the source, `I` the DIAG interpolant and `φ_U` the cell
corrector.  This exposes the frozen part `-a_{n,U} J ∇Iw` and the residual. -/

@[expose] public section

namespace ASDExplicitGamma.Main

open Homogenization MeasureTheory ASDExplicitGamma.Gaussian
  ASDExplicitGamma.Model ASDExplicitGamma.Response ASDExplicitGamma.Triadic
  ASDExplicitGamma.Variational ASDExplicitGamma.Scalar ASDExplicitGamma.Native
open scoped BigOperators

noncomputable section

/-- The `n`-th Gaussian mode of the source at the shell `(b, L)`. -/
abbrev hotCovPsi (b : ℝ) (L : {l : ℝ // 0 < l}) (n : whiteBasisIndex) : Vec 2 → ℝ :=
  q3Convolution b L h3Zero (whiteBasis n)

/-- Its `i`-th spatial derivative. -/
def hotCovPsiGrad (b : ℝ) (L : {l : ℝ // 0 < l}) (n : whiteBasisIndex) (i : Fin 2)
    (x : Vec 2) : ℝ :=
  (fderiv ℝ (q3Convolution b L h3Zero (whiteBasis n)) x) (basisVec i)

/-- The DIAG interpolant gradient of the coarse potential `w_P` of the load `P`. -/
def hotCovZ (Q : TriadicCube 2) (d : ℕ) (nu sigma : ℝ) (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (P : BlockVec 2) (x : Vec 2) : Vec 2 :=
  (diagInterpolant Q d (hotPatchPotential Q d nu sigma hnu hsigma k P).toH1Function).grad x

/-- Pointwise form of the hot source on an open cell, for one fresh mode. -/
theorem hot_cov_source_cell_formula (Q : TriadicCube 2) (d : ℕ) (nu sigma : ℝ)
    (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (b : ℝ) (L : {l : ℝ // 0 < l})
    (n : whiteBasisIndex) (P : BlockVec 2)
    (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth Q d)
    (x : Vec 2) (hx : x ∈ openCubeSet U) :
    (hotPatchSource Q d d nu sigma hnu hsigma k b L n P x).2 =
      planarQuarterTurn (fun i => -(hotCovPsi b L n x * hotCovZ Q d nu sigma hnu hsigma k P x i -
        hotCovPsiGrad b L n i x *
          ((hotPatchPotential Q d nu sigma hnu hsigma k P).toH1Function -
            diagInterpolant Q d (hotPatchPotential Q d nu sigma hnu hsigma k P).toH1Function).toFun x -
        hotCovPsiGrad b L n i x *
          (oldSignedCellFirstCorrector Q U
            (openCubeSet_subset_of_mem_descendantsAtDepth hU) nu sigma hnu hsigma k
            (fun _ => P) (memLp_const P)).toH1Function.toFun x)) := by
  classical
  let I := diagInterpolant Q d
  let w := hotPatchPotential Q d nu sigma hnu hsigma k P
  let φ := hotGluedCorrector Q d nu sigma hnu hsigma k P
  let φU := oldSignedCellFirstCorrector Q U
    (openCubeSet_subset_of_mem_descendantsAtDepth hU) nu sigma hnu hsigma k
    (fun _ => P) (memLp_const P)
  let η := (mainQ3DirectionW2 Q b L (whiteBasis n)).value
  have hvalue (x : Vec 2) : η.toFun x = hotCovPsi b L n x := by
    rw [mainQ3DirectionW2_value]
  have hgrad (x : Vec 2) (i : Fin 2) : η.grad x i = hotCovPsiGrad b L n i x := by
    have hj := mainQ3DirectionW2_jet Q b L (whiteBasis n) (.first i) x
    change (mainQ3DirectionW2 Q b L (whiteBasis n)).value.grad x i =
      q3Convolution b L (mainQ3JetIndex (.first i)) (whiteBasis n) x at hj
    have hderiv : (fderiv ℝ (q3Convolution b L h3Zero
        (whiteBasis n)) x) (basisVec i) =
        q3Convolution b L (mainQ3JetIndex (.first i))
          (whiteBasis n) x := by
      rw [q3Convolution_fderiv_basis b L h3Zero (by decide)]
      fin_cases i <;> norm_num [mainQ3JetIndex, h3Next, h3Zero,
        Model.Q3SpatialJet.count]
    exact hj.trans hderiv.symm
  have hφ : φ.toH1Function x = φU.toH1Function x :=
    hot_glued_corrector_cell Q d nu sigma hnu hsigma k P U hU x hx
  have e1 := congrFun (lemmaVH2_rowField_eq I η w.toH1Function) x
  have e2 := congrFun (lemmaVH2_rowField_eq
    (0 : H1Function (openCubeSet Q) →ₗ[ℝ] H1Function (openCubeSet Q)) η φ.toH1Function) x
  simp only [hotPatchSource, oldSignedLocalizedPotentialShear, Prod.snd_add]
  rw [e1, e2]
  funext i
  fin_cases i <;>
    simp [planarQuarterTurn, hotCovZ, hφ, hvalue, hgrad] <;> ring

end

end ASDExplicitGamma.Main
