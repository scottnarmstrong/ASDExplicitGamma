module

public import ASDExplicitGamma.Cold.SquareOptimizerProjection

/-! # The exact optimizer projection gap on the actual triadic partition -/

@[expose] public section
noncomputable section
open MeasureTheory Homogenization
open ASDExplicitGamma.Triadic
open scoped BigOperators
namespace ASDExplicitGamma.Cold

/-- Actual depth-r descendants of a square. -/
abbrev SquareCells (Q : TriadicCube 2) (r : ℕ) := {R // R ∈ descendantsAtDepth Q r}

/-- The equal-volume average over the actual cells. -/
def squareCellMean (Q : TriadicCube 2) (r : ℕ) (f : SquareCells Q r → ℝ) : ℝ :=
  ((descendantsAtDepth Q r).card : ℝ)⁻¹ * ∑ R, f R

/-- Linearity of the finite cell average. -/
theorem squareCellMean_add (Q : TriadicCube 2) (r : ℕ) (f g : SquareCells Q r → ℝ) :
    squareCellMean Q r (fun R => f R + g R) = squareCellMean Q r f + squareCellMean Q r g := by
  unfold squareCellMean
  rw [Finset.sum_add_distrib]
  ring

/-- Scalar linearity of the finite cell average. -/
theorem squareCellMean_mul (Q : TriadicCube 2) (r : ℕ) (c : ℝ) (f : SquareCells Q r → ℝ) :
    squareCellMean Q r (fun R => c*f R) = c*squareCellMean Q r f := by
  unfold squareCellMean
  rw [← Finset.mul_sum]
  ring

/-- Open-square volume averages are the same normalized averages used by the cell projection. -/
theorem square_volumeAverage_eq_cubeAverage (Q : TriadicCube 2) (f : Vec 2 → ℝ) :
    volumeAverage (openCubeSet Q) f = cubeAverage Q f := by
  unfold volumeAverage cubeAverage
  rw [volume_openCubeSet_toReal, setIntegral_cubeSet_eq_setIntegral_openCubeSet]

/-- Actual integrated densities, rather than pointwise stationary densities, partition exactly. -/
theorem squareCellMean_volumeAverage (Q : TriadicCube 2) (r : ℕ) {f : Vec 2 → ℝ}
    (hf : IntegrableOn f (openCubeSet Q)) :
    squareCellMean Q r (fun R => volumeAverage (openCubeSet R.val) f) =
      volumeAverage (openCubeSet Q) f := by
  simp_rw [square_volumeAverage_eq_cubeAverage]
  rw [cubeAverage_eq_descendantsAverage_cubeAverage_of_integrableOn Q r f
    (integrableOn_cubeSet_iff_integrableOn_openCubeSet.mpr hf)]
  unfold squareCellMean descendantsAverage
  congr 1
  exact Finset.sum_attach (descendantsAtDepth Q r) (fun R => cubeAverage R f)

/-- Restrict the actual parent harmonic function to an actual cell. -/
def squareCellRestriction (Q : TriadicCube 2) {a : CoeffField 2} {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (v : AHarmonicFunction a (openCubeSet Q)) {r : ℕ} (R : SquareCells Q r) :
    AHarmonicFunction a (openCubeSet R.val) :=
  v.restrictOfIsEllipticFieldOn (isOpen_openCubeSet Q) (isOpen_openCubeSet R.val)
    (openCubeSet_subset_of_mem_descendantsAtDepth R.property)
    (hEll.mono (measurableSet_openCubeSet R.val)
      (openCubeSet_subset_of_mem_descendantsAtDepth R.property))

/-- The actual own-cell-minus-parent harmonic difference. -/
def squareCellDifference (Q : TriadicCube 2) {a : CoeffField 2} {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (v : AHarmonicFunction a (openCubeSet Q)) {r : ℕ}
    (f : ∀ R : SquareCells Q r, AHarmonicFunction a (openCubeSet R.val)) (R : SquareCells Q r) :
    AHarmonicFunction a (openCubeSet R.val) :=
  squareHarmonicDifference R.val (hEll.mono (measurableSet_openCubeSet R.val)
    (openCubeSet_subset_of_mem_descendantsAtDepth R.property)) (f R) (squareCellRestriction Q hEll v R)

/-- The genuine pathwise projection-gap identity on all actual descendants. No gap premise
or optimizer independence is assumed. -/
theorem square_optimizer_partition_gap (Q : TriadicCube 2) {a : CoeffField 2} {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a) (p q : Vec 2) (r : ℕ)
    (v : AHarmonicFunction a (openCubeSet Q)) (hv : IsResponseMaximizer (openCubeSet Q) p q a v)
    (f : ∀ R : SquareCells Q r, AHarmonicFunction a (openCubeSet R.val))
    (hf : ∀ R, IsResponseMaximizer (openCubeSet R.val) p q a (f R)) :
    squareCellMean Q r (fun R => volumeAverage (openCubeSet R.val)
      (scalarVariationEnergyIntegrand a (squareCellDifference Q hEll v f R))) =
      squareCellMean Q r (fun R => volumeAverage (openCubeSet R.val) (scalarVariationEnergyIntegrand a (f R))) -
      volumeAverage (openCubeSet Q) (scalarVariationEnergyIntegrand a v) := by
  have hInt := ResponseLinearIntegrabilityData.of_isEllipticFieldOn hEll
  have heq (R : SquareCells Q r) :
      volumeAverage (openCubeSet R.val) (scalarVariationEnergyIntegrand a (squareCellDifference Q hEll v f R)) =
      volumeAverage (openCubeSet R.val) (scalarVariationEnergyIntegrand a (f R)) +
      volumeAverage (openCubeSet R.val) (scalarVariationEnergyIntegrand a v) -
      2*(volumeAverage (openCubeSet R.val) (fun x => vecDot q (v.toH1.grad x)) -
        volumeAverage (openCubeSet R.val) (fun x => vecDot p (matVecMul (a x) (v.toH1.grad x)))) :=
    square_optimizer_difference_energy R.val _ p q (f R) (squareCellRestriction Q hEll v R) (hf R)
  simp_rw [heq]
  have hrewrite : (fun R : SquareCells Q r =>
      volumeAverage (openCubeSet R.val) (scalarVariationEnergyIntegrand a (f R)) +
      volumeAverage (openCubeSet R.val) (scalarVariationEnergyIntegrand a v) -
      2*(volumeAverage (openCubeSet R.val) (fun x => vecDot q (v.toH1.grad x)) -
        volumeAverage (openCubeSet R.val) (fun x => vecDot p (matVecMul (a x) (v.toH1.grad x))))) =
      (fun R => volumeAverage (openCubeSet R.val) (scalarVariationEnergyIntegrand a (f R)) +
        (volumeAverage (openCubeSet R.val) (scalarVariationEnergyIntegrand a v) +
        ((-2)*volumeAverage (openCubeSet R.val) (fun x => vecDot q (v.toH1.grad x)) +
          2*volumeAverage (openCubeSet R.val) (fun x => vecDot p (matVecMul (a x) (v.toH1.grad x)))))) := by
    funext R
    ring
  rw [hrewrite]
  simp_rw [squareCellMean_add, squareCellMean_mul]
  rw [squareCellMean_volumeAverage Q r (hInt.energy v),
    squareCellMean_volumeAverage Q r (hInt.grad q v),
    squareCellMean_volumeAverage Q r (hInt.flux p v)]
  have hself := square_optimizer_linear_self Q hEll p q v hv
  linarith only [hself]

end ASDExplicitGamma.Cold
