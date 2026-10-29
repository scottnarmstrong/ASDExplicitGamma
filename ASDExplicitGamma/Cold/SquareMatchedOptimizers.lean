module

public import ASDExplicitGamma.Cold.SquareMatchedEnergy

/-! # Actual matched primal and adjoint optimizer families -/

@[expose] public section
noncomputable section
open MeasureTheory Homogenization
open ASDExplicitGamma.Triadic
open scoped BigOperators
namespace ASDExplicitGamma.Cold

/-- The four actual harmonic optimizers used by the source cold argument. -/
structure SquareMatchedOptimizers (Q : TriadicCube 2) (a : CoeffField 2) where
  primal : Fin 2 → AHarmonicFunction a (openCubeSet Q)
  adjoint : Fin 2 → AHarmonicFunction (adjointCoeffField a) (openCubeSet Q)
  primal_max : ∀ i, IsResponseMaximizer (openCubeSet Q) (Pi.single i 1) (Pi.single i 1) a (primal i)
  adjoint_max : ∀ i, IsResponseMaximizer (openCubeSet Q) (Pi.single i 1) (Pi.single i 1)
    (adjointCoeffField a) (adjoint i)

/-- The actual four-load total energy density. -/
def squareMatchedDensity (Q : TriadicCube 2) {a : CoeffField 2} (v : SquareMatchedOptimizers Q a)
    (x : Vec 2) : ℝ := ∑ i : Fin 2, (scalarVariationEnergyIntegrand a (v.primal i) x +
      scalarVariationEnergyIntegrand (adjointCoeffField a) (v.adjoint i) x)

/-- All four energy densities are locally integrable from source ellipticity. -/
theorem integrable_squareMatchedDensity (Q : TriadicCube 2) {a : CoeffField 2} {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a) (v : SquareMatchedOptimizers Q a) :
    IntegrableOn (squareMatchedDensity Q v) (openCubeSet Q) := by
  apply integrable_finsetSum
  intro i _
  exact ((ResponseLinearIntegrabilityData.of_isEllipticFieldOn hEll).energy (v.primal i)).add
    ((ResponseLinearIntegrabilityData.of_isEllipticFieldOn
      (isEllipticFieldOn_adjointCoeffField hEll)).energy (v.adjoint i))

/-- The ordinary integrated total energy is exactly twice the actual trace defect. -/
theorem squareMatchedDensity_average (Q : TriadicCube 2) {a : CoeffField 2} {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a) (v : SquareMatchedOptimizers Q a) :
    volumeAverage (openCubeSet Q) (squareMatchedDensity Q v) = 2*traceDefect (openCubeSet Q) a 1 := by
  unfold squareMatchedDensity
  rw [volumeAverage_sum (s := Finset.univ) (f := fun i x =>
    scalarVariationEnergyIntegrand a (v.primal i) x +
      scalarVariationEnergyIntegrand (adjointCoeffField a) (v.adjoint i) x)
    (fun i _ => ((ResponseLinearIntegrabilityData.of_isEllipticFieldOn hEll).energy (v.primal i)).add
      ((ResponseLinearIntegrabilityData.of_isEllipticFieldOn
        (isEllipticFieldOn_adjointCoeffField hEll)).energy (v.adjoint i)))]
  have heq (i : Fin 2) : volumeAverage (openCubeSet Q)
      (fun x => scalarVariationEnergyIntegrand a (v.primal i) x +
        scalarVariationEnergyIntegrand (adjointCoeffField a) (v.adjoint i) x) =
      volumeAverage (openCubeSet Q) (scalarVariationEnergyIntegrand a (v.primal i)) +
        volumeAverage (openCubeSet Q) (scalarVariationEnergyIntegrand (adjointCoeffField a) (v.adjoint i)) :=
    volumeAverage_add ((ResponseLinearIntegrabilityData.of_isEllipticFieldOn hEll).energy (v.primal i))
      ((ResponseLinearIntegrabilityData.of_isEllipticFieldOn
        (isEllipticFieldOn_adjointCoeffField hEll)).energy (v.adjoint i))
  simp_rw [heq]
  exact square_matched_optimizer_energy Q hEll v.primal v.adjoint v.primal_max v.adjoint_max

/-- The total actual four-load energy density is nonnegative on its cell. -/
theorem squareMatchedDensity_nonneg (Q : TriadicCube 2) {a : CoeffField 2} {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a) (v : SquareMatchedOptimizers Q a)
    {x : Vec 2} (hx : x ∈ openCubeSet Q) : 0 ≤ squareMatchedDensity Q v x :=
  Finset.sum_nonneg fun i _ => add_nonneg
    (scalarVariationEnergyIntegrand_nonneg_of_isEllipticFieldOn (openCubeSet Q) a hEll (v.primal i) x hx)
    (scalarVariationEnergyIntegrand_nonneg_of_isEllipticFieldOn (openCubeSet Q) (adjointCoeffField a)
      (isEllipticFieldOn_adjointCoeffField hEll) (v.adjoint i) x hx)

end ASDExplicitGamma.Cold
