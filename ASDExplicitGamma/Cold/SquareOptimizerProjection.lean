module

public import ASDExplicitGamma.Cold.PlateauGram

/-! # The actual first-variation identity behind the cold projection gap -/

@[expose] public section
noncomputable section
open MeasureTheory Homogenization
open ASDExplicitGamma.Triadic
namespace ASDExplicitGamma.Cold

/-- Actual harmonic subtraction, with its local integrability obtained from source ellipticity. -/
def squareHarmonicDifference (Q : TriadicCube 2) {a : CoeffField 2} {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (f v : AHarmonicFunction a (openCubeSet Q)) : AHarmonicFunction a (openCubeSet Q) :=
  AHarmonicFunction.subOfIntegrable f v
    ((ResponseLinearIntegrabilityData.of_isEllipticFieldOn hEll).weakFlux f)
    ((ResponseLinearIntegrabilityData.of_isEllipticFieldOn hEll).weakFlux v)

/-- The exact energy identity on an own cell, proved from the genuine maximizer first variation.
Summing its linear terms over the parent partition gives the source projection gap. -/
theorem square_optimizer_difference_energy (Q : TriadicCube 2) {a : CoeffField 2} {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a) (p q : Vec 2)
    (f v : AHarmonicFunction a (openCubeSet Q))
    (hf : IsResponseMaximizer (openCubeSet Q) p q a f) :
    volumeAverage (openCubeSet Q) (scalarVariationEnergyIntegrand a (squareHarmonicDifference Q hEll f v)) =
      volumeAverage (openCubeSet Q) (scalarVariationEnergyIntegrand a f) +
      volumeAverage (openCubeSet Q) (scalarVariationEnergyIntegrand a v) -
      2*(volumeAverage (openCubeSet Q) (fun x => vecDot q (v.toH1.grad x)) -
        volumeAverage (openCubeSet Q) (fun x => vecDot p (matVecMul (a x) (v.toH1.grad x)))) := by
  rw [squareHarmonicDifference,
    volumeAverage_scalarVariationEnergyIntegrand_subOfIntegrable (openCubeSet Q) a
      (ResponseLinearIntegrabilityData.of_isEllipticFieldOn hEll),
    ← basic_cg_identities_first_variation_eq_of_isResponseMaximizer (openCubeSet Q) a p q
      (ResponseLinearIntegrabilityData.of_isEllipticFieldOn hEll) f hf v]

/-- At the terminal optimizer itself, the linear response equals its full energy. -/
theorem square_optimizer_linear_self (Q : TriadicCube 2) {a : CoeffField 2} {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a) (p q : Vec 2)
    (v : AHarmonicFunction a (openCubeSet Q))
    (hv : IsResponseMaximizer (openCubeSet Q) p q a v) :
    volumeAverage (openCubeSet Q) (fun x => vecDot q (v.toH1.grad x)) -
      volumeAverage (openCubeSet Q) (fun x => vecDot p (matVecMul (a x) (v.toH1.grad x))) =
      volumeAverage (openCubeSet Q) (scalarVariationEnergyIntegrand a v) :=
  basic_cg_identities_first_variation_eq_of_isResponseMaximizer (openCubeSet Q) a p q
    (ResponseLinearIntegrabilityData.of_isEllipticFieldOn hEll) v hv v

/-- A matched optimizer's actual energy is twice its actual scalar response. -/
theorem square_optimizer_energy (Q : TriadicCube 2) {a : CoeffField 2} {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a) (p q : Vec 2)
    (v : AHarmonicFunction a (openCubeSet Q))
    (hv : IsResponseMaximizer (openCubeSet Q) p q a v) :
    volumeAverage (openCubeSet Q) (scalarVariationEnergyIntegrand a v) =
      2*ResponseJ (openCubeSet Q) p q a := by
  have h := responseJ_energy_of_isResponseMaximizer (openCubeSet Q) a p q v hv
    ((ResponseLinearIntegrabilityData.of_isEllipticFieldOn hEll).weakFlux v)
    ((ResponseLinearIntegrabilityData.of_isEllipticFieldOn hEll).response p q v)
    ((ResponseLinearIntegrabilityData.of_isEllipticFieldOn hEll).firstVariation p q v v)
    ((ResponseLinearIntegrabilityData.of_isEllipticFieldOn hEll).energy v)
  linarith only [h]

end ASDExplicitGamma.Cold
