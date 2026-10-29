module

public import ASDExplicitGamma.Native.OldSignedActualTrialExpansion
public import ASDExplicitGamma.Native.OldSignedFlatPatchedData
public import ASDExplicitGamma.Native.OldSignedFlatBoundaryEnergy
public import ASDExplicitGamma.Native.OldSignedSelectedSourceBudget

/-! Named terms of the literal actual OLD signed trial. Every field is
instantiated below from the same parent coefficient and fresh direction. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Gaussian Main Triadic
noncomputable section

/-- The nine complete-mode families in the signed OLD trial expansion. -/
structure OldSignedTrialTerms where
  flat : whiteBasisIndex → ℝ
  source : whiteBasisIndex → ℝ
  mixedPlus : whiteBasisIndex → ℝ
  mixedMinus : whiteBasisIndex → ℝ
  feedbackPlus : whiteBasisIndex → ℝ
  feedbackSource : whiteBasisIndex → ℝ
  feedbackMinus : whiteBasisIndex → ℝ
  covarianceTop : whiteBasisIndex → ℝ
  covarianceBottom : whiteBasisIndex → ℝ

/-- Actual source instantiation of the signed trial families. The flat
baseline includes the negative Dirichlet tangent; bottom covariance includes
its opposite, preserving the exact total before either is estimated. -/
def oldSignedTrialTerms (Q : TriadicCube 2) (depth : ℕ) (nu sigma : ℝ)
    (hnu : 0<nu) (hsigma : 0<sigma) (k : ResponseCoefficient (openCubeSet Q))
    (b : ℝ) (L : {l : ℝ // 0<l}) : OldSignedTrialTerms :=
  let E := oldSignedEnergyPairing Q nu sigma k
  let C := fun n => oldSignedPointwiseShear (q3Convolution b L h3Zero (whiteBasis n))
  let S := fun P => oldSignedFrameCanonicalField Q nu sigma hnu hsigma k P
  let Z := fun plus n i => oldSignedPatchedFlat Q depth nu sigma hnu hsigma k b L plus n i
  let R := fun n P => oldSignedPatchedOldError Q depth depth nu sigma hnu hsigma k b L n P
  let F := fun plus n i => oldSignedFlatInput Q b L plus n i
  let H := fun n P => oldSignedFrameOldErrorSource Q depth nu sigma hnu hsigma k b L n P
  { flat := fun n => (∑ i : Fin 2,E (Z true n i) (Z true n i))+
      (∑ i : Fin 2,E (Z false n i) (Z false n i))-2*oldSignedFlatDirichletModeEnergy Q b L n
    source := fun n => ∑ c : BlockCoord 2,E (R n (blockBasis c)) (R n (blockBasis c))
    mixedPlus := fun n => ∑ i : Fin 2,(E (Z true n i) (R n (oldSignedFlatLoad true i))-
      volumeAverage (openCubeSet Q) (fun x => vecDot (F true n i x).2 (H n (oldSignedFlatLoad true i) x).2))
    mixedMinus := fun n => ∑ i : Fin 2,(E (Z false n i) (R n (oldSignedFlatLoad false i))-
      volumeAverage (openCubeSet Q) (fun x => vecDot (F false n i x).2 (H n (oldSignedFlatLoad false i) x).2))
    feedbackPlus := fun n => ∑ i : Fin 2,E (S (blockBasis (Sum.inl i))) (C n (Z true n i))
    feedbackSource := fun n => ∑ c : BlockCoord 2,E (S (blockBasis c)) (C n (R n (blockBasis c)))
    feedbackMinus := fun n => (∑ i : Fin 2,E (S (blockBasis (Sum.inr i))) (C n (Z false n i)))-
      ∑ i : Fin 2,E (S (blockBasis (Sum.inr i))) (C n (F false n i))
    covarianceTop := fun n => 2*∑ i : Fin 2,volumeAverage (openCubeSet Q) (fun x =>
      vecDot (oldSignedFlatPlusBlock Q b L n i x).2 (H n (basisVec i,0) x).2)
    covarianceBottom := fun n => 2*∑ i : Fin 2,(-E (S (0,basisVec i)) (C n (F false n i))+
      ∑ j : Fin 2,energy Q (fun x => mainFlatMinusCoordinate Q b L n (i,j) x)) }

/-- The exact signed combination of the nine physical term families. -/
def OldSignedTrialTerms.total (T : OldSignedTrialTerms) (n : whiteBasisIndex) : ℝ :=
  T.flat n+T.source n+2*T.mixedPlus n-2*T.mixedMinus n+
    2*T.feedbackPlus n+2*T.feedbackSource n-2*T.feedbackMinus n+
    T.covarianceTop n+T.covarianceBottom n

end
end ASDExplicitGamma.Native
