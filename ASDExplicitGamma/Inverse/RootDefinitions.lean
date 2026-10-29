module

public import ASDExplicitGamma.Inverse.StoppedSelectedRootCertificates
public import ASDExplicitGamma.Inverse.StoppedResetDensityEZ
public import ASDExplicitGamma.Inverse.StoppedDiameterCharge
public import ASDExplicitGamma.Inverse.WhitneyRootLayerGeometry
public import ASDExplicitGamma.Inverse.ClippedMatrixEvent
public import ASDExplicitGamma.Model.Cutoff
public import Mathlib.Analysis.CStarAlgebra.Matrix

/-! Exact carriers and source positive series for the fixed root and
selected-height interfaces. These definitions assert no unproved estimate. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Model
open scoped ENNReal Matrix.Norms.Elementwise
noncomputable section

/-- The four distinct fixed source rows. -/
inductive RootRow where
  | globalInverse | localInverse | firstLocal | full
  deriving DecidableEq

def rootH0 : RootRow → ℕ
  | .globalInverse => 333
  | _ => 377

def rootTau : RootRow → ℝ
  | .full => 5000000000000000
  | _ => 10000000000

def rootWaveTuple : RootRow → WaveGateTuple
  | .full => .full
  | _ => .inverse

def rootMeanCap : RootRow → ℝ
  | .globalInverse | .localInverse => 10747/10000
  | _ => 29/25

def rootQ : RootRow → ℝ
  | .full => Numerics.Inverse.invFullQ
  | _ => Numerics.Inverse.invInverseQ

def rootMomentCutoff : RootRow → ℝ
  | .full => 1232
  | _ => 600

def rootResponseEnvelope (t : ℝ) : ℝ := 1+t+Real.sqrt (t*(t+2))

def rootEdelta (r : RootRow) : ℝ :=
  Real.exp ((17444/10000:ℝ)*(1+rootTau r)*(10*waveGateEta (rootWaveTuple r)))

def rootLayerSum (t : ℝ) : ℝ :=
  ∑' k : ℕ, bankLayerWeight k*(3:ℝ)^(t*(localizationProfileDepth (k+1):ℝ))

/-- Literal L_i of the source, in the row's true source normalization. -/
def rootLi (γ : ℝ) (r : RootRow) : ℝ :=
  rootEdelta r*(rootMeanCap r+3*(planarGradientCharge 40+1)*
    rootResponseEnvelope (6*rootTau r)*densityMomentBudget (rootQ r) 2 (rootMomentCutoff r))*
      rootLayerSum (2*γ)

/-- Actual finite deterministic attenuation, with the full ultraviolet cutoff
and the completed m law as its base; no new scalar frame is assigned. -/
def attenuatedCoefficient (M : ABKModel 2) (m J : ℤ) (weights : ℤ → ℝ)
    (ω : Cutoff.CutoffSample 2) : Vec 2 → Mat 2 :=
  fun x => Cutoff.coefficientCutoff M.nu m ω x+
    ∑ k ∈ Finset.Ioc m J, weights k • (ω.val k).forgetShell x

/-- The literal source inverse response in the true completed m frame. -/
def rootInverseResponse (M : ABKModel 2) (Q : TriadicCube 2) (m J : ℤ)
    (weights : ℤ → ℝ) (ω : Cutoff.CutoffSample 2) : ℝ :=
  (Annealed.sigmaBar M m:ℝ)*‖Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ)
    (coarseBlockMatrix (cubeSet Q) (attenuatedCoefficient M m J weights ω)).lowerRight‖

/-- Source H3 on the actual old history-clipped inverse block, uniformly over
every old label and physical cell. It contains no target-response assertion. -/
def ClippedInverseMeanInput (M : ABKModel 2) (m : ℤ) (r : RootRow) : Prop :=
  ∀ n < m, ∀ U : TriadicCube 2, U.scale=n-40 → ∀ v : Vec 2,
    fullMatrixQuadratic (toFullBlockVec (0,v))
      (∫ ω, clippedCellMatrix M n U (rootTau r) ω ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
        rootMeanCap r*dotProduct v v

/-- Deterministic height/layer label of the complete positive source series. -/
def rootLayerOldLabel (Q : TriadicCube 2) (H0 : ℕ) (hk : ℕ × ℕ) : ℤ :=
  Q.scale-resetDepth (H0+hk.1) (hk.2+1)+40

/-- The actual centered full-matrix layer fluctuation, with physical fine-cell
weights and no cluster mask. -/
def rootCenteredLayerMatrix (M : ABKModel 2) (Q : TriadicCube 2) (r : RootRow)
    (hk : ℕ × ℕ) (ω : Cutoff.CutoffSample 2) : FullBlockMat 2 :=
  ∑ U ∈ whitneyRootLayer Q (rootH0 r+hk.1) (hk.2+1),
    ((volume (cubeSet U)).toReal/(volume (cubeSet Q)).toReal) •
      (clippedCellMatrix M (rootLayerOldLabel Q (rootH0 r) hk) U (rootTau r) ω-
        ∫ ζ, clippedCellMatrix M (rootLayerOldLabel Q (rootH0 r) hk) U (rootTau r) ζ
          ∂(Cutoff.cutoffSampleLaw M).toMeasure)

/-- Positive largest directional deviation of the actual inverse compression,
not an entrywise positive part or a trace. -/
def rootMatrixPositiveError (M : ABKModel 2) (Q : TriadicCube 2) (r : RootRow)
    (hk : ℕ × ℕ) (ω : Cutoff.CutoffSample 2) : ℝ :=
  max 0 (sSup {a : ℝ | ∃ v : Vec 2, dotProduct v v=1 ∧
    a=fullMatrixQuadratic (toFullBlockVec (0,v)) (rootCenteredLayerMatrix M Q r hk ω)})

/-- Literal complete positive series (8.7). The extended carrier retains its
meaning even before finiteness is proved; it is never a difference of norms. -/
def positiveRootError (M : ABKModel 2) (Q : TriadicCube 2) (r : RootRow)
    (ω : Cutoff.CutoffSample 2) : ℝ≥0∞ :=
  ENNReal.ofReal (rootEdelta r)*∑' hk : ℕ × ℕ,
    ENNReal.ofReal ((3:ℝ)^(2*M.gamma*(localizationResetAbscissa (rootH0 r-38) hk.1 hk.2:ℝ)))*
      (ENNReal.ofReal (rootMatrixPositiveError M Q r hk ω)+
        ENNReal.ofReal (rootResponseEnvelope (6*rootTau r)*(planarGradientCharge 40+1))*
          ∑ e : Fin 3, ENNReal.ofReal (resetDensityExcess M Q (rootH0 r) (rootTau r)
            (waveGateEta (rootWaveTuple r)) (rootQ r) (rootMomentCutoff r) 2 hk e ω))

def rootMatrixErrorBudget (γ p : ℝ) (r : RootRow) : ℝ :=
  rootEdelta r*256*Real.sqrt p*rootResponseEnvelope (rootTau r)*
    ∑' hk : ℕ × ℕ, Real.sqrt (bankLayerWeight hk.2)*
      (3:ℝ)^(2*γ*(localizationResetAbscissa (rootH0 r-38) hk.1 hk.2:ℝ))*
      (3:ℝ)^(-((localizationResetAbscissa (rootH0 r-38) hk.1 hk.2:ℝ)+1))

def rootDensityErrorBudget (γ : ℝ) (r : RootRow) : ℝ :=
  rootEdelta r*rootResponseEnvelope (6*rootTau r)*
    densityEZ γ (planarGradientCharge 40) (rootH0 r-38)

/-- Retained PE alternative for the same actual positive density series. -/
def rootDensityRetainedBudget (γ p : ℝ) (r : RootRow) : ℝ :=
  rootEdelta r*rootResponseEnvelope (6*rootTau r)*
    densityD2 (rootQ r) p (rootMomentCutoff r) γ (planarGradientCharge 40) (rootH0 r-38)

/-- Exact intended pointwise-root conclusion, with the actual positive error
series and all real orders on one interface. This definition asserts no proof. -/
def PointwiseRootConclusion (M : ABKModel 2) (Q : TriadicCube 2) (m J : ℤ)
    (weights : ℤ → ℝ) (r : RootRow) : Prop :=
  Measurable (positiveRootError M Q r) ∧
  (∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
    ENNReal.ofReal (rootInverseResponse M Q m J weights ω) ≤
      ENNReal.ofReal ((3:ℝ)^(2*M.gamma*|((m-Q.scale+1:ℤ):ℝ)|))*
        (ENNReal.ofReal (rootLi M.gamma r)*
          selectedHeightClock M.gamma (q3StoppedHeight M Q (rootH0 r) (rootTau r)
            (waveGateEta (rootWaveTuple r))) ω+positiveRootError M Q r ω)) ∧
  ∀ p : ℝ, 2 ≤ p → p ≤ 256 →
    eLpNorm (positiveRootError M Q r) (ENNReal.ofReal p) (Cutoff.cutoffSampleLaw M).toMeasure ≤
      ENNReal.ofReal (rootMatrixErrorBudget M.gamma p r+rootDensityErrorBudget M.gamma r) ∧
    eLpNorm (positiveRootError M Q r) (ENNReal.ofReal p) (Cutoff.cutoffSampleLaw M).toMeasure ≤
      ENNReal.ofReal (rootMatrixErrorBudget M.gamma p r+rootDensityRetainedBudget M.gamma p r)

end
end ASDExplicitGamma.Inverse
