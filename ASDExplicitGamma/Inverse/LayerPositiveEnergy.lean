module

public import ASDExplicitGamma.Inverse.LayerObservables
public import ASDExplicitGamma.Inverse.RootDensityParameters

/-! Exact mean plus positive-error decomposition of each actual layer energy. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory Algsuperdiff.Section3
open scoped ENNReal
noncomputable section

/-- Single-layer source positive comparison, preserving the actual matrix
and three density excesses. The clock is arbitrary and nonnegative. -/
theorem root_layer_positive_energy (M : ABKModel 2) (Q : TriadicCube 2)
    (m : ℤ) (hQ : Q.scale ≤ m) (r : RootRow) (hmean : ClippedInverseMeanInput M m r)
    (hk : ℕ × ℕ) (ω : Cutoff.CutoffSample 2) (q : Vec 2) (hq : dotProduct q q=1)
    (w : ℝ) (hw : 0 ≤ w) :
    ENNReal.ofReal (w*rootLayerClippedQuadratic M Q r hk ω q)+
      ENNReal.ofReal (rootResponseEnvelope (6*rootTau r))*
        ENNReal.ofReal (w*(planarGradientCharge 40+1)*rootLayerDensityAverage M Q r hk ω) ≤
    ENNReal.ofReal (w*(rootMeanCap r+3*(planarGradientCharge 40+1)*
      rootResponseEnvelope (6*rootTau r)*densityMomentBudget (rootQ r) 2 (rootMomentCutoff r))*
        bankLayerWeight hk.2)+
    ENNReal.ofReal w*(ENNReal.ofReal (rootMatrixPositiveError M Q r hk ω)+
      ENNReal.ofReal (rootResponseEnvelope (6*rootTau r)*(planarGradientCharge 40+1))*
        ∑ e : Fin 3, ENNReal.ofReal (resetDensityExcess M Q (rootH0 r) (rootTau r)
          (ASDExplicitGamma.Gaussian.waveGateEta (rootWaveTuple r)) (rootQ r) (rootMomentCutoff r) 2 hk e ω)) := by
  let I := rootLayerClippedQuadratic M Q r hk ω q
  let D := rootLayerDensityAverage M Q r hk ω
  let a := rootMatrixPositiveError M Q r hk ω
  let d := fun e : Fin 3 => resetDensityExcess M Q (rootH0 r) (rootTau r)
    (ASDExplicitGamma.Gaussian.waveGateEta (rootWaveTuple r)) (rootQ r) (rootMomentCutoff r) 2 hk e ω
  let g := rootResponseEnvelope (6*rootTau r)
  let s := planarGradientCharge 40+1
  let b := rootMeanCap r
  let t := densityMomentBudget (rootQ r) 2 (rootMomentCutoff r)
  let v := bankLayerWeight hk.2
  let K := b+3*s*g*t
  have ha0 : 0 ≤ a := le_max_left _ _
  have hd0 (e : Fin 3) : 0 ≤ d e := reset_density_excess_nonneg M Q _ _ _ _ _ _ hk e ω
  have htau : 0 ≤ rootTau r := by cases r <;> norm_num [rootTau]
  have hg0 : 0 ≤ g := by dsimp only [g,rootResponseEnvelope]; positivity
  have hs0 : 0 ≤ s := by dsimp only [s,planarGradientCharge]; positivity
  have hI0 : 0 ≤ I := root_layer_clipped_quadratic_nonneg M Q r hk ω q
  have hD0 : 0 ≤ D := root_layer_density_average_nonneg M Q r hk ω
  have hI : I ≤ b*v+a := root_self_label_clipped_layer_comparison M Q m hQ r hmean hk ω q hq
  have hD : D ≤ 3*v*t+∑ e, d e := root_layer_density_sum_le_excess M Q r hk ω
  have hreal : w*I+g*(w*s*D) ≤ w*(K*v+a+g*s*∑ e, d e) := by
    have h1 := mul_le_mul_of_nonneg_left hI hw
    have h2 := mul_le_mul_of_nonneg_left hD (mul_nonneg hg0 (mul_nonneg hw hs0))
    have hh := add_le_add h1 h2
    dsimp only [K]
    convert hh using 1 <;> ring
  change ENNReal.ofReal (w*I)+ENNReal.ofReal g*ENNReal.ofReal (w*s*D) ≤
    ENNReal.ofReal (w*K*v)+ENNReal.ofReal w*(ENNReal.ofReal a+
      ENNReal.ofReal (g*s)*∑ e, ENNReal.ofReal (d e))
  rw [← ENNReal.ofReal_mul hg0,← ENNReal.ofReal_add (mul_nonneg hw hI0)
    (mul_nonneg hg0 (mul_nonneg (mul_nonneg hw hs0) hD0))]
  apply (ENNReal.ofReal_le_ofReal hreal).trans
  calc
    ENNReal.ofReal (w*(K*v+a+g*s*∑ e, d e))=
        ENNReal.ofReal (w*K*v+w*(a+g*s*∑ e, d e)) := by congr 1; ring
    _ ≤ ENNReal.ofReal (w*K*v)+ENNReal.ofReal (w*(a+g*s*∑ e, d e)) := ENNReal.ofReal_add_le
    _ = _ := by
      rw [ENNReal.ofReal_mul hw,ENNReal.ofReal_add ha0
        (mul_nonneg (mul_nonneg hg0 hs0) (Finset.sum_nonneg (fun e _ => hd0 e))),
        ENNReal.ofReal_mul (mul_nonneg hg0 hs0),ENNReal.ofReal_sum_of_nonneg (fun e _ => hd0 e)]

end
end ASDExplicitGamma.Inverse
