module

public import ASDExplicitGamma.Inverse.AssemblyLayerComparison
public import ASDExplicitGamma.Inverse.RootLayerProfile

/-! The positive layer comparison and its deterministic baseline. -/

@[expose] public section
namespace ASDExplicitGamma.Inverse

open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian
open scoped ENNReal
noncomputable section

/-- The literal deterministic inverse baseline before layer summation. -/
def assemblyInverseBaseline : ℝ :=
  29/25 + 3*(planarGradientCharge 40+1)*rootResponseEnvelope (6*resetAllOrderTau)*
    densityMomentBudget (allOrderDensity:ℝ) 2 1324

/-- The baseline coefficient after summing the exact planar layer weights. -/
def assemblyInverseLi (γ : ℝ) : ℝ :=
  rootAssemblySensitivity*assemblyInverseBaseline*rootLayerSum (2*γ)

/-- One actual nonnegative matrix and density error at a deterministic
height and layer. -/
def assemblyInverseErrorLayer (M : ABKModel 2) (Q : TriadicCube 2)
    (H0 : ℕ) (hk : ℕ × ℕ) (ω : Cutoff.CutoffSample 2) : ℝ≥0∞ :=
  ENNReal.ofReal (rootAssemblyClock M.gamma (H0+hk.1) (hk.2+1)) *
      (ENNReal.ofReal (resetRootMatrixPositiveError M Q (H0+hk.1) (hk.2+1) resetAllOrderTau ω) +
        ENNReal.ofReal (rootResponseEnvelope (6*resetAllOrderTau)*(planarGradientCharge 40+1)) *
          ∑ e : Fin 3, ENNReal.ofReal (resetDensityExcess M Q H0 resetAllOrderTau
            (waveGateEta .allOrder) (allOrderDensity:ℝ) 1324 2 hk e ω))

/-- The complete positive inverse error is defined on all deterministic
heights before selecting the actual geometric stopping height. -/
def assemblyInverseError (M : ABKModel 2) (Q : TriadicCube 2)
    (H0 : ℕ) (ω : Cutoff.CutoffSample 2) : ℝ≥0∞ :=
  ENNReal.ofReal rootAssemblySensitivity * ∑' hk : ℕ × ℕ,
    assemblyInverseErrorLayer M Q H0 hk ω

theorem assembly_inverse_baseline_nonneg : 0 ≤ assemblyInverseBaseline := by
  have hq : 0 ≤ (allOrderDensity:ℝ) := by norm_num [allOrderDensity]
  have ht := density_moment_budget_nonneg (allOrderDensity:ℝ) hq 2 1324 (by norm_num)
  have hτ : 0 ≤ resetAllOrderTau := by norm_num [resetAllOrderTau,Numerics.Wave.allOrderTau]
  have hg : 0 ≤ rootResponseEnvelope (6*resetAllOrderTau) := by
    unfold rootResponseEnvelope
    positivity
  have hs : 0 ≤ planarGradientCharge 40+1 := by unfold planarGradientCharge; positivity
  exact add_nonneg (by norm_num)
    (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hs) hg) ht)

/-- The root-relative clock is the source reset-series abscissa. -/
theorem assembly_clock_eq_reset (γ : ℝ) (H0 : ℕ) (hH0 : 38 ≤ H0)
    (hk : ℕ × ℕ) :
    rootAssemblyClock γ (H0+hk.1) (hk.2+1) =
      (3:ℝ)^(2*γ*(localizationResetAbscissa (H0-38) hk.1 hk.2:ℝ)) := by
  have he : layerRelativeOffset (H0+hk.1) (hk.2+1) =
      localizationResetAbscissa (H0-38) hk.1 hk.2 := by
    unfold layerRelativeOffset layerProfile localizationResetAbscissa
      localizationProfileDepth
    omega
  simp only [rootAssemblyClock,he]

/-- Factor the deterministic height clock from every exact layer weight. -/
theorem assembly_layer_clock_factor (γ : ℝ) (H : ℕ) (hH : 38 ≤ H) (i : ℕ) :
    rootAssemblyClock γ H (i+1) =
      (3:ℝ)^(2*γ*((H:ℝ)-38)) *
        (3:ℝ)^(2*γ*(localizationProfileDepth (i+1):ℝ)) := by
  have he : layerRelativeOffset H (i+1) = H-38+localizationProfileDepth (i+1) := by
    unfold layerRelativeOffset layerProfile localizationProfileDepth
    omega
  unfold rootAssemblyClock
  rw [he,Nat.cast_add,Nat.cast_sub hH,← Real.rpow_add (by norm_num : (0:ℝ)<3)]
  congr 1
  norm_num
  ring

theorem assembly_clocked_layer_weights_hasSum (γ : ℝ) (hγ : γ ≤ gammaZero)
    (H : ℕ) (hH : 38 ≤ H) :
    HasSum (fun i : ℕ => rootAssemblyClock γ H (i+1)*bankLayerWeight i)
      ((3:ℝ)^(2*γ*((H:ℝ)-38))*rootLayerSum (2*γ)) := by
  have hh := (root_layer_sum_summable γ hγ).hasSum.mul_left
    ((3:ℝ)^(2*γ*((H:ℝ)-38)))
  convert hh using 1
  · funext i
    rw [assembly_layer_clock_factor γ H hH i]
    ring
  · rfl

/-- Each actual unit-flux layer is its exact rare-mean baseline plus the
actual nonnegative matrix and three geometric-density errors. -/
theorem assembly_layer_positive_energy (M : ABKModel 2) (h : ℝ)
    (hγ : M.gamma ≤ gammaZero) (Q : TriadicCube 2) (k H0 : ℕ)
    (hH0 : heightEntrance k+5 ≤ H0)
    (hpast : ∀ n : ℤ, n ≤ Q.scale-342-12*k → nativeInductionState M h n)
    (hk : ℕ × ℕ) (ω : Cutoff.CutoffSample 2) (q : Vec 2) (hq : dotProduct q q=1)
    (w : ℝ) (hw : 0 ≤ w) :
    ENNReal.ofReal (w*assemblyClippedQuadratic M Q (H0+hk.1) (hk.2+1) ω q) +
      ENNReal.ofReal (rootResponseEnvelope (6*resetAllOrderTau)) *
        ENNReal.ofReal (w*(planarGradientCharge 40+1)*
          assemblyGeometricDensityAverage M Q (H0+hk.1) (hk.2+1) ω) ≤
      ENNReal.ofReal (w*assemblyInverseBaseline*bankLayerWeight hk.2) +
        ENNReal.ofReal w *
          (ENNReal.ofReal (resetRootMatrixPositiveError M Q (H0+hk.1) (hk.2+1) resetAllOrderTau ω) +
            ENNReal.ofReal (rootResponseEnvelope (6*resetAllOrderTau)*(planarGradientCharge 40+1)) *
              ∑ e : Fin 3, ENNReal.ofReal (resetDensityExcess M Q H0 resetAllOrderTau
                (waveGateEta .allOrder) (allOrderDensity:ℝ) 1324 2 hk e ω)) := by
  let I := assemblyClippedQuadratic M Q (H0+hk.1) (hk.2+1) ω q
  let D := assemblyGeometricDensityAverage M Q (H0+hk.1) (hk.2+1) ω
  let a := resetRootMatrixPositiveError M Q (H0+hk.1) (hk.2+1) resetAllOrderTau ω
  let d := fun e : Fin 3 => resetDensityExcess M Q H0 resetAllOrderTau
    (waveGateEta .allOrder) (allOrderDensity:ℝ) 1324 2 hk e ω
  let g := rootResponseEnvelope (6*resetAllOrderTau)
  let s := planarGradientCharge 40+1
  let t := densityMomentBudget (allOrderDensity:ℝ) 2 1324
  let v := bankLayerWeight hk.2
  have ha0 : 0 ≤ a := le_max_left _ _
  have hd0 (e : Fin 3) : 0 ≤ d e := le_max_right _ _
  have hτ : 0 ≤ resetAllOrderTau := by norm_num [resetAllOrderTau,Numerics.Wave.allOrderTau]
  have hg0 : 0 ≤ g := by dsimp only [g,rootResponseEnvelope]; positivity
  have hs0 : 0 ≤ s := by dsimp only [s,planarGradientCharge]; positivity
  have hI0 : 0 ≤ I := Finset.sum_nonneg fun P _ =>
    mul_nonneg (div_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)
      (clipped_cell_matrix_quadratic_nonneg M _ _ _ ω _)
  have hD0 : 0 ≤ D := div_nonneg
    (Finset.sum_nonneg fun _ _ => integral_nonneg fun _ => sq_nonneg _) ENNReal.toReal_nonneg
  have h333 : 333 ≤ H0 := by unfold heightEntrance at hH0; omega
  have hI : I ≤ (29/25:ℝ)*v+a := assembly_clipped_layer_mean_comparison
    M h hγ Q k (H0+hk.1) (by omega) hpast hk.2 ω q hq
  have hD : D ≤ 3*v*t+∑ e, d e :=
    assembly_geometric_density_sum_le_excess M Q H0 h333 hk ω
  have hreal : w*I+g*(w*s*D) ≤
      w*(assemblyInverseBaseline*v+a+g*s*∑ e, d e) := by
    have h1 := mul_le_mul_of_nonneg_left hI hw
    have h2 := mul_le_mul_of_nonneg_left hD (mul_nonneg hg0 (mul_nonneg hw hs0))
    have hh := add_le_add h1 h2
    dsimp only [assemblyInverseBaseline,g,s,t,v] at *
    convert hh using 1 <;> ring
  change ENNReal.ofReal (w*I)+ENNReal.ofReal g*ENNReal.ofReal (w*s*D) ≤
    ENNReal.ofReal (w*assemblyInverseBaseline*v) +
      ENNReal.ofReal w*(ENNReal.ofReal a+ENNReal.ofReal (g*s)*∑ e, ENNReal.ofReal (d e))
  rw [← ENNReal.ofReal_mul hg0,← ENNReal.ofReal_add (mul_nonneg hw hI0)
    (mul_nonneg hg0 (mul_nonneg (mul_nonneg hw hs0) hD0))]
  apply (ENNReal.ofReal_le_ofReal hreal).trans
  calc
    ENNReal.ofReal (w*(assemblyInverseBaseline*v+a+g*s*∑ e, d e)) =
        ENNReal.ofReal (w*assemblyInverseBaseline*v+w*(a+g*s*∑ e, d e)) := by congr 1; ring
    _ ≤ ENNReal.ofReal (w*assemblyInverseBaseline*v) +
        ENNReal.ofReal (w*(a+g*s*∑ e, d e)) := ENNReal.ofReal_add_le
    _ = _ := by
      rw [ENNReal.ofReal_mul hw,ENNReal.ofReal_add ha0
        (mul_nonneg (mul_nonneg hg0 hs0) (Finset.sum_nonneg fun e _ => hd0 e)),
        ENNReal.ofReal_mul (mul_nonneg hg0 hs0),
        ENNReal.ofReal_sum_of_nonneg (fun e _ => hd0 e)]

end
end ASDExplicitGamma.Inverse
