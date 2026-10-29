module

public import ASDExplicitGamma.Inverse.AssemblyPositiveLayer
public import ASDExplicitGamma.Inverse.RootOperatorNorm

/-! Complete positive inverse assembly before moment estimates. -/

@[expose] public section
namespace ASDExplicitGamma.Inverse

open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Model
open scoped ENNReal
noncomputable section

/-- Reindex the actual deterministic layer majorant by its nonempty layers. -/
theorem assembly_inverse_majorant_eq_clocked (M : ABKModel 2)
    (Q : TriadicCube 2) (H : ℕ) (ω : Cutoff.CutoffSample 2)
    (q : Vec 2) (hq : dotProduct q q=1) :
    assemblyInverseLayerMajorant M Q H ω q =
      ENNReal.ofReal rootAssemblySensitivity * ∑' i : ℕ,
        (ENNReal.ofReal (rootAssemblyClock M.gamma H (i+1) *
          assemblyClippedQuadratic M Q H (i+1) ω q) +
          ENNReal.ofReal (rootResponseEnvelope (6*resetAllOrderTau)) *
            ENNReal.ofReal (rootAssemblyClock M.gamma H (i+1) *
              (planarGradientCharge 40+1) *
                assemblyGeometricDensityAverage M Q H (i+1) ω)) := by
  let w := fun n => rootAssemblyClock M.gamma H n
  let I := fun n : ℕ => ∑ P ∈ whitneyRootLayer Q H n,
    w n*(volume (cubeSet P)).toReal/(volume (cubeSet Q)).toReal *
      fullMatrixQuadratic (toFullBlockVec (0,q))
        (clippedCellMatrix M (P.scale+40) P resetAllOrderTau ω)
  let D := fun n : ℕ => w n*(planarGradientCharge 40+1) *
    assemblyGeometricDensityAverage M Q H n ω * dotProduct q q
  have hI0 : I 0=0 := by simp only [I,root_whitney_layer_zero,Finset.sum_empty]
  have hD0 : D 0=0 := by
    simp only [D,assemblyGeometricDensityAverage,root_layer_carrier_zero,
      Measure.restrict_empty,integral_zero_measure,Finset.sum_const_zero,
      zero_div,mul_zero,zero_mul]
  have hI (i : ℕ) : I (i+1)=w (i+1)*assemblyClippedQuadratic M Q H (i+1) ω q := by
    dsimp only [I,assemblyClippedQuadratic]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro P _
    ring
  have hD (i : ℕ) : D (i+1)=w (i+1)*(planarGradientCharge 40+1) *
      assemblyGeometricDensityAverage M Q H (i+1) ω := by
    dsimp only [D]
    rw [hq,mul_one]
  change ENNReal.ofReal rootAssemblySensitivity *
    ((∑' n, ENNReal.ofReal (I n)) +
      ENNReal.ofReal (rootResponseEnvelope (6*resetAllOrderTau))*
        ∑' n, ENNReal.ofReal (D n)) = _
  rw [← ENNReal.tsum_mul_left,← ENNReal.tsum_add,tsum_eq_zero_add' ENNReal.summable,
    hI0,hD0,ENNReal.ofReal_zero,mul_zero,zero_add,zero_add]
  congr 1
  apply tsum_congr
  intro i
  rw [hI,hD]

/-- Sum the deterministic baseline exactly and enlarge the errors to every
height before selecting the root height. -/
theorem assembly_positive_series_le (M : ABKModel 2) (hγ : M.gamma ≤ gammaZero)
    (Q : TriadicCube 2) (H0 H : ℕ) (hH0 : 38 ≤ H0) (hH : H0 ≤ H)
    (ω : Cutoff.CutoffSample 2) :
    ENNReal.ofReal rootAssemblySensitivity * ∑' i : ℕ,
      (ENNReal.ofReal (rootAssemblyClock M.gamma H (i+1)*
        assemblyInverseBaseline*bankLayerWeight i) +
          assemblyInverseErrorLayer M Q H0 (H-H0,i) ω) ≤
      ENNReal.ofReal (assemblyInverseLi M.gamma) *
        ENNReal.ofReal ((3:ℝ)^(2*M.gamma*((H:ℝ)-38))) +
          assemblyInverseError M Q H0 ω := by
  have hB : 0 ≤ assemblyInverseBaseline := assembly_inverse_baseline_nonneg
  have hE : 0 ≤ rootAssemblySensitivity := root_assembly_sensitivity_pos.le
  have hLi : 0 ≤ assemblyInverseLi M.gamma := by
    exact mul_nonneg (mul_nonneg hE hB)
      (tsum_nonneg fun i => mul_nonneg (bankLayerWeight_nonneg i) (by positivity))
  have hbase : HasSum (fun i : ℕ => rootAssemblySensitivity *
      (rootAssemblyClock M.gamma H (i+1)*assemblyInverseBaseline*bankLayerWeight i))
      (assemblyInverseLi M.gamma*(3:ℝ)^(2*M.gamma*((H:ℝ)-38))) := by
    have hh := (assembly_clocked_layer_weights_hasSum M.gamma hγ H (hH0.trans hH)).mul_left
      (rootAssemblySensitivity*assemblyInverseBaseline)
    convert hh using 1
    · funext i
      ring
    · unfold assemblyInverseLi
      ring
  have hmean : ENNReal.ofReal rootAssemblySensitivity *
      (∑' i : ℕ, ENNReal.ofReal (rootAssemblyClock M.gamma H (i+1)*
        assemblyInverseBaseline*bankLayerWeight i)) =
      ENNReal.ofReal (assemblyInverseLi M.gamma) *
        ENNReal.ofReal ((3:ℝ)^(2*M.gamma*((H:ℝ)-38))) := by
    rw [← ENNReal.tsum_mul_left]
    simp_rw [← ENNReal.ofReal_mul hE]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun i => mul_nonneg hE
      (mul_nonneg (mul_nonneg (root_assembly_clock_pos _ _ _).le hB)
        (bankLayerWeight_nonneg i))) hbase.summable,
      hbase.tsum_eq,ENNReal.ofReal_mul hLi]
  have herr : ENNReal.ofReal rootAssemblySensitivity *
      (∑' i : ℕ, assemblyInverseErrorLayer M Q H0 (H-H0,i) ω) ≤
        assemblyInverseError M Q H0 ω := by
    have hi : Function.Injective (fun i : ℕ => (H-H0,i)) := by
      intro i j he
      exact congrArg Prod.snd he
    exact mul_le_mul_right (ENNReal.tsum_comp_le_tsum_of_injective hi
      (fun hk => assemblyInverseErrorLayer M Q H0 hk ω)) _
  rw [ENNReal.tsum_add,mul_add,hmean]
  exact add_le_add_right herr _

/-- A complete positive deterministic inverse majorant, uniform over all
unit flux loadings, with its exact baseline and actual positive errors. -/
theorem assembly_inverse_majorant_le_positive (M : ABKModel 2) (h : ℝ)
    (hγ : M.gamma ≤ gammaZero) (Q : TriadicCube 2) (k H0 H : ℕ)
    (hH0 : heightEntrance k+5 ≤ H0) (hH : H0 ≤ H)
    (hpast : ∀ n : ℤ, n ≤ Q.scale-342-12*k → nativeInductionState M h n)
    (ω : Cutoff.CutoffSample 2) (q : Vec 2) (hq : dotProduct q q=1) :
    assemblyInverseLayerMajorant M Q H ω q ≤
      ENNReal.ofReal (assemblyInverseLi M.gamma) *
        ENNReal.ofReal ((3:ℝ)^(2*M.gamma*((H:ℝ)-38))) +
          assemblyInverseError M Q H0 ω := by
  rw [assembly_inverse_majorant_eq_clocked M Q H ω q hq]
  have hterms := ENNReal.tsum_le_tsum (fun i : ℕ =>
    assembly_layer_positive_energy M h hγ Q k H0 hH0 hpast (H-H0,i) ω q hq
      (rootAssemblyClock M.gamma H (i+1)) (root_assembly_clock_pos _ _ _).le)
  simp only [Nat.add_sub_of_le hH] at hterms
  have hterms' :
      (∑' i : ℕ, (ENNReal.ofReal (rootAssemblyClock M.gamma H (i+1)*
        assemblyClippedQuadratic M Q H (i+1) ω q) +
        ENNReal.ofReal (rootResponseEnvelope (6*resetAllOrderTau))*
          ENNReal.ofReal (rootAssemblyClock M.gamma H (i+1)*(planarGradientCharge 40+1)*
            assemblyGeometricDensityAverage M Q H (i+1) ω))) ≤
      ∑' i : ℕ, (ENNReal.ofReal (rootAssemblyClock M.gamma H (i+1)*
        assemblyInverseBaseline*bankLayerWeight i) +
          assemblyInverseErrorLayer M Q H0 (H-H0,i) ω) := by
    simpa only [assemblyInverseErrorLayer,Prod.fst,Prod.snd,Nat.add_sub_of_le hH] using hterms
  have h38 : 38 ≤ H0 := by unfold heightEntrance at hH0; omega
  exact (mul_le_mul_right hterms' (ENNReal.ofReal rootAssemblySensitivity)).trans
    (assembly_positive_series_le M hγ Q H0 H h38 hH ω)

end
end ASDExplicitGamma.Inverse
