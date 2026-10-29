module

public import ASDExplicitGamma.Inverse.AssemblyHybridTraceCells
public import ASDExplicitGamma.Inverse.AssemblyIdentityLayerSum
public import ASDExplicitGamma.Inverse.AssemblyHybridTrace

/-! Complete positive trace majorant before taking probability moments. -/

@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory Algsuperdiff.Section3
open Algsuperdiff.Section3.Provider Algsuperdiff.Section3.Provider.Whitney
open ASDExplicitGamma.Gaussian
open scoped ENNReal
noncomputable section

/-- All four variational loads are combined before the exact quarter factor
is applied to each positive hybrid-cell contribution. -/
theorem assembly_four_load_normalization {I : Type*} (v : I → ℝ)
    (E : I → Fin 2 × Bool → ℝ) (hv : ∀ i, 0 ≤ v i) (hE : ∀ i j, 0 ≤ E i j) :
    (∑ j : Fin 2 × Bool, ∑' i, ENNReal.ofReal (v i*E i j))*ENNReal.ofReal (1/4:ℝ) =
      ∑' i, ENNReal.ofReal (v i*(∑ j : Fin 2 × Bool, E i j)/4) := by
  have hswap : (∑ j : Fin 2 × Bool, ∑' i, ENNReal.ofReal (v i*E i j)) =
      ∑' i, ∑ j : Fin 2 × Bool, ENNReal.ofReal (v i*E i j) := by
    simpa only [tsum_fintype] using
      (ENNReal.tsum_comm (f := fun (j : Fin 2 × Bool) (i : I) => ENNReal.ofReal (v i*E i j)))
  rw [hswap,← ENNReal.tsum_mul_right]
  apply tsum_congr
  intro i
  rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => mul_nonneg (hv i) (hE i j)),
    ← ENNReal.ofReal_mul (Finset.sum_nonneg fun j _ => mul_nonneg (hv i) (hE i j))]
  congr 1
  rw [← Finset.mul_sum]
  ring

/-- The literal positive trace envelope consists of the complete sheared
clipped identity layers and complete spatially weighted geometric densities.
Every height/layer is deterministic until the stopping height is substituted. -/
def assemblyTraceLayerMajorant (M : ABKModel 2) (Q : TriadicCube 2)
    (k H : ℕ) (N : ℤ) (weights : ℤ → ℝ) (ω : Cutoff.CutoffSample 2) : ℝ≥0∞ :=
  ENNReal.ofReal rootAssemblySensitivity *
    (∑' n : ℕ, ENNReal.ofReal (rootAssemblyClock M.gamma H n*
      assemblyShearedLayerTrace M Q H n N
        (sourceBandWeights (protectedOldLabel Q.scale k) weights) ω))+
    ENNReal.ofReal (4*rootAssemblySensitivity*(1+2*Real.sqrt 3*resetAllOrderTau))*
      ∑' n : ℕ, ENNReal.ofReal (rootAssemblyClock M.gamma H n*(planarGradientCharge 40+1)/
        (volume (cubeSet Q)).toReal*
          ∑ e : Fin 3, ∫ x in rootLayerCarrier Q H n,
            (layerResolutionDiameter M Q H resetAllOrderTau (waveGateEta .allOrder) n e ω x)^2*
              assemblyActiveSpatialPayment M Q k H n N weights ω x)

end
end ASDExplicitGamma.Inverse
