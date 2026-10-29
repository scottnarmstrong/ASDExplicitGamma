module

public import ASDExplicitGamma.Inverse.AssemblyPositiveLayer
public import ASDExplicitGamma.Inverse.PhysicalGaussianReconstruction

/-! Exact reconstruction of the clocked physical wave at the root endpoint. -/

@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization Algsuperdiff.Section3
noncomputable section

/-- The actual layer old label is the reset wave's exact old label. -/
theorem assembly_old_label_eq_reset (Q : TriadicCube 2) (H0 : ℕ) (hH0 : 377 ≤ H0)
    (hk : ℕ × ℕ) :
    layerOldCutoff Q.scale (H0+hk.1) (hk.2+1)=physicalResetOldLabel Q H0 hk := by
  rw [layer_old_cutoff_eq_source_offset Q.scale _ _ (by omega) (by omega)]
  unfold layerRelativeOffset layerProfile physicalResetOldLabel
    localizationResetAbscissa localizationProfileDepth
  omega

/-- The physical reset normalization is reversible also at N=Q.scale-1.
The actual old label is strictly below that endpoint. -/
theorem assembly_reset_wave_reconstruction (M : ABKModel 2) (Q : TriadicCube 2)
    (N : ℤ) (hN : Q.scale-1 ≤ N) (H0 : ℕ) (hH0 : 377 ≤ H0)
    (a c : ℝ) (weights : (ℕ × ℕ) → ℤ → ℝ) (hk : ℕ × ℕ)
    (ω : Cutoff.CutoffSample 2) :
    (M.gamma*(((N-Q.scale+1:ℤ):ℝ)+(localizationResetAbscissa (H0-38) hk.1 hk.2:ℝ))*
      (3:ℝ)^(2*M.gamma*((N-Q.scale+1:ℤ):ℝ)))*physicalResetWave M Q N H0 a c weights hk ω =
        rootAssemblyClock M.gamma (H0+hk.1) (hk.2+1)*
          physicalMissingWave M (layerOldCutoff Q.scale (H0+hk.1) (hk.2+1)) Q.scale N
            a c (weights hk) ω := by
  let j := physicalResetOldLabel Q H0 hk
  let x : ℝ := localizationResetAbscissa (H0-38) hk.1 hk.2
  let D : ℝ := ((N-Q.scale+1:ℤ):ℝ)
  have hjN : j < N := by
    dsimp only [j,physicalResetOldLabel,localizationResetAbscissa]
    omega
  have hΔ : 0 < (N:ℝ)-(j:ℝ) := by exact_mod_cast sub_pos.mpr hjN
  have hgap : (N:ℝ)-(j:ℝ)=D+x := by
    have hh := physical_reset_gap_eq Q N H0 hk
    dsimp only [D,x,j]
    push_cast
    exact hh
  have hDN : (N:ℝ)-(Q.scale:ℝ)+1=D := by dsimp only [D]; push_cast; ring
  rw [assembly_old_label_eq_reset Q H0 hH0 hk,
    assembly_clock_eq_reset M.gamma H0 (by omega)]
  unfold physicalResetWave
  change (M.gamma*(D+x)*(3:ℝ)^(2*M.gamma*D))*
    ((3:ℝ)^(2*M.gamma*(x-((N:ℝ)-(Q.scale:ℝ)+1)))/(M.gamma*((N:ℝ)-(j:ℝ)))*
      physicalMissingWave M j Q.scale N a c (weights hk) ω) = _
  rw [hDN,hgap]
  have hnonzero : M.gamma*(D+x) ≠ 0 := mul_ne_zero M.shellPrefix.gamma_pos.ne'
    (by rw [← hgap]; exact hΔ.ne')
  have hsum : M.gamma*D+M.gamma*x ≠ 0 := by
    rw [← mul_add]
    exact hnonzero
  calc
    _ = ((3:ℝ)^(2*M.gamma*D)*(3:ℝ)^(2*M.gamma*(x-D)))*
        (((M.gamma*(D+x))/(M.gamma*(D+x)))*
          physicalMissingWave M j Q.scale N a c (weights hk) ω) := by ring
    _ = _ := by
      rw [div_self hnonzero,one_mul,← Real.rpow_add (by norm_num : (0:ℝ) < 3)]
      congr 2
      ring

end
end ASDExplicitGamma.Inverse
