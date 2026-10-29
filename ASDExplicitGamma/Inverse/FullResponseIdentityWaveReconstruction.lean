module

public import ASDExplicitGamma.Inverse.FullResponseIdentityHeightWave

/-! Exact recovery of the identity-layer wave payment, including m_b/4. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Model
noncomputable section

/-- The identity shear's half mean square reconstructs with exactly one
quarter of the source W₀/W₁ profile and the original layer volume fraction. -/
theorem full_response_identity_wave_reconstruction
    (M : ABKModel 2) (Q : TriadicCube 2) (N : ℤ) (hN : Q.scale-1 ≤ N)
    (weights : ℤ → ℝ) (layer H : ℕ) (hH : 377 ≤ H)
    (ω : Cutoff.CutoffSample 2) :
    let x := (localizationResetAbscissa (377-38) (H-377) layer : ℝ)
    let f := (localizationProfileDepth (layer+1) : ℝ)
    let D := (N:ℝ)-(Q.scale:ℝ)+1
    (3:ℝ)^(2*M.gamma*x) *
      (assemblyLayerMeanSquare M Q H (layer+1) N
        (sourceBandWeights (Q.scale-342) weights) ω/2) =
      (M.gamma*(3:ℝ)^(2*M.gamma*D)/4)*bankLayerWeight layer*(3:ℝ)^(4*M.gamma*f)*
        ((D+f)*fullResponseIdentityWeightedWave M Q N weights layer 0 H ω +
          fullResponseIdentityWeightedWave M Q N weights layer 1 H ω) := by
  dsimp only
  let old := layerOldCutoff Q.scale H (layer+1)
  let x := (localizationResetAbscissa (377-38) (H-377) layer : ℝ)
  let f := (localizationProfileDepth (layer+1) : ℝ)
  let D := (N:ℝ)-(Q.scale:ℝ)+1
  let Δ := (N-old:ℝ)
  have hH0 : heightEntrance 0 ≤ H := by
    simpa only [heightEntrance,mul_zero,add_zero] using hH
  have hold : old ≤ Q.scale-342 := by
    simpa only [old,protectedOldLabel,Nat.cast_zero,mul_zero,sub_zero] using
      layer_old_cutoff_le_protected Q.scale 0 H (layer+1) hH0 (by omega)
  have hΔ : 0 < Δ := by
    dsimp only [Δ]
    exact_mod_cast (show 0 < N-old by omega)
  have hv := full_response_layer_weight_pos layer
  have hx : layerRelativeOffset H (layer+1) =
      localizationResetAbscissa (377-38) (H-377) layer := by
    unfold layerRelativeOffset layerProfile localizationResetAbscissa localizationProfileDepth
    omega
  have hgap : Δ = D+x := by
    dsimp only [Δ,old]
    rw [layer_old_cutoff_eq_source_offset Q.scale H (layer+1) (by omega) (by omega),hx]
    dsimp only [D,x]
    push_cast
    ring
  have hz : x=(H:ℝ)-38+f := physical_height_abscissa_eq 377 (by norm_num) H hH layer
  have hr : (3:ℝ)^(2*M.gamma*D)*(3:ℝ)^(4*M.gamma*f)*
      (3:ℝ)^(-4*M.gamma*f)*(3:ℝ)^(2*M.gamma*(x-D)) = (3:ℝ)^(2*M.gamma*x) := by
    rw [← Real.rpow_add (by norm_num : (0:ℝ)<3),
      ← Real.rpow_add (by norm_num : (0:ℝ)<3),
      ← Real.rpow_add (by norm_num : (0:ℝ)<3)]
    congr 1
    ring
  simp only [fullResponseIdentityWeightedWave, max_eq_right hH, Fin.val_zero,
    Fin.val_one, pow_zero, pow_one, one_mul, fullResponseIdentityHeightWave]
  change (3:ℝ)^(2*M.gamma*x)*(_/2) =
    (M.gamma*(3:ℝ)^(2*M.gamma*D)/4)*bankLayerWeight layer*(3:ℝ)^(4*M.gamma*f)*
      ((D+f)*((3:ℝ)^(-4*M.gamma*f)*((3:ℝ)^(2*M.gamma*(x-D))/(M.gamma*Δ))*
        (2/bankLayerWeight layer)*_) + ((H:ℝ)-38)*
        ((3:ℝ)^(-4*M.gamma*f)*((3:ℝ)^(2*M.gamma*(x-D))/(M.gamma*Δ))*
        (2/bankLayerWeight layer)*_))
  have hsplit : D+f+((H:ℝ)-38)=Δ := by linarith only [hgap,hz]
  rw [show ∀ a b c : ℝ, a*c+b*c=(a+b)*c from fun _ _ _ => by ring]
  rw [hsplit]
  calc
    _ = (1/2)*((3:ℝ)^(2*M.gamma*x))*
        assemblyLayerMeanSquare M Q H (layer+1) N
          (sourceBandWeights (Q.scale-342) weights) ω := by ring
    _ = (1/2)*((3:ℝ)^(2*M.gamma*D)*(3:ℝ)^(4*M.gamma*f)*
        (3:ℝ)^(-4*M.gamma*f)*(3:ℝ)^(2*M.gamma*(x-D)))*
        assemblyLayerMeanSquare M Q H (layer+1) N
          (sourceBandWeights (Q.scale-342) weights) ω := by rw [hr]
    _ = _ := by
      field_simp [M.shellPrefix.gamma_pos.ne',hΔ.ne',hv.ne']
      ring

end
end ASDExplicitGamma.Inverse
