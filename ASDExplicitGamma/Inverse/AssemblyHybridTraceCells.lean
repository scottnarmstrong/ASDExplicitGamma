module

public import ASDExplicitGamma.Inverse.AssemblyFrameTrace
public import ASDExplicitGamma.Inverse.AssemblyActiveCongruence
public import ASDExplicitGamma.Inverse.AssemblyActiveRootFrame
public import ASDExplicitGamma.Inverse.AssemblyActiveSpatialCharge

/-! Exact normalized four-load payments on the actual hybrid cells. -/

@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory Algsuperdiff.Section3
open Algsuperdiff.Section3.Provider Algsuperdiff.Section3.Provider.Whitney
open Algsuperdiff.Section3.Provider.Multiscale
open ASDExplicitGamma.Triadic ASDExplicitGamma.Response ASDExplicitGamma.Variational ASDExplicitGamma.Gaussian
open scoped ENNReal
noncomputable section

/-- Every actual hybrid load has nonnegative energy, even when its parent
lies below the protected attenuation cutoff. -/
theorem assembly_hybrid_trace_cell_load_nonneg (M : ABKModel 2) (Q : TriadicCube 2)
    (k H : ℕ) (hH : heightEntrance k ≤ H) (ω : Cutoff.CutoffSample 2)
    (N ref : ℤ) (hmN : protectedOldLabel Q.scale k ≤ N) (weights : ℤ → ℝ)
    (S : Set (TriadicCube 2)) (C : HybridCell Q H S → Mat 2)
    (i : HybridCell Q H S) (j : Fin 2 × Bool) :
    0 ≤ hybridFullTraceCellLoadEnergy (Annealed.sigmaBar M ref:ℝ)
      (coarseBlockMatrix (hybridDomain i:Set (Vec 2))
        (attenuatedCoefficient M (protectedOldLabel Q.scale k) N weights ω)) (C i) j := by
  let P := (hybridParent i).2.val
  let n := (hybridParent i).1
  have hP := (hybridParent i).2.property
  have hn := root_whitney_layer_pos Q H n hP
  have hlabel := root_whitney_old_cutoff_eq Q H n hP
  have hcut := layer_old_cutoff_le_protected Q.scale k H n hH hn
  have hold : P.scale+40 ≤ protectedOldLabel Q.scale k := by rwa [hlabel] at hcut
  have hh := assembly_attenuated_domain_quadratic_nonneg M P (P.scale+40)
    (protectedOldLabel Q.scale k) N hold hmN weights ω (hybridDomain i) (hybrid_domain_subset_parent i)
  exact hh _

/-- The identity slope retains exactly the four-load trace normalization. -/
theorem assembly_identity_load_sum (σ : ℝ) (hσ : 0 < σ) (A : BlockMat 2) :
    (∑ j : Fin 2 × Bool, hybridFullTraceCellLoadEnergy σ A (1:Mat 2) j) =
      Matrix.trace (toFullBlockMat (frameMatrix σ A)) := by
  rw [hybrid_full_trace_cell_load_sum_eq σ A 1 hσ]
  simp [planar_flux_matrix_one,frameMatrix,toFullBlockMat,Matrix.trace,
    Fintype.sum_sum_type,Fin.sum_univ_two]
  ring

/-- A good active cell's four-load energy is paid in the source root frame
by its actual parent mean and the common slope squared. -/
theorem assembly_active_cell_trace_payment (M : ABKModel 2) (Q : TriadicCube 2)
    (k H : ℕ) (hH : heightEntrance k ≤ H) (ω : Cutoff.CutoffSample 2)
    (N : ℤ) (hmN : protectedOldLabel Q.scale k ≤ N) (weights : ℤ → ℝ)
    (hw : ∀ n ∈ Finset.Ioc (protectedOldLabel Q.scale k) N, 0 ≤ weights n ∧ weights n ≤ 1)
    (C : HybridCell Q H (rootBadWhitneyCells M Q H resetAllOrderTau (waveGateEta .allOrder) ω) → Mat 2)
    (hCb : ∀ i, (hybridParent i).2.val ∈
      rootBadWhitneyCells M Q H resetAllOrderTau (waveGateEta .allOrder) ω → C i=0)
    (i : HybridActiveCell Q H (rootBadWhitneyCells M Q H resetAllOrderTau (waveGateEta .allOrder) ω)) :
    let S := rootBadWhitneyCells M Q H resetAllOrderTau (waveGateEta .allOrder) ω
    let v := (volume (hybridDomain (.inr i):Set (Vec 2))).toReal/(volume (cubeSet Q)).toReal
    ENNReal.ofReal (v*(∑ j : Fin 2 × Bool,
      hybridFullTraceCellLoadEnergy (Annealed.sigmaBar M (Q.scale-1):ℝ)
        (coarseBlockMatrix (hybridDomain (.inr i):Set (Vec 2))
          (attenuatedCoefficient M (protectedOldLabel Q.scale k) N weights ω)) (C (.inr i)) j)/4) ≤
      ENNReal.ofReal (4*rootAssemblySensitivity*(1+2*Real.sqrt 3*resetAllOrderTau))*
        ENNReal.ofReal (rootAssemblyClock M.gamma H i.1.val.1*v*
          (‖Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) (C (.inr i))‖^2*
            assemblyActiveParentMeanPayment M Q k H S N weights ω i)) := by
  classical
  let S := rootBadWhitneyCells M Q H resetAllOrderTau (waveGateEta .allOrder) ω
  let v := (volume (hybridDomain (.inr i):Set (Vec 2))).toReal/(volume (cubeSet Q)).toReal
  have hv : 0 ≤ v := div_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
  by_cases hb : (hybridParent (.inr i)).2.val ∈ S
  · have hz := hCb (.inr i) hb
    simp [hz,hybridFullTraceCellLoadEnergy,planar_flux_matrix_zero,
      matVecMul,blockVecDot,blockMatVecMul,vecDot]
  · let P := i.1.val.2.val
    let n := i.1.val.1
    have hP : P ∈ whitneyRootLayer Q H n := i.1.val.2.property
    have hn := root_whitney_layer_pos Q H n hP
    have hlabel := root_whitney_old_cutoff_eq Q H n hP
    have hold : P.scale+40 ≤ protectedOldLabel Q.scale k := by
      have hh := layer_old_cutoff_le_protected Q.scale k H n hH hn
      rwa [hlabel] at hh
    have hparent := hybrid_parent_good_of_not_bad M Q H resetAllOrderTau (waveGateEta .allOrder) ω (.inr i) hb
    obtain ⟨a,ha,hdepth⟩ := final_kuhn_support_depth_le_two Q H n i.1.val.2.property i.2.property
    have hlocal := assembly_active_triangle_transformed_trace M hdepth ha i.2.val.order
      (protectedOldLabel Q.scale k) N hold hmN weights hw ω hparent (C (.inr i))
    have hframe := assembly_active_load_sum_root_frame_le M Q H k hH ω N hmN weights C i
    have hK : i.2.val = Whitney.KuhnCell.mk i.2.val.supportCube i.2.val.order := by cases i.2.val; rfl
    rw [← hK] at hlocal
    have hh := hframe.trans (mul_le_mul_of_nonneg_left hlocal
      (show (0:ℝ≥0∞) ≤ ENNReal.ofReal (rootAssemblyClock M.gamma H n) from zero_le))
    have hscaled := mul_le_mul_of_nonneg_left hh (show (0:ℝ≥0∞) ≤ ENNReal.ofReal (v/4) from zero_le)
    have hE := root_assembly_sensitivity_pos.le
    have hclock := (root_assembly_clock_pos M.gamma H n).le
    have hτ : 0 ≤ resetAllOrderTau := by norm_num [resetAllOrderTau,Numerics.Wave.allOrderTau]
    have hold0 : 0 ≤ 1+2*Real.sqrt 3*resetAllOrderTau := by positivity
    have hcap0 : 0 ≤ assemblyActiveParentMeanPayment M Q k H S N weights ω i := by
      unfold assemblyActiveParentMeanPayment
      positivity
    have hnorm0 : 0 ≤ ‖Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) (C (.inr i))‖^2 := sq_nonneg _
    change ENNReal.ofReal (v/4)*ENNReal.ofReal _ ≤ _ at hscaled
    rw [← ENNReal.ofReal_mul (div_nonneg hv (by norm_num))] at hscaled
    have hre (z : ℝ) : v/4*z=v*z/4 := by ring
    rw [hre] at hscaled
    apply hscaled.trans_eq
    change ENNReal.ofReal (v/4)*(ENNReal.ofReal (rootAssemblyClock M.gamma H n)*
      (ENNReal.ofReal (8*‖Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) (C (.inr i))‖^2)*
        ENNReal.ofReal (2*rootAssemblySensitivity*assemblyActiveParentMeanPayment M Q k H S N weights ω i*
          (1+2*Real.sqrt 3*resetAllOrderTau)))) = _
    rw [← ENNReal.ofReal_mul (mul_nonneg (by norm_num) hnorm0),
      ← ENNReal.ofReal_mul hclock,← ENNReal.ofReal_mul (div_nonneg hv (by norm_num)),
      ← ENNReal.ofReal_mul (mul_nonneg (mul_nonneg (by norm_num) hE) hold0)]
    congr 1
    ring

end
end ASDExplicitGamma.Inverse
