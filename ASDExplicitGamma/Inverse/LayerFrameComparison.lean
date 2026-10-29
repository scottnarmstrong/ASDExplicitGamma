module

public import ASDExplicitGamma.Inverse.LayerMeanComparison
public import ASDExplicitGamma.Scalar.StructuralContinuity

/-! Exact conversion from every protected local old frame to the root frame. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization Algsuperdiff.Section3
noncomputable section

/-- The frame gap has exactly the source root gap plus x_{kh}. -/
theorem root_layer_frame_gap (Q : TriadicCube 2) (m : ℤ) (r : RootRow) (hk : ℕ × ℕ) :
    m-rootLayerOldLabel Q (rootH0 r) hk=
      (m-Q.scale+1)+(localizationResetAbscissa (rootH0 r-38) hk.1 hk.2:ℤ) := by
  have hH : 38 ≤ rootH0 r := by cases r <;> norm_num [rootH0]
  have hh := localization_reset_abscissa_source (rootH0 r) hk.1 hk.2 hH
  unfold rootLayerOldLabel
  omega

/-- The exact true scalar ratio obeys the source clock. No molecular frame
or incoming response estimate replaces structural continuity. -/
theorem root_layer_true_frame_ratio (M : ABKModel 2) (Q : TriadicCube 2)
    (m : ℤ) (hQ : Q.scale ≤ m) (r : RootRow) (hk : ℕ × ℕ) :
    (Annealed.sigmaBar M m:ℝ)/(Annealed.sigmaBar M (rootLayerOldLabel Q (rootH0 r) hk):ℝ) ≤
      (3:ℝ)^(2*M.gamma*|(m-Q.scale+1:ℤ)|)*
        (3:ℝ)^(2*M.gamma*(localizationResetAbscissa (rootH0 r-38) hk.1 hk.2:ℝ)) := by
  let n := rootLayerOldLabel Q (rootH0 r) hk
  have hn : n ≤ m := (root_layer_old_label_lt Q m hQ r hk).le
  have hh := (ASDExplicitGamma.Scalar.sigmaBar_structural_continuity M n (m-n) (by omega)).2
  rw [show n+(m-n)=m by ring] at hh
  apply hh.trans_eq
  rw [root_layer_frame_gap Q m r hk]
  rw [Int.cast_add,abs_of_nonneg (show (0:ℤ) ≤ m-Q.scale+1 by omega)]
  rw [← Real.rpow_add (by norm_num : (0:ℝ)<3)]
  congr 1
  push_cast
  ring

end
end ASDExplicitGamma.Inverse
