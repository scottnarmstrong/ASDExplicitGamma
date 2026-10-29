module

public import ASDExplicitGamma.Inverse.LayerFrameComparison
public import ASDExplicitGamma.Inverse.HybridLocalResponses

/-! The exact source clocks on every actual hybrid parent. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization Algsuperdiff.Section3
noncomputable section

/-- The hybrid parent's old true frame obeys exactly the source root gap
times the literal selected-layer clock, without a depth truncation. -/
theorem hybrid_parent_true_frame_ratio (M : ABKModel 2) (Q : TriadicCube 2)
    (H : ℕ) (r : RootRow) (hH : rootH0 r ≤ H) (S : Set (TriadicCube 2))
    (m : ℤ) (hQ : Q.scale ≤ m) (i : HybridCell Q H S) :
    (Annealed.sigmaBar M m:ℝ)/(Annealed.sigmaBar M ((hybridParent i).2.val.scale+40):ℝ) ≤
      (3:ℝ)^(2*M.gamma*|(m-Q.scale+1:ℤ)|)*
        (3:ℝ)^(2*M.gamma*(localizationResetAbscissa (rootH0 r-38) (H-rootH0 r)
          ((hybridParent i).1-1):ℝ)) := by
  let n := (hybridParent i).1
  let P := (hybridParent i).2.val
  have hn : 1 ≤ n := root_whitney_layer_pos Q H n (hybridParent i).2.property
  have hs := root_whitney_layer_scale Q H n (hybridParent i).2.property
  change P.scale=Q.scale-n-whitneyProfile H n at hs
  have hh := root_layer_true_frame_ratio M Q m hQ r (H-rootH0 r,n-1)
  have he : rootLayerOldLabel Q (rootH0 r) (H-rootH0 r,n-1)=P.scale+40 := by
    change Q.scale-resetDepth (rootH0 r+(H-rootH0 r)) (n-1+1)+40=P.scale+40
    rw [Nat.add_sub_of_le hH,Nat.sub_add_cancel hn]
    unfold resetDepth
    unfold whitneyProfile at hs
    omega
  rwa [he] at hh

/-- Elementary frame conversion for a local energy upper bound, with all
signs stated explicitly. The local quadratic itself need not be divided by
its value or assumed nonzero. -/
theorem convert_local_frame_energy {σ σold x B K : ℝ} (hσ : 0 ≤ σ) (hold : 0 < σold)
    (hlocal : σold*x ≤ B) (hB : 0 ≤ B) (hratio : σ/σold ≤ K) : σ*x ≤ K*B := by
  have hh := mul_le_mul_of_nonneg_left hlocal (div_nonneg hσ hold.le)
  have he : σ/σold*(σold*x)=σ*x := by field_simp
  rw [he] at hh
  exact hh.trans (mul_le_mul_of_nonneg_right hratio hB)

end
end ASDExplicitGamma.Inverse
