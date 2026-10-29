module

public import ASDExplicitGamma.Native.OldSignedErrorProfiles

/-! The actual top or bottom two-load OLD source family is part of the
same complete four-load source budget, without resampling or independence. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ASDExplicitGamma.Response ASDExplicitGamma.Scalar
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Triadic
noncomputable section

/-- The canonical top/bottom load matched to the selected physical flat input. -/
def oldSignedFlatLoad (plus : Bool) (i : Fin 2) : BlockVec 2 :=
  blockBasis (if plus then Sum.inl i else Sum.inr i)

/-- Either selected two-load source family has a convergent complete
positive square series, bounded by the actual four-load source size d_U. -/
theorem old_signed_selected_old_source_budget (m : ℤ) (mesh : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet (originCube 2 m)))
    (b : ℝ) (L : {l : ℝ // 0<l}) (plus : Bool)
    (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth (originCube 2 m) mesh) :
    let Q := originCube 2 m
    let p := fun n i => vectorPositiveHaarNorm U (fun x =>
      (oldSignedFrameOldErrorSource Q mesh nu sigma hnu hsigma k b L n (oldSignedFlatLoad plus i) x).2)
    Summable (fun n : whiteBasisIndex => ∑ i : Fin 2,p n i^2) ∧
      Real.sqrt (∑' n : whiteBasisIndex,∑ i : Fin 2,p n i^2)≤
        oldSignedOldSourceSize Q U mesh nu sigma hnu hsigma k b L := by
  intro Q p
  let f := fun n c => vectorPositiveHaarNorm U (fun x =>
    (oldSignedFrameOldErrorSource Q mesh nu sigma hnu hsigma k b L n (blockBasis c) x).2)^2
  have hs := old_signed_old_source_budget_series m mesh nu sigma hnu hsigma k b L U hU
  have hp (n : whiteBasisIndex) : (∑ i : Fin 2,p n i^2)≤∑ c : BlockCoord 2,f n c := by
    cases plus
    · change (∑ i : Fin 2,f n (Sum.inr i))≤∑ c : BlockCoord 2,f n c
      rw [Fintype.sum_sum_type]
      exact le_add_of_nonneg_left (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    · change (∑ i : Fin 2,f n (Sum.inl i))≤∑ c : BlockCoord 2,f n c
      rw [Fintype.sum_sum_type]
      exact le_add_of_nonneg_right (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  have hps := hs.of_nonneg_of_le (fun _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _)) hp
  exact ⟨hps,Real.sqrt_le_sqrt (hps.tsum_le_tsum hp hs)⟩

end
end ASDExplicitGamma.Native
