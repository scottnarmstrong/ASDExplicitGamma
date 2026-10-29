module

public import ASDExplicitGamma.Native.OldSignedOldSourceSharp
public import ASDExplicitGamma.Native.OldSignedErrorProfiles
public import ASDExplicitGamma.Native.OldSignedSeriesLinearBudget

/-! Complete four-load energy and first-potential budgets for the actual
localized OLD source. Correlated old-medium histories remain pathwise. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ASDExplicitGamma.Response ASDExplicitGamma.Scalar
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Triadic ASDExplicitGamma.Variational
noncomputable section

/-- Both complete OLD-source budgets, with actual mode convergence and
all source and potential inputs constructed from the parent minimizers. -/
theorem old_signed_actual_old_source_budget (m : ℤ) (mesh : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet (originCube 2 m)))
    (b : ℝ) (L : {l : ℝ // 0<l})
    (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth (originCube 2 m) mesh) :
    let Q := originCube 2 m
    let hsub := openCubeSet_subset_of_mem_descendantsAtDepth hU
    let a := responseFramePlanarCoefficientField nu sigma k
    let kU := oldSignedCellCoefficient Q U hsub k
    let F := fun n c => oldSignedFrameOldErrorSource Q mesh nu sigma hnu hsigma k b L n (blockBasis c)
    let R := fun n c => oldSignedCellResidual Q U hsub nu sigma hnu hsigma k (F n c)
      (old_signed_frame_old_error_source_memL2 Q mesh nu sigma hnu hsigma k b L n (blockBasis c))
    let v := fun n c => oldSignedCellErrorPotential Q U hsub mesh nu sigma hnu hsigma k b L n (blockBasis c)
    let E := fun n => ∑ c : BlockCoord 2,oldSignedEnergyPairing U nu sigma kU (R n c) (R n c)
    let K := fun n => ∑ c : BlockCoord 2,vectorWeakHaarNorm U (v n c).toH1Function.grad^2
    Summable E ∧ (∑' n,E n)≤oldSignedInverseHistory U a*
        oldSignedOldSourceSize Q U mesh nu sigma hnu hsigma k b L^2 ∧
      Summable K ∧ Real.sqrt (∑' n,K n)≤(1+inverseHistoryDiscount)*oldSignedInverseHistory U a*
        oldSignedOldSourceSize Q U mesh nu sigma hnu hsigma k b L := by
  intro Q hsub a kU F R v E K
  let p := fun n c => vectorPositiveHaarNorm U (fun x => (F n c x).2)
  let g := fun n c => vectorWeakHaarNorm U (v n c).toH1Function.grad
  have hps : Summable (fun n : whiteBasisIndex => ∑ c : BlockCoord 2,p n c^2) :=
    old_signed_old_source_budget_series m mesh nu sigma hnu hsigma k b L U hU
  have hB : 0≤oldSignedInverseHistory U a :=
    lemmaVInverseHistory_nonneg U a (Real.one_lt_rpow (by norm_num) (by norm_num))
  have hE (n : whiteBasisIndex) : 0≤E n := by
    apply Finset.sum_nonneg
    intro c _
    have hR : MemBlockL2 (openCubeSet U) (R n c) := Lp.memLp (R n c)
    rw [←old_signed_energy_inner_fields U nu sigma hnu hsigma kU hR hR]
    exact real_inner_self_nonneg
  have hpoint (n : whiteBasisIndex) : E n≤oldSignedInverseHistory U a*(∑ c : BlockCoord 2,p n c^2) := by
    have hh := Finset.sum_le_sum (s := Finset.univ) (fun c _ =>
      (old_signed_actual_old_source_sharp m mesh nu sigma hnu hsigma k (blockBasis c) b L n U hU).1)
    simpa only [←Finset.mul_sum] using hh
  have hEs := (hps.mul_left (oldSignedInverseHistory U a)).of_nonneg_of_le hE hpoint
  have hEt := hEs.tsum_le_tsum hpoint (hps.mul_left (oldSignedInverseHistory U a))
  rw [tsum_mul_left] at hEt
  have hd0 : 0≤∑' n : whiteBasisIndex,∑ c : BlockCoord 2,p n c^2 :=
    tsum_nonneg (fun _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  have hdeq : oldSignedOldSourceSize Q U mesh nu sigma hnu hsigma k b L^2=
      ∑' n : whiteBasisIndex,∑ c : BlockCoord 2,p n c^2 := Real.sq_sqrt hd0
  have hD : 0≤1+inverseHistoryDiscount := add_nonneg (by norm_num) inverse_history_discount_range.1.le
  have hfirst := old_signed_load_series_linear_budget p p g
    ((1+inverseHistoryDiscount)*oldSignedInverseHistory U a) 0
    (fun _ _ => Real.sqrt_nonneg _) (fun _ _ => Real.sqrt_nonneg _) (fun _ _ => Real.sqrt_nonneg _)
    (mul_nonneg hD hB) le_rfl hps hps (fun n c => by
      simpa only [zero_mul,add_zero] using
        (old_signed_actual_old_source_sharp m mesh nu sigma hnu hsigma k (blockBasis c) b L n U hU).2)
  refine ⟨hEs,?_,hfirst.1,?_⟩
  · rw [hdeq]
    exact hEt
  · simpa only [zero_mul,add_zero,K,g,oldSignedOldSourceSize,p,F] using hfirst.2

end
end ASDExplicitGamma.Native
