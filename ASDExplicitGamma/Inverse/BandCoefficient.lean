module

public import ASDExplicitGamma.Inverse.LaterBandW2
public import ASDExplicitGamma.Inverse.RootDefinitions
public import ASDExplicitGamma.Gaussian.SupMeanSkewTensor
public import Mathlib.Order.Interval.Finset.Basic

/-! Actual completed-cutoff plus finite-band identity at each protected old
label, retaining deterministic attenuation and the full ultraviolet cutoff. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory Algsuperdiff.Section3 Algsuperdiff.Frozen.Assumptions
open ASDExplicitGamma.Gaussian
open scoped Matrix.Norms.Elementwise
noncomputable section

/-- Full strength through m, followed by the actual fixed attenuation. -/
def sourceBandWeights (m : ℤ) (weights : ℤ → ℝ) (k : ℤ) : ℝ :=
  if k ≤ m then 1 else weights k

theorem source_band_weights_bounds (n m J : ℤ) (weights : ℤ → ℝ)
    (hw : ∀ k ∈ Finset.Ioc m J, 0 ≤ weights k ∧ weights k ≤ 1) :
    ∀ k ∈ Finset.Ioc n J, 0 ≤ sourceBandWeights m weights k ∧ sourceBandWeights m weights k ≤ 1 := by
  intro k hk
  by_cases hkm : k ≤ m
  · simp only [sourceBandWeights,ite_eq_left hkm]
    norm_num
  · simpa only [sourceBandWeights,ite_eq_right hkm] using hw k (Finset.mem_Ioc.mpr ⟨by omega,(Finset.mem_Ioc.mp hk).2⟩)

/-- The finite actual scalar band is the scalar stream of the full matrix band. -/
theorem later_band_skew_embedding (n J : ℤ) (weights : ℤ → ℝ)
    (ω : Cutoff.CutoffSample 2) (x : Vec 2) :
    supMeanSkewEmbedding (laterScalarBand n J weights ω x) =
      ∑ k ∈ Finset.Ioc n J, weights k • (ω.val k).forgetShell x := by
  unfold laterScalarBand
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro k _
  change supMeanSkewEmbedding (weights k • shellScalarValue (ω.val k) x)=_
  rw [map_smul]
  exact congrArg (fun A : Mat 2 => weights k • A) (supMean_shell_skew_embedding (ω.val k) x).symm

/-- Literal finite matrix-band split at its completed intermediate label. -/
theorem source_band_split (n m J : ℤ) (hn : n ≤ m) (hm : m ≤ J)
    (weights : ℤ → ℝ) (ω : Cutoff.CutoffSample 2) (x : Vec 2) :
    (∑ k ∈ Finset.Ioc n J, sourceBandWeights m weights k • (ω.val k).forgetShell x) =
      (∑ k ∈ Finset.Ioc n m, (ω.val k).forgetShell x)+
        ∑ k ∈ Finset.Ioc m J, weights k • (ω.val k).forgetShell x := by
  have hd : Disjoint (Finset.Ioc n m) (Finset.Ioc m J) := by
    apply Finset.disjoint_left.mpr
    intro k hk hl
    have h1 := Finset.mem_Ioc.mp hk
    have h2 := Finset.mem_Ioc.mp hl
    omega
  rw [← Finset.Ioc_union_Ioc_eq_Ioc hn hm,Finset.sum_union hd]
  congr 1
  · apply Finset.sum_congr rfl
    intro k hk
    simp only [sourceBandWeights,ite_eq_left (Finset.mem_Ioc.mp hk).2,one_smul]
  · apply Finset.sum_congr rfl
    intro k hk
    exact congrArg (fun c : ℝ => c • (ω.val k).forgetShell x)
      (ite_eq_right (not_le.mpr (Finset.mem_Ioc.mp hk).1))

/-- The actual attenuated coefficient equals its actual completed old cutoff
plus the actual later C2 band on every sample, without a replacement frame. -/
theorem attenuated_coefficient_eq_old_add_band (M : ABKModel 2) (n m J : ℤ)
    (hn : n ≤ m) (hm : m ≤ J) (weights : ℤ → ℝ) (ω : Cutoff.CutoffSample 2) (x : Vec 2) :
    attenuatedCoefficient M m J weights ω x =
      Cutoff.coefficientCutoff M.nu n ω x+
        supMeanSkewEmbedding (laterScalarBand n J (sourceBandWeights m weights) ω x) := by
  rw [later_band_skew_embedding,source_band_split n m J hn hm]
  have hc := congrArg (fun a : RegCoeffField 2 => a x) (Cutoff.cutoff_add_finiteShellIncrement ω hn)
  change Cutoff.cutoff n ω x+Cutoff.finiteShellIncrement ω.val n m x=Cutoff.cutoff m ω x at hc
  rw [Cutoff.finiteShellIncrement_apply] at hc
  have he : (∑ k ∈ Finset.Ioc n m, Cutoff.shellReg ω.val k x)=∑ k ∈ Finset.Ioc n m, (ω.val k).forgetShell x := rfl
  rw [he] at hc
  unfold attenuatedCoefficient
  rw [Cutoff.coefficientCutoff_apply,Cutoff.coefficientCutoff_apply,← hc]
  abel

end
end ASDExplicitGamma.Inverse
