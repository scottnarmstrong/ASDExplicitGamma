module

public import ASDExplicitGamma.Inverse.BankHistoryPopulation
public import ASDExplicitGamma.Scalar.InverseHistoryBlocks
public import ASDExplicitGamma.Variational.ProjectedSource

/-! Exact physical meaning of the extended inverse histories. -/
@[expose] public section

namespace ASDExplicitGamma.Inverse

open Homogenization MeasureTheory Algsuperdiff.Section3 ASDExplicitGamma.Variational
open scoped ENNReal

theorem bank_finite_max_ofReal {ι : Type*} (s : Finset ι) (hs : s.Nonempty) (f : ι → ℝ) :
    historyFiniteMax (Finset.univ : Finset ↥s) (fun i (_ : Unit) => ENNReal.ofReal (f i)) () =
      ENNReal.ofReal (Book.Ch02.finsetSupReal s f) := by
  classical
  have hfinite : (f '' (s:Set ι)).Finite := s.finite_toSet.image f
  have hne : (f '' (s:Set ι)).Nonempty := hs.to_set.image f
  have hmem := hne.csSup_mem hfinite
  obtain ⟨i,hi,heq⟩ := hmem
  apply le_antisymm
  · apply Finset.sup_le
    intro a _
    apply ENNReal.ofReal_le_ofReal
    exact le_csSup hfinite.bddAbove ⟨a.1,a.2,rfl⟩
  · change ENNReal.ofReal (sSup (f '' (s:Set ι))) ≤ _
    rw [← heq]
    exact Finset.le_sup (f:=fun a : ↥s => ENNReal.ofReal (f a.1))
      (Finset.mem_univ (⟨i,hi⟩ : ↥s))

/-- At each depth the ENNReal maximum is exactly the physical framed inverse maximum. -/
theorem bank_depth_max_physical (Q : TriadicCube 2) (M : ABKModel 2)
    (m J : ℤ) (weights : ℤ → ℝ) (ω : Cutoff.CutoffSample 2) (a : CoeffField 2)
    (ha : attenuatedCoefficient M m J weights ω = a)
    {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a) (j : ℕ) :
    bankFiniteRootResponseMax (descendantsAtDepth Q j) M m J weights ω =
      ENNReal.ofReal ((Annealed.sigmaBar M m:ℝ)*lemmaVInverseDepthMax Q a j) := by
  have hs := (Annealed.sigmaBar_characterization M m).1
  have hmax := bank_finite_max_ofReal (descendantsAtDepth Q j) (descendantsAtDepth_nonempty Q j)
    (fun R => rootInverseResponse M R m J weights ω)
  change bankFiniteRootResponseMax (descendantsAtDepth Q j) M m J weights ω = _ at hmax
  rw [hmax]
  congr 1
  calc
    _ = Book.Ch02.finsetSupReal (descendantsAtDepth Q j)
        (fun R => Book.Ch02.matrixNorm
          ((Annealed.sigmaBar M m:ℝ) • (coarseBlockMatrix (cubeSet R) a).lowerRight)) := by
      apply Book.Ch02.finsetSupReal_congr
      intro R _
      rw [Scalar.inverse_history_matrixNorm_smul _ _ hs.le]
      simp only [rootInverseResponse,ha,Book.Ch02.matrixNorm]
    _ = _ := Scalar.inverse_history_framed_depth_max Q a hEll _ hs j

/-- Complete histories use exactly the source geometric discount and physical inverse,
including their normalizing factor. -/
theorem bank_root_history_physical (Q : TriadicCube 2) (M : ABKModel 2)
    (m J : ℤ) (weights : ℤ → ℝ) (ω : Cutoff.CutoffSample 2) (a : CoeffField 2)
    (ha : attenuatedCoefficient M m J weights ω = a)
    {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a) :
    bankRootInverseHistory Q M m J weights ω =
      ENNReal.ofReal ((Annealed.sigmaBar M m:ℝ)*lemmaVInverseHistory Q a ((3:ℝ)^(1/4:ℝ))) := by
  let q : ℝ := (3:ℝ)^(1/4:ℝ)
  have hq : 1 < q := Real.one_lt_rpow (by norm_num) (by norm_num)
  have hs := (Annealed.sigmaBar_characterization M m).1
  have hi : q⁻¹ = (3:ℝ)^(-(1/4:ℝ)) := (Real.rpow_neg (by norm_num : (0:ℝ)≤3) (1/4:ℝ)).symm
  have hw : 0 ≤ q⁻¹ := inv_nonneg.mpr (zero_lt_one.trans hq).le
  have hw1 : q⁻¹ < 1 := (inv_lt_one₀ (zero_lt_one.trans hq)).mpr hq
  have hsum := (lemmaVInverseHistory_summable Q hEll hq).mul_left (Annealed.sigmaBar M m:ℝ)
  unfold bankRootInverseHistory
  simp_rw [bank_depth_max_physical Q M m J weights ω a ha hEll]
  unfold bankHistoryPrefactor bankHistoryAlpha
  rw [← hi]
  simp_rw [← ENNReal.ofReal_pow hw,← ENNReal.ofReal_mul (pow_nonneg hw _)]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun j => mul_nonneg (pow_nonneg hw j)
    (mul_nonneg hs.le (lemmaVInverseDepthMax_nonneg Q a j)))
    (by simpa only [mul_left_comm] using hsum)]
  rw [← ENNReal.ofReal_mul (sub_nonneg.mpr hw1.le)]
  congr 1
  change (1-q⁻¹)*(∑' j : ℕ, q⁻¹^j*((Annealed.sigmaBar M m:ℝ)*lemmaVInverseDepthMax Q a j)) =
    (Annealed.sigmaBar M m:ℝ)*((1-q⁻¹)*∑' j : ℕ, q⁻¹^j*lemmaVInverseDepthMax Q a j)
  rw [show (fun j : ℕ => q⁻¹^j*((Annealed.sigmaBar M m:ℝ)*lemmaVInverseDepthMax Q a j)) =
      (fun j => (Annealed.sigmaBar M m:ℝ)*(q⁻¹^j*lemmaVInverseDepthMax Q a j)) by
        funext j; ring, tsum_mul_left]
  ring


/-- Every depth maximum dominates depth zero, so normalization preserves the
root inverse response as a lower bound for its complete history. -/
theorem bank_inverse_depth_zero_le_history (Q : TriadicCube 2) (a : CoeffField 2)
    {lam Lam q : ℝ} (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a) (hq : 1 < q) :
    lemmaVInverseDepthMax Q a 0 ≤ lemmaVInverseHistory Q a q := by
  have hw : 0 ≤ q⁻¹ := inv_nonneg.mpr (zero_lt_one.trans hq).le
  have hw1 : q⁻¹ < 1 := (inv_lt_one₀ (zero_lt_one.trans hq)).mpr hq
  have hm : Monotone (lemmaVInverseDepthMax Q a) := monotone_nat_of_le_succ
    (fun j => lemmaVInverseDepthMax_le_succ Q hEll j)
  have h0 := (summable_geometric_of_lt_one hw hw1).mul_right (lemmaVInverseDepthMax Q a 0)
  have heq : (1-q⁻¹)*(∑' j : ℕ, (q⁻¹)^j*lemmaVInverseDepthMax Q a 0) =
      lemmaVInverseDepthMax Q a 0 := by
    rw [tsum_mul_right,tsum_geometric_of_lt_one hw hw1]
    field_simp [(sub_pos.mpr hw1).ne',(sub_pos.mpr hq).ne']
  rw [← heq]
  unfold lemmaVInverseHistory
  apply mul_le_mul_of_nonneg_left _ (sub_nonneg.mpr hw1.le)
  exact h0.tsum_le_tsum (fun j => mul_le_mul_of_nonneg_left (hm (Nat.zero_le j))
    (pow_nonneg hw j)) (lemmaVInverseHistory_summable Q hEll hq)

theorem bank_root_response_le_history (Q : TriadicCube 2) (M : ABKModel 2)
    (m J : ℤ) (weights : ℤ → ℝ) (ω : Cutoff.CutoffSample 2)
    {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q)
      (attenuatedCoefficient M m J weights ω)) :
    ENNReal.ofReal (rootInverseResponse M Q m J weights ω) ≤
      bankRootInverseHistory Q M m J weights ω := by
  rw [bank_root_history_physical Q M m J weights ω _ rfl hEll]
  apply ENNReal.ofReal_le_ofReal
  have hh := bank_inverse_depth_zero_le_history Q _ hEll
    (show 1 < (3:ℝ)^(1/4:ℝ) from Real.one_lt_rpow (by norm_num) (by norm_num))
  have he : lemmaVInverseDepthMax Q (attenuatedCoefficient M m J weights ω) 0 =
      Book.Ch02.matrixNorm (coarseBlockMatrix (cubeSet Q)
        (attenuatedCoefficient M m J weights ω)).lowerRight := by
    unfold lemmaVInverseDepthMax
    simp only [descendantsAtDepth_zero,Book.Ch02.finsetSupReal,Finset.coe_singleton,Set.image_singleton,
      csSup_singleton]
    exact congrArg Book.Ch02.matrixNorm (Scalar.inverse_history_lowerRight Q _ hEll)
  rw [he] at hh
  exact mul_le_mul_of_nonneg_left hh (Annealed.sigmaBar_characterization M m).1.le

end ASDExplicitGamma.Inverse
