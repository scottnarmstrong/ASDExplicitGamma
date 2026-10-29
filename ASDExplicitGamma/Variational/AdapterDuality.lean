module

public import ASDExplicitGamma.Variational.AdapterMu

@[expose] public section

namespace ASDExplicitGamma.Variational

open Homogenization MeasureTheory

private theorem adapter_isBoundedDomain_cubeSet {d : ℕ} (Q : TriadicCube d) :
    IsBoundedDomain (cubeSet Q) := by
  refine ⟨‖cubeCenter Q‖ + cubeRadius Q + 1, ?_, ?_⟩
  · have hnonneg : 0 ≤ ‖cubeCenter Q‖ + cubeRadius Q :=
      add_nonneg (norm_nonneg _) (cubeRadius_nonneg Q)
    linarith
  · intro x hx i
    have hxball : x ∈ Metric.closedBall (cubeCenter Q) (cubeRadius Q) :=
      cubeSet_subset_closedBall Q hx
    have hdist : ‖x - cubeCenter Q‖ ≤ cubeRadius Q := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hxball
    have hxnorm : ‖x‖ ≤ ‖cubeCenter Q‖ + cubeRadius Q + 1 := by
      calc
        ‖x‖ = ‖(x - cubeCenter Q) + cubeCenter Q‖ := by
          congr 1
          abel
        _ ≤ ‖x - cubeCenter Q‖ + ‖cubeCenter Q‖ := norm_add_le _ _
        _ ≤ cubeRadius Q + ‖cubeCenter Q‖ := add_le_add hdist le_rfl
        _ = ‖cubeCenter Q‖ + cubeRadius Q := by ring
        _ ≤ ‖cubeCenter Q‖ + cubeRadius Q + 1 := by linarith
    exact (by simpa [Real.norm_eq_abs] using (norm_le_pi_norm x i).trans hxnorm)

private theorem adapter_isSobolevRegularDomain_cubeSet {d : ℕ}
    (Q : TriadicCube d) :
    IsSobolevRegularDomain (cubeSet Q) :=
  ⟨measurableSet_cubeSet Q, adapter_isBoundedDomain_cubeSet Q⟩

private theorem adapter_ellipticFieldOn_adjoint {Q : TriadicCube 2} {ν Θ : ℝ}
    {a : CoeffField 2}
    (hEll : IsEllipticFieldOn ν Θ (cubeSet Q) a) :
    IsEllipticFieldOn ν Θ (cubeSet Q) (adjointCoeffField a) := by
  classical
  let U : Set (Vec 2) := cubeSet Q
  have hMeas : Measurable (fun x i j => if x ∈ U then a x i j else 0) := hEll.1
  refine ⟨?_, ?_⟩
  · apply measurable_pi_iff.2
    intro i
    apply measurable_pi_iff.2
    intro j
    change Measurable (fun x : Vec 2 => if x ∈ U then a x j i else 0)
    exact (measurable_pi_iff.mp (measurable_pi_iff.mp hMeas j) i)
  · intro x hx
    exact isEllipticMatrix_transpose (hEll.2 x hx)


/-- Variational pairing lower bound with arbitrary positive molecular part. -/
theorem Mu_ge_pairing_triCube {Q : TriadicCube 2} {ν Λ : ℝ} {a : CoeffField 2}
    (hEll : IsEllipticFieldOn ν Λ (cubeSet Q) a) (P : BlockVec 2) :
    vecDot P.1 P.2 ≤ Mu (cubeSet Q) P a := by
  exact IsBlockMuAdmissible.mu_ge_vecDot_of_isEllipticFieldOn_of_isSobolevRegularDomain
    (adapter_isSobolevRegularDomain_cubeSet Q) hEll (volume_cubeSet_toReal_pos Q).ne'

/-- Both signs of the load pairing are bounded by the actual coarse energy. -/
theorem coarse_energy_ge_abs_pairing {Q : TriadicCube 2} {ν Λ : ℝ}
    {a : CoeffField 2} (hν : 0 < ν) (hEll : IsEllipticFieldOn ν Λ (cubeSet Q) a)
    (P : BlockVec 2) :
    2 * |vecDot P.1 P.2| ≤
      blockVecDot P (blockMatVecMul (coarseBlockMatrix (cubeSet Q) a) P) := by
  have hp := Mu_ge_pairing_triCube hEll P
  have hn := Mu_ge_pairing_triCube (adapter_ellipticFieldOn_adjoint hEll)
    (blockVecFlipFlux P)
  rw [Mu_adjointCoeffField_flipFlux] at hn
  have hdot : vecDot (blockVecFlipFlux P).1 (blockVecFlipFlux P).2 =
      -vecDot P.1 P.2 := by simp [blockVecFlipFlux, vecDot_neg_right]
  rw [hdot] at hn
  rw [mu_eq_half_coarseBlockMatrix_elliptic_triCube hν hEll] at hp hn
  rcases le_total 0 (vecDot P.1 P.2) with hh | hh
  · rw [abs_of_nonneg hh]; linarith
  · rw [abs_of_nonpos hh]; linarith

private theorem energy_pairing_cross_bound {d : ℕ} (A : BlockMat d)
    (h : ∀ P : BlockVec d, 2 * |vecDot P.1 P.2| ≤ blockVecDot P (blockMatVecMul A P))
    (X Y : BlockVec d) :
    (blockVecDot X (Y.2, Y.1)) ^ 2 ≤
      blockVecDot X (blockMatVecMul A X) * blockVecDot Y (blockMatVecMul A Y) := by
  have hquad (t : ℝ) :
      0 ≤ blockVecDot Y (blockMatVecMul A Y) * (t * t) -
        2 * blockVecDot X (Y.2, Y.1) * t + blockVecDot X (blockMatVecMul A X) := by
    have hp := h (X + t • Y)
    have hn := h (X + (-t) • Y)
    have hap := le_abs_self (vecDot (X + t • Y).1 (X + t • Y).2)
    have han := neg_le_abs (vecDot (X + (-t) • Y).1 (X + (-t) • Y).2)
    have hpp : 2 * vecDot (X + t • Y).1 (X + t • Y).2 ≤
        blockVecDot (X + t • Y) (blockMatVecMul A (X + t • Y)) := by linarith
    have hnn : -2 * vecDot (X + (-t) • Y).1 (X + (-t) • Y).2 ≤
        blockVecDot (X + (-t) • Y) (blockMatVecMul A (X + (-t) • Y)) := by linarith
    simp only [blockMatVecMul_add, blockMatVecMul_smul, blockVecDot_add_left,
      blockVecDot_add_right, blockVecDot_smul_left, blockVecDot_smul_right,
      Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
      vecDot_add_left, vecDot_add_right, vecDot_smul_left, vecDot_smul_right] at hpp hnn
    change 0 ≤ _ - 2 * (vecDot X.1 Y.2 + vecDot X.2 Y.1) * t + _
    rw [vecDot_comm X.2 Y.1]
    nlinarith only [hpp, hnn]
  have hd := discrim_le_zero (a := blockVecDot Y (blockMatVecMul A Y))
    (b := -2 * blockVecDot X (Y.2, Y.1))
    (c := blockVecDot X (blockMatVecMul A X)) (fun t => by
      convert hquad t using 1; ring)
  dsimp only [discrim] at hd
  nlinarith only [hd]

private theorem posDef_of_energy_pairing_bound {d : ℕ} (A : BlockMat d)
    (hA : IsSymmetricBlockMat A)
    (h : ∀ P : BlockVec d, 2 * |vecDot P.1 P.2| ≤ blockVecDot P (blockMatVecMul A P)) :
    (toFullBlockMat A).PosDef := by
  apply Matrix.posDef_iff_dotProduct_mulVec.mpr
  refine ⟨?_, ?_⟩
  · rw [Matrix.isHermitian_iff_isSymm]
    ext α β
    exact hA β α
  · intro x hx
    let X := ofFullBlockVec x
    have he : blockVecDot X (blockMatVecMul A X) =
        dotProduct x (Matrix.mulVec (toFullBlockMat A) x) := by
      rw [← dotProduct_toFullBlockVec, toFullBlockVec_blockMatVecMul]
      simp only [X, toFullBlockVec_ofFullBlockVec]
    simp only [star_trivial]
    rw [← he]
    have hnonneg : 0 ≤ blockVecDot X (blockMatVecMul A X) :=
      le_trans (mul_nonneg (by norm_num) (abs_nonneg _)) (h X)
    apply lt_of_le_of_ne' hnonneg
    intro hz
    have hc := energy_pairing_cross_bound A h X (X.2, X.1)
    rw [hz, zero_mul] at hc
    have hzX : blockVecDot X X = 0 := by
      change (blockVecDot X X) ^ 2 ≤ 0 at hc
      nlinarith only [hc, blockVecDot_nonneg X]
    have hx0 : dotProduct x x = 0 := by
      rw [← dotProduct_toFullBlockVec] at hzX
      simpa only [X, toFullBlockVec_ofFullBlockVec] using hzX
    exact hx (dotProduct_self_eq_zero.mp hx0)

/-- The doubled coarse matrix is positive definite, with no recovery premise. -/
theorem coarseBlockMatrix_posDef {Q : TriadicCube 2} {ν Λ : ℝ}
    {a : CoeffField 2} (hν : 0 < ν) (hEll : IsEllipticFieldOn ν Λ (cubeSet Q) a) :
    (toFullBlockMat (coarseBlockMatrix (cubeSet Q) a)).PosDef :=
  posDef_of_energy_pairing_bound _ (coarseBlockMatrix_symmetric _ _)
    (coarse_energy_ge_abs_pairing hν hEll)

private theorem inverse_duality_of_energy_pairing_bound {d : ℕ} (A : BlockMat d)
    (hA : IsSymmetricBlockMat A)
    (h : ∀ P : BlockVec d, 2 * |vecDot P.1 P.2| ≤ blockVecDot P (blockMatVecMul A P)) :
    BlockMatLoewnerLE (ofFullBlockMat ((toFullBlockMat A)⁻¹)) (blockReflect A) := by
  have hpos := posDef_of_energy_pairing_bound A hA h
  have hdet : IsUnit (toFullBlockMat A).det := (Matrix.isUnit_iff_isUnit_det _).mp hpos.isUnit
  intro P
  let Y : BlockVec d := (P.2, P.1)
  let X : BlockVec d := blockMatVecMul (ofFullBlockMat ((toFullBlockMat A)⁻¹)) P
  have hAX : blockMatVecMul A X = P := by
    apply (show Function.Injective (@toFullBlockVec d) from fun V W hv => by
      simpa only [ofFullBlockVec_toFullBlockVec] using congrArg ofFullBlockVec hv)
    simp only [X, toFullBlockVec_blockMatVecMul, toFullBlockMat_ofFullBlockMat]
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
  have hc := energy_pairing_cross_bound A h X Y
  have hX : blockVecDot X (Y.2, Y.1) = blockVecDot X (blockMatVecMul A X) := by
    rw [hAX]
  rw [hX] at hc
  have hzero : 0 ≤ blockVecDot X (blockMatVecMul A X) :=
    le_trans (mul_nonneg (by norm_num) (abs_nonneg _)) (h X)
  have hle : blockVecDot X (blockMatVecMul A X) ≤ blockVecDot Y (blockMatVecMul A Y) := by
    by_cases hz : blockVecDot X (blockMatVecMul A X) = 0
    · rw [hz]
      exact le_trans (mul_nonneg (by norm_num) (abs_nonneg _)) (h Y)
    · have hp := lt_of_le_of_ne' hzero hz
      nlinarith only [hc, hp]
  rw [hAX, blockVecDot_comm] at hle
  change (1 / 2 : ℝ) * _ ≤ (1 / 2 : ℝ) * _
  apply mul_le_mul_of_nonneg_left ?_ (by norm_num)
  simpa only [blockVecDot_blockMatVecMul_blockReflect, X, Y] using hle

/-- VA-COARSE-DUALITY: A⁻¹ ≤ R A R for the actual coarse matrix. -/
theorem coarseBlockMatrix_inverse_duality {Q : TriadicCube 2} {ν Λ : ℝ}
    {a : CoeffField 2} (hν : 0 < ν) (hEll : IsEllipticFieldOn ν Λ (cubeSet Q) a) :
    BlockMatLoewnerLE
      (ofFullBlockMat ((toFullBlockMat (coarseBlockMatrix (cubeSet Q) a))⁻¹))
      (blockReflect (coarseBlockMatrix (cubeSet Q) a)) :=
  inverse_duality_of_energy_pairing_bound _ (coarseBlockMatrix_symmetric _ _)
    (coarse_energy_ge_abs_pairing hν hEll)

/-- Source inverse duality, discharging ellipticity from bounded continuous k. -/
theorem response_coarse_inverse_duality (Q : TriadicCube 2) (ν : ℝ) (hν : 0 < ν)
    (k : ASDExplicitGamma.Response.ResponseCoefficient (cubeSet Q)) :
    BlockMatLoewnerLE
      (ofFullBlockMat ((toFullBlockMat (coarseBlockMatrix (cubeSet Q)
        (ASDExplicitGamma.Response.responsePlanarCoefficientField ν k)))⁻¹))
      (blockReflect (coarseBlockMatrix (cubeSet Q)
        (ASDExplicitGamma.Response.responsePlanarCoefficientField ν k))) :=
  coarseBlockMatrix_inverse_duality hν
    (ASDExplicitGamma.Response.responsePlanarCoefficientField_isElliptic
      (measurableSet_cubeSet Q) ν hν k)

/-- Source all-load energy inequality with no separately supplied ellipticity. -/
theorem response_coarse_energy_ge_abs_pairing (Q : TriadicCube 2) (ν : ℝ) (hν : 0 < ν)
    (k : ASDExplicitGamma.Response.ResponseCoefficient (cubeSet Q)) (P : BlockVec 2) :
    2 * |vecDot P.1 P.2| ≤ blockVecDot P (blockMatVecMul
      (coarseBlockMatrix (cubeSet Q) (ASDExplicitGamma.Response.responsePlanarCoefficientField ν k)) P) :=
  coarse_energy_ge_abs_pairing hν
    (ASDExplicitGamma.Response.responsePlanarCoefficientField_isElliptic
      (measurableSet_cubeSet Q) ν hν k) P

end ASDExplicitGamma.Variational
