module

public import ASDExplicitGamma.Model.Cutoff
public import ASDExplicitGamma.Inverse.HistoryDefectSource
public import ASDExplicitGamma.Variational.AdapterShearTrace
public import ASDExplicitGamma.Variational.TraceDefect
public import Homogenization.CoarseGraining.BlockMatrixProperties

/-! The source full-response observable in an arbitrary fixed true frame. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse

open Homogenization Algsuperdiff.Section3 ASDExplicitGamma.Response ASDExplicitGamma.Variational
noncomputable section

/-- The four `(eᵢ, ±eᵢ)/√2` loads indexing a full response trace. -/
def fullResponseTraceLoad (j : Fin 2 × Bool) : BlockVec 2 :=
  orthonormalFrameLoad j.1 (if j.2 then 1 else -1)

/-- Algebraic trace identity for the frozen defect on any measurable carrier.
The source definition is the framed doubled-matrix trace minus four. -/
theorem traceDefect_eq_full_framedTrace (U : Set (Vec 2))
    (a : CoeffField 2) (σ : ℝ) :
    traceDefect U a σ =
      Matrix.trace (toFullBlockMat (frameMatrix σ (coarseBlockMatrix U a))) - 4 := by
  unfold traceDefect frameMatrix
  simp [Matrix.trace, toFullBlockMat, Fintype.sum_sum_type, Fin.sum_univ_two]
  ring

/-- Raising the scalar frame by at most `G` raises the full response trace by
at most `G`, provided both diagonal block traces are nonnegative. The upper
block uses the reverse scalar factor, so the lower bound on the frame ratio
is needed as well. -/
theorem full_response_framed_trace_le_of_scalar_frame_growth
    (A : BlockMat 2) (σold σ G : ℝ)
    (hσold : 0 < σold) (hσ : σold ≤ σ) (hG : 1 ≤ G)
    (hRatio : σ / σold ≤ G)
    (hUL : 0 ≤ Matrix.trace A.upperLeft)
    (hLR : 0 ≤ Matrix.trace A.lowerRight) :
    Matrix.trace (toFullBlockMat (frameMatrix σ A)) ≤
      G * Matrix.trace (toFullBlockMat (frameMatrix σold A)) := by
  have htrace (s : ℝ) :
      Matrix.trace (toFullBlockMat (frameMatrix s A)) =
        s⁻¹ * Matrix.trace A.upperLeft + s * Matrix.trace A.lowerRight := by
    simp [Matrix.trace, toFullBlockMat, frameMatrix, Fintype.sum_sum_type,
      Fin.sum_univ_two, Matrix.diag_apply]
    ring
  have hinv : σ⁻¹ ≤ σold⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le hσold hσ
  have hscale : σ ≤ G * σold := (div_le_iff₀ hσold).mp hRatio
  have hULstep : σ⁻¹ * Matrix.trace A.upperLeft ≤
      G * (σold⁻¹ * Matrix.trace A.upperLeft) := by
    calc
      _ ≤ σold⁻¹ * Matrix.trace A.upperLeft :=
        mul_le_mul_of_nonneg_right hinv hUL
      _ ≤ G * (σold⁻¹ * Matrix.trace A.upperLeft) :=
        by
          simpa only [one_mul] using
            (mul_le_mul_of_nonneg_right hG
              (mul_nonneg (inv_nonneg.mpr hσold.le) hUL))
  have hLRstep : σ * Matrix.trace A.lowerRight ≤
      G * (σold * Matrix.trace A.lowerRight) := by
    calc
      _ ≤ (G * σold) * Matrix.trace A.lowerRight :=
        mul_le_mul_of_nonneg_right hscale hLR
      _ = _ := by ring
  rw [htrace σ, htrace σold]
  nlinarith only [hULstep, hLRstep]

/-- The framed full matrix trace is the sum of its four orthonormal load
quadratics. This is the exact four-load basis used in the trace assembly. -/
theorem full_response_trace_eq_four_orthonormal_loads (σ : ℝ) (A : BlockMat 2) :
    Matrix.trace (toFullBlockMat (frameMatrix σ A)) =
      ∑ i : Fin 2,
        (blockVecDot (orthonormalFrameLoad i 1)
            (blockMatVecMul (frameMatrix σ A) (orthonormalFrameLoad i 1)) +
          blockVecDot (orthonormalFrameLoad i (-1))
            (blockMatVecMul (frameMatrix σ A) (orthonormalFrameLoad i (-1)))) := by
  have hp : ∀ i : Fin 2,
      blockVecDot (orthonormalFrameLoad i (1:ℝ))
        (blockMatVecMul (frameMatrix σ A) (orthonormalFrameLoad i 1)) =
        (σ⁻¹ * A.upperLeft i i + σ * A.lowerRight i i +
          (1:ℝ) * (A.upperRight i i + A.lowerLeft i i)) / 2 :=
    fun i => orthonormalFrameLoad_energy A σ i 1 (by norm_num)
  have hm : ∀ i : Fin 2,
      blockVecDot (orthonormalFrameLoad i (-1:ℝ))
        (blockMatVecMul (frameMatrix σ A) (orthonormalFrameLoad i (-1))) =
        (σ⁻¹ * A.upperLeft i i + σ * A.lowerRight i i +
          (-1:ℝ) * (A.upperRight i i + A.lowerLeft i i)) / 2 :=
    fun i => orthonormalFrameLoad_energy A σ i (-1) (by norm_num)
  simp_rw [hp, hm]
  simp [Matrix.trace, toFullBlockMat, frameMatrix, Fintype.sum_sum_type,
    Fin.sum_univ_two]
  ring

/-- The same four-load trace identity after the positive scalar frame has
been transferred from the response matrix to each loading vector. -/
theorem full_response_frame_trace_eq_scaled_loads (σ : ℝ) (A : BlockMat 2)
    (hσ : 0 < σ) :
    Matrix.trace (toFullBlockMat (frameMatrix σ A)) =
      ∑ j : Fin 2 × Bool,
        let P := fullResponseTraceLoad j
        let Pσ := ((Real.sqrt σ)⁻¹ • P.1, Real.sqrt σ • P.2)
        blockVecDot Pσ (blockMatVecMul A Pσ) := by
  have htrace := full_response_trace_eq_four_orthonormal_loads σ A
  let s := Real.sqrt σ
  have hs : 0 < s := Real.sqrt_pos.mpr hσ
  have hs2 : s^2 = σ := Real.sq_sqrt hσ.le
  have hframe (i : Fin 2) (ε : ℝ) :
      blockVecDot (orthonormalFrameLoad i ε)
        (blockMatVecMul (frameMatrix σ A) (orthonormalFrameLoad i ε)) =
      blockVecDot (s⁻¹ • (orthonormalFrameLoad i ε).1,
        s • (orthonormalFrameLoad i ε).2)
        (blockMatVecMul A (s⁻¹ • (orthonormalFrameLoad i ε).1,
          s • (orthonormalFrameLoad i ε).2)) := by
    have hh := Variational.frame_load_quadratic A (orthonormalFrameLoad i ε) s hs.ne'
    rw [hs2] at hh
    exact hh.symm
  rw [htrace]
  classical
  have hsum :
      (∑ j : Fin 2 × Bool,
        let P := fullResponseTraceLoad j
        let Pσ := (s⁻¹ • P.1, s • P.2)
        blockVecDot Pσ (blockMatVecMul A Pσ)) =
      ∑ i : Fin 2,
        (blockVecDot (s⁻¹ • (orthonormalFrameLoad i 1).1,
            s • (orthonormalFrameLoad i 1).2)
          (blockMatVecMul A (s⁻¹ • (orthonormalFrameLoad i 1).1,
            s • (orthonormalFrameLoad i 1).2)) +
        blockVecDot (s⁻¹ • (orthonormalFrameLoad i (-1)).1,
            s • (orthonormalFrameLoad i (-1)).2)
          (blockMatVecMul A (s⁻¹ • (orthonormalFrameLoad i (-1)).1,
            s • (orthonormalFrameLoad i (-1)).2))) := by
    rw [Fintype.sum_prod_type]
    simp [fullResponseTraceLoad]
  rw [hsum]
  simp_rw [hframe]

/-- A quadratic-form domination for every paired load transfers directly to
the complete fixed-frame trace. -/
theorem full_response_frame_trace_le_of_pair_quadratic (σ c : ℝ)
    (hσ : 0 < σ) (A B : BlockMat 2)
    (hAB : ∀ P : BlockVec 2,
      blockVecDot P (blockMatVecMul A P) ≤
        c * blockVecDot P (blockMatVecMul B P)) :
    Matrix.trace (toFullBlockMat (frameMatrix σ A)) / 4 ≤
      c * (Matrix.trace (toFullBlockMat (frameMatrix σ B)) / 4) := by
  let s := Real.sqrt σ
  have hs : 0 < s := Real.sqrt_pos.mpr hσ
  have hload (i : Fin 2) (ε : ℝ) :
      blockVecDot (orthonormalFrameLoad i ε)
          (blockMatVecMul (frameMatrix σ A) (orthonormalFrameLoad i ε)) ≤
        c * blockVecDot (orthonormalFrameLoad i ε)
          (blockMatVecMul (frameMatrix σ B) (orthonormalFrameLoad i ε)) := by
    have hqa := Variational.frame_load_quadratic A
      (orthonormalFrameLoad i ε) s hs.ne'
    have hqb := Variational.frame_load_quadratic B
      (orthonormalFrameLoad i ε) s hs.ne'
    have hAB' := hAB
      ((s⁻¹ • (orthonormalFrameLoad i ε).1,
        s • (orthonormalFrameLoad i ε).2) : BlockVec 2)
    have hs2 : s ^ 2 = σ := Real.sq_sqrt hσ.le
    rw [hs2] at hqa hqb
    rw [← hqa, ← hqb]
    exact hAB'
  have hsum :
      (∑ i : Fin 2,
        (blockVecDot (orthonormalFrameLoad i 1)
            (blockMatVecMul (frameMatrix σ A) (orthonormalFrameLoad i 1)) +
          blockVecDot (orthonormalFrameLoad i (-1))
            (blockMatVecMul (frameMatrix σ A) (orthonormalFrameLoad i (-1))))) ≤
      c * ∑ i : Fin 2,
        (blockVecDot (orthonormalFrameLoad i 1)
            (blockMatVecMul (frameMatrix σ B) (orthonormalFrameLoad i 1)) +
          blockVecDot (orthonormalFrameLoad i (-1))
            (blockMatVecMul (frameMatrix σ B) (orthonormalFrameLoad i (-1)))) := by
    calc
      _ ≤ ∑ i : Fin 2,
          (c * blockVecDot (orthonormalFrameLoad i 1)
              (blockMatVecMul (frameMatrix σ B) (orthonormalFrameLoad i 1)) +
            c * blockVecDot (orthonormalFrameLoad i (-1))
              (blockMatVecMul (frameMatrix σ B) (orthonormalFrameLoad i (-1)))) := by
        apply Finset.sum_le_sum
        intro i hi
        exact add_le_add (hload i 1) (hload i (-1))
      _ = _ := by simp_rw [← mul_add, ← Finset.mul_sum]
  rw [← full_response_trace_eq_four_orthonormal_loads σ A,
    ← full_response_trace_eq_four_orthonormal_loads σ B] at hsum
  nlinarith only [hsum]

/-- Algebraic shear payment: if the signed linear coefficient satisfies the
source discriminant bound `z² ≤ d*T`, then a unit-frame shear costs at most
`T + 2*g²*d` in the defect. -/
theorem full_response_shear_quadratic_payment {T d z g : ℝ}
    (hT : 0 ≤ T) (hd : 0 ≤ d) (hz : z ^ 2 ≤ d * T) :
    T + 2 * g * z + g ^ 2 * d ≤ 2 * T + 2 * g ^ 2 * d := by
  by_cases hd0 : d = 0
  · have hz0 : z = 0 := by rw [hd0] at hz; nlinarith only [hz]
    rw [hd0, hz0]
    nlinarith only [hT, sq_nonneg g]
  · have hdpos : 0 < d := lt_of_le_of_ne hd (Ne.symm hd0)
    have hsqrt : 0 < Real.sqrt d := Real.sqrt_pos.mpr hdpos
    have hsqrt2 : (Real.sqrt d)^2 = d := Real.sq_sqrt hd
    have hquot : z ^ 2 / d ≤ T := (div_le_iff₀ hdpos).2 (by nlinarith only [hz])
    let u := g*Real.sqrt d
    let v := z/Real.sqrt d
    have hu2 : u^2=g^2*d := by dsimp only [u]; rw [mul_pow,hsqrt2]
    have hv2 : v^2=z^2/d := by dsimp only [v]; rw [div_pow,hsqrt2]
    have huv : u*v=g*z := by
      dsimp only [u,v]
      field_simp [hsqrt.ne']
    have hv2T : v^2 ≤ T := by rw [hv2]; exact hquot
    have hYoung : 2*u*v ≤ u^2+v^2 := by nlinarith only [sq_nonneg (u-v)]
    calc
      T+2*g*z+g^2*d = T+2*(g*z)+g^2*d := by ring
      _ = T+2*(u*v)+u^2 := by rw [← huv, hu2]
      _ ≤ T+(u^2+v^2)+u^2 := by linarith only [hYoung]
      _ ≤ 2*T+2*g^2*d := by rw [hu2]; linarith only [hv2T]

/-- The exact constant-skew trace identity and its discriminant inequality
give the later-shear bound without replacing the shear by an independent
variable. -/
theorem response_traceDefect_constantSkew_upper_bound (Q : TriadicCube 2) (ν σ : ℝ)
    (hν : 0 < ν) (hσ : 0 < σ) (k : ResponseCoefficient (cubeSet Q)) (g : ℝ) :
    traceDefect (cubeSet Q)
        (fun x => responsePlanarCoefficient ν (responseCoefficientExtension k x + σ*g)) σ ≤
      2*traceDefect (cubeSet Q) (responsePlanarCoefficientField ν k) σ +
        2*g^2*Matrix.trace (frameMatrix σ
          (coarseBlockMatrix (cubeSet Q) (responsePlanarCoefficientField ν k))).lowerRight := by
  let A := coarseBlockMatrix (cubeSet Q) (responsePlanarCoefficientField ν k)
  let T := traceDefect (cubeSet Q) (responsePlanarCoefficientField ν k) σ
  let d := Matrix.trace (frameMatrix σ A).lowerRight
  let z := shearTraceLinear A
  have hEll := responsePlanarCoefficientField_isElliptic (measurableSet_cubeSet Q) ν hν k
  have hT : 0 ≤ T := Variational.traceDefect_nonneg_of_ellipticFieldOn_triCube hν hEll hσ
  have hpair := history_framed_pair_bounds Q (responsePlanarCoefficientField ν k) hν hEll σ hσ
  have hdiag (i : Fin 2) : 0 ≤ A.lowerRight i i := by
    let q : Vec 2 := Pi.single i 1
    have hq := hpair.1 0 q
    have hq' : 0 ≤ σ*A.lowerRight i i := by
      simpa [q, A, Variational.frameMatrix, blockVecDot, blockMatVecMul, vecDot,
        matVecMul, Matrix.mulVec, Matrix.smul_apply, Pi.single_apply, Fin.sum_univ_two] using hq
    have hdiv := div_nonneg hq' hσ.le
    have he : (σ*A.lowerRight i i)/σ=A.lowerRight i i := by field_simp [hσ.ne']
    rw [he] at hdiv
    exact hdiv
  have hd : 0 ≤ d := by
    dsimp only [d, A]
    simp only [Matrix.trace, Fin.sum_univ_two, Matrix.diag_apply, Variational.frameMatrix,
      Matrix.smul_apply, smul_eq_mul]
    exact add_nonneg (mul_nonneg hσ.le (hdiag 0)) (mul_nonneg hσ.le (hdiag 1))
  have hz := Variational.shearTraceLinear_sq_le Q ν σ hν hσ k
  have hpayment := full_response_shear_quadratic_payment (g := g) hT hd hz
  rw [Variational.response_traceDefect_constantSkew Q ν σ hν hσ k g]
  simpa only [T, d, z] using hpayment

/-- The later-shear trace payment after a centered full-pair comparison.
The comparison is applied to all four paired loads, and the same matrix order
also controls the lower-right trace which multiplies the quadratic shear. -/
theorem full_response_shear_trace_bound_of_pair_control (Q : TriadicCube 2)
    (ν σ g c : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (k : ResponseCoefficient (cubeSet Q)) (B : BlockMat 2)
    (hpair : ∀ P : BlockVec 2,
      blockVecDot P (blockMatVecMul
        (coarseBlockMatrix (cubeSet Q) (responsePlanarCoefficientField ν k)) P) ≤
        c * blockVecDot P (blockMatVecMul B P)) :
    traceDefect (cubeSet Q)
        (fun x => responsePlanarCoefficient ν (responseCoefficientExtension k x + σ*g)) σ ≤
      2 * (c * Matrix.trace (toFullBlockMat (frameMatrix σ B)) - 4) +
        2 * g^2 * c * Matrix.trace (frameMatrix σ B).lowerRight := by
  let A := coarseBlockMatrix (cubeSet Q) (responsePlanarCoefficientField ν k)
  have htrace := full_response_frame_trace_le_of_pair_quadratic σ c hσ A B hpair
  have htrace' : Matrix.trace (toFullBlockMat (frameMatrix σ A)) ≤
      c * Matrix.trace (toFullBlockMat (frameMatrix σ B)) := by
    nlinarith only [htrace]
  have hdiag (i : Fin 2) : A.lowerRight i i ≤ c * B.lowerRight i i := by
    have h := hpair (0, Pi.single i 1)
    simpa [A, blockVecDot, blockMatVecMul, vecDot, matVecMul, Matrix.mulVec,
      Pi.single_apply, Fin.sum_univ_two] using h
  have hlower : Matrix.trace (frameMatrix σ A).lowerRight ≤
      c * Matrix.trace (frameMatrix σ B).lowerRight := by
    have hsum : (∑ i : Fin 2, A.lowerRight i i) ≤
        c * ∑ i : Fin 2, B.lowerRight i i := by
      calc
        _ ≤ ∑ i : Fin 2, c * B.lowerRight i i :=
          Finset.sum_le_sum (fun i hi => hdiag i)
        _ = _ := by rw [Finset.mul_sum]
    simp only [Matrix.trace, Matrix.diag, Fin.sum_univ_two, frameMatrix,
      Matrix.smul_apply, smul_eq_mul]
    calc
      _ = σ * (A.lowerRight 0 0 + A.lowerRight 1 1) := by ring
      _ ≤ σ * (c * (B.lowerRight 0 0 + B.lowerRight 1 1)) :=
        mul_le_mul_of_nonneg_left (by simpa only [Fin.sum_univ_two] using hsum) hσ.le
      _ = _ := by ring
  have hdef : traceDefect (cubeSet Q) (responsePlanarCoefficientField ν k) σ + 4 =
      Matrix.trace (toFullBlockMat (frameMatrix σ A)) := by
    unfold traceDefect
    simp only [A, Matrix.trace, Matrix.diag, toFullBlockMat, Fintype.sum_sum_type,
      Fin.sum_univ_two, frameMatrix, Matrix.smul_apply, smul_eq_mul]
    ring
  have hbase : traceDefect (cubeSet Q) (responsePlanarCoefficientField ν k) σ ≤
      c * Matrix.trace (toFullBlockMat (frameMatrix σ B)) - 4 := by
    linarith only [htrace', hdef]
  have hshear := response_traceDefect_constantSkew_upper_bound Q ν σ hν hσ k g
  calc
    _ ≤ 2 * traceDefect (cubeSet Q) (responsePlanarCoefficientField ν k) σ +
        2 * g^2 * Matrix.trace (frameMatrix σ A).lowerRight := hshear
    _ ≤ 2 * (c * Matrix.trace (toFullBlockMat (frameMatrix σ B)) - 4) +
        2 * g^2 * c * Matrix.trace (frameMatrix σ B).lowerRight := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left hbase (by norm_num)
      · have hscaled := mul_le_mul_of_nonneg_left hlower (sq_nonneg g)
        have hscaled' := mul_le_mul_of_nonneg_left hscaled (by norm_num : (0:ℝ) ≤ 2)
        nlinarith only [hscaled']

end
end ASDExplicitGamma.Inverse
