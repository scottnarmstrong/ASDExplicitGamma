module

public import ASDExplicitGamma.Variational.LemmaVTrace
public import ASDExplicitGamma.Variational.LemmaVRowEstimate

/-! Lemma V for an abstract linear interpolant. The concrete DIAG interpolant
and its boundary property are deliberately separate. H2 includes convergence
of the positive Haar series: this is what asserting a finite P_br norm means,
without treating the real tsum of a divergent series as zero. -/

@[expose] public section

namespace ASDExplicitGamma.Variational

open Homogenization MeasureTheory ASDExplicitGamma.Response ASDExplicitGamma.Triadic

noncomputable section

/-- Lemma V with exactly the abstract interpolation assumptions: linearity
(the type of I), the affine H¹₀ residual property, and the finite row-form
product bound H2. The weak direction representatives describe W¹,∞ regularity
and column divergence in the coefficient normalized by σ. -/
theorem lemmaV_of_interpolant (m : ℤ) (j : ℕ) (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (k : ResponseCoefficient (openCubeSet (originCube 2 m))) :
    let Q := originCube 2 m
    let U := openCubeSet Q
    let hU := isOpenBoundedConvexDomain_openCubeSet Q
    ∀ (I : H1Function U →ₗ[ℝ] H1Function U)
      (H : ℕ → ResponseCoefficient U) (η : ℕ → H1Function U),
      (∀ l, MemLp (η l) (⊤ : ENNReal) (volume.restrict U)) →
      (∀ l b, MemLp (fun x => (η l).grad x b) (⊤ : ENNReal) (volume.restrict U)) →
      (∀ l, (η l).toFun =ᵐ[volume.restrict U]
        fun x => responseCoefficientExtension (H l) x / σ) →
      (∀ p (r : H10Function U), MemH10 U
        (lemmaVAffinePotential hU p r - I (lemmaVAffinePotential hU p r)).toFun) →
      ∀ κ : ℝ, 0 ≤ κ →
      (∀ p (r : H10Function U) (s : Finset ℕ) (c : ℕ → ℝ),
        (∑ l ∈ s, c l ^ 2) ≤ 1 →
        let v := lemmaVAffinePotential hU p r
        (∀ R ∈ descendantsAtDepth Q j, ∀ b,
          Summable (fun n => (Real.sqrt 3) ^ (n + 1) * energy R
            (cubeIncrement R (n + 1) (fun x => lemmaVRowCombination I η v s c x b)))) ∧
        Real.sqrt (lemmaVTiledPositiveEnergy Q j (lemmaVRowCombination I η v s c)) ≤
          κ * Real.sqrt (∑ l ∈ s, c l ^ 2) * Real.sqrt (lemmaVTiledWeakEnergy Q j v.grad)) →
      (∀ (s : Finset ℕ) (c : ℕ → ℝ), (∑ l ∈ s, c l ^ 2) ≤ 1 →
        |fderiv ℝ (lemmaVTrace m ν σ) k (∑ l ∈ s, c l • H l)| ≤
          2 * κ * lemmaVTileHistory Q j (responseFramePlanarCoefficientField ν σ k) *
            Real.sqrt (lemmaVTrace m ν σ k * (lemmaVTrace m ν σ k + 4)) *
              Real.sqrt (∑ l ∈ s, c l ^ 2)) ∧
      Summable (fun l : ℕ => (fderiv ℝ (lemmaVTrace m ν σ) k (H l)) ^ 2) ∧
      (∑' l : ℕ, (fderiv ℝ (lemmaVTrace m ν σ) k (H l)) ^ 2) ≤
        4 * κ ^ 2 * (lemmaVTileHistory Q j (responseFramePlanarCoefficientField ν σ k)) ^ 2 *
          lemmaVTrace m ν σ k * (lemmaVTrace m ν σ k + 4) := by
  intro Q U hU I H η hη hDη hlink hI κ hκ hH2
  let B := lemmaVTileHistory Q j (responseFramePlanarCoefficientField ν σ k)
  let E := lemmaVLoadEnergy m ν σ hν hσ
  choose r w hWT hVE hTP hDer using
    (fun p : Fin 2 × Bool => lemmaV_load_bounds m j ν σ hν hσ k p.1 p.2)
  let V (p : Fin 2 × Bool) := lemmaVAffinePotential hU
    (orthonormalFrameLoad p.1 (lemmaVLoadSign p.2)).1 (r p)
  let Wn (p : Fin 2 × Bool) := Real.sqrt (lemmaVTiledWeakEnergy Q j (w p).grad)
  let Vn (p : Fin 2 × Bool) := Real.sqrt (lemmaVTiledWeakEnergy Q j (V p).grad)
  let TP (p : Fin 2 × Bool) := E p k - 1
  let EP (p : Fin 2 × Bool) := E p k
  let T := ∑ p : Fin 2 × Bool, TP p
  let F := ∑ p : Fin 2 × Bool, EP p
  have hB : 0 ≤ B := lemmaVTileHistory_nonneg Q j _
  have hTP' (p : Fin 2 × Bool) : 0 ≤ TP p := hTP p
  have hEP (p : Fin 2 × Bool) : 0 ≤ EP p := by
    have h := hTP' p
    change 0 ≤ E p k - 1 at h
    change 0 ≤ E p k
    linarith only [h]
  have hT : 0 ≤ T := Finset.sum_nonneg fun p _ => hTP' p
  have hF : 0 ≤ F := Finset.sum_nonneg fun p _ => hEP p
  have hTF : 0 ≤ T * F := mul_nonneg hT hF
  have hTtrace : T = lemmaVTrace m ν σ k := by
    rw [lemmaVTrace_eq_load_sum m ν σ hν hσ]
    dsimp only [T, TP, E]
    rw [Finset.sum_sub_distrib]
    simp
  have hFtrace : F = lemmaVTrace m ν σ k + 4 := by
    rw [lemmaVTrace_eq_load_sum m ν σ hν hσ]
    dsimp only [F, EP, E]
    ring
  have hnorm : (∑ p : Fin 2 × Bool, Wn p * Vn p) ≤ B * Real.sqrt (T * F) := by
    apply lemmaV_load_norm_product_sum_le Finset.univ Wn Vn TP EP hB
      (fun p _ => Real.sqrt_nonneg _) (fun p _ => Real.sqrt_nonneg _)
      (fun p _ => hTP' p) (fun p _ => hEP p)
    · intro p _
      rw [show Wn p ^ 2 = lemmaVTiledWeakEnergy Q j (w p).grad from
        Real.sq_sqrt (lemmaVTiledWeakEnergy_nonneg Q j _)]
      exact hWT p
    · intro p _
      rw [show Vn p ^ 2 = lemmaVTiledWeakEnergy Q j (V p).grad from
        Real.sq_sqrt (lemmaVTiledWeakEnergy_nonneg Q j _)]
      exact hVE p
  have hdual (s : Finset ℕ) (c : ℕ → ℝ) (hc : (∑ l ∈ s, c l ^ 2) ≤ 1) :
      |∑ l ∈ s, c l * fderiv ℝ (lemmaVTrace m ν σ) k (H l)| ≤
        (2 * κ * B * Real.sqrt (T * F)) * Real.sqrt (∑ l ∈ s, c l ^ 2) := by
    have hload (p : Fin 2 × Bool) :
        |∑ l ∈ s, c l * fderiv ℝ (E p) k (H l)| ≤
          (2 * κ * Real.sqrt (∑ l ∈ s, c l ^ 2)) * (Wn p * Vn p) := by
      obtain ⟨hpos, hP⟩ := hH2
        (orthonormalFrameLoad p.1 (lemmaVLoadSign p.2)).1 (r p) s c hc
      have habs : |lemmaVLoadSign p.2| = 1 := by cases p.2 <;> norm_num [lemmaVLoadSign]
      apply lemmaV_directional_row_bound Q j I η (V p) (w p) H σ
        (fun l => fderiv ℝ (E p) k (H l)) (lemmaVLoadSign p.2) habs s c κ
        (hI _ (r p)) hη hDη hlink _ hpos hP
      intro l
      exact hDer p (H l)
    have heq : (∑ l ∈ s, c l * fderiv ℝ (lemmaVTrace m ν σ) k (H l)) =
        ∑ p : Fin 2 × Bool, ∑ l ∈ s, c l * fderiv ℝ (E p) k (H l) := by
      simp_rw [lemmaVTrace_fderiv_eq_load_sum m ν σ hν hσ, Finset.mul_sum]
      exact Finset.sum_comm
    rw [heq]
    calc
      _ ≤ ∑ p : Fin 2 × Bool, |∑ l ∈ s, c l * fderiv ℝ (E p) k (H l)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ p : Fin 2 × Bool, (2 * κ * Real.sqrt (∑ l ∈ s, c l ^ 2)) * (Wn p * Vn p) :=
        Finset.sum_le_sum fun p _ => hload p
      _ = (2 * κ * Real.sqrt (∑ l ∈ s, c l ^ 2)) * (∑ p : Fin 2 × Bool, Wn p * Vn p) :=
        (Finset.mul_sum _ _ _).symm
      _ ≤ (2 * κ * Real.sqrt (∑ l ∈ s, c l ^ 2)) * (B * Real.sqrt (T * F)) :=
        mul_le_mul_of_nonneg_left hnorm (by positivity)
      _ = _ := by ring
  have hCnonneg : 0 ≤ 2 * κ * B * Real.sqrt (T * F) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hκ) hB) (Real.sqrt_nonneg _)
  have hbr := lemmaV_bracket_summable_and_le_of_unit_dual_bound
    (fun l => fderiv ℝ (lemmaVTrace m ν σ) k (H l))
    (C := 2 * κ * B * Real.sqrt (T * F)) hCnonneg hdual
  have hC : (2 * κ * B * Real.sqrt (T * F)) ^ 2 = 4 * κ ^ 2 * B ^ 2 * T * F := by
    rw [mul_pow, Real.sq_sqrt hTF]
    ring
  obtain ⟨hsum, hbr⟩ := hbr
  rw [hC, hTtrace, hFtrace] at hbr
  refine ⟨?_, hsum, hbr⟩
  intro s c hc
  have h := hdual s c hc
  rw [hTtrace, hFtrace] at h
  simpa only [map_sum, map_smul, smul_eq_mul] using h

end

end ASDExplicitGamma.Variational
