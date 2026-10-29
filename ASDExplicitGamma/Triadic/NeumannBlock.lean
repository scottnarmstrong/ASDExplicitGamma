module

-- Ported from GMCExplicitDelta Haar/NeumannBlock.lean (Apache-2.0).

public import ASDExplicitGamma.Triadic.NeumannTest

/-!
# H5: the Neumann primitive of a Haar block (duality with the projected Poincaré inequality)

For `k = m + 1 ≥ 1` and a Neumann primitive `w = T D_k 𝐅` on a triadic cube `Q` of side `ℓ`:
`‖w‖² ≤ (5/54)(ℓ/3^m)² ‖D_k 𝐅‖²`, given the projected Poincaré inequality H4 on every cube
(`ProjectedPoincare`). Proof (step H5): for a finite set `S` of nonzero natural frequency
vectors put `A_S = ∑_{q ∈ S} m_q c_q²` (`c_q` the cosine coefficients of `w`). The spectral identity
gives `A_S = ∑_j ⟨G_j, v_j⟩` for the test fields `v_j = ∂_j z` of `z = ∑ (m_q c_q/λ_q) C_q`; since
`G_j = D_k F_j`, `⟨G_j, v_j⟩ = ⟨G_j, D_k v_j⟩`; H4 on the depth-`m` cells bounds
`‖D_k v_j‖² ≤ (5/54)(ℓ/3^m)² ∑_i ‖∂_i v_j‖²` and the Hessian identity gives
`∑_{i,j} ‖∂_i v_j‖² = A_S`. Hence `A_S ≤ (5/54)(ℓ/3^m)²‖G‖²`, and the cosine Parseval identity
(grouping `p ∈ ℤ^d` by `|p|`, at most `m_q` vectors per class) gives the bound for `‖w‖²`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology
open Homogenization

namespace ASDExplicitGamma.Triadic

variable {d : ℕ}

open Torus

/-! ### Grouping integer frequencies by their absolute values -/

/-- `|p|`, componentwise. -/
def natAbsVec (p : Fin d → ℤ) : Fin d → ℕ := fun i => (p i).natAbs

theorem card_filter_natAbsVec_le (T : Finset (Fin d → ℤ)) (q : Fin d → ℕ) :
    (((T.filter fun p => natAbsVec p = q).card : ℕ) : ℝ) ≤ modeMult q := by
  classical
  have hsub : T.filter (fun p => natAbsVec p = q) ⊆
      Fintype.piFinset (fun i => ({(q i : ℤ), -(q i : ℤ)} : Finset ℤ)) := by
    intro p hp
    rw [Finset.mem_filter] at hp
    rw [Fintype.mem_piFinset]
    intro i
    have h := congrFun hp.2 i
    simp only [natAbsVec] at h
    rcases Int.natAbs_eq (p i) with h' | h'
    · rw [h', h]
      simp
    · rw [h', h]
      simp
  calc (((T.filter fun p => natAbsVec p = q).card : ℕ) : ℝ)
      ≤ ((Fintype.piFinset (fun i => ({(q i : ℤ), -(q i : ℤ)} : Finset ℤ))).card : ℝ) :=
        Nat.cast_le.2 (Finset.card_le_card hsub)
    _ = ∏ i, (({(q i : ℤ), -(q i : ℤ)} : Finset ℤ).card : ℝ) := by
        rw [Fintype.card_piFinset, Nat.cast_prod]
    _ = modeMult q := by
        unfold modeMult
        refine Finset.prod_congr rfl fun i _ => ?_
        by_cases h : q i = 0
        · simp [h]
        · rw [ite_eq_right h, Finset.card_pair (by omega)]
          norm_num

theorem sum_le_sum_image_natAbsVec (T : Finset (Fin d → ℤ)) (φ : (Fin d → ℕ) → ℝ)
    (hφ : ∀ q, 0 ≤ φ q) :
    ∑ p ∈ T, φ (natAbsVec p) ≤ ∑ q ∈ T.image natAbsVec, modeMult q * φ q := by
  classical
  rw [Finset.sum_comp]
  refine Finset.sum_le_sum fun q _ => ?_
  rw [nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_right (card_filter_natAbsVec_le T q) (hφ q)

theorem cubeCos_natAbsVec (Q : TriadicCube d) (p : Fin d → ℤ) :
    cubeCos Q p = cubeCos Q (natVec (natAbsVec p)) := by
  funext x
  unfold cubeCos
  rw [boxMode_eq_prod_modeFactor, boxMode_eq_prod_modeFactor]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp only [modeFactor, Finset.notMem_empty, ite_false, natVec, natAbsVec]
  rcases Int.natAbs_eq (p i) with h | h
  · conv_lhs => rw [h]
  · conv_lhs => rw [h]
    rw [← Real.cos_neg]
    congr 1
    push_cast
    ring

theorem cubeCos_natVec_zero (Q : TriadicCube d) (x : Vec d) :
    cubeCos Q (natVec (0 : Fin d → ℕ)) x = 1 := by
  simp [cubeCos, boxMode, natVec]

/-! ### The H5 bound -/

end ASDExplicitGamma.Triadic
