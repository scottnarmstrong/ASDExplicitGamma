module

public import ASDExplicitGamma.Scalar.PhysicalResolventParity

/-! The defect source `S(H, H') = C_H (B C_{H'} u − u_flat(H'))` in the pure-flux pair space is
a continuous bilinear map of the fresh coefficients; its Wick expansion and continuity. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar

open Filter
open scoped BigOperators Topology InnerProductSpace

noncomputable section

theorem bil_tendsto {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (B : E →L[ℝ] E →L[ℝ] F) {Hn : ℕ → E} {H : E}
    (h : Tendsto Hn Filter.atTop (𝓝 H)) :
    Tendsto (fun n => B (Hn n) (Hn n)) Filter.atTop (𝓝 (B H H)) := by
  have hc : Continuous (fun p : E × E => B p.1 p.2) :=
    (B.continuous.comp continuous_fst).clm_apply continuous_snd
  exact (hc.tendsto (H, H)).comp (h.prodMk_nhds h)

section Generic

variable {Y X 𝓗 : Type*}
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup 𝓗] [NormedSpace ℝ 𝓗]

theorem block_smul (c : ℝ) (D : X →L[ℝ] Y) :
    pureFluxBlockOperator 0 (c • D) = c • pureFluxBlockOperator 0 D := by
  ext z
  refine WithLp.ofLp_injective 2 ?_
  rw [ContinuousLinearMap.smul_apply, WithLp.ofLp_smul, pureFluxBlockOperator_apply,
    pureFluxBlockOperator_apply]
  ext <;> simp

/-- The insertion block as a linear map of the coefficient operator. -/
def blockLin : (X →L[ℝ] Y) →ₗ[ℝ]
    (pureFluxPair (Y := Y) (X := X) →L[ℝ] pureFluxPair (Y := Y) (X := X)) where
  toFun := fun D => pureFluxBlockOperator 0 D
  map_add' := fun D D' => by
    have := pureFluxBlockOperator_add (Y := Y) (X := X) 0 D D'
    exact this.symm
  map_smul' := fun c D => by
    simp only [RingHom.id_apply]
    exact block_smul c D

/-- The insertion block as a continuous linear map of the coefficient operator. -/
def blockCLM : (X →L[ℝ] Y) →L[ℝ]
    (pureFluxPair (Y := Y) (X := X) →L[ℝ] pureFluxPair (Y := Y) (X := X)) :=
  LinearMap.mkContinuous (E := X →L[ℝ] Y)
    (F := pureFluxPair (Y := Y) (X := X) →L[ℝ] pureFluxPair (Y := Y) (X := X))
    (blockLin (Y := Y) (X := X)) 1 (fun D => by
    have h := pureFluxBlockInserted_opNorm_le D
    rw [one_mul]
    exact h)

theorem blockCLM_apply (D : X →L[ℝ] Y) :
    blockCLM (Y := Y) (X := X) D = pureFluxBlockOperator 0 D := rfl

/-- The pure-second injection `x ↦ (0, x)`. -/
def inr'' : X →L[ℝ] pureFluxPair (Y := Y) (X := X) :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ Y X).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.inr ℝ Y X)

theorem inr_apply' (x : X) :
    inr'' (Y := Y) x = (WithLp.toLp 2 (0, x) : pureFluxPair (Y := Y) (X := X)) := rfl


/-- The fresh block `H ↦ C_H`. -/
def cm'' (Vm : 𝓗 →L[ℝ] (X →L[ℝ] Y)) : 𝓗 →L[ℝ] (pureFluxPair (Y := Y) (X := X) →L[ℝ] pureFluxPair (Y := Y) (X := X)) :=
  (blockCLM (Y := Y) (X := X)).comp Vm

/-- The first-response defect `δu₁(H) = B C_H u − (0, σ F(H))`. -/
def delta' (Vm : 𝓗 →L[ℝ] (X →L[ℝ] Y)) (Fl : 𝓗 →L[ℝ] X)
    (Bop : pureFluxPair (Y := Y) (X := X) →L[ℝ] pureFluxPair (Y := Y) (X := X))
    (u : pureFluxPair (Y := Y) (X := X)) (σ : ℝ) : 𝓗 →L[ℝ] pureFluxPair (Y := Y) (X := X) :=
  (Bop.comp ((ContinuousLinearMap.apply ℝ (pureFluxPair (Y := Y) (X := X)) u).comp
    (cm'' Vm))) - σ • (inr'' (Y := Y)).comp Fl

theorem delta_apply' (Vm : 𝓗 →L[ℝ] (X →L[ℝ] Y)) (Fl : 𝓗 →L[ℝ] X)
    (Bop : pureFluxPair (Y := Y) (X := X) →L[ℝ] pureFluxPair (Y := Y) (X := X))
    (u : pureFluxPair (Y := Y) (X := X)) (σ : ℝ) (H : 𝓗) :
    delta' Vm Fl Bop u σ H =
      Bop (pureFluxBlockOperator 0 (Vm H) u) - σ • inr'' (Y := Y) (Fl H) := by
  simp only [delta', sub_apply, ContinuousLinearMap.comp_apply, smul_apply,
    ContinuousLinearMap.apply_apply, cm'', blockCLM_apply]

/-- The defect source as a continuous bilinear map. -/
def sbil (Vm : 𝓗 →L[ℝ] (X →L[ℝ] Y)) (Fl : 𝓗 →L[ℝ] X)
    (Bop : pureFluxPair (Y := Y) (X := X) →L[ℝ] pureFluxPair (Y := Y) (X := X))
    (u : pureFluxPair (Y := Y) (X := X)) (σ : ℝ) : 𝓗 →L[ℝ] 𝓗 →L[ℝ] pureFluxPair (Y := Y) (X := X) :=
  ((ContinuousLinearMap.compL ℝ 𝓗 (pureFluxPair (Y := Y) (X := X))
    (pureFluxPair (Y := Y) (X := X))).flip (delta' Vm Fl Bop u σ)).comp (cm'' Vm)

theorem sbil_apply (Vm : 𝓗 →L[ℝ] (X →L[ℝ] Y)) (Fl : 𝓗 →L[ℝ] X)
    (Bop : pureFluxPair (Y := Y) (X := X) →L[ℝ] pureFluxPair (Y := Y) (X := X))
    (u : pureFluxPair (Y := Y) (X := X)) (σ : ℝ) (H H' : 𝓗) :
    sbil Vm Fl Bop u σ H H' =
      pureFluxBlockOperator 0 (Vm H) (delta' Vm Fl Bop u σ H') := rfl

theorem sbil_expand (Vm : 𝓗 →L[ℝ] (X →L[ℝ] Y)) (Fl : 𝓗 →L[ℝ] X)
    (Bop : pureFluxPair (Y := Y) (X := X) →L[ℝ] pureFluxPair (Y := Y) (X := X))
    (u : pureFluxPair (Y := Y) (X := X)) (σ : ℝ) {n : ℕ} (x : Fin n → ℝ) (Hs : Fin n → 𝓗) :
    sbil Vm Fl Bop u σ (∑ i, x i • Hs i) (∑ j, x j • Hs j) =
      ∑ i, ∑ j, (x i * x j) • sbil Vm Fl Bop u σ (Hs i) (Hs j) := by
  simp only [map_sum, map_smul, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    smul_smul, Finset.smul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [mul_comm (x j) (x i)]

theorem sbil_tendsto (Vm : 𝓗 →L[ℝ] (X →L[ℝ] Y)) (Fl : 𝓗 →L[ℝ] X)
    (Bop : pureFluxPair (Y := Y) (X := X) →L[ℝ] pureFluxPair (Y := Y) (X := X))
    (u : pureFluxPair (Y := Y) (X := X)) (σ : ℝ) {Hn : ℕ → 𝓗} {H : 𝓗}
    (h : Tendsto Hn Filter.atTop (𝓝 H)) :
    Tendsto (fun n => sbil Vm Fl Bop u σ (Hn n) (Hn n)) Filter.atTop
      (𝓝 (sbil Vm Fl Bop u σ H H)) :=
  bil_tendsto (sbil Vm Fl Bop u σ) h

end Generic

end

end ASDExplicitGamma.Scalar
