module

public import ASDExplicitGamma.Scalar.PairedTwoSlotShear
public import ASDExplicitGamma.Scalar.PairedTwoSlotCellData

/-! Function representatives of Hilbert fields, the inner product as an integral, and
the pointwise skewness of the physical positive shear. -/

@[expose] public section

namespace ASDExplicitGamma.Scalar

open Homogenization MeasureTheory ASDExplicitGamma.Response ASDExplicitGamma.Triadic
  ASDExplicitGamma.Variational
open scoped InnerProduct InnerProductSpace

noncomputable section

/-- The function representative of a Hilbert field. -/
def rep' {U : Set (Vec 2)} (u : HilbertVectorL2 U) : Vec 2 → Vec 2 :=
  fun z => (hilbertVectorL2ToVectorL2 u : Vec 2 → Vec 2) z

theorem rep_memL2 {U : Set (Vec 2)} (u : HilbertVectorL2 U) :
    MemVectorL2 U (rep' u) := MeasureTheory.Lp.memLp (hilbertVectorL2ToVectorL2 u)

theorem hilbert_rebuild {U : Set (Vec 2)} (u : HilbertVectorL2 U) :
    toHilbertVectorL2OfVecField (rep_memL2 u) = u := by
  have h1 := hilbertVectorL2ToVectorL2_toHilbertVectorL2 (U := U) (rep_memL2 u)
  have h2 : toVectorL2 (rep_memL2 u) = hilbertVectorL2ToVectorL2 u := by
    unfold toVectorL2
    exact MeasureTheory.Lp.toLp_coeFn _ _
  rw [h2] at h1
  have h3 := congrArg (vectorL2ToHilbertVectorL2 (U := U)) h1
  rw [vectorL2ToHilbertVectorL2_hilbertVectorL2ToVectorL2,
    vectorL2ToHilbertVectorL2_hilbertVectorL2ToVectorL2] at h3
  exact h3

theorem inner_rep {U : Set (Vec 2)} (u v : HilbertVectorL2 U) :
    ⟪u, v⟫_ℝ = ∫ z in U, vecDot (rep' u z) (rep' v z) ∂volume := by
  conv_lhs => rw [← hilbert_rebuild u, ← hilbert_rebuild v]
  exact inner_toHilbertVectorL2OfVecField_eq_integral (rep_memL2 u) (rep_memL2 v)

theorem inner_ofField {U : Set (Vec 2)} {f g : Vec 2 → Vec 2}
    (hf : MemVectorL2 U f) (hg : MemVectorL2 U g) :
    ⟪toHilbertVectorL2OfVecField hf, toHilbertVectorL2OfVecField hg⟫_ℝ =
      ∫ z in U, vecDot (f z) (g z) ∂volume :=
  inner_toHilbertVectorL2OfVecField_eq_integral hf hg

theorem norm_sq_ofField {U : Set (Vec 2)} {f : Vec 2 → Vec 2}
    (hf : MemVectorL2 U f) :
    ‖toHilbertVectorL2OfVecField hf‖ ^ 2 = ∫ z in U, vecNormSq (f z) ∂volume := by
  rw [← real_inner_self_eq_norm_sq, inner_ofField hf hf]
  rfl

/-- The representative of the physical positive shear is the pointwise shear. -/
theorem rep_positiveShear (Q : TriadicCube 2) (σ : ℝ) (hσ : 0 < σ)
    (k : ResponseCoefficient (openCubeSet Q)) (p : HilbertVectorL2 (openCubeSet Q)) :
    rep' (physicalPositiveShear Q σ hσ k p) =ᵐ[volumeMeasureOn (openCubeSet Q)]
      fun z => shear' σ k z (rep' p z) := by
  filter_upwards [positiveShear_toPlain_ae Q σ hσ k p] with z hz
  exact hz

/-- The physical positive shear is skew for the Hilbert inner product. -/
theorem positiveShear_skew (Q : TriadicCube 2) (σ : ℝ) (hσ : 0 < σ)
    (k : ResponseCoefficient (openCubeSet Q)) (u v : HilbertVectorL2 (openCubeSet Q)) :
    ⟪physicalPositiveShear Q σ hσ k u, v⟫_ℝ =
      -⟪u, physicalPositiveShear Q σ hσ k v⟫_ℝ := by
  rw [inner_rep, inner_rep, ← MeasureTheory.integral_neg]
  apply MeasureTheory.integral_congr_ae
  filter_upwards [rep_positiveShear Q σ hσ k u, rep_positiveShear Q σ hσ k v]
    with z hu hv
  rw [hu, hv]
  have h := vecDot_J_skew (rep' u z) (rep' v z)
  simp only [shear', vecDot_smul_left, vecDot_smul_right]
  linarith [mul_comm (responseCoefficientExtension k z / σ)
    (vecDot (matVecMul responsePlanarJ (rep' u z)) (rep' v z)),
    show (responseCoefficientExtension k z / σ) *
      (vecDot (matVecMul responsePlanarJ (rep' u z)) (rep' v z) +
        vecDot (rep' u z) (matVecMul responsePlanarJ (rep' v z))) = 0 by rw [h]; ring]

end

end ASDExplicitGamma.Scalar
