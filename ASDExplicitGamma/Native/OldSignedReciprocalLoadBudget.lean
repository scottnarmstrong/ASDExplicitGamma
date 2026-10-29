module

public import ASDExplicitGamma.Native.OldSignedWeakTriangle
public import ASDExplicitGamma.Native.OldSignedErrorProfiles
public import ASDExplicitGamma.Native.OldSignedCellReciprocalPotential
public import ASDExplicitGamma.Native.OldSignedHaarCongr
public import ASDExplicitGamma.Main.InverseLowerRowBound

/-! The combined reciprocal-gradient size for the actual four parent
loads, retaining their affine second components and the same old medium. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ASDExplicitGamma.Response ASDExplicitGamma.Scalar
open ASDExplicitGamma.Triadic ASDExplicitGamma.Main
noncomputable section

/-- A constant reciprocal load costs at most its Euclidean norm. -/
theorem old_signed_constant_weak_bound (Q : TriadicCube 2) (p : Vec 2) :
    vectorWeakHaarNorm Q (fun _ => p)≤Real.sqrt (vecDot p p) := by
  apply Real.sqrt_le_sqrt
  have hh := main_vectorWeakHaarEnergy_le_coordinateEnergy Q (fun _ => p)
    (fun i => memLp_const (p i))
  simpa only [energy_const,vecDot,pow_two] using hh

/-- Adding an affine reciprocal load costs at most its Euclidean norm
in the actual cell weak norm. -/
theorem old_signed_vector_weak_affine_bound (Q : TriadicCube 2) (g : Vec 2 → Vec 2) (p : Vec 2)
    (hg : ∀ i : Fin 2,MemLp (fun x => g x i) 2 (normalizedCubeMeasure Q)) :
    vectorWeakHaarNorm Q g≤vectorWeakHaarNorm Q (fun x => g x-p)+Real.sqrt (vecDot p p) := by
  have hh := old_signed_vector_weak_triangle Q (f := fun x => g x-p) (g := fun _ => p)
    (fun i => (hg i).sub (memLp_const (p i))) (fun i => memLp_const (p i))
  have he : (fun x => (g x-p)+p)=g := by funext x; exact sub_add_cancel _ _
  rw [he] at hh
  exact hh.trans (add_le_add le_rfl (old_signed_constant_weak_bound Q p))

/-- All four actual parent reciprocal gradients have joint size at most
sqrt(2)+G_U. They remain restricted parent solutions, not cell solutions. -/
theorem old_signed_actual_reciprocal_load_budget (Q U : TriadicCube 2)
    (hsub : openCubeSet U ⊆ openCubeSet Q)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) :
    Real.sqrt (∑ c : BlockCoord 2,vectorWeakHaarNorm U
      (oldSignedCellReciprocalPotential Q U hsub nu sigma hnu hsigma k (blockBasis c)).grad^2) ≤
      Real.sqrt 2+oldSignedReciprocalErrorSize Q U nu sigma hnu hsigma k := by
  let g := fun c => (oldSignedCellReciprocalPotential Q U hsub nu sigma hnu hsigma k (blockBasis c)).grad
  let e := fun c => vectorWeakHaarNorm U (fun x => g c x-(blockBasis c).2)
  let p := fun c : BlockCoord 2 => Real.sqrt (vecDot (blockBasis c).2 (blockBasis c).2)
  have hp (c : BlockCoord 2) : vectorWeakHaarNorm U (g c)≤e c+p c :=
    old_signed_vector_weak_affine_bound U (g c) (blockBasis c).2
      (fun i => memLp_normalized_of_memL2On
        ((oldSignedCellReciprocalPotential Q U hsub nu sigma hnu hsigma k (blockBasis c)).grad_memVectorL2.eval i))
  have he (c : BlockCoord 2) : e c=vectorWeakHaarNorm U (fun x =>
      (blockMatVecMul (blockCoeffField (responseFramePlanarCoefficientField nu sigma k) x)
        (oldSignedFrameCanonicalField Q nu sigma hnu hsigma k (blockBasis c) x)).2-(blockBasis c).2) := by
    apply old_signed_vector_weak_congr
    have hg := ae_restrict_of_ae_restrict_of_subset hsub
      (old_signed_frame_reciprocal_potential_grad Q nu sigma hnu hsigma k (blockBasis c))
    filter_upwards [hg] with x hx
    change (oldSignedFrameReciprocalPotential Q nu sigma hnu hsigma k (blockBasis c)).grad x-_= _
    rw [hx]
  have hpsum : (∑ c : BlockCoord 2,p c^2)=(2:ℝ) := by
    simp [p,blockBasis,vecDot,Fintype.sum_sum_type,Fin.sum_univ_two]
    norm_num
  calc
    _ ≤ Real.sqrt (∑ c : BlockCoord 2,(e c+p c)^2) :=
      Real.sqrt_le_sqrt (Finset.sum_le_sum (fun c _ =>
        pow_le_pow_left₀ (Real.sqrt_nonneg _) (hp c) 2))
    _ ≤ Real.sqrt (∑ c : BlockCoord 2,e c^2)+Real.sqrt (∑ c : BlockCoord 2,p c^2) :=
      sqrt_finset_sq_add_le Finset.univ e p
    _ = _ := by simp_rw [he]; rw [hpsum]; exact add_comm _ _

/-- Top loads have zero affine reciprocal part, so their restricted
parent reciprocal gradients cost only G_U, with no sqrt(2) term. -/
theorem old_signed_actual_top_reciprocal_budget (Q U : TriadicCube 2)
    (hsub : openCubeSet U ⊆ openCubeSet Q)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) :
    Real.sqrt (∑ i : Fin 2,vectorWeakHaarNorm U
      (oldSignedCellReciprocalPotential Q U hsub nu sigma hnu hsigma k (blockBasis (Sum.inl i))).grad^2) ≤
      oldSignedReciprocalErrorSize Q U nu sigma hnu hsigma k := by
  let e := fun c : BlockCoord 2 => vectorWeakHaarNorm U (fun x =>
    (blockMatVecMul (blockCoeffField (responseFramePlanarCoefficientField nu sigma k) x)
      (oldSignedFrameCanonicalField Q nu sigma hnu hsigma k (blockBasis c) x)).2-(blockBasis c).2)
  have he (i : Fin 2) : vectorWeakHaarNorm U
      (oldSignedCellReciprocalPotential Q U hsub nu sigma hnu hsigma k (blockBasis (Sum.inl i))).grad=
      e (Sum.inl i) := by
    apply old_signed_vector_weak_congr
    have hg := ae_restrict_of_ae_restrict_of_subset hsub
      (old_signed_frame_reciprocal_potential_grad Q nu sigma hnu hsigma k (blockBasis (Sum.inl i)))
    filter_upwards [hg] with x hx
    change (oldSignedFrameReciprocalPotential Q nu sigma hnu hsigma k (blockBasis (Sum.inl i))).grad x= _
    rw [hx]
    exact (sub_zero _).symm
  apply Real.sqrt_le_sqrt
  simp_rw [he]
  change (∑ i : Fin 2,e (Sum.inl i)^2)≤∑ c : BlockCoord 2,e c^2
  rw [Fintype.sum_sum_type]
  exact le_add_of_nonneg_right (Finset.sum_nonneg (fun _ _ => sq_nonneg _))

end
end ASDExplicitGamma.Native
