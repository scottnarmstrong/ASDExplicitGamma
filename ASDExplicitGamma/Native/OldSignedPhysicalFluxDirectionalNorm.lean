module

public import ASDExplicitGamma.Native.OldSignedPhysicalFluxDirection
public import ASDExplicitGamma.Native.OldSignedFullWeakProjection

/-! Sharp complete directional norm of the actual physical-flux affine error. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Variational Triadic Inverse
noncomputable section

/-- Pure-direction physical flux has the sharp complete OLD weak payment,
with the affine mean and every depth retained. -/
theorem old_signed_physical_flux_directional_weak_norm (Q : TriadicCube 2)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (bottom : Bool) (e : Vec 2) :
    let a := responseFramePlanarCoefficientField nu sigma k
    let P := oldSignedDirectionalLoad bottom e
    let S : Vec 2 → BlockVec 2 := oldSignedFrameCanonicalField Q nu sigma hnu hsigma k P
    (oldSignedBlockWeakNorm Q (fun x => scalarCoefficientFlux a S x-P))^2 ≤
      2*oldSignedCorrectorHistory Q a*vecNormSq e := by
  intro a P S
  let JS := oldSignedDualReflection Q nu sigma k S
  let G : Vec 2 → BlockVec 2 := fun x => JS x-P.swap
  let F : Vec 2 → BlockVec 2 := fun x => scalarCoefficientFlux a S x-P
  have hS : MemBlockL2 (openCubeSet Q) S :=
    Lp.memLp (oldSignedFrameCanonicalField Q nu sigma hnu hsigma k P)
  have hJS := old_signed_dual_reflection_memL2 Q nu sigma hnu hsigma k hS
  have hG : MemBlockL2 (openCubeSet Q) G := hJS.sub (memLp_const P.swap)
  have hdepth (j : ℕ) : oldSignedFullProjectionEnergy Q j G ≤
      (2*vecNormSq e)*(fullResponseDepthMax Q a j*
        descendantsAverage Q j (fun U => traceDefect (openCubeSet U) a 1)) := by
    have hp := old_signed_full_patch_projection_bound Q j nu sigma hnu hsigma k P.swap JS
      (old_signed_reflected_canonical_compatible Q nu sigma hnu hsigma k P)
    dsimp only at hp
    have he := old_signed_physical_flux_directional_energy Q j nu sigma hnu hsigma k bottom e
    dsimp only at he
    rw [he] at hp
    have hd := old_signed_physical_flux_directional_two_trace_bound Q j nu sigma hnu hsigma k bottom e
    have hh := hp.trans (mul_le_mul_of_nonneg_left hd (full_response_depth_max_nonneg Q a j))
    have halg : fullResponseDepthMax Q a j*
        (2*descendantsAverage Q j (fun U => traceDefect (openCubeSet U) a 1)*vecNormSq e)=
        (2*vecNormSq e)*(fullResponseDepthMax Q a j*
          descendantsAverage Q j (fun U => traceDefect (openCubeSet U) a 1)) := by ring
    simpa only [oldSignedFullProjectionEnergy,G,Pi.sub_apply,Prod.fst_sub,Prod.snd_sub] using hh.trans_eq halg
  have hEll := responseFramePlanarCoefficientField_isElliptic (measurableSet_openCubeSet Q)
    nu sigma hnu hsigma k
  have hb := old_signed_full_weak_proxy_bound Q a hEll G hG (2*vecNormSq e) hdepth
  have hc := mul_le_mul_of_nonneg_left (old_signed_full_trace_proxy_le_history Q a hEll)
    (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) (vecNormSq_nonneg e))
  have hh := hb.trans hc
  have he : (fun x => (F x).swap)=G := rfl
  have hn := old_signed_block_weak_norm_sq_swap Q F
  rw [he] at hn
  change (oldSignedBlockWeakNorm Q F)^2 ≤ _
  rw [←hn]
  exact hh.trans_eq (by ring)

end
end ASDExplicitGamma.Native
