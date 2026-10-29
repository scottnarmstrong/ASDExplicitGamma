module

public import ASDExplicitGamma.Main.HotCovReceiver

/-! MA-E-COVARIANCE, step 6: the exact principal identity.  The frozen-source
cross against a top (resp. bottom) affine receiver, summed over the source cells,
equals the same cross against the reciprocal block of the cell comparison `W`.
All parent terms vanish after global assembly. -/

@[expose] public section

namespace ASDExplicitGamma.Main

open Homogenization MeasureTheory ASDExplicitGamma.Native
  ASDExplicitGamma.Response ASDExplicitGamma.Scalar ASDExplicitGamma.Triadic
  ASDExplicitGamma.Variational

noncomputable section

local instance hotCovPrincipalFiniteMeasure (Q : TriadicCube 2) :
    IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
  (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume

theorem hotCov_vecDot_sub_right {d : ℕ} (x y z : Vec d) :
    vecDot x (y - z) = vecDot x y - vecDot x z := by
  simp [vecDot, mul_sub, Finset.sum_sub_distrib]

theorem hotCov_memVectorL2_of_coord {U : Set (Vec 2)} {f : Vec 2 → Vec 2}
    (hf : ∀ i, MemLp (fun x => f x i) 2 (volumeMeasureOn U)) : MemVectorL2 U f :=
  memLp_pi_iff.mpr hf

theorem hotCov_memVectorL2_quarterTurn {U : Set (Vec 2)} {f : Vec 2 → Vec 2}
    (hf : MemVectorL2 U f) : MemVectorL2 U (fun x => planarQuarterTurn (f x)) := by
  have h0 := memScalarL2_coord_of_memVectorL2 hf 0
  have h1 := memScalarL2_coord_of_memVectorL2 hf 1
  apply hotCov_memVectorL2_of_coord
  intro i
  fin_cases i
  · simp only [planarQuarterTurn, if_true]
    exact h1.neg
  · simpa [planarQuarterTurn] using h0

/-- The interpolant gradient `z` of a zero-trace coarse potential. -/
abbrev hotCovZfield (Q : TriadicCube 2) (d : ℕ) (w : H10Function (openCubeSet Q)) (x : Vec 2) :
    Vec 2 := (diagInterpolant Q d w.toH1Function).grad x

/-- The cell cross between the frozen direction `J z` and a field `e`. -/
abbrev hotCovCross (U : TriadicCube 2) (z e : Vec 2 → Vec 2) : ℝ :=
  volumeAverage (openCubeSet U) (fun x => vecDot (planarQuarterTurn (z x)) (e x))

theorem hotCov_cross_integrable (Q U : TriadicCube 2) (hU : openCubeSet U ⊆ openCubeSet Q)
    {z e : Vec 2 → Vec 2} (hz : MemVectorL2 (openCubeSet Q) z)
    (he : MemVectorL2 (openCubeSet U) e) :
    IntegrableOn (fun x => vecDot (planarQuarterTurn (z x)) (e x)) (openCubeSet U) volume :=
  integrableOn_vecDot_of_memVectorL2
    (hotCov_memVectorL2_quarterTurn (hz.mono_measure (Measure.restrict_mono_set volume hU))) he

theorem hotCov_cmpRecip_memL2 (Q : TriadicCube 2) (d : ℕ) (nu sigma : ℝ)
    (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (U : OldSignedCellIndex Q d) (P : BlockVec 2) :
    MemVectorL2 (openCubeSet U.val) (hotCovCmpRecip Q d nu sigma hnu hsigma k U P) := by
  have hsub := openCubeSet_subset_of_mem_descendantsAtDepth U.property
  have hEll := (responseFramePlanarCoefficientField_isElliptic (measurableSet_openCubeSet Q)
    nu sigma hnu hsigma k).mono (measurableSet_openCubeSet U.val) hsub
  have hm := old_hessian_parent_cell_comparison_memL2 Q U.val hsub nu sigma hnu hsigma k P
  have hf := scalar_coefficient_flux_memL2 U.val _ hEll hm
  exact memVectorL2_snd_of_memBlockL2 hf

theorem hotCov_parentRecip_memL2 (Q : TriadicCube 2) (nu sigma : ℝ)
    (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (P : BlockVec 2) :
    MemVectorL2 (openCubeSet Q) (hotCovParentRecip Q nu sigma hnu hsigma k P) :=
  memVectorL2_fst_of_memBlockL2
    (old_signed_dual_reflection_memL2 Q nu sigma hnu hsigma k (Lp.memLp _))

theorem hotCov_zfield_memL2 (Q : TriadicCube 2) (d : ℕ) (w : H10Function (openCubeSet Q)) :
    MemVectorL2 (openCubeSet Q) (hotCovZfield Q d w) :=
  (diagInterpolant Q d w.toH1Function).grad_memVectorL2

/-- Abstract principal assembly: if on every cell the receiver `e U` is `c U - G` with
a global field `G` orthogonal to `J z` on the parent, the receiver cross and the
`c`-cross have equal cell averages. -/
theorem hotCov_principal_split (Q : TriadicCube 2) (d : ℕ)
    (z G : Vec 2 → Vec 2) (e c : OldSignedCellIndex Q d → Vec 2 → Vec 2)
    (hz : MemVectorL2 (openCubeSet Q) z) (hG : MemVectorL2 (openCubeSet Q) G)
    (hGorth : ∫ x in openCubeSet Q, vecDot (planarQuarterTurn (z x)) (G x) ∂volume = 0)
    (hc : ∀ U, MemVectorL2 (openCubeSet U.val) (c U))
    (hsplit : ∀ U, ∀ᵐ x ∂(volumeMeasureOn (openCubeSet U.val)), e U x = c U x - G x) :
    oldSignedCellAverage Q d (fun U => hotCovCross U.val z (e U)) =
      oldSignedCellAverage Q d (fun U => hotCovCross U.val z (c U)) := by
  have hsub (U : OldSignedCellIndex Q d) :=
    openCubeSet_subset_of_mem_descendantsAtDepth U.property
  have hGU (U : OldSignedCellIndex Q d) : MemVectorL2 (openCubeSet U.val) G :=
    hG.mono_measure (Measure.restrict_mono_set volume (hsub U))
  have hcell (U : OldSignedCellIndex Q d) :
      hotCovCross U.val z (e U) = hotCovCross U.val z (c U) - hotCovCross U.val z G := by
    have hint1 := hotCov_cross_integrable Q U.val (hsub U) hz (hc U)
    have hint2 := hotCov_cross_integrable Q U.val (hsub U) hz (hGU U)
    have hae : (fun x => vecDot (planarQuarterTurn (z x)) (e U x)) =ᵐ[volume.restrict (openCubeSet U.val)]
        (fun x => vecDot (planarQuarterTurn (z x)) (c U x) - vecDot (planarQuarterTurn (z x)) (G x)) := by
      filter_upwards [hsplit U] with x hx
      rw [hx, hotCov_vecDot_sub_right]
    unfold hotCovCross volumeAverage
    rw [integral_congr_ae hae, integral_sub hint1 hint2, mul_sub]
  have hsum : oldSignedCellAverage Q d (fun U => hotCovCross U.val z G) = 0 := by
    have hint : IntegrableOn (fun x => vecDot (planarQuarterTurn (z x)) (G x)) (openCubeSet Q) volume :=
      integrableOn_vecDot_of_memVectorL2 (hotCov_memVectorL2_quarterTurn hz) hG
    have h1 := old_signed_volumeAverage_descendants Q d
      (fun x => vecDot (planarQuarterTurn (z x)) (G x)) hint
    have h2 := old_signed_cell_average_eq_descendantsAverage Q d
      (fun R => volumeAverage (openCubeSet R) (fun x => vecDot (planarQuarterTurn (z x)) (G x)))
    change oldSignedCellAverage Q d (fun U => volumeAverage (openCubeSet U.val)
      (fun x => vecDot (planarQuarterTurn (z x)) (G x))) = 0
    rw [h2, ← h1]
    unfold volumeAverage
    rw [hGorth, mul_zero]
  have : oldSignedCellAverage Q d (fun U => hotCovCross U.val z (e U)) =
      oldSignedCellAverage Q d (fun U => hotCovCross U.val z (c U)) -
        oldSignedCellAverage Q d (fun U => hotCovCross U.val z G) := by
    rw [← old_signed_cell_average_sub]
    congr 1
    funext U
    exact hcell U
  rw [this, hsum, sub_zero]

/-- Exact principal identity for a TOP-load source: the frozen cross with the receiver
`-B_U^rec ν` equals the cross with the reciprocal block `g_W` of the drop for the bottom
load `(0,ν)`. -/
theorem hotCov_top_principal_identity (Q : TriadicCube 2) (d : ℕ) (nu sigma : ℝ)
    (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (w : H10Function (openCubeSet Q)) (ν : Vec 2) :
    oldSignedCellAverage Q d (fun U => hotCovCross U.val (hotCovZfield Q d w)
      (hotCovTopRcv Q d nu sigma hnu hsigma k U ν)) =
    oldSignedCellAverage Q d (fun U => hotCovCross U.val (hotCovZfield Q d w)
      (hotCovCmpRecip Q d nu sigma hnu hsigma k U (0, ν))) := by
  refine hotCov_principal_split Q d (hotCovZfield Q d w)
    (fun x => hotCovParentRecip Q nu sigma hnu hsigma k (0, ν) x - ν)
    (fun U => hotCovTopRcv Q d nu sigma hnu hsigma k U ν)
    (fun U => hotCovCmpRecip Q d nu sigma hnu hsigma k U (0, ν))
    (hotCov_zfield_memL2 Q d w)
    ((hotCov_parentRecip_memL2 Q nu sigma hnu hsigma k (0, ν)).sub (memVectorL2_const ν))
    (hotCov_parent_orth Q d nu sigma hnu hsigma k (0, ν) ν w)
    (fun U => hotCov_cmpRecip_memL2 Q d nu sigma hnu hsigma k U (0, ν))
    (fun U => ?_)
  filter_upwards [hotCov_topRcv_split Q d nu sigma hnu hsigma k U ν] with x hx
  rw [hx]

/-- Exact principal identity for a BOTTOM-load source. -/
theorem hotCov_bot_principal_identity (Q : TriadicCube 2) (d : ℕ) (nu sigma : ℝ)
    (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (w : H10Function (openCubeSet Q)) (ν : Vec 2) :
    oldSignedCellAverage Q d (fun U => hotCovCross U.val (hotCovZfield Q d w)
      (hotCovBotRcv Q d nu sigma hnu hsigma k U ν)) =
    oldSignedCellAverage Q d (fun U => hotCovCross U.val (hotCovZfield Q d w)
      (hotCovCmpRecip Q d nu sigma hnu hsigma k U (ν, 0))) := by
  refine hotCov_principal_split Q d (hotCovZfield Q d w)
    (fun x => hotCovParentRecip Q nu sigma hnu hsigma k (ν, 0) x - 0)
    (fun U => hotCovBotRcv Q d nu sigma hnu hsigma k U ν)
    (fun U => hotCovCmpRecip Q d nu sigma hnu hsigma k U (ν, 0))
    (hotCov_zfield_memL2 Q d w)
    ((hotCov_parentRecip_memL2 Q nu sigma hnu hsigma k (ν, 0)).sub (memVectorL2_const 0))
    (hotCov_parent_orth Q d nu sigma hnu hsigma k (ν, 0) 0 w)
    (fun U => hotCov_cmpRecip_memL2 Q d nu sigma hnu hsigma k U (ν, 0))
    (fun U => ?_)
  filter_upwards [hotCov_botRcv_split Q d nu sigma hnu hsigma k U ν] with x hx
  rw [hx, sub_zero]

end

end ASDExplicitGamma.Main
