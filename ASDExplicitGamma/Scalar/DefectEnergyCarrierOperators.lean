module

public import ASDExplicitGamma.Scalar.DefectEnergyPhysicalOperators
public import ASDExplicitGamma.Gaussian.AllOrderProjectedSource
public import ASDExplicitGamma.Gaussian.SquareColumnBound
public import ASDExplicitGamma.Gaussian.CovarianceRow

/-! Physical projected-source operators on the completed H10 graph carrier. -/

@[expose] public section

namespace ASDExplicitGamma.Scalar

open Homogenization MeasureTheory Response ASDExplicitGamma.Gaussian
  ASDExplicitGamma.Main ASDExplicitGamma.Triadic ASDExplicitGamma.Variational

noncomputable section

local instance carrierOperatorFiniteMeasure (Q : TriadicCube 2) :
    IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
  (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume

/-- The actual DIAG shear field of a weak-Haar graph potential is the negative
Lemma-V row. This provides its normalized L2 representative. -/
theorem defectPotentialSourceFieldCarrier_memLp (Q : TriadicCube 2)
    (b : ℝ) (L : {l : ℝ // 0 < l}) (n : whiteBasisIndex)
    (x : defectWeakPotential Q) :
    MemLp (defectPotentialSourceFieldCarrier Q b L n x) 2
      (normalizedCubeMeasure Q) := by
  let r := defectWeakPotentialRepresentative Q x
  let v := r.toH1Function
  let η := mainQ3DirectionW2 Q b L (whiteBasis n)
  let I := diagInterpolant Q 0
  let F := defectPotentialSourceFieldCarrier Q b L n x
  have hη : MemLp η.value.toFun ⊤ (volume.restrict (openCubeSet Q)) :=
    η.value_memLp_top
  have hDη : ∀ i, MemLp (fun p => η.value.grad p i) ⊤
      (volume.restrict (openCubeSet Q)) :=
    fun i => PlanarW2Infinity.gradient_memLp_top_volume η i
  have hrow := lemmaVPlanarRowField_memL2 I η.value v hη hDη
  have hrowEq : F = fun p => -lemmaVPlanarRowField I η.value v p := by
    funext p i
    rw [lemmaVH2_rowField_eq]
    simp [F, defectPotentialSourceFieldCarrier,
      defectPotentialSourceFieldH1, planarShearSourceField,
      planarQuarterTurn, r, v, η, I]
  have hFvec : MemVectorL2 (openCubeSet Q) F := by
    rw [hrowEq]
    exact hrow.neg
  apply MemLp.of_eval
  intro i
  exact memLp_normalized_of_memL2On
    (memScalarL2_coord_of_memVectorL2 hFvec i)

theorem defectPotentialSourceFieldCarrier_eq_neg_row (Q : TriadicCube 2)
    (b : ℝ) (L : {l : ℝ // 0 < l}) (n : whiteBasisIndex)
    (x : defectWeakPotential Q) :
    defectPotentialSourceFieldCarrier Q b L n x =
      fun p => -lemmaVPlanarRowField (diagInterpolant Q 0)
        (mainQ3DirectionW2 Q b L (whiteBasis n)).value
        (defectWeakPotentialRepresentative Q x).toH1Function p := by
  let r := defectWeakPotentialRepresentative Q x
  let v := r.toH1Function
  let η := mainQ3DirectionW2 Q b L (whiteBasis n)
  let I := diagInterpolant Q 0
  funext p i
  rw [lemmaVH2_rowField_eq]
  simp [defectPotentialSourceFieldCarrier,
    defectPotentialSourceFieldH1, planarShearSourceField,
    planarQuarterTurn, r, v, η, I]

private theorem defectPotentialSourceFieldCarrier_increment_summable
    (Q : TriadicCube 2) (b : ℝ) (L : {l : ℝ // 0 < l})
    (n : whiteBasisIndex) (x : defectWeakPotential Q) (i : Fin 2) :
    Summable (fun j : ℕ => (Real.sqrt 3)^(j+1) *
      energy Q (cubeIncrement Q (j+1)
        (fun p => defectPotentialSourceFieldCarrier Q b L n x p i))) := by
  let r := defectWeakPotentialRepresentative Q x
  let S : Vec 2 → Vec 2 := fun p => lemmaVPlanarRowField
    (diagInterpolant Q 0) (mainQ3DirectionW2 Q b L (whiteBasis n)).value
    r.toH1Function p
  have hrow := q3_distinct_h10_row_generatorKB whiteBasis {n} b L Q 0
    (fun _ : whiteBasisIndex => r)
  have hcoord (i : Fin 2) : Summable (fun j : ℕ => (Real.sqrt 3)^(j+1) *
      energy Q (cubeIncrement Q (j+1) (fun p => S p i))) := by
    have h := hrow.1 Q (by simp) i
    simpa [S, q3DistinctRow] using h
  have hsource := defectPotentialSourceFieldCarrier_eq_neg_row Q b L n x
  have hcoordEq : (fun p => defectPotentialSourceFieldCarrier Q b L n x p i) =
      fun p => -(S p i) := by
    funext p
    rw [hsource]
    rfl
  simpa only [hcoordEq, cubeIncrement_neg, energy_neg] using hcoord i

private theorem squareQ3RowEnergy_zero_eq (Q : TriadicCube 2)
    (b : ℝ) (L : {l : ℝ // 0 < l}) (r : H10Function (openCubeSet Q))
    (n : whiteBasisIndex) :
    squareQ3RowEnergy Q b 1 L 0 0 r n =
      vectorPositiveHaarEnergy Q
        (lemmaVPlanarRowField (diagInterpolant Q 0)
          (mainQ3DirectionW2 Q b L (whiteBasis n)).value r.toH1Function) := by
  let hzero : lemmaVAffinePotential
      (isOpenBoundedConvexDomain_openCubeSet Q) 0 r = r.toH1Function := by
    ext p
    · simp only [lemmaVAffinePotential, H1Function.add_toFun,
        H1Function.affineOnIsSobolevRegularDomain_apply]
      simp
    · simp only [lemmaVAffinePotential, H1Function.add_grad,
        H1Function.affineOnIsSobolevRegularDomain_grad]
      simp
  simp [squareQ3RowEnergy, squareQ3BasisMultiplier, hzero,
    descendantsAverage, descendantsAtDepth_zero]

private theorem defectPotentialSourceFieldCarrier_positive_energy_eq_row
    (Q : TriadicCube 2) (b : ℝ) (L : {l : ℝ // 0 < l})
    (n : whiteBasisIndex) (x : defectWeakPotential Q) :
    vectorPositiveHaarEnergy Q
      (defectPotentialSourceFieldCarrier Q b L n x) =
        squareQ3RowEnergy Q b 1 L 0 0
          (defectWeakPotentialRepresentative Q x) n := by
  rw [squareQ3RowEnergy_zero_eq]
  rw [defectPotentialSourceFieldCarrier_eq_neg_row]
  simp only [vectorPositiveHaarEnergy, Pi.neg_apply]
  apply Finset.sum_congr rfl
  intro i hi
  exact primalEnergy_neg Q (Real.sqrt 3)
    (fun p => lemmaVPlanarRowField (diagInterpolant Q 0)
      (mainQ3DirectionW2 Q b L (whiteBasis n)).value
      (defectWeakPotentialRepresentative Q x).toH1Function p i)

private theorem carrierField_coord_memLp (Q : TriadicCube 2)
    (x : defectWeakPotential Q) (i : Fin 2) :
    MemLp (fun p => graphPotentialField Q x.down p i) 2
      (normalizedCubeMeasure Q) := by
  have hvec : MemVectorL2 (openCubeSet Q) (graphPotentialField Q x.down) :=
    MeasureTheory.Lp.memLp _
  exact memLp_normalized_of_memL2On
    (memScalarL2_coord_of_memVectorL2 hvec i)

private theorem carrierWeakScalarPairing_self (Q : TriadicCube 2)
    {f : Vec 2 → ℝ} (hf : MemLp f 2 (normalizedCubeMeasure Q)) :
    weakScalarPairing Q f f = dualEnergy Q (Real.sqrt 3) f := by
  have hq : 1 < Real.sqrt 3 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num),
      Real.sqrt_nonneg (3 : ℝ)]
  have hs := summable_weighted_projections Q hq hf
  rw [weakScalarPairing, dualEnergy_eq_weighted_projections Q hq hf hs]
  rfl

private theorem carrierWeakVectorPairing_self (Q : TriadicCube 2)
    {F : Vec 2 → Fin 2 → ℝ}
    (hF : ∀ i, MemLp (fun p => F p i) 2 (normalizedCubeMeasure Q)) :
    weakVectorPairing Q F F = vectorWeakHaarEnergy Q F := by
  unfold weakVectorPairing vectorWeakHaarEnergy
  apply Finset.sum_congr rfl
  intro i hi
  exact carrierWeakScalarPairing_self Q (hF i)

private theorem normalized_ae_to_cube_carrier (Q : TriadicCube 2)
    {f g : Vec 2 → ℝ} (h : f =ᵐ[normalizedCubeMeasure Q] g) :
    f =ᵐ[cubeMeasure Q] g := by
  have hc : ENNReal.ofReal ((cubeVolume Q)⁻¹) ≠ 0 :=
    ENNReal.ofReal_ne_zero_iff.mpr (inv_pos.mpr (cubeVolume_pos Q))
  have h' : f =ᵐ[ENNReal.ofReal ((cubeVolume Q)⁻¹) • cubeMeasure Q] g := by
    simpa [normalizedCubeMeasure] using h
  exact (Measure.ae_ennreal_smul_measure_iff hc).1 h'

private theorem weakScalarPairing_congr_ae_carrier (Q : TriadicCube 2)
    {f f' g g' : Vec 2 → ℝ}
    (hf : f =ᵐ[normalizedCubeMeasure Q] f')
    (hg : g =ᵐ[normalizedCubeMeasure Q] g') :
    weakScalarPairing Q f g = weakScalarPairing Q f' g' := by
  have hfp (j : ℕ) : cubeProjection Q j f = cubeProjection Q j f' :=
    lemmaV_cubeProjection_congr_ae Q j
      (normalized_ae_to_cube_carrier Q hf)
  have hgp (j : ℕ) : cubeProjection Q j g = cubeProjection Q j g' :=
    lemmaV_cubeProjection_congr_ae Q j
      (normalized_ae_to_cube_carrier Q hg)
  unfold weakScalarPairing
  congr 1
  apply tsum_congr
  intro j
  rw [hfp j, hgp j]

private theorem weakVectorPairing_congr_ae_carrier (Q : TriadicCube 2)
    {F F' G G' : Vec 2 → Fin 2 → ℝ}
    (hF : F =ᵐ[normalizedCubeMeasure Q] F')
    (hG : G =ᵐ[normalizedCubeMeasure Q] G') :
    weakVectorPairing Q F G = weakVectorPairing Q F' G' := by
  unfold weakVectorPairing
  apply Finset.sum_congr rfl
  intro i hi
  apply weakScalarPairing_congr_ae_carrier Q
  · filter_upwards [hF] with p hp
    exact congrFun hp i
  · filter_upwards [hG] with p hp
    exact congrFun hp i

theorem vectorWeakHaarEnergy_congr_ae (Q : TriadicCube 2)
    {F G : Vec 2 → Fin 2 → ℝ}
    (hFmem : ∀ i, MemLp (fun p => F p i) 2 (normalizedCubeMeasure Q))
    (hGmem : ∀ i, MemLp (fun p => G p i) 2 (normalizedCubeMeasure Q))
    (h : F =ᵐ[normalizedCubeMeasure Q] G) :
    vectorWeakHaarEnergy Q F = vectorWeakHaarEnergy Q G := by
  rw [← carrierWeakVectorPairing_self Q hFmem,
    ← carrierWeakVectorPairing_self Q hGmem]
  exact weakVectorPairing_congr_ae_carrier Q h h

theorem defectWeakPotential_norm_sq (Q : TriadicCube 2)
    (x : defectWeakPotential Q) :
    ‖x‖ ^ 2 = vectorWeakHaarEnergy Q
      (graphPotentialField Q x.down) := by
  rw [← real_inner_self_eq_norm_sq]
  change weakVectorPairing Q (graphPotentialField Q x.down)
      (graphPotentialField Q x.down) = _
  exact carrierWeakVectorPairing_self Q
    (fun i => carrierField_coord_memLp Q x i)

theorem defectWeakPotential_norm_sq_eq_representative (Q : TriadicCube 2)
    (x : defectWeakPotential Q) :
    ‖x‖ ^ 2 = vectorWeakHaarEnergy Q
      (defectWeakPotentialRepresentative Q x).toH1Function.grad := by
  rw [defectWeakPotential_norm_sq]
  apply vectorWeakHaarEnergy_congr_ae Q
    (fun i => carrierField_coord_memLp Q x i)
    (fun i => (defectWeakPotentialRepresentative Q x).toH1Function.grad_memL2_normalizedCubeMeasure i)
    ?_
  have hraw := graphPotentialField_ofRepresentative Q x
  have hnorm : graphPotentialField Q x.down =ᵐ[normalizedCubeMeasure Q]
      (defectWeakPotentialRepresentative Q x).toH1Function.grad := by
    have hmeasure : cubeMeasure Q = volumeMeasureOn (openCubeSet Q) := by
      rw [cubeMeasure, volumeMeasureOn]
      exact volume_restrict_cubeSet_eq_volume_restrict_openCubeSet Q
    have hcube : graphPotentialField Q x.down =ᵐ[cubeMeasure Q]
        (defectWeakPotentialRepresentative Q x).toH1Function.grad := by
      rw [hmeasure]
      exact hraw
    rw [normalizedCubeMeasure]
    exact Measure.ae_smul_measure hcube (ENNReal.ofReal ((cubeVolume Q)⁻¹))
  exact hnorm

private theorem toHilbertVectorL2OfVecField_eq_of_ae {U : Set (Vec 2)}
    {F G : Vec 2 → Vec 2} (hF : MemVectorL2 U F) (hG : MemVectorL2 U G)
    (hfg : F =ᵐ[volumeMeasureOn U] G) :
    toHilbertVectorL2OfVecField hF = toHilbertVectorL2OfVecField hG := by
  let hFH := memHilbertVectorL2_hilbertifyVecField hF
  let hGH := memHilbertVectorL2_hilbertifyVecField hG
  change toHilbertVectorL2 hFH = toHilbertVectorL2 hGH
  apply (toHilbertVectorL2_eq_toHilbertVectorL2_iff hFH hGH).2
  filter_upwards [hfg] with x hx
  exact congrArg HilbertVec.ofVec hx

private theorem projectedSourceLoad_add_ae (Q : TriadicCube 2)
    {F G H : Vec 2 → Vec 2}
    (hF : MemLp F 2 (normalizedCubeMeasure Q))
    (hG : MemLp G 2 (normalizedCubeMeasure Q))
    (hH : MemLp H 2 (normalizedCubeMeasure Q))
    (hfield : H =ᵐ[volumeMeasureOn (openCubeSet Q)] fun p => F p + G p) :
    projectedSourceLoad Q hH = projectedSourceLoad Q hF + projectedSourceLoad Q hG := by
  let hFvec := memVectorL2_openCubeSet_of_memLp_normalizedCubeMeasure Q hF
  let hGvec := memVectorL2_openCubeSet_of_memLp_normalizedCubeMeasure Q hG
  let hHvec := memVectorL2_openCubeSet_of_memLp_normalizedCubeMeasure Q hH
  have hclass : toHilbertVectorL2OfVecField hHvec =
      toHilbertVectorL2OfVecField (hFvec.add hGvec) :=
    toHilbertVectorL2OfVecField_eq_of_ae hHvec (hFvec.add hGvec) hfield
  calc
    projectedSourceLoad Q hH =
        hilbertPureSecondL2 (openCubeSet Q)
          (toHilbertVectorL2OfVecField (hFvec.add hGvec)) := by
      change hilbertPureSecondL2 (openCubeSet Q)
        (toHilbertVectorL2OfVecField hHvec) = _
      rw [hclass]
    _ = hilbertPureSecondL2 (openCubeSet Q)
        (toHilbertVectorL2OfVecField hFvec) +
          hilbertPureSecondL2 (openCubeSet Q)
            (toHilbertVectorL2OfVecField hGvec) := by
      rw [toHilbertVectorL2OfVecField_add hFvec hGvec]
      simp only [map_add]
    _ = projectedSourceLoad Q hF + projectedSourceLoad Q hG := rfl

private theorem projectedSourceLoad_smul_ae (Q : TriadicCube 2)
    {F G : Vec 2 → Vec 2} (c : ℝ)
    (hF : MemLp F 2 (normalizedCubeMeasure Q))
    (hG : MemLp G 2 (normalizedCubeMeasure Q))
    (hfield : G =ᵐ[volumeMeasureOn (openCubeSet Q)] fun p => c • F p) :
    projectedSourceLoad Q hG = c • projectedSourceLoad Q hF := by
  let hFvec := memVectorL2_openCubeSet_of_memLp_normalizedCubeMeasure Q hF
  let hGvec := memVectorL2_openCubeSet_of_memLp_normalizedCubeMeasure Q hG
  have hclass : toHilbertVectorL2OfVecField hGvec =
      c • toHilbertVectorL2OfVecField hFvec := by
    calc
      toHilbertVectorL2OfVecField hGvec =
          toHilbertVectorL2OfVecField (hFvec.const_smul c) :=
            toHilbertVectorL2OfVecField_eq_of_ae hGvec
              (hFvec.const_smul c) hfield
      _ = c • toHilbertVectorL2OfVecField hFvec := by
        change toHilbertVectorL2 (memHilbertVectorL2_hilbertifyVecField
          (hFvec.const_smul c)) = _
        exact MeasureTheory.MemLp.toLp_const_smul c
          (memHilbertVectorL2_hilbertifyVecField hFvec)
  calc
    projectedSourceLoad Q hG =
        hilbertPureSecondL2 (openCubeSet Q)
          (c • toHilbertVectorL2OfVecField hFvec) := by
      change hilbertPureSecondL2 (openCubeSet Q)
        (toHilbertVectorL2OfVecField hGvec) = _
      rw [hclass]
    _ = c • hilbertPureSecondL2 (openCubeSet Q)
        (toHilbertVectorL2OfVecField hFvec) := by simp only [map_smul]
    _ = c • projectedSourceLoad Q hF := rfl

private theorem projectedSourceLoad_finset_sum (Q : TriadicCube 2)
    {ι : Type*} (s : Finset ι) (F : ι → Vec 2 → Vec 2)
    (hF : ∀ n, MemLp (F n) 2 (normalizedCubeMeasure Q)) :
    projectedSourceLoad Q (memLp_finsetSum s (fun n _ => hF n)) =
      ∑ n ∈ s, projectedSourceLoad Q (hF n) := by
  classical
  revert hF
  induction s using Finset.induction_on with
  | empty =>
      intro hF
      have hzero : MemLp (fun _ : Vec 2 => (0 : Vec 2)) 2
          (normalizedCubeMeasure Q) := by
        simpa using (memLp_finsetSum (∅ : Finset ι)
          (fun n hn => hF n))
      let hvecRaw := memVectorL2_openCubeSet_of_memLp_normalizedCubeMeasure Q hzero
      have hvec : toHilbertVectorL2OfVecField hvecRaw = 0 := by
        apply Lp.ext
        filter_upwards [coeFn_toHilbertVectorL2OfVecField hvecRaw,
          (Lp.coeFn_zero (E := HilbertVec 2) 2
            (volumeMeasureOn (openCubeSet Q)))] with p hp hz
        rw [hp, hz]
        simp [hilbertifyVecField]
      simp [projectedSourceLoad, hvec]
  | @insert a s ha ih =>
      intro hF
      let htail : ∀ n, MemLp (F n) 2 (normalizedCubeMeasure Q) := hF
      let hfirst := hF a
      let hsum := memLp_finsetSum s (fun n _ => htail n)
      let hall := memLp_finsetSum (insert a s) (fun n _ => hF n)
      have hfield : (fun p => ∑ n ∈ insert a s, F n p) =ᵐ[
          volumeMeasureOn (openCubeSet Q)]
          fun p => F a p + ∑ n ∈ s, F n p := by
        filter_upwards [] with p
        simp [Finset.sum_insert, ha]
      have hadd := projectedSourceLoad_add_ae Q hfirst hsum hall hfield
      rw [hadd]
      rw [ih htail]
      rw [Finset.sum_insert ha]

/-- The actual pure-second projected-source load of one physical q3 shear
mode, as a linear map on the completed weak-Haar H10 graph. -/
noncomputable def defectPotentialProjectedLoadMap (Q : TriadicCube 2)
    (b : ℝ) (L : {l : ℝ // 0 < l}) (n : whiteBasisIndex) :
    defectWeakPotential Q →ₗ[ℝ] HilbertBlockL2 (openCubeSet Q) where
  toFun x := projectedSourceLoad Q
    (defectPotentialSourceFieldCarrier_memLp Q b L n x)
  map_add' x y := by
    exact projectedSourceLoad_add_ae Q
      (defectPotentialSourceFieldCarrier_memLp Q b L n x)
      (defectPotentialSourceFieldCarrier_memLp Q b L n y)
      (defectPotentialSourceFieldCarrier_memLp Q b L n (x + y))
      (defectPotentialSourceFieldCarrier_add_ae Q b L n x y)
  map_smul' c x := by
    exact projectedSourceLoad_smul_ae Q c
      (defectPotentialSourceFieldCarrier_memLp Q b L n x)
      (defectPotentialSourceFieldCarrier_memLp Q b L n (c • x))
      (defectPotentialSourceFieldCarrier_smul_ae Q b c L n x)

/-- The physical second-shear operator on the H10 graph carrier, projected
onto the complementary response space exactly as in the source window. -/
noncomputable def defectPotentialSourceComplementLinear (Q : TriadicCube 2)
    (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (k : ResponseCoefficient (openCubeSet Q)) (b : ℝ)
    (L : {l : ℝ // 0 < l}) (n : whiteBasisIndex) :
    defectWeakPotential Q →ₗ[ℝ]
      EnergyCarrier (responseFrameEnergyData (measurableSet_openCubeSet Q)
        (by rw [volume_openCubeSet_toReal]; exact cubeVolume_pos Q)
        ν σ hν hσ k) := by
  let hU := measurableSet_openCubeSet Q
  let hv : 0 < (volume (openCubeSet Q)).toReal := by
    rw [volume_openCubeSet_toReal]
    exact cubeVolume_pos Q
  let D := responseFrameEnergyData hU hv ν σ hν hσ k
  let V := responseFrameEnergyVariationSpace hU hv ν σ hν hσ k
  exact (V.toSubmoduleᗮ.starProjection.toLinearMap).comp
    ((responseEnergyUpLinear D).comp
      (defectPotentialProjectedLoadMap Q b L n))

/-- Applying the physical operator is precisely the complementary response
projection of the actual projected-source residual. -/
theorem defectPotentialSourceComplementLinear_apply (Q : TriadicCube 2)
    (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (k : ResponseCoefficient (openCubeSet Q)) (b : ℝ)
    (L : {l : ℝ // 0 < l}) (n : whiteBasisIndex)
    (x : defectWeakPotential Q) :
    defectPotentialSourceComplementLinear Q ν σ hν hσ k b L n x =
      responseEnergyUp
        (responseFrameEnergyData (measurableSet_openCubeSet Q)
          (by rw [volume_openCubeSet_toReal]; exact cubeVolume_pos Q)
          ν σ hν hσ k)
        (scalarProjectionResidual Q ν σ hν hσ k
          (projectedSourceLoad Q
            (defectPotentialSourceFieldCarrier_memLp Q b L n x))) := by
  let hU := measurableSet_openCubeSet Q
  let hv : 0 < (volume (openCubeSet Q)).toReal := by
    rw [volume_openCubeSet_toReal]
    exact cubeVolume_pos Q
  let D := responseFrameEnergyData hU hv ν σ hν hσ k
  let V := responseFrameEnergyVariationSpace hU hv ν σ hν hσ k
  change V.toSubmoduleᗮ.starProjection
      (responseEnergyUp D (projectedSourceLoad Q
        (defectPotentialSourceFieldCarrier_memLp Q b L n x))) = _
  exact projectedSource_carrier_complement_eq Q hU hv ν σ hν hσ k
    (defectPotentialSourceFieldCarrier_memLp Q b L n x)

/-- The physical source-complement mode is bounded by the constant-one
projected-source estimate applied to its actual Lemma-V field. -/
theorem defectPotentialSourceComplementLinear_norm_sq_le (Q : TriadicCube 2)
    (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (k : ResponseCoefficient (openCubeSet Q)) (b : ℝ)
    (L : {l : ℝ // 0 < l}) (n : whiteBasisIndex)
    (x : defectWeakPotential Q) :
    ‖defectPotentialSourceComplementLinear Q ν σ hν hσ k b L n x‖ ^ 2 ≤
      lemmaVInverseHistory Q (responseFramePlanarCoefficientField ν σ k)
        ((3 : ℝ) ^ (1 / 4 : ℝ)) *
        vectorPositiveHaarEnergy Q
          (defectPotentialSourceFieldCarrier Q b L n x) := by
  let hU := measurableSet_openCubeSet Q
  let hv : 0 < (volume (openCubeSet Q)).toReal := by
    rw [volume_openCubeSet_toReal]
    exact cubeVolume_pos Q
  let D := responseFrameEnergyData hU hv ν σ hν hσ k
  let F := defectPotentialSourceFieldCarrier Q b L n x
  let hF := defectPotentialSourceFieldCarrier_memLp Q b L n x
  have hFpos : ∀ i : Fin 2, Summable (fun j : ℕ =>
      (Real.sqrt 3) ^ (j + 1) * energy Q (cubeIncrement Q (j + 1)
        (fun p => F p i))) := by
    intro i
    exact defectPotentialSourceFieldCarrier_increment_summable Q b L n x i
  have hnorm :
      ‖defectPotentialSourceComplementLinear Q ν σ hν hσ k b L n x‖ ^ 2 =
        (scalarFrameRealization Q ν σ hν hσ k).energyBilin
          (scalarProjectionResidual Q ν σ hν hσ k (projectedSourceLoad Q hF))
          (scalarProjectionResidual Q ν σ hν hσ k (projectedSourceLoad Q hF)) := by
    rw [defectPotentialSourceComplementLinear_apply]
    rw [energyCarrier_norm_sq, responseEnergyUp_down]
    dsimp [D, responseFrameEnergyData, responseEnergyHilbertData,
      scalarFrameRealization]
  rw [hnorm]
  simpa only [F, hF] using projected_source_energy_le_source_history
    Q ν σ hν hσ k hF hFpos

/-- The finite q3 source column is Hilbert--Schmidt on the actual weak-Haar
potential carrier. The coefficient is the inverse-history square root times
the source-column constant. -/
theorem defectPotentialSourceComplementLinear_finite_column_bound
    (Q : TriadicCube 2) (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (k : ResponseCoefficient (openCubeSet Q)) (b : ℝ)
    (L : {l : ℝ // 0 < l}) (s : Finset whiteBasisIndex)
    (x : defectWeakPotential Q) :
    (∑ n ∈ s,
      ‖defectPotentialSourceComplementLinear Q ν σ hν hσ k b L n x‖ ^ 2) ≤
      (Real.sqrt (lemmaVInverseHistory Q (responseFramePlanarCoefficientField ν σ k)
        ((3 : ℝ) ^ (1 / 4 : ℝ))) *
        (|b| * Numerics.generatorKA (diagMeshRadius Q 0 / L.1))) ^ 2 * ‖x‖ ^ 2 := by
  let B := lemmaVInverseHistory Q (responseFramePlanarCoefficientField ν σ k)
    ((3 : ℝ) ^ (1 / 4 : ℝ))
  let C := |b| * Numerics.generatorKA (diagMeshRadius Q 0 / L.1)
  let r := defectWeakPotentialRepresentative Q x
  have hq : 1 < (3 : ℝ) ^ (1 / 4 : ℝ) :=
    Real.one_lt_rpow (by norm_num) (by norm_num)
  have hB : 0 ≤ B := by
    dsimp [B]
    exact lemmaVInverseHistory_nonneg Q (responseFramePlanarCoefficientField ν σ k) hq
  have hρ : 0 ≤ diagMeshRadius Q 0 / L.1 :=
    div_nonneg (diagMeshRadius_pos Q 0).le L.2.le
  have hC : 0 ≤ C := by
    dsimp [C, Numerics.generatorKA]
    positivity
  have hW : 0 ≤ lemmaVTiledWeakEnergy Q 0 r.toH1Function.grad :=
    lemmaVTiledWeakEnergy_nonneg Q 0 r.toH1Function.grad
  have hWnorm : lemmaVTiledWeakEnergy Q 0 r.toH1Function.grad = ‖x‖ ^ 2 := by
    rw [defectWeakPotential_norm_sq_eq_representative]
    simp [lemmaVTiledWeakEnergy, descendantsAverage, descendantsAtDepth_zero, r]
  have hVgrad : (lemmaVAffinePotential
      (isOpenBoundedConvexDomain_openCubeSet Q) (0 : Vec 2) r).grad =
      r.toH1Function.grad := by
    funext p i
    simp [lemmaVAffinePotential, H1Function.add_grad,
      H1Function.affineOnIsSobolevRegularDomain_grad]
  have hWaff : lemmaVTiledWeakEnergy Q 0
      (lemmaVAffinePotential (isOpenBoundedConvexDomain_openCubeSet Q) (0 : Vec 2) r).grad =
        lemmaVTiledWeakEnergy Q 0 r.toH1Function.grad := by
    rw [hVgrad]
  have hrowNonneg (n : whiteBasisIndex) :
      0 ≤ squareQ3RowEnergy Q b 1 L 0 0 r n := by
    rw [← defectPotentialSourceFieldCarrier_positive_energy_eq_row Q b L n x]
    exact vectorPositiveHaarEnergy_nonneg Q _
  have htrace := square_q3_row_source_trace_bound Q b 1 L 0 0 r
  have htraceSq : (∑' n, squareQ3RowEnergy Q b 1 L 0 0 r n) ≤
      C ^ 2 * lemmaVTiledWeakEnergy Q 0 r.toH1Function.grad := by
    have hs := pow_le_pow_left₀ (Real.sqrt_nonneg _) htrace.2 2
    rw [Real.sq_sqrt (tsum_nonneg hrowNonneg), mul_pow,
      Real.sq_sqrt (lemmaVTiledWeakEnergy_nonneg Q 0
        (lemmaVAffinePotential (isOpenBoundedConvexDomain_openCubeSet Q) 0 r).grad)] at hs
    rw [hWaff] at hs
    simpa [C, Numerics.generatorKA, abs_one] using hs
  have hsumRow := htrace.1.sum_le_tsum s (fun n _ => hrowNonneg n)
  have hsumRowBound :
      (∑ n ∈ s, squareQ3RowEnergy Q b 1 L 0 0 r n) ≤
        C ^ 2 * ‖x‖ ^ 2 := by
    rw [← hWnorm]
    exact hsumRow.trans htraceSq
  have hsumMode :
      (∑ n ∈ s,
        ‖defectPotentialSourceComplementLinear Q ν σ hν hσ k b L n x‖ ^ 2) ≤
        B * ∑ n ∈ s, squareQ3RowEnergy Q b 1 L 0 0 r n := by
    calc
      _ ≤ ∑ n ∈ s, B * squareQ3RowEnergy Q b 1 L 0 0 r n := by
        apply Finset.sum_le_sum
        intro n hn
        calc
          _ ≤ B * vectorPositiveHaarEnergy Q
              (defectPotentialSourceFieldCarrier Q b L n x) :=
            defectPotentialSourceComplementLinear_norm_sq_le Q ν σ hν hσ k b L n x
          _ = B * squareQ3RowEnergy Q b 1 L 0 0 r n := by
            rw [defectPotentialSourceFieldCarrier_positive_energy_eq_row Q b L n x]
      _ = _ := by rw [Finset.mul_sum]
  calc
    _ ≤ B * (C ^ 2 * ‖x‖ ^ 2) :=
      hsumMode.trans (mul_le_mul_of_nonneg_left hsumRowBound hB)
    _ = (Real.sqrt B * C) ^ 2 * ‖x‖ ^ 2 := by
      calc
        B * (C ^ 2 * ‖x‖ ^ 2) = B * C ^ 2 * ‖x‖ ^ 2 := by ring
        _ = (Real.sqrt B) ^ 2 * C ^ 2 * ‖x‖ ^ 2 := by
          rw [Real.sq_sqrt hB]
        _ = (Real.sqrt B * C) ^ 2 * ‖x‖ ^ 2 := by ring

private theorem vectorPositiveHaarEnergy_neg (Q : TriadicCube 2)
    (F : Vec 2 → Vec 2) :
    vectorPositiveHaarEnergy Q (fun p => -F p) = vectorPositiveHaarEnergy Q F := by
  unfold vectorPositiveHaarEnergy
  apply Finset.sum_congr rfl
  intro i hi
  change primalEnergy Q (Real.sqrt 3) (fun p => -(F p i)) =
    primalEnergy Q (Real.sqrt 3) (fun p => F p i)
  exact primalEnergy_neg Q (Real.sqrt 3) (fun p => F p i)

/-- The finite q3 source row obeys the actual distinct-potential bound.
Each entry is the physical H10 potential from the weak-Haar carrier, and the
row field is precisely the sum of their Lemma-V source shears. -/
theorem defectPotentialSourceFieldCarrier_finite_row_bound
    (Q : TriadicCube 2) (b : ℝ) (L : {l : ℝ // 0 < l})
    (s : Finset whiteBasisIndex) (x : whiteBasisIndex → defectWeakPotential Q) :
    vectorPositiveHaarEnergy Q
      (fun p => ∑ n ∈ s, defectPotentialSourceFieldCarrier Q b L n (x n) p) ≤
      (Numerics.generatorKB (diagMeshRadius Q 0 / L.1) * |b|) ^ 2 *
        ∑ n ∈ s, ‖x n‖ ^ 2 := by
  let r : whiteBasisIndex → H10Function (openCubeSet Q) := fun n =>
    defectWeakPotentialRepresentative Q (x n)
  let S := q3DistinctRow whiteBasis s b L Q 0 r
  let F : Vec 2 → Vec 2 := fun p =>
    ∑ n ∈ s, defectPotentialSourceFieldCarrier Q b L n (x n) p
  have hfield : F = fun p => -S p := by
    funext p
    funext i
    dsimp [F]
    rw [Finset.sum_apply]
    calc
      ∑ n ∈ s, (defectPotentialSourceFieldCarrier Q b L n (x n) p) i =
          ∑ n ∈ s, -(lemmaVPlanarRowField (diagInterpolant Q 0)
            (mainQ3DirectionW2 Q b L (whiteBasis n)).value
            (r n).toH1Function p i) := by
          apply Finset.sum_congr rfl
          intro n hn
          exact congrFun (congrFun
            (defectPotentialSourceFieldCarrier_eq_neg_row Q b L n (x n)) p) i
      _ = -(∑ n ∈ s, lemmaVPlanarRowField (diagInterpolant Q 0)
          (mainQ3DirectionW2 Q b L (whiteBasis n)).value
          (r n).toH1Function p i) := by rw [Finset.sum_neg_distrib]
      _ = -S p i := by simp [S, q3DistinctRow]
  have hpos : vectorPositiveHaarEnergy Q F =
      lemmaVTiledPositiveEnergy Q 0 S := by
    rw [hfield, vectorPositiveHaarEnergy_neg]
    simp [lemmaVTiledPositiveEnergy, descendantsAverage, descendantsAtDepth_zero, S]
  let C := Numerics.generatorKB (diagMeshRadius Q 0 / L.1) * |b|
  have hρ : 0 ≤ diagMeshRadius Q 0 / L.1 :=
    div_nonneg (diagMeshRadius_pos Q 0).le L.2.le
  have hC : 0 ≤ C := by
    dsimp [C, Numerics.generatorKB]
    positivity
  have hrow := q3_distinct_h10_row_generatorKB whiteBasis s b L Q 0 r
  have hweakNonneg : 0 ≤ ∑ n ∈ s, lemmaVTiledWeakEnergy Q 0 (r n).toH1Function.grad :=
    Finset.sum_nonneg fun n hn => lemmaVTiledWeakEnergy_nonneg Q 0 _
  have hweakEq :
      (∑ n ∈ s, lemmaVTiledWeakEnergy Q 0 (r n).toH1Function.grad) =
        ∑ n ∈ s, ‖x n‖ ^ 2 := by
    apply Finset.sum_congr rfl
    intro n hn
    rw [defectWeakPotential_norm_sq_eq_representative]
    simp [lemmaVTiledWeakEnergy, descendantsAverage, descendantsAtDepth_zero, r]
  have hsq : lemmaVTiledPositiveEnergy Q 0 S ≤
      C ^ 2 * ∑ n ∈ s, ‖x n‖ ^ 2 := by
    have hs := pow_le_pow_left₀ (Real.sqrt_nonneg _) hrow.2 2
    rw [Real.sq_sqrt (lemmaVTiledPositiveEnergy_nonneg Q 0 S), mul_pow,
      Real.sq_sqrt hweakNonneg] at hs
    simpa [C, hweakEq] using hs
  change vectorPositiveHaarEnergy Q F ≤ _
  rw [hpos]
  simpa [C] using hsq

private theorem defectPotentialSourceFieldCarrier_finite_row_increment_summable
    (Q : TriadicCube 2) (b : ℝ) (L : {l : ℝ // 0 < l})
    (s : Finset whiteBasisIndex)
    (x : whiteBasisIndex → defectWeakPotential Q) (i : Fin 2) :
    Summable (fun j : ℕ => (Real.sqrt 3)^(j+1) *
      energy Q (cubeIncrement Q (j+1)
        (fun p => (∑ n ∈ s,
          defectPotentialSourceFieldCarrier Q b L n (x n) p) i))) := by
  let r : whiteBasisIndex → H10Function (openCubeSet Q) := fun n =>
    defectWeakPotentialRepresentative Q (x n)
  let S := q3DistinctRow whiteBasis s b L Q 0 r
  let F : Vec 2 → Vec 2 := fun p =>
    ∑ n ∈ s, defectPotentialSourceFieldCarrier Q b L n (x n) p
  have hfield : F = fun p => -S p := by
    funext p
    funext k
    dsimp [F, S]
    rw [Finset.sum_apply]
    calc
      ∑ n ∈ s, (defectPotentialSourceFieldCarrier Q b L n (x n) p) k =
          ∑ n ∈ s, -(lemmaVPlanarRowField (diagInterpolant Q 0)
            (mainQ3DirectionW2 Q b L (whiteBasis n)).value
            (r n).toH1Function p k) := by
          apply Finset.sum_congr rfl
          intro n hn
          exact congrFun (congrFun
            (defectPotentialSourceFieldCarrier_eq_neg_row Q b L n (x n)) p) k
      _ = -(∑ n ∈ s, lemmaVPlanarRowField (diagInterpolant Q 0)
          (mainQ3DirectionW2 Q b L (whiteBasis n)).value
          (r n).toH1Function p k) := by rw [Finset.sum_neg_distrib]
      _ = -S p k := by simp [S, q3DistinctRow]
  have hcoord :
      (fun p => (∑ n ∈ s,
        defectPotentialSourceFieldCarrier Q b L n (x n) p) i) =
        fun p => -(S p i) := by
    funext p
    change F p i = -(S p i)
    rw [hfield]
    rfl
  have hrow := q3_distinct_h10_row_generatorKB whiteBasis s b L Q 0 r
  have hi := hrow.1 Q (by simp) i
  simpa only [hcoord, cubeIncrement_neg, energy_neg] using hi

/-- The finite response-source row estimate follows from the common
complementary projection, the constant-one projected-source bound, and the
actual distinct-potential row estimate. -/
theorem defectPotentialSourceComplementLinear_finite_row_bound
    (Q : TriadicCube 2) (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (k : ResponseCoefficient (openCubeSet Q)) (b : ℝ)
    (L : {l : ℝ // 0 < l}) (s : Finset whiteBasisIndex)
    (x : whiteBasisIndex → defectWeakPotential Q) :
    ‖∑ n ∈ s,
      defectPotentialSourceComplementLinear Q ν σ hν hσ k b L n (x n)‖ ^ 2 ≤
      lemmaVInverseHistory Q (responseFramePlanarCoefficientField ν σ k)
        ((3 : ℝ) ^ (1 / 4 : ℝ)) *
        (Numerics.generatorKB (diagMeshRadius Q 0 / L.1) * |b|) ^ 2 *
        ∑ n ∈ s, ‖x n‖ ^ 2 := by
  let hU := measurableSet_openCubeSet Q
  let hv : 0 < (volume (openCubeSet Q)).toReal := by
    rw [volume_openCubeSet_toReal]
    exact cubeVolume_pos Q
  let D := responseFrameEnergyData hU hv ν σ hν hσ k
  let V := responseFrameEnergyVariationSpace hU hv ν σ hν hσ k
  let F : Vec 2 → Vec 2 := fun p =>
    ∑ n ∈ s, defectPotentialSourceFieldCarrier Q b L n (x n) p
  let hF : MemLp F 2 (normalizedCubeMeasure Q) :=
    memLp_finsetSum s (fun n _ =>
      defectPotentialSourceFieldCarrier_memLp Q b L n (x n))
  let P : HilbertBlockL2 (openCubeSet Q) →ₗ[ℝ]
      EnergyCarrier D :=
    (V.toSubmoduleᗮ.starProjection.toLinearMap).comp (responseEnergyUpLinear D)
  have hload : projectedSourceLoad Q hF =
      ∑ n ∈ s, projectedSourceLoad Q
        (defectPotentialSourceFieldCarrier_memLp Q b L n (x n)) := by
    simpa [F, hF] using projectedSourceLoad_finset_sum Q s
      (fun n => defectPotentialSourceFieldCarrier Q b L n (x n))
      (fun n => defectPotentialSourceFieldCarrier_memLp Q b L n (x n))
  have hop (n : whiteBasisIndex) :
      defectPotentialSourceComplementLinear Q ν σ hν hσ k b L n (x n) =
        P (projectedSourceLoad Q
          (defectPotentialSourceFieldCarrier_memLp Q b L n (x n))) := by
    change (V.toSubmoduleᗮ.starProjection.toLinearMap)
      (responseEnergyUpLinear D (projectedSourceLoad Q
        (defectPotentialSourceFieldCarrier_memLp Q b L n (x n)))) = _
    rfl
  have hsum :
      (∑ n ∈ s,
        defectPotentialSourceComplementLinear Q ν σ hν hσ k b L n (x n)) =
      P (projectedSourceLoad Q hF) := by
    calc
      _ = ∑ n ∈ s, P (projectedSourceLoad Q
          (defectPotentialSourceFieldCarrier_memLp Q b L n (x n))) := by
        apply Finset.sum_congr rfl
        intro n hn
        exact hop n
      _ = P (∑ n ∈ s, projectedSourceLoad Q
          (defectPotentialSourceFieldCarrier_memLp Q b L n (x n))) := by
        rw [map_sum]
      _ = P (projectedSourceLoad Q hF) := by rw [← hload]
  have hPcomp : P (projectedSourceLoad Q hF) =
      responseEnergyUp D (scalarProjectionResidual Q ν σ hν hσ k
        (projectedSourceLoad Q hF)) := by
    exact projectedSource_carrier_complement_eq Q hU hv ν σ hν hσ k hF
  have hFpos : ∀ i : Fin 2, Summable (fun j : ℕ =>
      (Real.sqrt 3)^(j+1) * energy Q (cubeIncrement Q (j+1)
        (fun p => F p i))) := by
    intro i
    exact defectPotentialSourceFieldCarrier_finite_row_increment_summable
      Q b L s x i
  let B := lemmaVInverseHistory Q (responseFramePlanarCoefficientField ν σ k)
    ((3 : ℝ) ^ (1 / 4 : ℝ))
  have hB : 0 ≤ B := by
    dsimp [B]
    have hq : 1 < (3 : ℝ) ^ (1 / 4 : ℝ) :=
      Real.one_lt_rpow (by norm_num) (by norm_num)
    exact lemmaVInverseHistory_nonneg Q (responseFramePlanarCoefficientField ν σ k) hq
  have hnorm :
      ‖∑ n ∈ s,
        defectPotentialSourceComplementLinear Q ν σ hν hσ k b L n (x n)‖ ^ 2 =
      (scalarFrameRealization Q ν σ hν hσ k).energyBilin
        (scalarProjectionResidual Q ν σ hν hσ k (projectedSourceLoad Q hF))
        (scalarProjectionResidual Q ν σ hν hσ k (projectedSourceLoad Q hF)) := by
    rw [hsum, hPcomp, energyCarrier_norm_sq, responseEnergyUp_down]
    dsimp [D, responseFrameEnergyData, responseEnergyHilbertData,
      scalarFrameRealization]
  rw [hnorm]
  have hsource := projected_source_energy_le_source_history
    Q ν σ hν hσ k hF hFpos
  have hrow := defectPotentialSourceFieldCarrier_finite_row_bound Q b L s x
  calc
    _ ≤ B * vectorPositiveHaarEnergy Q F := by
      simpa only [B, F, hF] using hsource
    _ ≤ B * ((Numerics.generatorKB (diagMeshRadius Q 0 / L.1) * |b|) ^ 2 *
        ∑ n ∈ s, ‖x n‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hrow hB
    _ = B * (Numerics.generatorKB (diagMeshRadius Q 0 / L.1) * |b|) ^ 2 *
        ∑ n ∈ s, ‖x n‖ ^ 2 := by ring

/-- The one common q3 covariance coefficient for both physical Wick
directions: the inverse-history square root times the larger actual
generator constant. The source amplitude enters separately as `|b|=sqrt v`. -/
noncomputable def defectSourceCovarianceA (Q : TriadicCube 2)
    (ν σ : ℝ) (k : ResponseCoefficient (openCubeSet Q))
    (L : {l : ℝ // 0 < l}) : ℝ :=
  Real.sqrt (lemmaVInverseHistory Q (responseFramePlanarCoefficientField ν σ k)
    ((3 : ℝ) ^ (1 / 4 : ℝ))) *
      max (Numerics.generatorKA (diagMeshRadius Q 0 / L.1))
        (Numerics.generatorKB (diagMeshRadius Q 0 / L.1))

private theorem defectSource_history_nonneg (Q : TriadicCube 2)
    (ν σ : ℝ) (k : ResponseCoefficient (openCubeSet Q)) :
    0 ≤ lemmaVInverseHistory Q (responseFramePlanarCoefficientField ν σ k)
      ((3 : ℝ) ^ (1 / 4 : ℝ)) := by
  have hq : 1 < (3 : ℝ) ^ (1 / 4 : ℝ) :=
    Real.one_lt_rpow (by norm_num) (by norm_num)
  exact lemmaVInverseHistory_nonneg Q (responseFramePlanarCoefficientField ν σ k) hq

private theorem generator_constants_nonneg (ρ : ℝ) (hρ : 0 ≤ ρ) :
    0 ≤ Numerics.generatorKA ρ ∧ 0 ≤ Numerics.generatorKB ρ := by
  constructor <;> (dsimp [Numerics.generatorKA, Numerics.generatorKB]; positivity)

theorem defectSourceCovarianceA_nonneg (Q : TriadicCube 2)
    (ν σ : ℝ) (k : ResponseCoefficient (openCubeSet Q))
    (L : {l : ℝ // 0 < l}) :
    0 ≤ defectSourceCovarianceA Q ν σ k L := by
  have hρ : 0 ≤ diagMeshRadius Q 0 / L.1 :=
    div_nonneg (diagMeshRadius_pos Q 0).le L.2.le
  have hgen := generator_constants_nonneg _ hρ
  unfold defectSourceCovarianceA
  exact mul_nonneg (Real.sqrt_nonneg _)
    (hgen.1.trans (le_max_left _ _))

private theorem defectSourceKA_le_common (Q : TriadicCube 2)
    (ν σ : ℝ) (k : ResponseCoefficient (openCubeSet Q))
    (L : {l : ℝ // 0 < l}) (b : ℝ) :
    Real.sqrt (lemmaVInverseHistory Q (responseFramePlanarCoefficientField ν σ k)
      ((3 : ℝ) ^ (1 / 4 : ℝ))) *
        (|b| * Numerics.generatorKA (diagMeshRadius Q 0 / L.1)) ≤
      defectSourceCovarianceA Q ν σ k L * |b| := by
  have hρ : 0 ≤ diagMeshRadius Q 0 / L.1 :=
    div_nonneg (diagMeshRadius_pos Q 0).le L.2.le
  calc
    _ = |b| * (Real.sqrt (lemmaVInverseHistory Q
        (responseFramePlanarCoefficientField ν σ k) ((3 : ℝ) ^ (1 / 4 : ℝ))) *
        Numerics.generatorKA (diagMeshRadius Q 0 / L.1)) := by ring
    _ ≤ |b| * (Real.sqrt (lemmaVInverseHistory Q
        (responseFramePlanarCoefficientField ν σ k) ((3 : ℝ) ^ (1 / 4 : ℝ))) *
        max (Numerics.generatorKA (diagMeshRadius Q 0 / L.1))
          (Numerics.generatorKB (diagMeshRadius Q 0 / L.1))) := by
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg b)
      exact mul_le_mul_of_nonneg_left (le_max_left _ _) (Real.sqrt_nonneg _)
    _ = _ := by unfold defectSourceCovarianceA; ring

private theorem defectSourceKB_le_common (Q : TriadicCube 2)
    (ν σ : ℝ) (k : ResponseCoefficient (openCubeSet Q))
    (L : {l : ℝ // 0 < l}) (b : ℝ) :
    Real.sqrt (lemmaVInverseHistory Q (responseFramePlanarCoefficientField ν σ k)
      ((3 : ℝ) ^ (1 / 4 : ℝ))) *
        (Numerics.generatorKB (diagMeshRadius Q 0 / L.1) * |b|) ≤
      defectSourceCovarianceA Q ν σ k L * |b| := by
  have hρ : 0 ≤ diagMeshRadius Q 0 / L.1 :=
    div_nonneg (diagMeshRadius_pos Q 0).le L.2.le
  calc
    _ = |b| * (Real.sqrt (lemmaVInverseHistory Q
        (responseFramePlanarCoefficientField ν σ k) ((3 : ℝ) ^ (1 / 4 : ℝ))) *
        Numerics.generatorKB (diagMeshRadius Q 0 / L.1)) := by ring
    _ ≤ |b| * (Real.sqrt (lemmaVInverseHistory Q
        (responseFramePlanarCoefficientField ν σ k) ((3 : ℝ) ^ (1 / 4 : ℝ))) *
        max (Numerics.generatorKA (diagMeshRadius Q 0 / L.1))
          (Numerics.generatorKB (diagMeshRadius Q 0 / L.1))) := by
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg b)
      exact mul_le_mul_of_nonneg_left (le_max_right _ _) (Real.sqrt_nonneg _)
    _ = _ := by unfold defectSourceCovarianceA; ring

/-- Common-A form of the finite column covariance estimate, with
`κ=A sqrt(v)` and `v=b^2`. -/
theorem defectPotentialSourceComplementLinear_finite_column_bound_common
    (Q : TriadicCube 2) (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (k : ResponseCoefficient (openCubeSet Q)) (b : ℝ)
    (L : {l : ℝ // 0 < l}) (s : Finset whiteBasisIndex)
    (x : defectWeakPotential Q) :
    (∑ n ∈ s,
      ‖defectPotentialSourceComplementLinear Q ν σ hν hσ k b L n x‖ ^ 2) ≤
      (defectSourceCovarianceA Q ν σ k L * |b|) ^ 2 * ‖x‖ ^ 2 := by
  let B := lemmaVInverseHistory Q (responseFramePlanarCoefficientField ν σ k)
    ((3 : ℝ) ^ (1 / 4 : ℝ))
  let C := Real.sqrt B * (|b| * Numerics.generatorKA (diagMeshRadius Q 0 / L.1))
  let K := defectSourceCovarianceA Q ν σ k L * |b|
  have hcoeff : C ≤ K := by
    dsimp [C, B, K]
    exact defectSourceKA_le_common Q ν σ k L b
  have hC : 0 ≤ C := by
    have hρ : 0 ≤ diagMeshRadius Q 0 / L.1 :=
      div_nonneg (diagMeshRadius_pos Q 0).le L.2.le
    have hKA := generator_constants_nonneg _ hρ |>.1
    dsimp [C, B]
    exact mul_nonneg (Real.sqrt_nonneg _) (mul_nonneg (abs_nonneg b) hKA)
  have hcoefSq : C ^ 2 ≤ K ^ 2 := pow_le_pow_left₀ hC hcoeff 2
  have hcol := defectPotentialSourceComplementLinear_finite_column_bound
    Q ν σ hν hσ k b L s x
  calc
    _ ≤ C ^ 2 * ‖x‖ ^ 2 := by simpa [C, B] using hcol
    _ ≤ K ^ 2 * ‖x‖ ^ 2 :=
      mul_le_mul_of_nonneg_right hcoefSq (sq_nonneg ‖x‖)
    _ = (defectSourceCovarianceA Q ν σ k L * |b|) ^ 2 * ‖x‖ ^ 2 := by rfl

/-- Common-A form of the finite row covariance estimate, with
`κ=A sqrt(v)` and `v=b^2`. -/
theorem defectPotentialSourceComplementLinear_finite_row_bound_common
    (Q : TriadicCube 2) (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (k : ResponseCoefficient (openCubeSet Q)) (b : ℝ)
    (L : {l : ℝ // 0 < l}) (s : Finset whiteBasisIndex)
    (x : whiteBasisIndex → defectWeakPotential Q) :
    ‖∑ n ∈ s,
      defectPotentialSourceComplementLinear Q ν σ hν hσ k b L n (x n)‖ ^ 2 ≤
      (defectSourceCovarianceA Q ν σ k L * |b|) ^ 2 *
        ∑ n ∈ s, ‖x n‖ ^ 2 := by
  let B := lemmaVInverseHistory Q (responseFramePlanarCoefficientField ν σ k)
    ((3 : ℝ) ^ (1 / 4 : ℝ))
  let K := defectSourceCovarianceA Q ν σ k L * |b|
  let C := Real.sqrt B *
    (Numerics.generatorKB (diagMeshRadius Q 0 / L.1) * |b|)
  have hcoeff : C ≤ K := by
    dsimp [C, B, K]
    exact defectSourceKB_le_common Q ν σ k L b
  have hC : 0 ≤ C := by
    have hρ : 0 ≤ diagMeshRadius Q 0 / L.1 :=
      div_nonneg (diagMeshRadius_pos Q 0).le L.2.le
    have hKB := generator_constants_nonneg _ hρ |>.2
    dsimp [C, B]
    exact mul_nonneg (Real.sqrt_nonneg _) (mul_nonneg hKB (abs_nonneg b))
  have hcoefSq : C ^ 2 ≤ K ^ 2 := pow_le_pow_left₀ hC hcoeff 2
  have hB := defectSource_history_nonneg Q ν σ k
  have hB' : 0 ≤ B := by simpa [B] using hB
  have hrow := defectPotentialSourceComplementLinear_finite_row_bound
    Q ν σ hν hσ k b L s x
  have hrow' : ‖∑ n ∈ s,
      defectPotentialSourceComplementLinear Q ν σ hν hσ k b L n (x n)‖ ^ 2 ≤
      C ^ 2 * ∑ n ∈ s, ‖x n‖ ^ 2 := by
    calc
      _ ≤ B *
          (Numerics.generatorKB (diagMeshRadius Q 0 / L.1) * |b|) ^ 2 *
          ∑ n ∈ s, ‖x n‖ ^ 2 := hrow
      _ = _ := by
        change B *
            (Numerics.generatorKB (diagMeshRadius Q 0 / L.1) * |b|) ^ 2 *
              ∑ n ∈ s, ‖x n‖ ^ 2 =
          (Real.sqrt B * (Numerics.generatorKB (diagMeshRadius Q 0 / L.1) * |b|)) ^ 2 *
            ∑ n ∈ s, ‖x n‖ ^ 2
        calc
          _ = (Real.sqrt B) ^ 2 *
              (Numerics.generatorKB (diagMeshRadius Q 0 / L.1) * |b|) ^ 2 *
                ∑ n ∈ s, ‖x n‖ ^ 2 := by rw [Real.sq_sqrt hB']
          _ = _ := by ring
  calc
    _ ≤ C ^ 2 * ∑ n ∈ s, ‖x n‖ ^ 2 := hrow'
    _ ≤ K ^ 2 * ∑ n ∈ s, ‖x n‖ ^ 2 :=
      mul_le_mul_of_nonneg_right hcoefSq
        (Finset.sum_nonneg fun n hn => sq_nonneg ‖x n‖)
    _ = (defectSourceCovarianceA Q ν σ k L * |b|) ^ 2 *
        ∑ n ∈ s, ‖x n‖ ^ 2 := by rfl

end
end ASDExplicitGamma.Scalar
