module

public import ASDExplicitGamma.Scalar.SmoothFeedbackResponse
public import ASDExplicitGamma.Scalar.CutoffProjection
public import ASDExplicitGamma.Variational.PairedBessel

/-! Actual response-space witnesses for the recovered cell minimizers.

These bind the cell tests used in the directional Gamma to the public Hodge
and response-space API, so later projection estimates can use compatibility
of the literal recovered fields and their coefficient reflections.
-/

@[expose] public section

namespace ASDExplicitGamma.Scalar

open Homogenization MeasureTheory Variational Response

/-- The actual recovered affine test lies in the coefficient response space. -/
theorem scalarCellResponseTest_mem_responseSpace
    (Q : TriadicCube 2) (a : CoeffField 2) {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a) (P : BlockVec 2) :
    BlockResponseSpace a (openCubeSet Q) (scalarCellResponseTest Q a hEll P) := by
  let hConv := isOpenBoundedConvexDomain_openCubeSet Q
  have hvol : (volume (openCubeSet Q)).toReal ≠ 0 := by
    rw [volume_openCubeSet_toReal]
    exact (cubeVolume_pos Q).ne'
  let R := (lemmaVRecoveryData hConv).toMuCorrectionSpaceRecoveryData
  exact R.recoveredField_mem_responseSpace_of_isEllipticFieldOn_of_isOpenBoundedConvexDomain
    (scalarCellSystem Q a hEll) hConv hEll hvol P

/-- The weighted projection representative of a constant affine load agrees
almost everywhere with the literal recovered cell response. -/
theorem scalarFrameResidual_eq_responseTest_ae
    (Q : TriadicCube 2) (nu sigma : ℝ) (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (P : BlockVec 2) :
    (fun x => scalarResidualField Q nu sigma hnu hsigma k
      ((scalarFrameRealization Q nu sigma hnu hsigma k).constantField P) x) =ᵐ[
        volumeMeasureOn (openCubeSet Q)]
      (scalarCellResponseTest Q
        (responseFramePlanarCoefficientField nu sigma k)
        (responseFramePlanarCoefficientField_isElliptic
          (measurableSet_openCubeSet Q) nu sigma hnu hsigma k) P).eval := by
  let a := responseFramePlanarCoefficientField nu sigma k
  let hEll := responseFramePlanarCoefficientField_isElliptic
    (measurableSet_openCubeSet Q) nu sigma hnu hsigma k
  let hConv := isOpenBoundedConvexDomain_openCubeSet Q
  let S := scalarCellSystem Q a hEll
  have hvol : 0 < (volume (openCubeSet Q)).toReal := by
    rw [volume_openCubeSet_toReal]
    exact cubeVolume_pos Q
  have hrec := Variational.lemmaV_recovered_minimizer_ae
    (U := openCubeSet Q) (hU := hConv) (a := a) (hEll := hEll)
    (hvol := hvol) P
  let recovery := Variational.lemmaVRecoveryData hConv
  change hilbertBlockL2ToBlockL2 (S.toMuHilbertRealization.minimizerMap P) =ᵐ[
      volumeMeasureOn (openCubeSet Q)]
    (fun x => (recovery.toMuCorrectionSpaceRecoveryData.recoveredField S P).eval x)
      at hrec
  have hprojection :
      scalarProjectionResidual Q nu sigma hnu hsigma k
        ((scalarFrameRealization Q nu sigma hnu hsigma k).constantField P) =
      S.toMuHilbertRealization.minimizerMap P := by
    rw [scalarProjectionResidual_eq_affineMinimizer]
    rfl
  change (fun x => hilbertBlockL2ToBlockL2
      (scalarProjectionResidual Q nu sigma hnu hsigma k
        ((scalarFrameRealization Q nu sigma hnu hsigma k).constantField P)) x) =ᵐ[
        volumeMeasureOn (openCubeSet Q)]
      (scalarCellResponseTest Q a hEll P).eval
  rw [hprojection]
  simpa [scalarCellResponseTest, recovery, S, a, hEll] using hrec

/-- The literal scalar-frame projection residual is a genuine coefficient
response-space field, through its equality with the recovered affine solve. -/
theorem scalarFrameResidual_mem_responseSpace
    (Q : TriadicCube 2) (nu sigma : ℝ) (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (P : BlockVec 2) :
    BlockResponseSpace (responseFramePlanarCoefficientField nu sigma k)
      (openCubeSet Q)
      ⟨fun x => (scalarResidualField Q nu sigma hnu hsigma k
          ((scalarFrameRealization Q nu sigma hnu hsigma k).constantField P) x).1,
        fun x => (scalarResidualField Q nu sigma hnu hsigma k
          ((scalarFrameRealization Q nu sigma hnu hsigma k).constantField P) x).2⟩ := by
  let a := responseFramePlanarCoefficientField nu sigma k
  let hEll := responseFramePlanarCoefficientField_isElliptic
    (measurableSet_openCubeSet Q) nu sigma hnu hsigma k
  let X := scalarCellResponseTest Q a hEll P
  let Z : BlockState 2 := ⟨
    fun x => (scalarResidualField Q nu sigma hnu hsigma k
      ((scalarFrameRealization Q nu sigma hnu hsigma k).constantField P) x).1,
    fun x => (scalarResidualField Q nu sigma hnu hsigma k
      ((scalarFrameRealization Q nu sigma hnu hsigma k).constantField P) x).2⟩
  have hX : BlockResponseSpace a (openCubeSet Q) X :=
    scalarCellResponseTest_mem_responseSpace Q a hEll P
  have hAE : Z.eval =ᵐ[volumeMeasureOn (openCubeSet Q)] X.eval := by
    change (fun x => scalarResidualField Q nu sigma hnu hsigma k
        ((scalarFrameRealization Q nu sigma hnu hsigma k).constantField P) x) =ᵐ[
          volumeMeasureOn (openCubeSet Q)]
      (scalarCellResponseTest Q a hEll P).eval
    exact scalarFrameResidual_eq_responseTest_ae Q nu sigma hnu hsigma k P
  have hPotAE : Z.potential =ᵐ[volumeMeasureOn (openCubeSet Q)] X.potential :=
    hAE.mono fun x hx => congrArg Prod.fst hx
  have hFluxAE : Z.flux =ᵐ[volumeMeasureOn (openCubeSet Q)] X.flux :=
    hAE.mono fun x hx => congrArg Prod.snd hx
  have hXpot : IsPotentialOn (openCubeSet Q) X.potential := hX.1
  have hXsol : IsSolenoidalOn (openCubeSet Q) X.flux := hX.2.1
  have hPot : IsPotentialOn (openCubeSet Q) Z.potential := by
    exact IsPotentialOn.congr_ae hPotAE.symm hXpot
  have hSol : IsSolenoidalOn (openCubeSet Q) Z.flux := by
    intro φ
    calc
      ∫ x in openCubeSet Q, vecDot (Z.flux x) (φ.toH1Function.grad x) ∂volume =
          ∫ x in openCubeSet Q, vecDot (X.flux x) (φ.toH1Function.grad x) ∂volume := by
        apply integral_congr_ae
        exact hFluxAE.mono fun x hx => by simp [hx]
      _ = 0 := hXsol φ
  refine ⟨hPot, hSol, ?_⟩
  intro Y hY
  have hInt : (fun x => blockVecDot (Y.eval x)
      (blockMatVecMul (blockCoeffField a x) (Z.eval x))) =ᵐ[
        volumeMeasureOn (openCubeSet Q)]
      (fun x => blockVecDot (Y.eval x)
        (blockMatVecMul (blockCoeffField a x) (X.eval x))) := by
    filter_upwards [hAE, ae_restrict_mem (measurableSet_openCubeSet Q)] with x hx _
    rw [hx]
  rw [integral_congr_ae hInt]
  exact hX.2.2 Y hY

/-- A finite-energy response field remains a response field when restricted
to a descendant cube. This follows from the local Hodge equations for its two
coefficient images. -/
theorem blockResponseSpace_restrict_subcube
    (Q R : TriadicCube 2) (hRQ : openCubeSet R ⊆ openCubeSet Q)
    (a : CoeffField 2) {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (X : BlockState 2) (hX : BlockResponseSpace a (openCubeSet Q) X)
    (hXmem : MemBlockL2 (openCubeSet Q) X.eval) :
    BlockResponseSpace a (openCubeSet R) X := by
  let : Fact (volume (openCubeSet Q) < ⊤) := ⟨volume_openCubeSet_lt_top Q⟩
  let : IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) := by infer_instance
  let : Fact (volume (openCubeSet R) < ⊤) := ⟨volume_openCubeSet_lt_top R⟩
  let : IsFiniteMeasure (volumeMeasureOn (openCubeSet R)) := by infer_instance
  have hEllR : IsEllipticFieldOn lam Lam (openCubeSet R) a :=
    hEll.mono (measurableSet_openCubeSet R) hRQ
  have hPotMemQ : MemVectorL2 (openCubeSet Q) X.potential :=
    memVectorL2_fst_of_memBlockL2 hXmem
  have hFluxMemQ : MemVectorL2 (openCubeSet Q) X.flux :=
    memVectorL2_snd_of_memBlockL2 hXmem
  have hPotMemR : MemVectorL2 (openCubeSet R) X.potential :=
    hPotMemQ.mono_measure (Measure.restrict_mono_set volume hRQ)
  have hFluxMemR : MemVectorL2 (openCubeSet R) X.flux :=
    hFluxMemQ.mono_measure (Measure.restrict_mono_set volume hRQ)
  have hUpperMemR : MemVectorL2 (openCubeSet R)
      (fun x => (blockMatVecMul (blockCoeffField a x) (X.eval x)).1) := by
    have hLowerMemR : MemVectorL2 (openCubeSet R)
        (fun x => (blockMatVecMul (blockCoeffField a x) (X.eval x)).2) := by
      have hLowerQ :=
        blockResponse_lowerImage_memVectorL2_of_flux_memVectorL2_of_mem_responseSpace_of_isEllipticFieldOn
          hX hFluxMemQ hEll
      exact hLowerQ.mono_measure (Measure.restrict_mono_set volume hRQ)
    have hUpper1 := memVectorL2_matVecMul_symmPart_of_isEllipticFieldOn hEllR hPotMemR
    have hUpper2 := memVectorL2_matVecMul_skewPart_of_isEllipticFieldOn hEllR hLowerMemR
    have hSum : MemVectorL2 (openCubeSet R)
        (fun x => matVecMul (symmPart (a x)) (X.potential x) +
          matVecMul (skewPart (a x))
            ((blockMatVecMul (blockCoeffField a x) (X.eval x)).2)) := hUpper1.add hUpper2
    have hUpperEq : (fun x =>
        (blockMatVecMul (blockCoeffField a x) (X.eval x)).1) =ᵐ[
          volume.restrict (openCubeSet R)]
        (fun x => matVecMul (symmPart (a x)) (X.potential x) +
          matVecMul (skewPart (a x))
            ((blockMatVecMul (blockCoeffField a x) (X.eval x)).2)) := by
      change (fun x => (blockMatVecMul (blockMatrixOfCoeff (a x))
          (X.potential x, X.flux x)).1) =ᵐ[volume.restrict (openCubeSet R)]
        (fun x => matVecMul (symmPart (a x)) (X.potential x) +
          matVecMul (skewPart (a x))
            ((blockMatVecMul (blockMatrixOfCoeff (a x))
              (X.potential x, X.flux x)).2))
      filter_upwards with x
      calc
        (blockMatVecMul (blockMatrixOfCoeff (a x))
            (X.potential x, X.flux x)).1 =
          matVecMul (symmPart (a x)) (X.potential x) +
            matVecMul (skewPart (a x))
              (matVecMul (symmPart (a x))⁻¹
                (X.flux x - matVecMul (skewPart (a x)) (X.potential x))) :=
          blockMatVecMul_blockMatrixOfCoeff_fst (a x) (X.potential x) (X.flux x)
        _ = matVecMul (symmPart (a x)) (X.potential x) +
            matVecMul (skewPart (a x))
              ((blockMatVecMul (blockMatrixOfCoeff (a x))
                (X.potential x, X.flux x)).2) := by
          rw [blockMatVecMul_blockMatrixOfCoeff_snd]
    exact hSum.ae_eq hUpperEq.symm
  have hUpperSolQ : IsSolenoidalOn (openCubeSet Q)
      (fun x => (blockMatVecMul (blockCoeffField a x) (X.eval x)).1) :=
    blockResponse_upperImage_isSolenoidalOn_of_mem_responseSpace hX
  have hUpperSolR : IsSolenoidalOn (openCubeSet R)
      (fun x => (blockMatVecMul (blockCoeffField a x) (X.eval x)).1) :=
    hUpperSolQ.restrict_of_isOpen_of_memVectorL2 (isOpen_openCubeSet Q)
      (isOpen_openCubeSet R) hRQ hUpperMemR
  have hLowerMemQ : MemVectorL2 (openCubeSet Q)
      (fun x => (blockMatVecMul (blockCoeffField a x) (X.eval x)).2) :=
    blockResponse_lowerImage_memVectorL2_of_flux_memVectorL2_of_mem_responseSpace_of_isEllipticFieldOn
      hX hFluxMemQ hEll
  have hLowerMemR : MemVectorL2 (openCubeSet R)
      (fun x => (blockMatVecMul (blockCoeffField a x) (X.eval x)).2) :=
    hLowerMemQ.mono_measure (Measure.restrict_mono_set volume hRQ)
  have hLowerPotQ : IsPotentialOn (openCubeSet Q)
      (fun x => (blockMatVecMul (blockCoeffField a x) (X.eval x)).2) :=
    blockResponse_lowerImage_isPotential_of_mem_responseSpace_of_memVectorL2_of_isOpenBoundedConvexDomain
      (isOpenBoundedConvexDomain_openCubeSet Q) hX hLowerMemQ
  have hLowerPotR : IsPotentialOn (openCubeSet R)
      (fun x => (blockMatVecMul (blockCoeffField a x) (X.eval x)).2) :=
    hLowerPotQ.restrict_of_isOpen_of_memVectorL2
      (isOpen_openCubeSet Q) (isOpen_openCubeSet R) hRQ hLowerMemR
  refine ⟨?_, ?_, ?_⟩
  · exact hX.1.restrict_of_isOpen_of_memVectorL2
      (isOpen_openCubeSet Q) (isOpen_openCubeSet R) hRQ hPotMemR
  · exact hX.2.1.restrict_of_isOpen_of_memVectorL2
      (isOpen_openCubeSet Q) (isOpen_openCubeSet R) hRQ hFluxMemR
  · intro Y hY
    let upper : Vec 2 → Vec 2 := fun x =>
      (blockMatVecMul (blockCoeffField a x) (X.eval x)).1
    let lower : Vec 2 → Vec 2 := fun x =>
      (blockMatVecMul (blockCoeffField a x) (X.eval x)).2
    have hfirst : ∫ x in openCubeSet R, vecDot (Y.potential x) (upper x)
        ∂volume = 0 := by
      rcases hY.1 with ⟨φ, hφ⟩
      have hz := hUpperSolR φ
      simpa [upper, hφ, vecDot_comm] using hz
    have hsecond : ∫ x in openCubeSet R, vecDot (Y.flux x) (lower x)
        ∂volume = 0 := by
      rcases hLowerPotR with ⟨ψ, hψ⟩
      have hz := hY.2 ψ
      simpa [lower, hψ, vecDot_comm] using hz
    have hpoint : ∀ x ∈ openCubeSet R,
        blockVecDot (Y.eval x)
          (blockMatVecMul (blockCoeffField a x) (X.eval x)) =
        vecDot (Y.potential x) (upper x) + vecDot (Y.flux x) (lower x) := by
      intro x hx
      simp [upper, lower, BlockState.eval, blockVecDot]
    have hrewrite : ∫ x in openCubeSet R,
        blockVecDot (Y.eval x)
          (blockMatVecMul (blockCoeffField a x) (X.eval x)) ∂volume =
        ∫ x in openCubeSet R,
          (vecDot (Y.potential x) (upper x) + vecDot (Y.flux x) (lower x)) ∂volume := by
      apply setIntegral_congr_fun (measurableSet_openCubeSet R)
      exact hpoint
    have hPotentialMemR : MemVectorL2 (openCubeSet R) Y.potential := by
      rcases hY.1 with ⟨φ, hφ⟩
      simpa [hφ] using φ.toH1Function.grad_memVectorL2
    have hTerm1Int : IntegrableOn
        (fun x => vecDot (Y.potential x) (upper x)) (openCubeSet R) :=
      integrableOn_vecDot_of_memVectorL2 hPotentialMemR hUpperMemR
    rw [hrewrite]
    by_cases hTerm2Int : IntegrableOn
        (fun x => vecDot (Y.flux x) (lower x)) (openCubeSet R)
    · rw [integral_add hTerm1Int hTerm2Int, hfirst, hsecond]
      simp
    · have hSumNotInt : ¬ IntegrableOn
          (fun x => vecDot (Y.potential x) (upper x) +
            vecDot (Y.flux x) (lower x)) (openCubeSet R) := by
        intro hSumInt
        exact hTerm2Int ((integrable_add_iff_integrable_right' hTerm1Int).mp hSumInt)
      rw [integral_undef hSumNotInt]

private theorem blockResponse_upperImage_memVectorL2
    {U : Set (Vec 2)} {a : CoeffField 2} {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam U a) (X : BlockState 2)
    (hX : BlockResponseSpace a U X) (hXmem : MemBlockL2 U X.eval) :
    MemVectorL2 U (fun x => (blockMatVecMul (blockCoeffField a x) (X.eval x)).1) := by
  have hPotMem : MemVectorL2 U X.potential := memVectorL2_fst_of_memBlockL2 hXmem
  have hFluxMem : MemVectorL2 U X.flux := memVectorL2_snd_of_memBlockL2 hXmem
  have hLower :=
    blockResponse_lowerImage_memVectorL2_of_flux_memVectorL2_of_mem_responseSpace_of_isEllipticFieldOn
      hX hFluxMem hEll
  have hUpper1 := memVectorL2_matVecMul_symmPart_of_isEllipticFieldOn hEll hPotMem
  have hUpper2 := memVectorL2_matVecMul_skewPart_of_isEllipticFieldOn hEll hLower
  have hSum : MemVectorL2 U (fun x => matVecMul (symmPart (a x)) (X.potential x) +
      matVecMul (skewPart (a x))
        ((blockMatVecMul (blockCoeffField a x) (X.eval x)).2)) := hUpper1.add hUpper2
  have hUpperEq : (fun x =>
      (blockMatVecMul (blockCoeffField a x) (X.eval x)).1) =ᵐ[volume.restrict U]
      (fun x => matVecMul (symmPart (a x)) (X.potential x) +
        matVecMul (skewPart (a x))
          ((blockMatVecMul (blockCoeffField a x) (X.eval x)).2)) := by
    filter_upwards with x
    change (blockMatVecMul (blockMatrixOfCoeff (a x))
        (X.potential x, X.flux x)).1 =
      matVecMul (symmPart (a x)) (X.potential x) +
        matVecMul (skewPart (a x))
          ((blockMatVecMul (blockMatrixOfCoeff (a x))
            (X.potential x, X.flux x)).2)
    calc
      (blockMatVecMul (blockMatrixOfCoeff (a x))
          (X.potential x, X.flux x)).1 =
        matVecMul (symmPart (a x)) (X.potential x) +
          matVecMul (skewPart (a x))
            (matVecMul (symmPart (a x))⁻¹
              (X.flux x - matVecMul (skewPart (a x)) (X.potential x))) :=
        blockMatVecMul_blockMatrixOfCoeff_fst (a x) (X.potential x) (X.flux x)
      _ = matVecMul (symmPart (a x)) (X.potential x) +
          matVecMul (skewPart (a x))
            ((blockMatVecMul (blockMatrixOfCoeff (a x))
              (X.potential x, X.flux x)).2) := by
        rw [blockMatVecMul_blockMatrixOfCoeff_snd]
  exact hSum.ae_eq hUpperEq.symm

/-- The difference of two finite-energy response fields is a response field.
The orthogonality follows from the solenoidal upper coefficient image and the
potential lower coefficient image, so no integrability is imposed on test
fields beyond the response-space API. -/
theorem blockResponseSpace_sub
    {Q : TriadicCube 2} {a : CoeffField 2} {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (X Y : BlockState 2)
    (hX : BlockResponseSpace a (openCubeSet Q) X)
    (hY : BlockResponseSpace a (openCubeSet Q) Y)
    (hXmem : MemBlockL2 (openCubeSet Q) X.eval)
    (hYmem : MemBlockL2 (openCubeSet Q) Y.eval) :
    BlockResponseSpace a (openCubeSet Q)
      (X + (-1 : ℝ) • Y) := by
  let U : Set (Vec 2) := openCubeSet Q
  let : Fact (volume U < ⊤) := ⟨volume_openCubeSet_lt_top Q⟩
  let : IsFiniteMeasure (volumeMeasureOn U) := by infer_instance
  have hConv : IsOpenBoundedConvexDomain U := isOpenBoundedConvexDomain_openCubeSet Q
  have hXpotMem : MemVectorL2 U X.potential := memVectorL2_fst_of_memBlockL2 hXmem
  have hYpotMem : MemVectorL2 U Y.potential := memVectorL2_fst_of_memBlockL2 hYmem
  have hXfluxMem : MemVectorL2 U X.flux := memVectorL2_snd_of_memBlockL2 hXmem
  have hYfluxMem : MemVectorL2 U Y.flux := memVectorL2_snd_of_memBlockL2 hYmem
  let upperX : Vec 2 → Vec 2 := fun x =>
    (blockMatVecMul (blockCoeffField a x) (X.eval x)).1
  let upperY : Vec 2 → Vec 2 := fun x =>
    (blockMatVecMul (blockCoeffField a x) (Y.eval x)).1
  let lowerX : Vec 2 → Vec 2 := fun x =>
    (blockMatVecMul (blockCoeffField a x) (X.eval x)).2
  let lowerY : Vec 2 → Vec 2 := fun x =>
    (blockMatVecMul (blockCoeffField a x) (Y.eval x)).2
  let Z : BlockState 2 := X + (-1 : ℝ) • Y
  have hUpperXmem : MemVectorL2 U upperX := by
    simpa [upperX, U] using blockResponse_upperImage_memVectorL2 hEll X hX hXmem
  have hUpperYmem : MemVectorL2 U upperY := by
    simpa [upperY, U] using blockResponse_upperImage_memVectorL2 hEll Y hY hYmem
  have hLowerXmem : MemVectorL2 U lowerX := by
    simpa [lowerX, U] using
      blockResponse_lowerImage_memVectorL2_of_flux_memVectorL2_of_mem_responseSpace_of_isEllipticFieldOn
        hX hXfluxMem hEll
  have hLowerYmem : MemVectorL2 U lowerY := by
    simpa [lowerY, U] using
      blockResponse_lowerImage_memVectorL2_of_flux_memVectorL2_of_mem_responseSpace_of_isEllipticFieldOn
        hY hYfluxMem hEll
  have hUpperXsol : IsSolenoidalOn U upperX := by
    simpa [upperX, U] using blockResponse_upperImage_isSolenoidalOn_of_mem_responseSpace hX
  have hUpperYsol : IsSolenoidalOn U upperY := by
    simpa [upperY, U] using blockResponse_upperImage_isSolenoidalOn_of_mem_responseSpace hY
  have hZeval (x : Vec 2) : Z.eval x = X.eval x + (-1 : ℝ) • Y.eval x := by
    simp [Z]
  have hUpperZeq : (fun x =>
      (blockMatVecMul (blockCoeffField a x) (Z.eval x)).1) =
      upperX + (-1 : ℝ) • upperY := by
    funext x
    rw [hZeval x, blockMatVecMul_add, blockMatVecMul_smul]
    rfl
  have hUpperZsol : IsSolenoidalOn U
      (fun x => (blockMatVecMul (blockCoeffField a x) (Z.eval x)).1) := by
    have hneg : IsSolenoidalOn U ((-1 : ℝ) • upperY) :=
      isSolenoidalOn_smul hUpperYsol (-1)
    have hnegMem : MemVectorL2 U ((-1 : ℝ) • upperY) :=
      hUpperYmem.const_smul (-1)
    have hsum := isSolenoidalOn_add_of_memVectorL2 hUpperXmem
      hnegMem hUpperXsol hneg
    rw [hUpperZeq]
    exact hsum
  have hLowerXpot : IsPotentialOn U lowerX := by
    simpa [lowerX, U] using
      blockResponse_lowerImage_isPotential_of_mem_responseSpace_of_memVectorL2_of_isOpenBoundedConvexDomain
        hConv hX hLowerXmem
  have hLowerYpot : IsPotentialOn U lowerY := by
    simpa [lowerY, U] using
      blockResponse_lowerImage_isPotential_of_mem_responseSpace_of_memVectorL2_of_isOpenBoundedConvexDomain
        hConv hY hLowerYmem
  have hLowerZeq : (fun x =>
      (blockMatVecMul (blockCoeffField a x) (Z.eval x)).2) =
      lowerX + (-1 : ℝ) • lowerY := by
    funext x
    rw [hZeval x, blockMatVecMul_add, blockMatVecMul_smul]
    rfl
  have hLowerZpot : IsPotentialOn U
      (fun x => (blockMatVecMul (blockCoeffField a x) (Z.eval x)).2) := by
    have hsum := isPotentialOn_add hLowerXpot
      (isPotentialOn_smul hLowerYpot (-1))
    rw [hLowerZeq]
    exact hsum
  have hZpot : IsPotentialOn U Z.potential := by
    have hsum := isPotentialOn_add hX.1 (isPotentialOn_smul hY.1 (-1))
    change IsPotentialOn U (X.potential + (-1 : ℝ) • Y.potential)
    exact hsum
  have hZflux : IsSolenoidalOn U Z.flux := by
    have hnegMem : MemVectorL2 U ((-1 : ℝ) • Y.flux) := hYfluxMem.const_smul (-1)
    have hsum := isSolenoidalOn_add_of_memVectorL2 hXfluxMem
      hnegMem hX.2.1 (isSolenoidalOn_smul hY.2.1 (-1))
    change IsSolenoidalOn U (X.flux + (-1 : ℝ) • Y.flux)
    exact hsum
  have hUpperZmem : MemVectorL2 U
      (fun x => (blockMatVecMul (blockCoeffField a x) (Z.eval x)).1) := by
    rw [hUpperZeq]
    exact hUpperXmem.add (hUpperYmem.const_smul (-1))
  refine ⟨hZpot, hZflux, ?_⟩
  intro T hT
  have hfirst : ∫ x in U, vecDot (T.potential x)
      ((blockMatVecMul (blockCoeffField a x) (Z.eval x)).1) ∂volume = 0 := by
    rcases hT.1 with ⟨φ, hφ⟩
    have hz := hUpperZsol φ
    simpa [hφ, vecDot_comm] using hz
  have hsecond : ∫ x in U, vecDot (T.flux x)
      ((blockMatVecMul (blockCoeffField a x) (Z.eval x)).2) ∂volume = 0 := by
    rcases hLowerZpot with ⟨ψ, hψ⟩
    have hz := hT.2 ψ
    simpa [hψ, vecDot_comm] using hz
  have hpoint : ∀ x ∈ U,
      blockVecDot (T.eval x)
        (blockMatVecMul (blockCoeffField a x) (Z.eval x)) =
      vecDot (T.potential x)
          ((blockMatVecMul (blockCoeffField a x) (Z.eval x)).1) +
        vecDot (T.flux x)
          ((blockMatVecMul (blockCoeffField a x) (Z.eval x)).2) := by
    intro x hx
    simp [BlockState.eval, blockVecDot]
  have hrewrite : ∫ x in U,
      blockVecDot (T.eval x)
        (blockMatVecMul (blockCoeffField a x) (Z.eval x)) ∂volume =
      ∫ x in U,
        (vecDot (T.potential x)
            ((blockMatVecMul (blockCoeffField a x) (Z.eval x)).1) +
          vecDot (T.flux x)
            ((blockMatVecMul (blockCoeffField a x) (Z.eval x)).2)) ∂volume := by
    apply setIntegral_congr_fun (measurableSet_openCubeSet Q)
    exact hpoint
  have hTpotMem : MemVectorL2 U T.potential := by
    rcases hT.1 with ⟨φ, hφ⟩
    simpa [hφ] using φ.toH1Function.grad_memVectorL2
  have hTerm1Int : IntegrableOn
      (fun x => vecDot (T.potential x)
        ((blockMatVecMul (blockCoeffField a x) (Z.eval x)).1)) U :=
    integrableOn_vecDot_of_memVectorL2 hTpotMem hUpperZmem
  rw [hrewrite]
  by_cases hTerm2Int : IntegrableOn
      (fun x => vecDot (T.flux x)
        ((blockMatVecMul (blockCoeffField a x) (Z.eval x)).2)) U
  · rw [integral_add hTerm1Int hTerm2Int, hfirst, hsecond]
    simp
  · have hSumNotInt : ¬ IntegrableOn
        (fun x => vecDot (T.potential x)
            ((blockMatVecMul (blockCoeffField a x) (Z.eval x)).1) +
          vecDot (T.flux x)
            ((blockMatVecMul (blockCoeffField a x) (Z.eval x)).2)) U := by
      intro hSumInt
      exact hTerm2Int ((integrable_add_iff_integrable_right' hTerm1Int).mp hSumInt)
    rw [integral_undef hSumNotInt]

theorem pairedReflectState_mem_responseSpace'
    {U : Set (Vec 2)} {a : CoeffField 2} {X : BlockState 2}
    {lam Lam : ℝ} [IsFiniteMeasure (volumeMeasureOn U)]
    (hConv : IsOpenBoundedConvexDomain U)
    (hEll : IsEllipticFieldOn lam Lam U a)
    (hX : BlockResponseSpace a U X) (hFlux : MemVectorL2 U X.flux) :
    BlockResponseSpace a U (pairedReflectState a X) := by
  have hLower := blockResponse_lowerImage_memVectorL2_of_flux_memVectorL2_of_mem_responseSpace_of_isEllipticFieldOn
    hX hFlux hEll
  have hLowerPot : IsPotentialOn U
      (fun x => (blockMatVecMul (blockCoeffField a x) (X.eval x)).2) := by
    apply IsPotentialOn.of_orthogonal_to_solenoidalZeroNormalTrace_of_memVectorL2_of_hodgeConverseCriterion
      (hodgeConverseCriterion_of_isOpenBoundedConvexDomain hConv) hLower
    intro g hg hsol
    exact blockResponse_lowerImage_orthogonal_of_mem_responseSpace hX hsol
  have hUpperSol : IsSolenoidalOn U
      (fun x => (blockMatVecMul (blockCoeffField a x) (X.eval x)).1) :=
    blockResponse_upperImage_isSolenoidalOn_of_mem_responseSpace hX
  refine ⟨?_, ?_, ?_⟩
  · change IsPotentialOn U (pairedReflectState a X).potential
    simpa [pairedReflectState] using hLowerPot
  · change IsSolenoidalOn U (pairedReflectState a X).flux
    simpa [pairedReflectState] using hUpperSol
  · intro Y hY
    have hpoint : ∀ x ∈ U,
        blockVecDot (Y.eval x)
          (blockMatVecMul (blockCoeffField a x) ((pairedReflectState a X).eval x)) =
          vecDot (Y.potential x) (X.flux x) + vecDot (Y.flux x) (X.potential x) := by
      intro x hx
      rw [pairedReflectState_action hEll X hx]
      simp [BlockState.eval, blockVecDot, vecDot_comm]
    have hzero₁ : ∫ x in U, vecDot (Y.potential x) (X.flux x)
        ∂volume = 0 := by
      rcases hY.1 with ⟨φ, hφ⟩
      have hz := hX.2.1 φ
      simpa [hφ, vecDot_comm] using hz
    have hzero₂ : ∫ x in U, vecDot (Y.flux x) (X.potential x)
        ∂volume = 0 := by
      rcases hX.1 with ⟨φ, hφ⟩
      have hz := hY.2 φ
      simpa [hφ, vecDot_comm] using hz
    have hYpotL2 : MemVectorL2 U Y.potential := by
      rcases hY.1 with ⟨φ, hφ⟩
      simpa [hφ] using φ.grad_memVectorL2
    have hTerm1Int : IntegrableOn
        (fun x => vecDot (Y.potential x) (X.flux x)) U :=
      integrableOn_vecDot_of_memVectorL2 hYpotL2 hFlux
    have hrewrite :
        ∫ x in U, blockVecDot (Y.eval x)
          (blockMatVecMul (blockCoeffField a x)
            ((pairedReflectState a X).eval x)) ∂volume =
        ∫ x in U,
          (vecDot (Y.potential x) (X.flux x) +
            vecDot (Y.flux x) (X.potential x)) ∂volume := by
      apply setIntegral_congr_fun (measurableSet_of_isEllipticFieldOn hEll)
      intro x hx
      simpa only [Function.comp_apply] using hpoint x hx
    rw [hrewrite]
    by_cases hTerm2Int : IntegrableOn
        (fun x => vecDot (Y.flux x) (X.potential x)) U
    · rw [integral_add hTerm1Int hTerm2Int, hzero₁, hzero₂]
      simp
    · have hSumNotInt : ¬ IntegrableOn
          (fun x => vecDot (Y.potential x) (X.flux x) +
            vecDot (Y.flux x) (X.potential x)) U := by
        intro hSumInt
        exact hTerm2Int ((integrable_add_iff_integrable_right'
          (μ := volume.restrict U) hTerm1Int).mp hSumInt)
      rw [integral_undef hSumNotInt]

end ASDExplicitGamma.Scalar
