module

public import ASDExplicitGamma.Main.HotPatchCellWeak
public import ASDExplicitGamma.Variational.LemmaVTiles

/-! Observer-level cell coercivity (source (1.2)) through the cell inverse history, with no
ellipticity constant: the weak energy of the potential of a finite family of compatible fields
on a cell is at most the cell inverse history times the cell energy of the family. -/

@[expose] public section

namespace ASDExplicitGamma.Main

open Homogenization MeasureTheory Response Scalar Triadic Variational ASDExplicitGamma.Native ASDExplicitGamma.Triadic ASDExplicitGamma.Variational
open scoped BigOperators

noncomputable section

/-- Pairing average (energy) of a compatible field `W` on the cell `U`, in the field `a`. -/
def obsCellEnergy (U : TriadicCube 2) (a : CoeffField 2) (W : Vec 2 → BlockVec 2) : ℝ :=
  cubeAverage U (blockPairingIntegrand a ⟨fun x => (W x).1, fun x => (W x).2⟩
    ⟨fun x => (W x).1, fun x => (W x).2⟩)

theorem obsCellEnergy_nonneg (U : TriadicCube 2) {a : CoeffField 2} {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet U) a) (W : Vec 2 → BlockVec 2)
    (hcomp : ScalarCompatible (openCubeSet U) W) : 0 ≤ obsCellEnergy U a W := by
  letI : IsFiniteMeasure (volumeMeasureOn (openCubeSet U)) :=
    (isOpenBoundedConvexDomain_openCubeSet U).isFiniteMeasure_restrict_volume
  have h := compatible_blockPairingAverage_nonneg hEll
    (⟨fun x => (W x).1, fun x => (W x).2⟩ : BlockState 2)
  unfold obsCellEnergy
  rw [cubeAverage_eq_integralAverage_openCubeSet U]
  exact h

/-- Cell coercivity for a finite family of compatible fields. -/
theorem obs_compat_family_weak_cell {ι : Type*} [Fintype ι] (U : TriadicCube 2)
    {a : CoeffField 2} {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet U) a)
    (Dc : ι → Vec 2 → BlockVec 2) (hcomp : ∀ c, ScalarCompatible (openCubeSet U) (Dc c)) :
    ∑ c, vectorWeakHaarEnergy U (fun x => (Dc c x).1) ≤
      oldSignedInverseHistory U a * ∑ c, obsCellEnergy U a (Dc c) := by
  classical
  let Eu : ι → ℝ := fun c => obsCellEnergy U a (Dc c)
  let E : ℝ := ∑ c, Eu c
  have hEu0 (c : ι) : 0 ≤ Eu c := obsCellEnergy_nonneg U hEll (Dc c) (hcomp c)
  have hE0 : 0 ≤ E := Finset.sum_nonneg fun c _ => hEu0 c
  have hF (c : ι) (i : Fin 2) :
      MemLp (fun x => (Dc c x).1 i) 2 (normalizedCubeMeasure U) :=
    memLp_normalized_of_memL2On
      (memScalarL2_coord_of_memVectorL2 (memVectorL2_fst_of_memBlockL2 (hcomp c).1) i)
  have hprojc (c : ι) (j : ℕ) :
      (∑ i, energy U (cubeProjection U j (fun x => (Dc c x).1 i))) ≤
        lemmaVInverseDepthMax U a j * Eu c := by
    exact compatible_projectionEnergy_bound hEll
      ⟨fun x => (Dc c x).1, fun x => (Dc c x).2⟩
      (hcomp c).2.1 (hcomp c).2.2 (hcomp c).1 j
  have hproj (j : ℕ) : (∑ c, ∑ i, energy U (cubeProjection U j (fun x => (Dc c x).1 i))) ≤
      lemmaVInverseDepthMax U a j * E := by
    calc _ ≤ ∑ c, lemmaVInverseDepthMax U a j * Eu c :=
          Finset.sum_le_sum fun c _ => hprojc c j
      _ = _ := by rw [← Finset.mul_sum]
  obtain ⟨hsum, hid⟩ := old_signed_finite_weak_projection_series U
    (fun c x => (Dc c x).1) hF
  rw [hid]
  have hα := Scalar.inverse_history_discount_range
  have hq : 1 < (3 : ℝ) ^ (1 / 4 : ℝ) := Real.one_lt_rpow (by norm_num) (by norm_num)
  have hqinv : ((3 : ℝ) ^ (1 / 4 : ℝ))⁻¹ = Scalar.inverseHistoryDiscount :=
    (Scalar.inverse_history_discount_eq).symm
  have hs1 : Summable (fun j : ℕ => Scalar.inverseHistoryDiscount ^ j *
      lemmaVInverseDepthMax U a j) := by
    have := lemmaVInverseHistory_summable U hEll hq
    rwa [hqinv] at this
  have hpow (j : ℕ) : Scalar.inverseHistoryDiscount ^ (2 * j) ≤ Scalar.inverseHistoryDiscount ^ j :=
    pow_le_pow_of_le_one hα.1.le hα.2.le (by omega)
  have hs2 : Summable (fun j : ℕ => Scalar.inverseHistoryDiscount ^ (2 * j) *
      lemmaVInverseDepthMax U a j) :=
    Summable.of_nonneg_of_le (fun j => mul_nonneg (by have := hα.1; positivity)
      (lemmaVInverseDepthMax_nonneg U a j))
      (fun j => mul_le_mul_of_nonneg_right (hpow j) (lemmaVInverseDepthMax_nonneg U a j)) hs1
  have hcmp : (∑' j : ℕ, Scalar.inverseHistoryDiscount ^ (2 * j) *
      ∑ c, ∑ i, energy U (cubeProjection U j (fun x => (Dc c x).1 i))) ≤
      ∑' j : ℕ, Scalar.inverseHistoryDiscount ^ (2 * j) *
        (lemmaVInverseDepthMax U a j * E) :=
    hsum.tsum_le_tsum (fun j => mul_le_mul_of_nonneg_left (hproj j) (by
      have := hα.1; positivity)) ((hs2.mul_right E).congr (fun j => by ring))
  have hfac : 0 ≤ 1 - Scalar.inverseHistoryDiscount ^ 2 := by
    nlinarith [hα.1, hα.2]
  calc (1 - Scalar.inverseHistoryDiscount ^ 2) * ∑' j : ℕ, Scalar.inverseHistoryDiscount ^ (2 * j) *
        ∑ c, ∑ i, energy U (cubeProjection U j (fun x => (Dc c x).1 i))
      ≤ (1 - Scalar.inverseHistoryDiscount ^ 2) * ∑' j : ℕ, Scalar.inverseHistoryDiscount ^ (2 * j) *
        (lemmaVInverseDepthMax U a j * E) := mul_le_mul_of_nonneg_left hcmp hfac
    _ = ((1 - Scalar.inverseHistoryDiscount ^ 2) * ∑' j : ℕ, Scalar.inverseHistoryDiscount ^ (2 * j) *
        lemmaVInverseDepthMax U a j) * E := by
      rw [show (∑' j : ℕ, Scalar.inverseHistoryDiscount ^ (2 * j) *
          (lemmaVInverseDepthMax U a j * E)) = (∑' j : ℕ, Scalar.inverseHistoryDiscount ^ (2 * j) *
          lemmaVInverseDepthMax U a j) * E by
        rw [← tsum_mul_right]; exact tsum_congr fun j => by ring]
      ring
    _ ≤ oldSignedInverseHistory U a * E :=
      mul_le_mul_of_nonneg_right (hot_weak_weights_le_inverse_history U a hEll) hE0

/-- Tiled coercivity at the root: for compatible fields on `Q`, the depth-`m` tiled weak energy of
the potentials is at most `B` times the root energy, where `B` bounds all depth-`m` cell
histories. No ellipticity constant enters. -/
theorem obs_compat_family_weak_tiled {ι : Type*} [Fintype ι] (Q : TriadicCube 2) (m : ℕ)
    {a : CoeffField 2} {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (Dc : ι → Vec 2 → BlockVec 2) (hcomp : ∀ c, ScalarCompatible (openCubeSet Q) (Dc c))
    (B : ℝ) (hhist : ∀ U ∈ descendantsAtDepth Q m, lemmaVInverseHistory U a ((3 : ℝ) ^ (1 / 4 : ℝ)) ≤ B) :
    ∑ c, lemmaVTiledWeakEnergy Q m (fun x => (Dc c x).1) ≤
      B * ∑ c, obsCellEnergy Q a (Dc c) := by
  classical
  letI : IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
    (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume
  have hcell (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth Q m) :
      ∑ c, vectorWeakHaarEnergy U (fun x => (Dc c x).1) ≤
        B * ∑ c, obsCellEnergy U a (Dc c) := by
    have hsub := openCubeSet_subset_of_mem_descendantsAtDepth hU
    have hEllU := hEll.mono (measurableSet_openCubeSet U) hsub
    have hcU (c : ι) : ScalarCompatible (openCubeSet U) (Dc c) :=
      old_signed_compatible_restrict Q U hsub (hcomp c)
    have h := obs_compat_family_weak_cell U hEllU Dc hcU
    have hE0 : 0 ≤ ∑ c, obsCellEnergy U a (Dc c) :=
      Finset.sum_nonneg fun c _ => obsCellEnergy_nonneg U hEllU (Dc c) (hcU c)
    exact h.trans (mul_le_mul_of_nonneg_right (hhist U hU) hE0)
  have hint (c : ι) : IntegrableOn (blockPairingIntegrand a
      (⟨fun x => (Dc c x).1, fun x => (Dc c x).2⟩ : BlockState 2)
      (⟨fun x => (Dc c x).1, fun x => (Dc c x).2⟩ : BlockState 2)) (cubeSet Q) := by
    have hmem : MemBlockL2 (openCubeSet Q)
        (BlockState.eval (⟨fun x => (Dc c x).1, fun x => (Dc c x).2⟩ : BlockState 2)) := (hcomp c).1
    exact integrableOn_cubeSet_iff_integrableOn_openCubeSet.mpr
      (blockPairingIntegrand_integrableOn_of_memBlockL2_of_isEllipticFieldOn hmem hmem hEll)
  have havg (c : ι) : descendantsAverage Q m (fun U => obsCellEnergy U a (Dc c)) =
      obsCellEnergy Q a (Dc c) :=
    (cubeAverage_eq_descendantsAverage_cubeAverage_of_integrableOn Q m _ (hint c)).symm
  have hsumAvg : descendantsAverage Q m (fun U => ∑ c, obsCellEnergy U a (Dc c)) =
      ∑ c, obsCellEnergy Q a (Dc c) := by
    rw [Homogenization.descendantsAverage_sum]
    exact Finset.sum_congr rfl fun c _ => havg c
  have hweak : ∑ c, lemmaVTiledWeakEnergy Q m (fun x => (Dc c x).1) =
      descendantsAverage Q m (fun U => ∑ c, vectorWeakHaarEnergy U (fun x => (Dc c x).1)) := by
    unfold lemmaVTiledWeakEnergy
    rw [Homogenization.descendantsAverage_sum]
  rw [hweak, ← hsumAvg, ← descendantsAverage_mul_left]
  exact descendantsAverage_le fun U hU => hcell U hU

end

end ASDExplicitGamma.Main
