module

public import ASDExplicitGamma.Scalar.GSlotWick
public import ASDExplicitGamma.Scalar.PairedTwoSlotRep
public import ASDExplicitGamma.Native.OldSignedAveragePairing

/-! The weak embedding of an `L²` field class is a Lipschitz map `Θ`. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar

open Homogenization MeasureTheory Filter ASDExplicitGamma.Triadic ASDExplicitGamma.Variational
  ASDExplicitGamma.Gaussian ASDExplicitGamma.Native
open scoped BigOperators Topology InnerProductSpace ENNReal

noncomputable section

theorem dual_le_energy (R : TriadicCube 2) {f : Vec 2 → ℝ}
    (hf : MemLp f 2 (normalizedCubeMeasure R)) :
    dualEnergy R (Real.sqrt 3) f ≤ energy R f := by
  have h1 : (1 : ℝ) ≤ Real.sqrt 3 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt (by norm_num)
  have hq0 : (0 : ℝ) ≤ (Real.sqrt 3)⁻¹ := by positivity
  have hq1 : (Real.sqrt 3)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ h1
  have hs := summable_cubeIncrement_energy R hf
  have hsw : Summable (fun k : ℕ => (Real.sqrt 3)⁻¹ ^ k * energy R (cubeIncrement R k f)) :=
    Summable.of_nonneg_of_le (fun k => mul_nonneg (pow_nonneg hq0 _) (energy_nonneg R _))
      (fun k => by
        have := pow_le_one₀ hq0 hq1 (n := k)
        nlinarith [energy_nonneg R (cubeIncrement R k f)]) hs
  unfold dualEnergy
  rw [primalEnergy_eq_tsum R _ f hsw, ← tsum_cubeIncrement_energy R hf]
  refine Summable.tsum_le_tsum (fun k => ?_) hsw hs
  have := pow_le_one₀ hq0 hq1 (n := k)
  nlinarith [energy_nonneg R (cubeIncrement R k f)]

variable (nQ : ℤ) (m : ℕ)

local notation "QQ" => originCube 2 nQ

/-- A function representative of an `L²` class as a tile field. -/
def rep2 (u : HilbertVectorL2 (openCubeSet QQ)) : TiledL2Field QQ m :=
  ⟨rep' u, fun _ hR i => memLp_normalized_of_memL2On
    (memL2On_mono (openCubeSet_subset_of_mem_descendantsAtDepth hR)
      ((rep_memL2 u).eval i))⟩

theorem sum_energy_rep (u : HilbertVectorL2 (openCubeSet QQ)) :
    ∑ i : Fin 2, energy QQ (fun x => rep' u x i) = (cubeVolume QQ)⁻¹ * ‖u‖ ^ 2 := by
  have hmem := rep_memL2 u
  have h := old_signed_vector_average_pairing QQ (rep' u) (rep' u) hmem hmem
  have hn : ‖u‖ ^ 2 = ∫ x in openCubeSet QQ, vecDot (rep' u x) (rep' u x) ∂volume := by
    rw [← real_inner_self_eq_norm_sq, inner_rep]
  rw [hn]
  have hv : (volume (openCubeSet QQ)).toReal = cubeVolume QQ := volume_openCubeSet_toReal QQ
  unfold volumeAverage at h
  rw [hv] at h
  exact h.symm

theorem weak_le_sum_energy (h : TiledL2Field QQ m)
    (hmemQ : ∀ i : Fin 2, MemLp (fun x => h.1 x i) 2 (normalizedCubeMeasure QQ)) :
    lemmaVTiledWeakEnergy QQ m h.1 ≤ ∑ i : Fin 2, energy QQ (fun x => h.1 x i) := by
  have hE : ∀ i : Fin 2, energy QQ (fun x => h.1 x i) =
      descendantsAverage QQ m (fun R => energy R (fun x => h.1 x i)) := by
    intro i
    have hint : IntegrableOn (fun x => h.1 x i * h.1 x i) (cubeSet QQ) volume :=
      integrableOn_of_integrable_normalizedCubeMeasure QQ
        ((hmemQ i).integrable_mul (hmemQ i))
    exact cubeAverage_eq_descendantsAverage_cubeAverage_of_integrableOn QQ m _ hint
  simp only [hE]
  unfold lemmaVTiledWeakEnergy vectorWeakHaarEnergy descendantsAverage
  dsimp only
  rw [← Finset.mul_sum, Finset.sum_comm (s := descendantsAtDepth QQ m) (t := Finset.univ)]
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => ?_) (by positivity)
  exact Finset.sum_le_sum fun R hR => dual_le_energy R (h.2 R hR i)

theorem ae_transfer {f g : Vec 2 → ℝ}
    (h : f =ᵐ[volumeMeasureOn (openCubeSet QQ)] g) :
    f =ᵐ[normalizedCubeMeasure QQ] g := by
  unfold normalizedCubeMeasure cubeMeasure
  rw [volume_restrict_cubeSet_eq_volume_restrict_openCubeSet]
  exact Measure.ae_smul_measure h _

/-- The weak embedding of an `L²` class. -/
def gSlotTheta (u : HilbertVectorL2 (openCubeSet QQ)) : GSpace QQ m :=
  PsiL QQ m (rep2 nQ m u)

theorem theta_sub_norm_sq (u u' : HilbertVectorL2 (openCubeSet QQ)) :
    ‖gSlotTheta nQ m u - gSlotTheta nQ m u'‖ ^ 2 ≤ (cubeVolume QQ)⁻¹ * ‖u - u'‖ ^ 2 := by
  have hrep : ∀ v : HilbertVectorL2 (openCubeSet QQ), ∀ i : Fin 2,
      MemLp (fun x => rep' v x i) 2 (normalizedCubeMeasure QQ) :=
    fun v i => memLp_normalized_of_memL2On ((rep_memL2 v).eval i)
  let h : TiledL2Field QQ m := rep2 nQ m u - rep2 nQ m u'
  have hΘ : gSlotTheta nQ m u - gSlotTheta nQ m u' = PsiL QQ m h := by
    unfold gSlotTheta; rw [← map_sub]
  rw [hΘ, psi_norm_sq]
  have hmemQ : ∀ i : Fin 2, MemLp (fun x => h.1 x i) 2 (normalizedCubeMeasure QQ) :=
    fun i => (hrep u i).sub (hrep u' i)
  refine (weak_le_sum_energy nQ m h hmemQ).trans ?_
  rw [← sum_energy_rep]
  refine le_of_eq (Finset.sum_congr rfl fun i _ => ?_)
  rw [energy_eq_integral_sq, energy_eq_integral_sq]
  refine integral_congr_ae ?_
  have hsub : (fun x => rep' (u - u') x) =ᵐ[volumeMeasureOn (openCubeSet QQ)]
      fun x => rep' u x - rep' u' x := by
    unfold rep'
    rw [map_sub]
    filter_upwards [Lp.coeFn_sub (hilbertVectorL2ToVectorL2 u) (hilbertVectorL2ToVectorL2 u')]
      with x hx
    exact hx
  have := ae_transfer nQ (f := fun x => rep' (u - u') x i)
    (g := fun x => rep' u x i - rep' u' x i) (by
      filter_upwards [hsub] with x hx
      simp only [hx, Pi.sub_apply])
  filter_upwards [this] with x hx
  change (rep' u x i - rep' u' x i) ^ 2 = _
  rw [hx]

end

end ASDExplicitGamma.Scalar
