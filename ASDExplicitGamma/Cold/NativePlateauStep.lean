module

public import ASDExplicitGamma.Cold.NativeHistoryRepresentative
public import ASDExplicitGamma.Cold.NativeMatchedCutoff
public import ASDExplicitGamma.Cold.NativeOwnGraph
public import ASDExplicitGamma.Cold.CanonicalGraphMeasurable
public import ASDExplicitGamma.Cold.ColdPlateauNumericStep

/-! # The actual fixed-native-model plateau step has no expectation or graph premises -/

@[expose] public section
noncomputable section
open MeasureTheory Homogenization Algsuperdiff.Section3
open scoped ENNReal
namespace ASDExplicitGamma.Cold
open ASDExplicitGamma.Numerics.Cold

/-- Every updated lag has the genuine even-lag plateau parameterization with J>=2. -/
theorem cold_updated_lag_even {j : ℕ} (hj : j ∈ coldUpdatedLags) : ∃ J, 2 ≤ J ∧ j = 2*J := by
  rcases List.mem_map.mp hj with ⟨i,hi,he⟩
  exact ⟨i+2,by omega,by omega⟩

/-- The actual native P1--P6 recurrence, using root/strong inputs and only strictly earlier
means. Canonical measurability, ordinary integrability, histories and actual graph estimates are
all produced internally at this one coefficient/frame. -/
theorem cold_native_plateau_step (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (m : ℤ)
    {θ : ℝ} (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hroot : root20 M m ≤ ENNReal.ofReal (θ*(coldR20:ℝ)))
    (hstrong : strong20 M m ≤ ENNReal.ofReal (θ*(coldS20:ℝ)))
    {j r4 : ℕ} (hr4 : r4 = 4) (hj : j ∈ coldUpdatedLags)
    (hmean : ∀ k < j, coldNativeMean M m k ≤ θ*(coldMeanAt k:ℝ)) :
    coldExactDenominator j*coldNativeMean M m j ≤ coldExactWeightedMeans (coldNativeMean M m) j+
      θ*((coldGraphContribution j:ℝ)+(coldBadHistory j:ℝ)) := by
  obtain ⟨J,hJ,rfl⟩ := cold_updated_lag_even hj
  let Q := originCube 2 (m+((2*J:ℕ):ℤ))
  let F := coldNativePlateauFamily M m Q
  let μprob := (Cutoff.cutoffSampleLaw M).toMeasure
  let μsmall := fun (r : ℕ) => ∫ ω, cutoffTraceDefect M m (Q.scale-(r:ℤ)) ω ∂μprob
  obtain ⟨D,hD,_he,hDn,h20,hMoment,hDroot,hmax⟩ :=
    cold_native_history_representative M h hM m hθ hroot hstrong hj hmean
  have hstat (r : ℕ) (R : SquareCells Q r) :
      (∫ ω, (F.atDepth r).cellTrace R ω ∂μprob) = μsmall r := by
    change (∫ ω, ((coldNativePlateauFamily M m Q).atDepth r).cellTrace R ω ∂μprob) = μsmall r
    simp_rw [coldNativePlateauFamily_cellTrace]
    rw [coldNativeCellTrace_integral,scale_eq_sub_of_mem_descendantsAtDepth R.property]
  have hnear (r : ℕ) (hr : r ≤ 2*J) : μsmall r = coldNativeMean M m (2*J-r) := by
    have he : Q.scale-(r:ℤ) = m+((2*J-r:ℕ):ℤ) := by
      change m+((2*J:ℕ):ℤ)-(r:ℤ) = _
      omega
    dsimp only [μsmall]
    rw [he]
    rfl
  have hparent : (∫ ω, (F.atDepth 0).parentTrace ω ∂μprob) = coldNativeMean M m (2*J) := by
    change (∫ ω, ((coldNativePlateauFamily M m Q).atDepth 0).parentTrace ω ∂μprob) = coldNativeMean M m (2*J)
    simp_rw [coldNativePlateauFamily_parentTrace]
    rfl
  have hG (k : ℕ) (hk : k < J) := cold_native_own_graph_cap M h hM m hθ hroot Q (2*(k+1))
    (cold_updated_lag_bounds _ hj).2 (by omega : 2*J-2*(k+1) < 2*J)
    (by have hh := (cold_updated_lag_bounds _ hj).2; omega : 2*J-2*(k+1) ≤ 126)
    (by change m+((2*J:ℕ):ℤ)-((2*(k+1):ℕ):ℤ) = m+((2*J-2*(k+1):ℕ):ℤ); omega) hmean
  exact cold_plateau_numeric_step F hJ hr4 hj hθ hθ1 hD hDn h20 hMoment
    (fun k => coldNativePlateauFamily_projectedGraph_measurable M m Q (2*(k+1))) hDroot hmax
    (coldNativePlateauFamily_recoveryIntegrable M m Q r4)
    (fun r R => (coldNativePlateauFamily_recoveryIntegrable M m Q r).cellTrace R)
    (fun k hk => (hG k hk).1) (fun k hk => (hG k hk).2) hstat hnear hparent

end ASDExplicitGamma.Cold
