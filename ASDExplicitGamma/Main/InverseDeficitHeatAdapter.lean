module

public import ASDExplicitGamma.Main.InverseDeficitInitial
public import ASDExplicitGamma.Main.Q3HeatIdentity
public import ASDExplicitGamma.Main.InverseDeficitODE

/-! Apply the absolute inverse branch to the actual OLD-frame q3 heat path. -/

@[expose] public section

namespace ASDExplicitGamma.Main

open Homogenization MeasureTheory Set ASDExplicitGamma.Gaussian Algsuperdiff.Section3

/-- The q3 heat identity and true-frame initial value reduce the source
absolute-branch conclusion to the a.e. lower generator row for the actual
inverse-observable covariance trace. -/
theorem main_inverse_heat_absolute_branch_of_generator_bound
    (n : ℤ) (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (m : ℤ)
    (v t : ℝ) (hmu : 0 < mainInverseMuMinusSource v) (hv : 0 ≤ v)
    (ht : t ∈ Icc (0 : ℝ) 1)
    (hgen : ∀ᵐ s : ℝ, s ∈ Icc (0 : ℝ) 1 →
      -mainKappa (mainInverseMuMinusSource v) * mainInverseHeatAverage n M m s -
        mainKappa (mainInverseMuMinusSource v) * mainRho ≤
      (1 / 2 : ℝ) * modelHeatTraceAverage
        (closure (cubeSet (originCube 2 n))) M m
        (mainInverseObservable n M.nu (Annealed.sigmaBar M m : ℝ))
        (fun j => mainCubeH3Value n
          (q3ModelAmplitude M h (m + 1)) (q3ModelLength (m + 1))
          (mainCubeQ3Directions n (q3ModelAmplitude M h (m + 1))
            (q3ModelLength (m + 1)) j)) s) :
    -v * (mainInverseHeatAverage n M m t - 2) ≤
      mainInverseAbs v (mainInverseMuMinusSource v) t := by
  let b := q3ModelAmplitude M h (m + 1)
  let L := q3ModelLength (m + 1)
  let K := closure (cubeSet (originCube 2 n))
  let H := fun j => mainCubeH3Value n b L (mainCubeQ3Directions n b L j)
  let d := fun s => (1 / 2 : ℝ) * modelHeatTraceAverage K M m
    (mainInverseObservable n M.nu (Annealed.sigmaBar M m : ℝ)) H s
  let u := mainInverseHeatAverage n M m
  have hHeat := main_actual_q3_heat_identities n M h hM m
  have hPanel : mainHeatPanelIdentity u d := by
    change mainHeatPanelIdentity (modelTraceHeatAverage n M m) _ ∧
      mainHeatPanelIdentity u d at hHeat
    exact hHeat.2
  have hderiv : ∀ᵐ s : ℝ, s ∈ Icc (0 : ℝ) 1 →
      -mainKappa (mainInverseMuMinusSource v) * u s -
        mainKappa (mainInverseMuMinusSource v) * mainRho ≤ deriv u s := by
    filter_upwards [hPanel.2.1, hgen] with s hs hg hs01
    have hd : deriv u s = d s := (hs hs01).deriv
    rw [hd]
    simpa [u, d, K, H, b, L] using hg hs01
  have hinit : 2 ≤ u 0 := by
    simpa [u] using main_inverse_heat_initial_ge_two M m n
  exact main_inverse_deficit_absolute_branch_source
    hmu hv hPanel.1 hinit hderiv ht

end ASDExplicitGamma.Main
