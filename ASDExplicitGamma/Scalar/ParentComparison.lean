module

public import ASDExplicitGamma.Scalar.VariationalTrial
public import ASDExplicitGamma.Scalar.TrialIntegrability

/-! The complete parent energy comparison with a pure-flux cutoff error. -/

@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Response Algsuperdiff.Section3

/-- A compatible parent competitor differing from a tiled trial only in its
flux is bounded by the complete tiled energy and the exact L² error cost. -/
theorem bottom_error_top_trial_le (M : ABKModel 2) (N : ℤ)
    (σ τ : ℝ) (hσ : 0 < σ) (hτ : 0 < τ) (Q : TriadicCube 2)
    (ω : Cutoff.CutoffSample 2) (e : Vec 2)
    (Y : Vec 2 → BlockVec 2) (d : Vec 2 → Vec 2)
    (hY : MemBlockL2 (openCubeSet Q) Y) (hd : MemVectorL2 (openCubeSet Q) d)
    (hF : ScalarVariation (openCubeSet Q)
      (Y+(fun x => ((0:Vec 2),d x))-constantBlockLoad (e,0))) :
    σ⁻¹*vecDot e (matVecMul (coarseBlockMatrix (cubeSet Q)
      (Cutoff.coefficientCutoff M.nu N ω).toFun).upperLeft e) ≤
      (1+τ)*volumeAverage (openCubeSet Q) (fun x => responseFrameEnergyDensity M.nu σ
        (Cutoff.cutoff N ω x 1 0) (Y x)) +
        (1+τ⁻¹)*(σ/M.nu)*volumeAverage (openCubeSet Q) (fun x => vecNormSq (d x)) := by
  let U := openCubeSet Q
  let F : Vec 2 → BlockVec 2 := Y + fun x => ((0:Vec 2),d x)
  let f : Vec 2 → ℝ := fun x => responseFrameEnergyDensity M.nu σ
    (Cutoff.cutoff N ω x 1 0) (Y x)
  let g : Vec 2 → ℝ := fun x => vecNormSq (d x)
  let b := (1+τ⁻¹)*(σ/M.nu)
  have hmemF : MemBlockL2 U F := hY.add (scalar_bottom_load_memL2 hd)
  have hiY : IntegrableOn f U := cutoff_energy_density_integrableOn M N σ hσ Q ω Y hY
  have hiF := cutoff_energy_density_integrableOn M N σ hσ Q ω F hmemF
  have hid : IntegrableOn g U := by
    simpa only [g, vecNormSq] using integrableOn_vecDot_of_memVectorL2 hd hd
  have hib : IntegrableOn (fun x => (1+τ)*f x+b*g x) U :=
    (hiY.const_mul (1+τ)).add (hid.const_mul b)
  have hpoint (x : Vec 2) : responseFrameEnergyDensity M.nu σ (Cutoff.cutoff N ω x 1 0) (F x) ≤
      (1+τ)*f x+b*g x :=
    frame_energy_bottom_perturbation_le M.nu σ (Cutoff.cutoff N ω x 1 0) τ
      M.nu_pos hσ hτ (Y x) (d x)
  have hmono := integral_mono_ae hiF hib (Filter.Eventually.of_forall hpoint)
  have havg := mul_le_mul_of_nonneg_left hmono
    (show 0 ≤ (volume U).toReal⁻¹ by positivity)
  change volumeAverage U (fun x => responseFrameEnergyDensity M.nu σ
      (Cutoff.cutoff N ω x 1 0) (F x)) ≤ volumeAverage U (fun x => (1+τ)*f x+b*g x) at havg
  have hlinear : volumeAverage U (fun x => (1+τ)*f x+b*g x) =
      (1+τ)*volumeAverage U f+b*volumeAverage U g := by
    change volumeAverage U (((1+τ) • f)+(b • g)) = _
    have hif : IntegrableOn ((1+τ) • f) U := by
      change Integrable (fun x => (1+τ)*f x) (volume.restrict U)
      exact hiY.const_mul (1+τ)
    have hig : IntegrableOn (b • g) U := by
      change Integrable (fun x => b*g x) (volume.restrict U)
      exact hid.const_mul b
    rw [volumeAverage_add hif hig, volumeAverage_smul, volumeAverage_smul]
  exact (cutoff_top_quadratic_le_trial M N σ hσ Q ω e F hF).trans
    (havg.trans_eq hlinear)

/-- The physical top quadratic is integrable before its expectation is used. -/
theorem integrable_cutoff_top_quadratic (M : ABKModel 2) (N k : ℤ) (e : Vec 2) :
    Integrable (fun ω => vecDot e (matVecMul (coarseBlockMatrix (cubeSet (originCube 2 k))
      (Cutoff.coefficientCutoff M.nu N ω).toFun).upperLeft e)) (Cutoff.cutoffSampleLaw M).toMeasure := by
  unfold vecDot matVecMul
  exact integrable_finsetSum Finset.univ fun i _ =>
    (integrable_finsetSum Finset.univ fun j _ =>
      (integrable_cutoff_top_entry M N k i j).mul_const (e j)).const_mul (e i)

end ASDExplicitGamma.Scalar
