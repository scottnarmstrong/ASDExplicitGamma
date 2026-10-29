module

public import ASDExplicitGamma.Inverse.AssemblyAffineSelectedTail
public import ASDExplicitGamma.Inverse.AssemblyWaveSeries

/-! Direct whole-root wave moments at the selected full stopping height. -/

@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Model
open scoped ENNReal
noncomputable section

/-- Uniform deterministic bound for the twelve source candidate heights. -/
def assemblyWholeRootWaveCandidateBound (γ p D : ℝ) (H0 i : ℕ) : ℝ :=
  160*γ*Real.sqrt (bankLayerWeight i)*
    (selectedFirstClock H0+5+(localizationProfileDepth (i+1):ℝ)+p*(D+1))*
      (3:ℝ)^(2*γ*D+4*γ*(selectedFirstClock H0+4+
        (localizationProfileDepth (i+1):ℝ))+2*γ)

/-- The common tail scale before its linear-height and constant payments. -/
def assemblyWholeRootWaveTailScale (γ D : ℝ) (i : ℕ) : ℝ :=
  160*γ*Real.sqrt (bankLayerWeight i)*
    (3:ℝ)^(2*γ*D+4*γ*(localizationProfileDepth (i+1):ℝ)+22*γ)

/-- The sharp selected-height wave bound for one root layer. -/
def assemblyWholeRootWaveSelectedLayerBudget
    (γ p D : ℝ) (H0 i : ℕ) : ℝ :=
  (12:ℝ)^(1/p:ℝ)*assemblyWholeRootWaveCandidateBound γ p D H0 i+
  assemblyWholeRootWaveTailScale γ D i*
      selectedWaveExactTail γ p H0 (1:Fin 2)+
    (assemblyWholeRootWaveTailScale γ D i*
      (localizationProfileDepth (i+1)+6+2*p*(D+1)))*
        selectedWaveExactTail γ p H0 (0:Fin 2)

/-- At a bounded selected candidate, direct moments use the root gap and
the terminal depth only. -/
theorem assembly_trace_wave_candidate_height_Lp
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (Q : TriadicCube 2) (k : ℕ) (p : ℝ) (hp : 2 ≤ p)
    (hpast : ∀ n : ℤ,
      n ≤ Q.scale-342-12*k → nativeInductionState M h n)
    (N : ℤ) (hN : Q.scale-1 ≤ N) (weights : ℤ → ℝ)
    (hw : ∀ n ∈ Finset.Ioc (protectedOldLabel Q.scale k) N,
      0 ≤ weights n ∧ weights n ≤ 1)
    (i H : ℕ) (hHlo : heightEntrance k ≤ H) (hHhi : H ≤ heightEntrance k+11) :
    eLpNorm (assemblyTraceWaveAtHeight M Q k (H+5) N weights i)
      (ENNReal.ofReal p) (Cutoff.cutoffSampleLaw M).toMeasure ≤
      ENNReal.ofReal (assemblyWholeRootWaveCandidateBound M.gamma p
        ((N-Q.scale+1:ℤ):ℝ) (heightEntrance k) i) := by
  let H0 := heightEntrance k
  let D : ℝ := ((N-Q.scale+1:ℤ):ℝ)
  let z := selectedFirstClock H0
  let d : ℝ := localizationProfileDepth (i+1)
  let x := localizationResetAbscissa (H0+5-38) (H+5-(H0+5)) i
  have hbase : 377 ≤ H0+5 := by unfold H0 heightEntrance; omega
  have hD : 0 ≤ D := by
    dsimp only [D]
    exact_mod_cast (show 0 ≤ N-Q.scale+1 by omega)
  have hbaseH : H0+5 ≤ H+5 := by omega
  have hxEq := physical_height_abscissa_eq (H0+5) (by omega) (H+5) hbaseH i
  have hxLe : (x:ℝ) ≤ z+4+d := by
    rw [show x=localizationResetAbscissa (H0+5-38) (H+5-(H0+5)) i by rfl,
      hxEq]
    have hHr : (H:ℝ) ≤ (H0:ℝ)+11 := by exact_mod_cast hHhi
    unfold z selectedFirstClock
    dsimp only [H0,d]
    push_cast
    linarith only [hHr]
  have hDet := assembly_trace_wave_at_height_Lp M h hM Q k (H+5)
    (by omega) hpast N hN weights hw i p hp
  have hγ : 0 ≤ M.gamma := M.shellPrefix.gamma_pos.le
  have hcoef : 0 ≤ 160*M.gamma*Real.sqrt (bankLayerWeight i) := by positivity
  have hpoly : x+1+p*(D+1) ≤
      selectedFirstClock H0+5+d+p*(D+1) := by
    have hx := hxLe
    dsimp only [z,d] at hx
    linarith only [hx]
  have hexp : 2*M.gamma*D+4*M.gamma*x+2*M.gamma ≤
      2*M.gamma*D+4*M.gamma*(selectedFirstClock H0+4+d)+2*M.gamma := by
    have hxγ : (4*M.gamma)*(x:ℝ) ≤
        (4*M.gamma)*(z+4+d) :=
      mul_le_mul_of_nonneg_left hxLe (by positivity)
    dsimp only [z] at hxγ
    calc
      _ = 2*M.gamma*D+(4*M.gamma)*(x:ℝ)+2*M.gamma := by ring
      _ ≤ 2*M.gamma*D+(4*M.gamma)*(z+4+d)+2*M.gamma := by linarith only [hxγ]
      _ = _ := by ring
  have hpow := Real.rpow_le_rpow_of_exponent_le
    (by norm_num : (1:ℝ)≤3) hexp
  have hreal :
      160*M.gamma*Real.sqrt (bankLayerWeight i)*(x+1+p*(D+1))*
          (3:ℝ)^(2*M.gamma*D+4*M.gamma*x+2*M.gamma) ≤
        assemblyWholeRootWaveCandidateBound M.gamma p D H0 i := by
    unfold assemblyWholeRootWaveCandidateBound
    calc
      _ ≤ 160*M.gamma*Real.sqrt (bankLayerWeight i)*
          (selectedFirstClock H0+5+d+p*(D+1))*
          (3:ℝ)^(2*M.gamma*D+4*M.gamma*x+2*M.gamma) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hpoly hcoef) (by positivity)
      _ ≤ _ := by
        have hz0 : 0 ≤ selectedFirstClock H0 := by
          unfold selectedFirstClock
          have h26 : (26:ℝ) ≤ (H0:ℝ) := by
            exact_mod_cast (show 26 ≤ H0 by unfold H0 heightEntrance; omega)
          linarith
        have hd0 : 0 ≤ d := by dsimp only [d]; positivity
        have hp0 : 0 ≤ p := by linarith only [hp]
        have hpoly0 : 0 ≤ selectedFirstClock H0+5+d+p*(D+1) := by
          have hD1 : 0 ≤ D+1 := by linarith
          positivity
        exact mul_le_mul_of_nonneg_left hpow (mul_nonneg hcoef hpoly0)
  exact hDet.trans (ENNReal.ofReal_le_ofReal hreal)

/-- The source's full selected tail remains correlated with the wave and keeps
the coefficient of the terminal-depth term separate from the first-height
moment. -/
theorem assembly_trace_wave_tail_atom_Lp
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (Q : TriadicCube 2) (k : ℕ)
    (p : ℝ) (hp : 2 ≤ p)
    (hpast : ∀ n : ℤ,
      n ≤ Q.scale-342-12*k → nativeInductionState M h n)
    (N : ℤ) (hN : Q.scale-1 ≤ N) (weights : ℤ → ℝ)
    (hw : ∀ n ∈ Finset.Ioc (protectedOldLabel Q.scale k) N,
      0 ≤ weights n ∧ weights n ≤ 1)
    (i n : ℕ) :
    let H0 := heightEntrance k
    let D : ℝ := ((N-Q.scale+1:ℤ):ℝ)
    let z := selectedFirstClock H0
    let d : ℝ := localizationProfileDepth (i+1)
    let A := assemblyWholeRootWaveTailScale M.gamma D i
    let B := A*(d+6+2*p*(D+1))
    eLpNorm (assemblyTraceWaveAtHeight M Q k (heightEntrance k+17+n)
      N weights i) (ENNReal.ofReal (2*p)) (Cutoff.cutoffSampleLaw M).toMeasure ≤
      ENNReal.ofReal ((A*(z+(n:ℝ))+B)*(3:ℝ)^(4*M.gamma*(z+(n:ℝ)))) := by
  let H0 := heightEntrance k
  let D : ℝ := ((N-Q.scale+1:ℤ):ℝ)
  let z := selectedFirstClock H0
  let d : ℝ := localizationProfileDepth (i+1)
  let x := localizationResetAbscissa (H0+5-38) (H0+17+n-(H0+5)) i
  let A := assemblyWholeRootWaveTailScale M.gamma D i
  let B := A*(d+6+2*p*(D+1))
  have hbase : 38 ≤ H0+5 := by unfold H0 heightEntrance; omega
  have hAbscissa := physical_height_abscissa_eq (H0+5) hbase
    (H0+17+n) (by omega) i
  have hx : (x:ℝ)=z+(n:ℝ)+5+d := by
    rw [show x=localizationResetAbscissa (H0+5-38)
      (H0+17+n-(H0+5)) i by rfl,hAbscissa]
    unfold z selectedFirstClock
    dsimp only [H0,d]
    push_cast
    ring
  have hDet := assembly_trace_wave_at_height_Lp M h hM Q k
    (H0+17+n) (by omega) hpast N hN weights hw i (2*p) (by linarith only [hp])
  change eLpNorm (assemblyTraceWaveAtHeight M Q k (H0+17+n) N weights i)
      (ENNReal.ofReal (2*p)) (Cutoff.cutoffSampleLaw M).toMeasure ≤
    ENNReal.ofReal (160*M.gamma*Real.sqrt (bankLayerWeight i)*
      (x+1+2*p*(D+1))*(3:ℝ)^(2*M.gamma*D+4*M.gamma*x+2*M.gamma)) at hDet
  have hexp : 2*M.gamma*D+4*M.gamma*x+2*M.gamma =
      4*M.gamma*(z+(n:ℝ))+(2*M.gamma*D+4*M.gamma*d+22*M.gamma) := by
    rw [hx]
    ring
  have hpow : (3:ℝ)^(2*M.gamma*D+4*M.gamma*x+2*M.gamma) =
      (3:ℝ)^(4*M.gamma*(z+(n:ℝ)))*
        (3:ℝ)^(2*M.gamma*D+4*M.gamma*d+22*M.gamma) := by
    rw [hexp,Real.rpow_add (by norm_num : (0:ℝ)<3)]
  have hreal : 160*M.gamma*Real.sqrt (bankLayerWeight i)*
      (x+1+2*p*(D+1))*(3:ℝ)^(2*M.gamma*D+4*M.gamma*x+2*M.gamma) =
      (A*(z+(n:ℝ))+B)*(3:ℝ)^(4*M.gamma*(z+(n:ℝ))) := by
    rw [hpow,hx]
    dsimp only [A,B,assemblyWholeRootWaveTailScale]
    ring
  rw [hreal] at hDet
  exact hDet

end
end ASDExplicitGamma.Inverse
