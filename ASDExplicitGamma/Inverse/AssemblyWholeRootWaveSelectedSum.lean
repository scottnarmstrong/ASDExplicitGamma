module

public import ASDExplicitGamma.Inverse.AssemblyWholeRootWaveSelectedSeries

/-! Sum the sharp selected whole-root wave payments over root layers. -/

@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian
open scoped ENNReal
noncomputable section

/-- The closed all-layer budget after sharp selected-height extraction. -/
def assemblyWholeRootWaveSelectedSeriesBudget (γ p D : ℝ) (H0 : ℕ) : ℝ :=
  let z := selectedFirstClock H0
  let C := (12:ℝ)^(1/p:ℝ)*(3:ℝ)^(4*γ*(z+4)+2*γ)
  let E := (3:ℝ)^(22*γ)
  let T0 := selectedWaveExactTail γ p H0 (0:Fin 2)
  let T1 := selectedWaveExactTail γ p H0 (1:Fin 2)
  480*γ*(3:ℝ)^(2*γ*D)*
    ((C*(z+5+p*(D+1))+E*(T1+(6+2*p*(D+1))*T0))*assemblyWaveGeom0 γ+
      (2*C+2*E*T0)*assemblyWaveGeom1 γ)

/-- The geometric majorant for a sharp selected wave layer. -/
def assemblyWholeRootWaveSelectedLayerMajorant
    (γ p D : ℝ) (H0 i : ℕ) : ℝ :=
  let z := selectedFirstClock H0
  let C := (12:ℝ)^(1/p:ℝ)*(3:ℝ)^(4*γ*(z+4)+2*γ)
  let E := (3:ℝ)^(22*γ)
  let T0 := selectedWaveExactTail γ p H0 (0:Fin 2)
  let T1 := selectedWaveExactTail γ p H0 (1:Fin 2)
  let q := assemblyWaveDecayRatio γ
  480*γ*(3:ℝ)^(2*γ*D)*
    ((C*(z+5+p*(D+1))+E*(T1+(6+2*p*(D+1))*T0))*q^(i+1)+
      (2*C+2*E*T0)*((i+1:ℕ):ℝ)*q^(i+1))

private theorem assembly_selected_sqrt_layer_decay (i : ℕ) :
    Real.sqrt (bankLayerWeight i) ≤ 3*(3:ℝ)^(-((i+1:ℕ):ℝ)/2) := by
  let k : ℝ := (i+1:ℕ)
  have hkpow : (1/3:ℝ)^(i+1)=(3:ℝ)^(-k) := by
    dsimp only [k]
    rw [show (1/3:ℝ)=(3:ℝ)^((-1:ℝ)) by norm_num,
      ← Real.rpow_natCast ((3:ℝ)^((-1:ℝ))) (i+1),
      ← Real.rpow_mul (by norm_num : (0:ℝ)≤3)]
    congr 1
    ring
  have hsq : ((3:ℝ)^(-k/2))^2=(3:ℝ)^(-k) := by
    rw [← Real.rpow_natCast ((3:ℝ)^(-k/2)) 2,
      ← Real.rpow_mul (by norm_num : (0:ℝ)≤3)]
    congr 1
    ring
  have hA : 0 ≤ 3*(3:ℝ)^(-k/2) := by positivity
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity,?_⟩
  calc
    bankLayerWeight i ≤ 8*(1/3:ℝ)^(i+1) := layer_weight_le_eight i
    _ = 8*(3:ℝ)^(-k) := by rw [hkpow]
    _ ≤ 9*(3:ℝ)^(-k) := by
      exact mul_le_mul_of_nonneg_right (by norm_num)
        (Real.rpow_nonneg (by norm_num) _)
    _ = (3*(3:ℝ)^(-k/2))^2 := by rw [mul_pow,hsq]; norm_num

private theorem assembly_selected_depth_le (i : ℕ) :
    localizationProfileDepth (i+1) ≤ 2*(i+1) := by
  unfold localizationProfileDepth
  omega

private theorem assembly_selected_tail_nonneg
    (γ p : ℝ) (H0 : ℕ) (hH0 : 333 ≤ H0) (j : Fin 2) :
    0 ≤ selectedWaveExactTail γ p H0 j := by
  have hz : 0 ≤ selectedFirstClock H0 := by
    unfold selectedFirstClock
    have hh : (333:ℝ) ≤ (H0:ℝ) := by exact_mod_cast hH0
    linarith
  unfold selectedWaveExactTail
  apply tsum_nonneg
  intro n
  have hn : 0 ≤ (n:ℝ) := Nat.cast_nonneg n
  have hclock : 0 ≤ selectedFirstClock H0+(n:ℝ) := by linarith
  unfold selectedTailProbability
  positivity

/-- The closed selected wave series budget is nonnegative throughout the
parameter range. -/
theorem assembly_whole_root_wave_selected_series_budget_nonneg
    (γ p D : ℝ) (hγ : γ ≤ gammaZero) (hγ0 : 0 ≤ γ) (hp : 2 ≤ p)
    (H0 : ℕ) (hH0 : 333 ≤ H0) (hD : 0 ≤ D) :
    0 ≤ assemblyWholeRootWaveSelectedSeriesBudget γ p D H0 := by
  let z := selectedFirstClock H0
  let T0 := selectedWaveExactTail γ p H0 (0:Fin 2)
  let T1 := selectedWaveExactTail γ p H0 (1:Fin 2)
  have hz : 0 ≤ z := by
    dsimp only [z,selectedFirstClock]
    have hh : (333:ℝ) ≤ H0 := by exact_mod_cast hH0
    linarith
  have hT0 : 0 ≤ T0 := by
    dsimp only [T0]
    exact assembly_selected_tail_nonneg γ p H0 hH0 0
  have hT1 : 0 ≤ T1 := by
    dsimp only [T1]
    exact assembly_selected_tail_nonneg γ p H0 hH0 1
  have hq0 : 0 ≤ assemblyWaveDecayRatio γ :=
    (assembly_wave_decay_ratio_pos γ).le
  have hq1 : assemblyWaveDecayRatio γ < 1 :=
    assembly_wave_decay_ratio_lt_one γ hγ
  have hg0 : 0 ≤ assemblyWaveGeom0 γ := by
    unfold assemblyWaveGeom0
    exact div_nonneg hq0 (sub_nonneg.mpr hq1.le)
  have hg1 : 0 ≤ assemblyWaveGeom1 γ := by
    unfold assemblyWaveGeom1
    exact div_nonneg hq0 (sq_nonneg _)
  have hD1 : 0 ≤ D+1 := by linarith
  have hp0 : 0 ≤ p := by linarith only [hp]
  unfold assemblyWholeRootWaveSelectedSeriesBudget
  dsimp only [z,T0,T1]
  positivity

private theorem assembly_selected_wave_layer_scale_le_majorant
    (γ p D : ℝ) (hγ : γ ≤ gammaZero) (hγ0 : 0 ≤ γ) (hp : 2 ≤ p)
    (H0 : ℕ) (hH0 : 333 ≤ H0) (hD : 0 ≤ D) (i : ℕ) :
    assemblyWholeRootWaveSelectedLayerBudget γ p D H0 i ≤
      assemblyWholeRootWaveSelectedLayerMajorant γ p D H0 i := by
  let z := selectedFirstClock H0
  let d : ℝ := localizationProfileDepth (i+1)
  let m : ℝ := ((i+1:ℕ):ℝ)
  let C := (12:ℝ)^(1/p:ℝ)*(3:ℝ)^(4*γ*(z+4)+2*γ)
  let E := (3:ℝ)^(22*γ)
  let T0 := selectedWaveExactTail γ p H0 (0:Fin 2)
  let T1 := selectedWaveExactTail γ p H0 (1:Fin 2)
  let q := assemblyWaveDecayRatio γ
  let s := Real.sqrt (bankLayerWeight i)*(3:ℝ)^(4*γ*d)
  have hz0 : 0 ≤ z := by
    dsimp only [z,selectedFirstClock]
    have hh : (333:ℝ) ≤ H0 := by exact_mod_cast hH0
    linarith
  have hd0 : 0 ≤ d := by dsimp only [d]; positivity
  have hm0 : 0 ≤ m := by dsimp only [m]; positivity
  have hdepth : d ≤ 2*m := by
    dsimp only [d,m]
    exact_mod_cast (assembly_selected_depth_le i)
  have hD1 : 0 ≤ D+1 := by linarith
  have hp0 : 0 ≤ p := by linarith only [hp]
  have hpoly0 : 0 ≤ z+5+d+p*(D+1) := by positivity
  have hpolyTail0 : 0 ≤ d+6+2*p*(D+1) := by positivity
  have hT0 : 0 ≤ T0 := by dsimp only [T0]; exact assembly_selected_tail_nonneg γ p H0 hH0 0
  have hT1 : 0 ≤ T1 := by dsimp only [T1]; exact assembly_selected_tail_nonneg γ p H0 hH0 1
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hE : 0 ≤ E := by dsimp only [E]; positivity
  have hs : 0 ≤ s := by dsimp only [s]; positivity
  have hratio0 : 0 < q := by dsimp only [q]; exact assembly_wave_decay_ratio_pos γ
  have hratio1 : q < 1 := by dsimp only [q]; exact assembly_wave_decay_ratio_lt_one γ hγ
  have hgeom := assembly_wave_geometric_sums γ hγ
  have hsqrt := assembly_selected_sqrt_layer_decay i
  have hdepthPow : (3:ℝ)^(4*γ*d) ≤ (3:ℝ)^(8*γ*m) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤3) (by
      calc
        4*γ*d ≤ 4*γ*(2*m) := mul_le_mul_of_nonneg_left hdepth (by positivity)
        _ = 8*γ*m := by ring)
  have hdecay : s ≤ 3*q^(i+1) := by
    calc
      _ ≤ (3*(3:ℝ)^(-m/2))*(3:ℝ)^(8*γ*m) :=
        mul_le_mul hsqrt hdepthPow (by positivity) (by positivity)
      _ = 3*q^(i+1) := by
        have hq : q^(i+1)=(3:ℝ)^((8*γ-1/2)*m) := by
          dsimp only [q,assemblyWaveDecayRatio,m]
          rw [← Real.rpow_natCast,← Real.rpow_mul (by norm_num : (0:ℝ)≤3)]
        calc
          _ = 3*((3:ℝ)^(-m/2)*(3:ℝ)^(8*γ*m)) := by ring
          _ = 3*(3:ℝ)^(-m/2+8*γ*m) := by
            congr 1
            rw [← Real.rpow_add (by norm_num : (0:ℝ)<3)]
          _ = 3*(3:ℝ)^((8*γ-1/2)*m) := by congr 2; ring
          _ = 3*q^(i+1) := by rw [← hq]
  have hpoly : z+5+d+p*(D+1) ≤ z+5+2*m+p*(D+1) := by linarith
  have htailPoly : d+6+2*p*(D+1) ≤ 2*m+6+2*p*(D+1) := by linarith
  have hpolyUpper0 : 0 ≤ z+5+2*m+p*(D+1) := by positivity
  have htailUpper0 : 0 ≤ 2*m+6+2*p*(D+1) := by positivity
  have hbase0 : 0 ≤ 160*γ*(3:ℝ)^(2*γ*D) := by positivity
  have hpowC : (3:ℝ)^(2*γ*D+4*γ*(z+4+d)+2*γ) =
      (3:ℝ)^(2*γ*D)*(3:ℝ)^(4*γ*(z+4)+2*γ)*(3:ℝ)^(4*γ*d) := by
    rw [show 2*γ*D+4*γ*(z+4+d)+2*γ =
      (2*γ*D)+(4*γ*(z+4)+2*γ)+(4*γ*d) by ring,
      Real.rpow_add (by norm_num : (0:ℝ)<3),Real.rpow_add (by norm_num : (0:ℝ)<3)]
  have hpowT : (3:ℝ)^(2*γ*D+4*γ*d+22*γ) =
      (3:ℝ)^(2*γ*D)*(3:ℝ)^(22*γ)*(3:ℝ)^(4*γ*d) := by
    rw [show 2*γ*D+4*γ*d+22*γ=(2*γ*D)+(22*γ)+(4*γ*d) by ring,
      Real.rpow_add (by norm_num : (0:ℝ)<3),Real.rpow_add (by norm_num : (0:ℝ)<3)]
  have hrepr : assemblyWholeRootWaveSelectedLayerBudget γ p D H0 i =
      160*γ*(3:ℝ)^(2*γ*D)*
        (C*(z+5+d+p*(D+1))*s+E*(T1+(d+6+2*p*(D+1))*T0)*s) := by
    unfold assemblyWholeRootWaveSelectedLayerBudget assemblyWholeRootWaveTailScale
      assemblyWholeRootWaveCandidateBound
    rw [hpowC,hpowT]
    dsimp only [C,E,T0,T1,z,d,s]
    ring
  have hcand : C*(z+5+d+p*(D+1))*s ≤
      C*(z+5+2*m+p*(D+1))*(3*q^(i+1)) := by
    calc
      _ ≤ C*(z+5+2*m+p*(D+1))*s :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hpoly hC) hs
      _ ≤ _ := mul_le_mul_of_nonneg_left hdecay
        (mul_nonneg hC hpolyUpper0)
  have htail : E*(T1+(d+6+2*p*(D+1))*T0)*s ≤
      E*(T1+(2*m+6+2*p*(D+1))*T0)*(3*q^(i+1)) := by
    have hinner : T1+(d+6+2*p*(D+1))*T0 ≤
        T1+(2*m+6+2*p*(D+1))*T0 := by
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_right htailPoly hT0)
    have hinner0 : 0 ≤ T1+(2*m+6+2*p*(D+1))*T0 := by positivity
    calc
      _ ≤ E*(T1+(2*m+6+2*p*(D+1))*T0)*s :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hinner hE) hs
      _ ≤ _ := mul_le_mul_of_nonneg_left hdecay (mul_nonneg hE hinner0)
  have hmain := add_le_add hcand htail
  have hmain' := hmain
  dsimp only [z,C,E,T0,T1,q,m] at hmain'
  rw [hrepr]
  unfold assemblyWholeRootWaveSelectedLayerMajorant
  dsimp only [z,C,E,T0,T1,q]
  calc
    _ ≤ 160*γ*(3:ℝ)^(2*γ*D)*
        (C*(z+5+2*m+p*(D+1))*(3*q^(i+1))+
          E*(T1+(2*m+6+2*p*(D+1))*T0)*(3*q^(i+1))) :=
      mul_le_mul_of_nonneg_left hmain' hbase0
    _ = _ := by
      dsimp only [z,C,E,T0,T1,q,m]
      push_cast
      ring_nf

/-- The sharp selected whole-root wave layer series has a closed
all-order budget, with the entrance-height coefficient paid only once. -/
theorem assembly_trace_wave_selected_series_Lp
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero) (Q : TriadicCube 2) (p : ℝ) (hp : 2 ≤ p)
    (hpast : ∀ n : ℤ,
      n ≤ Q.scale-342-12*orderBand p → nativeInductionState M h n)
    (N : ℤ) (hN : Q.scale-1 ≤ N) (weights : ℤ → ℝ)
    (hw : ∀ n ∈ Finset.Ioc
      (protectedOldLabel Q.scale (orderBand p)) N,
      0 ≤ weights n ∧ weights n ≤ 1) :
    (∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      Summable (fun i => ‖assemblyTraceWaveLayer M Q (orderBand p) p N weights i ω‖)) ∧
    eLpNorm (fun ω => ∑' i,
      |assemblyTraceWaveLayer M Q (orderBand p) p N weights i ω|)
      (ENNReal.ofReal p) (Cutoff.cutoffSampleLaw M).toMeasure ≤
      ENNReal.ofReal (assemblyWholeRootWaveSelectedSeriesBudget M.gamma p
        ((N-Q.scale+1:ℤ):ℝ) (heightEntrance (orderBand p))) := by
  let H0 := heightEntrance (orderBand p)
  let D : ℝ := ((N-Q.scale+1:ℤ):ℝ)
  let F := fun i ω => |assemblyTraceWaveLayer M Q (orderBand p) p N weights i ω|
  have hH0 : 333 ≤ H0 := by unfold H0 heightEntrance; omega
  have hD : 0 ≤ D := by dsimp only [D]; exact_mod_cast (by omega : 0 ≤ N-Q.scale+1)
  have hγ0 : 0 ≤ M.gamma := M.shellPrefix.gamma_pos.le
  have hgeom := assembly_wave_geometric_sums M.gamma hγ
  let majorant := assemblyWholeRootWaveSelectedLayerMajorant M.gamma p D H0
  let budget := assemblyWholeRootWaveSelectedSeriesBudget M.gamma p D H0
  have hhas : HasSum majorant budget := by
    let z := selectedFirstClock H0
    have hz : 0 ≤ z := by
      dsimp only [z,selectedFirstClock]
      have hh : (333:ℝ) ≤ H0 := by exact_mod_cast hH0
      linarith
    let C := (12:ℝ)^(1/p:ℝ)*(3:ℝ)^(4*M.gamma*(z+4)+2*M.gamma)
    let E := (3:ℝ)^(22*M.gamma)
    let T0 := selectedWaveExactTail M.gamma p H0 (0:Fin 2)
    let T1 := selectedWaveExactTail M.gamma p H0 (1:Fin 2)
    let u := C*(z+5+p*(D+1))+E*(T1+(6+2*p*(D+1))*T0)
    let v := 2*C+2*E*T0
    let a := 480*M.gamma*(3:ℝ)^(2*M.gamma*D)
    have hs0 := hgeom.1.mul_left u
    have hs1 := hgeom.2.mul_left v
    have hs := (hs0.add hs1).mul_left a
    convert hs using 1
    · funext i
      dsimp only [majorant,assemblyWholeRootWaveSelectedLayerMajorant,
        u,v,a,C,E,T0,T1,z]
      ring_nf
    · dsimp only [budget,assemblyWholeRootWaveSelectedSeriesBudget,u,v,a,C,E,T0,T1,z]
  have hbound (i : ℕ) : eLpNorm (F i) (ENNReal.ofReal p)
      (Cutoff.cutoffSampleLaw M).toMeasure ≤ ENNReal.ofReal (majorant i) := by
    have hmeas := assembly_trace_wave_layer_measurable M Q (orderBand p) p N weights i
    have hnorm := assembly_trace_wave_selected_layer_Lp M h hM hγ Q p hp hpast N hN
      weights hw i
    have hscale := assembly_selected_wave_layer_scale_le_majorant M.gamma p D hγ hγ0 hp
      H0 hH0 hD i
    have hEq : eLpNorm (F i) (ENNReal.ofReal p) (Cutoff.cutoffSampleLaw M).toMeasure =
        eLpNorm (assemblyTraceWaveLayer M Q (orderBand p) p N weights i)
          (ENNReal.ofReal p) (Cutoff.cutoffSampleLaw M).toMeasure := by
      simpa only [F,Real.norm_eq_abs] using
        eLpNorm_norm (assemblyTraceWaveLayer M Q (orderBand p) p N weights i)
          hmeas.aestronglyMeasurable
    rw [hEq]
    exact hnorm.trans (ENNReal.ofReal_le_ofReal hscale)
  have hseries := countable_density_series_Lp
    (Cutoff.cutoffSampleLaw M).toMeasure (ENNReal.ofReal p)
    (ENNReal.one_le_ofReal.mpr (by linarith only [hp])) F
    (fun i => (assembly_trace_wave_layer_measurable M Q (orderBand p) p
      N weights i).abs)
    majorant (fun i => by
      have hT0 := assembly_selected_tail_nonneg M.gamma p H0 hH0 (0:Fin 2)
      have hT1 := assembly_selected_tail_nonneg M.gamma p H0 hH0 (1:Fin 2)
      have hratio : 0 ≤ assemblyWaveDecayRatio M.gamma :=
        (assembly_wave_decay_ratio_pos M.gamma).le
      have hD1 : 0 ≤ D+1 := by linarith
      have hp0 : 0 ≤ p := by linarith only [hp]
      have hz : 0 ≤ selectedFirstClock H0 := by
        unfold selectedFirstClock
        have hh : (333:ℝ) ≤ H0 := by exact_mod_cast hH0
        linarith
      unfold majorant assemblyWholeRootWaveSelectedLayerMajorant
      positivity)
    budget hhas hbound
  simpa only [F,D,H0,majorant,budget,Real.norm_eq_abs,abs_abs] using hseries

end
end ASDExplicitGamma.Inverse
