module
public import ASDExplicitGamma.Numerics.Native.Gap137Taylor
public import ASDExplicitGamma.Numerics.Native.MatrixReplay
/-! Real exponential enclosure for the complete configured gap-137 system. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native
open Matrix

theorem nativeGap137Old_source : nativeOld 137 = nativeGap137Old := by
  unfold nativeOld
  rw [nativeGap137Raw_formula]
  exact nativeGap137Old_formula

theorem nativeGap137Exp_bound : ∀ i : Fin 21,
    (NormedSpace.exp (nativeSystemMatrix nativeGap137System) *ᵥ nativeVectorReal nativeGap137System.v) i ≤ nativeVectorReal nativeGap137Result i := by
  have hd := nativeGap137Domain
  have hr (i : Fin 21) : nativeGap137System.diag.getD i.val 0+nativeGap137System.subdiag.getD i.val 0+nativeGap137System.force.getD i.val 0 ≤ 6 := by
    rw [add_comm (nativeGap137System.diag.getD i.val 0) (nativeGap137System.subdiag.getD i.val 0)]
    exact hd.2.2.2 i
  have h := nativeTaylor_replay_sound nativeGap137System (by decide +kernel)
    (fun i => (hd.2.2.1 i).1) (fun i => (hd.2.1 i).1)
    (fun i => (hd.2.2.1 i).2.1) hr hd.1
  rw [nativeGap137Taylor160] at h
  simpa only [nativeGap137Result_formula] using h

end ASDExplicitGamma.Numerics.Native
