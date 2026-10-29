module
public import ASDExplicitGamma.Numerics.Native.Heat136Passes
public import ASDExplicitGamma.Numerics.Native.HeatComposition

@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

theorem nativeHeat136Y00_formula : nativeHeat136Y00 = nativeHeat136Frames.y := by
  decide +kernel

theorem nativeHeat136All48 : nativeHeatPasses nativeGap137Old nativeHeat136Frames nativeHeat136Coef nativeHeat136Fixed nativeHeat136Base 48 nativeHeat136Frames.y = nativeHeat136Y48 := by
  rw [← nativeHeat136Y00_formula]
  have h4 : nativeHeatPasses nativeGap137Old nativeHeat136Frames nativeHeat136Coef nativeHeat136Fixed nativeHeat136Base 4 nativeHeat136Y00 = nativeHeat136Y04 := nativeHeat136Pass04
  have h8 : nativeHeatPasses nativeGap137Old nativeHeat136Frames nativeHeat136Coef nativeHeat136Fixed nativeHeat136Base 8 nativeHeat136Y00 = nativeHeat136Y08 := by
    rw [show (8 : ℕ) = 4+4 from rfl,nativeHeatPasses_add,h4,nativeHeat136Pass08]
  have h12 : nativeHeatPasses nativeGap137Old nativeHeat136Frames nativeHeat136Coef nativeHeat136Fixed nativeHeat136Base 12 nativeHeat136Y00 = nativeHeat136Y12 := by
    rw [show (12 : ℕ) = 8+4 from rfl,nativeHeatPasses_add,h8,nativeHeat136Pass12]
  have h16 : nativeHeatPasses nativeGap137Old nativeHeat136Frames nativeHeat136Coef nativeHeat136Fixed nativeHeat136Base 16 nativeHeat136Y00 = nativeHeat136Y16 := by
    rw [show (16 : ℕ) = 12+4 from rfl,nativeHeatPasses_add,h12,nativeHeat136Pass16]
  have h20 : nativeHeatPasses nativeGap137Old nativeHeat136Frames nativeHeat136Coef nativeHeat136Fixed nativeHeat136Base 20 nativeHeat136Y00 = nativeHeat136Y20 := by
    rw [show (20 : ℕ) = 16+4 from rfl,nativeHeatPasses_add,h16,nativeHeat136Pass20]
  have h24 : nativeHeatPasses nativeGap137Old nativeHeat136Frames nativeHeat136Coef nativeHeat136Fixed nativeHeat136Base 24 nativeHeat136Y00 = nativeHeat136Y24 := by
    rw [show (24 : ℕ) = 20+4 from rfl,nativeHeatPasses_add,h20,nativeHeat136Pass24]
  have h28 : nativeHeatPasses nativeGap137Old nativeHeat136Frames nativeHeat136Coef nativeHeat136Fixed nativeHeat136Base 28 nativeHeat136Y00 = nativeHeat136Y28 := by
    rw [show (28 : ℕ) = 24+4 from rfl,nativeHeatPasses_add,h24,nativeHeat136Pass28]
  have h32 : nativeHeatPasses nativeGap137Old nativeHeat136Frames nativeHeat136Coef nativeHeat136Fixed nativeHeat136Base 32 nativeHeat136Y00 = nativeHeat136Y32 := by
    rw [show (32 : ℕ) = 28+4 from rfl,nativeHeatPasses_add,h28,nativeHeat136Pass32]
  have h36 : nativeHeatPasses nativeGap137Old nativeHeat136Frames nativeHeat136Coef nativeHeat136Fixed nativeHeat136Base 36 nativeHeat136Y00 = nativeHeat136Y36 := by
    rw [show (36 : ℕ) = 32+4 from rfl,nativeHeatPasses_add,h32,nativeHeat136Pass36]
  have h40 : nativeHeatPasses nativeGap137Old nativeHeat136Frames nativeHeat136Coef nativeHeat136Fixed nativeHeat136Base 40 nativeHeat136Y00 = nativeHeat136Y40 := by
    rw [show (40 : ℕ) = 36+4 from rfl,nativeHeatPasses_add,h36,nativeHeat136Pass40]
  have h44 : nativeHeatPasses nativeGap137Old nativeHeat136Frames nativeHeat136Coef nativeHeat136Fixed nativeHeat136Base 44 nativeHeat136Y00 = nativeHeat136Y44 := by
    rw [show (44 : ℕ) = 40+4 from rfl,nativeHeatPasses_add,h40,nativeHeat136Pass44]
  have h48 : nativeHeatPasses nativeGap137Old nativeHeat136Frames nativeHeat136Coef nativeHeat136Fixed nativeHeat136Base 48 nativeHeat136Y00 = nativeHeat136Y48 := by
    rw [show (48 : ℕ) = 44+4 from rfl,nativeHeatPasses_add,h44,nativeHeat136Pass48]
  exact h48

end ASDExplicitGamma.Numerics.Native
