module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ3Part001

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ3B23 : ModeBlockData :=
  ⟨⟨23, 24, (91378445842696206327/5000000000000000000000 : ℚ), (348978585023646407/1250000000000000000000 : ℚ)⟩, [
    (23, modeDataJ3M24)], (182756891685392412653/10000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j3_b23 : entryChecks 3 bflatBlockJ3B23.entries = true := by
  simp only [entryChecks,bflatBlockJ3B23,List.all_cons,List.all_nil,
    mode_checked_j3_m24,Bool.and_self]
theorem block_mass_checked_j3_b23 : blockMassCheck bflatBlockJ3B23 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
