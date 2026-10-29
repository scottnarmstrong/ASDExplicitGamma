module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ1Part000

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ1B15 : ModeBlockData :=
  ⟨⟨15, 16, (2364265657614938307/1250000000000000000000 : ℚ), (1055059868110038549/625000000000000000000 : ℚ)⟩, [
    (15, modeDataJ1M16)], (3782825052183901291/2000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j1_b15 : entryChecks 1 bflatBlockJ1B15.entries = true := by
  simp only [entryChecks,bflatBlockJ1B15,List.all_cons,List.all_nil,
    mode_checked_j1_m16,Bool.and_self]
theorem block_mass_checked_j1_b15 : blockMassCheck bflatBlockJ1B15 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
