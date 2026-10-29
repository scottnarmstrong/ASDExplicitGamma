module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ1Part000

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ1B1 : ModeBlockData :=
  ⟨⟨1, 2, (114106980093975423111/625000000000000000000 : ℚ), (60004175862256748371/2500000000000000000000 : ℚ)⟩, [
    (1, modeDataJ1M2)], (73028467260144270791/400000000000000000000 : ℚ)⟩

theorem block_entries_checked_j1_b1 : entryChecks 1 bflatBlockJ1B1.entries = true := by
  simp only [entryChecks,bflatBlockJ1B1,List.all_cons,List.all_nil,
    mode_checked_j1_m2,Bool.and_self]
theorem block_mass_checked_j1_b1 : blockMassCheck bflatBlockJ1B1 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
