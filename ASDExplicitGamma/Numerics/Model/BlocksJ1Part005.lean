module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ1Part000

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ1B5 : ModeBlockData :=
  ⟨⟨5, 6, (362719924084020235833/5000000000000000000000 : ℚ), (5319105376649539857/400000000000000000000 : ℚ)⟩, [
    (5, modeDataJ1M6)], (145087969633608094333/2000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j1_b5 : entryChecks 1 bflatBlockJ1B5.entries = true := by
  simp only [entryChecks,bflatBlockJ1B5,List.all_cons,List.all_nil,
    mode_checked_j1_m6,Bool.and_self]
theorem block_mass_checked_j1_b5 : blockMassCheck bflatBlockJ1B5 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
