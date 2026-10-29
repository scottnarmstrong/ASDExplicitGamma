module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ5Part001

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ5B19 : ModeBlockData :=
  ⟨⟨19, 20, (12586853352914467477/5000000000000000000000 : ℚ), (39468613715931677/10000000000000000000000 : ℚ)⟩, [
    (19, modeDataJ5M20)], (25173706705828934953/10000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j5_b19 : entryChecks 5 bflatBlockJ5B19.entries = true := by
  simp only [entryChecks,bflatBlockJ5B19,List.all_cons,List.all_nil,
    mode_checked_j5_m20,Bool.and_self]
theorem block_mass_checked_j5_b19 : blockMassCheck bflatBlockJ5B19 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
