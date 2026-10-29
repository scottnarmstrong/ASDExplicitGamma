module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ5Part000

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ5B1 : ModeBlockData :=
  ⟨⟨1, 2, (25219990644679940867/10000000000000000000000 : ℚ), (9878684669252183/2500000000000000000000 : ℚ)⟩, [
    (1, modeDataJ5M2)], (12609995322339970433/5000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j5_b1 : entryChecks 5 bflatBlockJ5B1.entries = true := by
  simp only [entryChecks,bflatBlockJ5B1,List.all_cons,List.all_nil,
    mode_checked_j5_m2,Bool.and_self]
theorem block_mass_checked_j5_b1 : blockMassCheck bflatBlockJ5B1 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
