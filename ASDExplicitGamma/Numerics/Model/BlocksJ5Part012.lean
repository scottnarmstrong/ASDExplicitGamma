module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ5Part000

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ5B12 : ModeBlockData :=
  ⟨⟨12, 13, (25200696272610262759/10000000000000000000000 : ℚ), (9873878195728447/2500000000000000000000 : ℚ)⟩, [
    (12, modeDataJ5M13)], (12600348136305131379/5000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j5_b12 : entryChecks 5 bflatBlockJ5B12.entries = true := by
  simp only [entryChecks,bflatBlockJ5B12,List.all_cons,List.all_nil,
    mode_checked_j5_m13,Bool.and_self]
theorem block_mass_checked_j5_b12 : blockMassCheck bflatBlockJ5B12 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
