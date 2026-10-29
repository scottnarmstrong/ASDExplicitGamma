module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ2Part003

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ2B50 : ModeBlockData :=
  ⟨⟨50, 51, (48721199630928399/250000000000000000000 : ℚ), (329790165034190303/2000000000000000000000 : ℚ)⟩, [
    (50, modeDataJ2M51)], (1948847985237135959/10000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j2_b50 : entryChecks 2 bflatBlockJ2B50.entries = true := by
  simp only [entryChecks,bflatBlockJ2B50,List.all_cons,List.all_nil,
    mode_checked_j2_m51,Bool.and_self]
theorem block_mass_checked_j2_b50 : blockMassCheck bflatBlockJ2B50 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
