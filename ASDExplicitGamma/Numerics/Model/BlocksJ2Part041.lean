module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ2Part002

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ2B41 : ModeBlockData :=
  ⟨⟨41, 42, (2901206779724531213/10000000000000000000000 : ℚ), (1254173384550245011/5000000000000000000000 : ℚ)⟩, [
    (41, modeDataJ2M42)], (725301694931132803/2500000000000000000000 : ℚ)⟩

theorem block_entries_checked_j2_b41 : entryChecks 2 bflatBlockJ2B41.entries = true := by
  simp only [entryChecks,bflatBlockJ2B41,List.all_cons,List.all_nil,
    mode_checked_j2_m42,Bool.and_self]
theorem block_mass_checked_j2_b41 : blockMassCheck bflatBlockJ2B41 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
