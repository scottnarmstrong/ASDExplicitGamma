module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ2Part001

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ2B31 : ModeBlockData :=
  ⟨⟨31, 32, (3612013710603786663/2500000000000000000000 : ℚ), (1205515777467819821/2500000000000000000000 : ℚ)⟩, [
    (31, modeDataJ2M32)], (14448054842415146651/10000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j2_b31 : entryChecks 2 bflatBlockJ2B31.entries = true := by
  simp only [entryChecks,bflatBlockJ2B31,List.all_cons,List.all_nil,
    mode_checked_j2_m32,Bool.and_self]
theorem block_mass_checked_j2_b31 : blockMassCheck bflatBlockJ2B31 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
