module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ2Part000

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ2B12 : ModeBlockData :=
  ⟨⟨12, 13, (19266092991345824241/500000000000000000000 : ℚ), (10085744241868798697/5000000000000000000000 : ℚ)⟩, [
    (12, modeDataJ2M13)], (385321859826916484819/10000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j2_b12 : entryChecks 2 bflatBlockJ2B12.entries = true := by
  simp only [entryChecks,bflatBlockJ2B12,List.all_cons,List.all_nil,
    mode_checked_j2_m13,Bool.and_self]
theorem block_mass_checked_j2_b12 : blockMassCheck bflatBlockJ2B12 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
