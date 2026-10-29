module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ2Part003

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ2B55 : ModeBlockData :=
  ⟨⟨55, 56, (72853937236765121/500000000000000000000 : ℚ), (1353142076251588939/10000000000000000000000 : ℚ)⟩, [
    (55, modeDataJ2M56)], (1457078744735302419/10000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j2_b55 : entryChecks 2 bflatBlockJ2B55.entries = true := by
  simp only [entryChecks,bflatBlockJ2B55,List.all_cons,List.all_nil,
    mode_checked_j2_m56,Bool.and_self]
theorem block_mass_checked_j2_b55 : blockMassCheck bflatBlockJ2B55 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
