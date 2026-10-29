module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ2Part000

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ2B0 : ModeBlockData :=
  ⟨⟨0, 1, (678712941768121470329/10000000000000000000000 : ℚ), (28744716043729917119/10000000000000000000000 : ℚ)⟩, [
    (0, modeDataJ2M1)], (84839117721015183791/1250000000000000000000 : ℚ)⟩

theorem block_entries_checked_j2_b0 : entryChecks 2 bflatBlockJ2B0.entries = true := by
  simp only [entryChecks,bflatBlockJ2B0,List.all_cons,List.all_nil,
    mode_checked_j2_m1,Bool.and_self]
theorem block_mass_checked_j2_b0 : blockMassCheck bflatBlockJ2B0 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
