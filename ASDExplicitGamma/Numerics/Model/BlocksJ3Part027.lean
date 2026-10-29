module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ3Part001

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ3B27 : ModeBlockData :=
  ⟨⟨27, 28, (168824804807012179753/10000000000000000000000 : ℚ), (2658679511985743867/10000000000000000000000 : ℚ)⟩, [
    (27, modeDataJ3M28)], (21103100600876522469/1250000000000000000000 : ℚ)⟩

theorem block_entries_checked_j3_b27 : entryChecks 3 bflatBlockJ3B27.entries = true := by
  simp only [entryChecks,bflatBlockJ3B27,List.all_cons,List.all_nil,
    mode_checked_j3_m28,Bool.and_self]
theorem block_mass_checked_j3_b27 : blockMassCheck bflatBlockJ3B27 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
