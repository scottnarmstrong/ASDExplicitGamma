module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ3Part001

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ3B22 : ModeBlockData :=
  ⟨⟨22, 23, (46511645155011479059/2500000000000000000000 : ℚ), (2822933454299821299/10000000000000000000000 : ℚ)⟩, [
    (22, modeDataJ3M23)], (37209316124009183247/2000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j3_b22 : entryChecks 3 bflatBlockJ3B22.entries = true := by
  simp only [entryChecks,bflatBlockJ3B22,List.all_cons,List.all_nil,
    mode_checked_j3_m23,Bool.and_self]
theorem block_mass_checked_j3_b22 : blockMassCheck bflatBlockJ3B22 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
