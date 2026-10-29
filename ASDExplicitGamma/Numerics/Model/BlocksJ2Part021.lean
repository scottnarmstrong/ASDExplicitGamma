module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ2Part001

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ2B21 : ModeBlockData :=
  ⟨⟨21, 22, (123676648483626011537/10000000000000000000000 : ℚ), (5466859611244593417/5000000000000000000000 : ℚ)⟩, [
    (21, modeDataJ2M22)], (7729790530226625721/625000000000000000000 : ℚ)⟩

theorem block_entries_checked_j2_b21 : entryChecks 2 bflatBlockJ2B21.entries = true := by
  simp only [entryChecks,bflatBlockJ2B21,List.all_cons,List.all_nil,
    mode_checked_j2_m22,Bool.and_self]
theorem block_mass_checked_j2_b21 : blockMassCheck bflatBlockJ2B21 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
