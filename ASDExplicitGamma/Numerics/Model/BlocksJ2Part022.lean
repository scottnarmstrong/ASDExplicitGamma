module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ2Part001

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ2B22 : ModeBlockData :=
  ⟨⟨22, 23, (104247585487978065797/10000000000000000000000 : ℚ), (5044636921519191759/5000000000000000000000 : ℚ)⟩, [
    (22, modeDataJ2M23)], (26061896371994516449/2500000000000000000000 : ℚ)⟩

theorem block_entries_checked_j2_b22 : entryChecks 2 bflatBlockJ2B22.entries = true := by
  simp only [entryChecks,bflatBlockJ2B22,List.all_cons,List.all_nil,
    mode_checked_j2_m23,Bool.and_self]
theorem block_mass_checked_j2_b22 : blockMassCheck bflatBlockJ2B22 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
