module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ3Part001

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ3B30 : ModeBlockData :=
  ⟨⟨30, 31, (31547657510516595987/2000000000000000000000 : ℚ), (637738222533289333/2500000000000000000000 : ℚ)⟩, [
    (30, modeDataJ3M31)], (78869143776291489967/5000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j3_b30 : entryChecks 3 bflatBlockJ3B30.entries = true := by
  simp only [entryChecks,bflatBlockJ3B30,List.all_cons,List.all_nil,
    mode_checked_j3_m31,Bool.and_self]
theorem block_mass_checked_j3_b30 : blockMassCheck bflatBlockJ3B30 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
