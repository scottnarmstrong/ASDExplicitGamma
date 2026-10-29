module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ4Part001

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ4B21 : ModeBlockData :=
  ⟨⟨21, 22, (74149674531393441089/10000000000000000000000 : ℚ), (351099450608956199/10000000000000000000000 : ℚ)⟩, [
    (21, modeDataJ4M22)], (1158588664553022517/156250000000000000000 : ℚ)⟩

theorem block_entries_checked_j4_b21 : entryChecks 4 bflatBlockJ4B21.entries = true := by
  simp only [entryChecks,bflatBlockJ4B21,List.all_cons,List.all_nil,
    mode_checked_j4_m22,Bool.and_self]
theorem block_mass_checked_j4_b21 : blockMassCheck bflatBlockJ4B21 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
