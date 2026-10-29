module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ5Part001

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ5B18 : ModeBlockData :=
  ⟨⟨18, 19, (12589130770278761509/5000000000000000000000 : ℚ), (7894630742135907/2000000000000000000000 : ℚ)⟩, [
    (18, modeDataJ5M19)], (25178261540557523017/10000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j5_b18 : entryChecks 5 bflatBlockJ5B18.entries = true := by
  simp only [entryChecks,bflatBlockJ5B18,List.all_cons,List.all_nil,
    mode_checked_j5_m19,Bool.and_self]
theorem block_mass_checked_j5_b18 : blockMassCheck bflatBlockJ5B18 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
