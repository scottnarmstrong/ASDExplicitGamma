module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ2Part000

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ2B11 : ModeBlockData :=
  ⟨⟨11, 12, (419882197749936598473/10000000000000000000000 : ℚ), (21242333968732303763/10000000000000000000000 : ℚ)⟩, [
    (11, modeDataJ2M12)], (52485274718742074809/1250000000000000000000 : ℚ)⟩

theorem block_entries_checked_j2_b11 : entryChecks 2 bflatBlockJ2B11.entries = true := by
  simp only [entryChecks,bflatBlockJ2B11,List.all_cons,List.all_nil,
    mode_checked_j2_m12,Bool.and_self]
theorem block_mass_checked_j2_b11 : blockMassCheck bflatBlockJ2B11 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
