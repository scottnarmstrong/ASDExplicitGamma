module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ4Part000

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ4B11 : ModeBlockData :=
  ⟨⟨11, 12, (75208707916839380607/10000000000000000000000 : ℚ), (44285025805538527/1250000000000000000000 : ℚ)⟩, [
    (11, modeDataJ4M12)], (37604353958419690303/5000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j4_b11 : entryChecks 4 bflatBlockJ4B11.entries = true := by
  simp only [entryChecks,bflatBlockJ4B11,List.all_cons,List.all_nil,
    mode_checked_j4_m12,Bool.and_self]
theorem block_mass_checked_j4_b11 : blockMassCheck bflatBlockJ4B11 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
