module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ5Part000

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ5B11 : ModeBlockData :=
  ⟨⟨11, 12, (5040723759816344407/2000000000000000000000 : ℚ), (39498425139480213/10000000000000000000000 : ℚ)⟩, [
    (11, modeDataJ5M12)], (12601809399540861017/5000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j5_b11 : entryChecks 5 bflatBlockJ5B11.entries = true := by
  simp only [entryChecks,bflatBlockJ5B11,List.all_cons,List.all_nil,
    mode_checked_j5_m12,Bool.and_self]
theorem block_mass_checked_j5_b11 : blockMassCheck bflatBlockJ5B11 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
