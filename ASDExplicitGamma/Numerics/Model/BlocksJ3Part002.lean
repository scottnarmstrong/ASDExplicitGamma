module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ3Part000

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ3B2 : ModeBlockData :=
  ⟨⟨2, 3, (226223914899313327443/10000000000000000000000 : ℚ), (1596928669096106507/5000000000000000000000 : ℚ)⟩, [
    (2, modeDataJ3M3)], (113111957449656663721/5000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j3_b2 : entryChecks 3 bflatBlockJ3B2.entries = true := by
  simp only [entryChecks,bflatBlockJ3B2,List.all_cons,List.all_nil,
    mode_checked_j3_m3,Bool.and_self]
theorem block_mass_checked_j3_b2 : blockMassCheck bflatBlockJ3B2 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
