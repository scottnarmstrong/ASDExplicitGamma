module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ4Part002

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ4B44 : ModeBlockData :=
  ⟨⟨44, 45, (69517802860963337163/10000000000000000000000 : ℚ), (337070481867655403/10000000000000000000000 : ℚ)⟩, [
    (44, modeDataJ4M45)], (34758901430481668581/5000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j4_b44 : entryChecks 4 bflatBlockJ4B44.entries = true := by
  simp only [entryChecks,bflatBlockJ4B44,List.all_cons,List.all_nil,
    mode_checked_j4_m45,Bool.and_self]
theorem block_mass_checked_j4_b44 : blockMassCheck bflatBlockJ4B44 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
