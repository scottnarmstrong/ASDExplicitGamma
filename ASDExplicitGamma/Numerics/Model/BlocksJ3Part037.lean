module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ3Part002

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ3B37 : ModeBlockData :=
  ⟨⟨37, 38, (65384133208188482387/5000000000000000000000 : ℚ), (1140603269204616687/5000000000000000000000 : ℚ)⟩, [
    (37, modeDataJ3M38)], (130768266416376964773/10000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j3_b37 : entryChecks 3 bflatBlockJ3B37.entries = true := by
  simp only [entryChecks,bflatBlockJ3B37,List.all_cons,List.all_nil,
    mode_checked_j3_m38,Bool.and_self]
theorem block_mass_checked_j3_b37 : blockMassCheck bflatBlockJ3B37 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
