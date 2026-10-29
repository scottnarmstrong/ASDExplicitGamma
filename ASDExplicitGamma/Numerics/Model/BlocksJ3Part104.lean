module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ3Part010

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ3B104 : ModeBlockData :=
  ⟨⟨171, 175, (299881829915608117/5000000000000000000000 : ℚ), (140514594928166743/2500000000000000000000 : ℚ)⟩, [
    (171, modeDataJ3M172),
    (172, modeDataJ3M173),
    (173, modeDataJ3M174),
    (174, modeDataJ3M175)], (59976365983121623/1000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j3_b104 : entryChecks 3 bflatBlockJ3B104.entries = true := by
  simp only [entryChecks,bflatBlockJ3B104,List.all_cons,List.all_nil,
    mode_checked_j3_m172,
    mode_checked_j3_m173,
    mode_checked_j3_m174,
    mode_checked_j3_m175,Bool.and_self]
theorem block_mass_checked_j3_b104 : blockMassCheck bflatBlockJ3B104 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
