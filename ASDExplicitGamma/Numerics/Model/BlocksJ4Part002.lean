module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ4Part000

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ4B2 : ModeBlockData :=
  ⟨⟨2, 3, (15126602285812469393/2000000000000000000000 : ℚ), (355551887877520273/10000000000000000000000 : ℚ)⟩, [
    (2, modeDataJ4M3)], (18908252857265586741/2500000000000000000000 : ℚ)⟩

theorem block_entries_checked_j4_b2 : entryChecks 4 bflatBlockJ4B2.entries = true := by
  simp only [entryChecks,bflatBlockJ4B2,List.all_cons,List.all_nil,
    mode_checked_j4_m3,Bool.and_self]
theorem block_mass_checked_j4_b2 : blockMassCheck bflatBlockJ4B2 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
