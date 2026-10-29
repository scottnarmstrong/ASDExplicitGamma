module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ4Part001

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ4B30 : ModeBlockData :=
  ⟨⟨30, 31, (72686783910773273963/10000000000000000000000 : ℚ), (43336205054849683/1250000000000000000000 : ℚ)⟩, [
    (30, modeDataJ4M31)], (36343391955386636981/5000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j4_b30 : entryChecks 4 bflatBlockJ4B30.entries = true := by
  simp only [entryChecks,bflatBlockJ4B30,List.all_cons,List.all_nil,
    mode_checked_j4_m31,Bool.and_self]
theorem block_mass_checked_j4_b30 : blockMassCheck bflatBlockJ4B30 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
