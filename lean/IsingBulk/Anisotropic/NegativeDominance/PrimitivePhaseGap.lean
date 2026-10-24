import IsingBulk.Anisotropic.RegularEdges.PhasePrime

namespace IsingBulk.Anisotropic.NegativeDominance
noncomputable section

/-- A primitive phase has one positive separation at every nonmultiple order,
obtained from its finite residue classes. -/
theorem primitiveRoot_uniform_power_gap {z : ℂ} {p : ℕ} (hp : 2≤p)
    (hz : IsPrimitiveRoot z p) :
    ∃κ : ℝ,0<κ ∧ ∀N : ℕ,¬p∣N → κ≤‖1-z^N‖ := by
  let S := Finset.Ioo 0 p
  have hS : S.Nonempty := ⟨1,by simp only [S,Finset.mem_Ioo]; omega⟩
  obtain ⟨k,hk,hmin⟩ := S.exists_min_image (fun k=>‖1-z^k‖) hS
  have hk' : 0<k ∧ k<p := Finset.mem_Ioo.mp hk
  have hkz : z^k≠1 := fun h=> (Nat.not_dvd_of_pos_of_lt hk'.1 hk'.2) ((hz.pow_eq_one_iff_dvd k).mp h)
  refine ⟨‖1-z^k‖,norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hkz)),?_⟩
  intro N hN
  rw [pow_eq_pow_mod N hz.pow_eq_one]
  apply hmin
  simp only [S,Finset.mem_Ioo]
  exact ⟨Nat.pos_of_ne_zero (fun h => hN (Nat.dvd_of_mod_eq_zero h)),Nat.mod_lt _ (by omega)⟩

end
end IsingBulk.Anisotropic.NegativeDominance
