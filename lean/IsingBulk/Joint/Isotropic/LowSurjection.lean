import IsingBulk.Joint.Isotropic.ExteriorRoot

namespace IsingBulk.Joint
noncomputable section
open IsingBulk.Anisotropic

/-- Every exterior point has a preimage in the exact right-hand temperature cell. -/
theorem sinh_surjOn_low : Set.SurjOn Complex.sinh (omegaL 1) {s : ℂ | 1 < ‖s‖} := by
  intro s hs
  obtain ⟨v,hv,hvs⟩ := exists_outer_joukowski_root hs
  have hv0 : v ≠ 0 := by intro h; norm_num [h] at hv
  have hrel : Complex.sinh (Complex.log v) = s := by
    rw [sinh_eq_joukowski_exp, Complex.exp_log hv0, hvs]
  refine ⟨Complex.log v,?_,hrel⟩
  rw [mem_omegaL_one_iff, hrel]
  exact ⟨by rw [Complex.log_re]; exact Real.log_pos hv, hs⟩

/-- No identification across real-part signs is used: in the right cell the
outside Joukowski root is unique, so equal sinh values have equal exponentials. -/
theorem exp_eq_of_sinh_eq_low {z w : ℂ} (hz : z ∈ omegaL 1) (hw : w ∈ omegaL 1)
    (he : Complex.sinh z = Complex.sinh w) : Complex.exp z = Complex.exp w := by
  apply joukowski_injOn_outer
  · change 1 < ‖Complex.exp z‖
    rw [Complex.norm_exp]
    exact Real.one_lt_exp_iff.mpr ((mem_omegaL_one_iff z).mp hz).1
  · change 1 < ‖Complex.exp w‖
    rw [Complex.norm_exp]
    exact Real.one_lt_exp_iff.mpr ((mem_omegaL_one_iff w).mp hw).1
  · simpa only [← sinh_eq_joukowski_exp] using he

/-- Exact fibers, hence the complete deck translation group. -/
theorem sinh_fiber_low {z w : ℂ} (hz : z ∈ omegaL 1) (hw : w ∈ omegaL 1) :
    Complex.sinh z = Complex.sinh w ↔
      ∃ n : ℤ, z = w + n * (2 * Real.pi * Complex.I) := by
  constructor
  · intro he
    exact Complex.exp_eq_exp_iff_exists_int.mp (exp_eq_of_sinh_eq_low hz hw he)
  · intro he
    have hx := Complex.exp_eq_exp_iff_exists_int.mpr he
    rw [sinh_eq_joukowski_exp, sinh_eq_joukowski_exp, hx]

/-- Literal deck translations preserve the whole low-temperature cell. -/
theorem deck_mem_low_iff (z : ℂ) (n : ℤ) :
    z + n * (2 * Real.pi * Complex.I) ∈ omegaL 1 ↔ z ∈ omegaL 1 := by
  have he : Complex.exp (z + n * (2 * Real.pi * Complex.I)) = Complex.exp z :=
    Complex.exp_eq_exp_iff_exists_int.mpr ⟨n,rfl⟩
  have hs : Complex.sinh (z+n*(2*Real.pi*Complex.I)) = Complex.sinh z := by
    rw [sinh_eq_joukowski_exp, sinh_eq_joukowski_exp, he]
  rw [mem_omegaL_one_iff, mem_omegaL_one_iff, hs]
  simp

end
end IsingBulk.Joint
