import IsingBulk.AnisoF002.C03.IsotropicRightShellCover
import IsingBulk.AnisoF002.C03.IsotropicAffineConstraintCalculus
import IsingBulk.AnisoF002.C03.IsotropicActualSharpCovariance

/-!
# Actual shell scales vanish at the single centered coincidence

Every nonconstant finite tuple admits a true diameter witness. On the
centered constrained chart that witness is bounded by the norm of the
real chart variable. At a fixed positive radial parameter the actual
Δ therefore vanishes linearly with that variable.
-/

namespace IsingBulk.AnisoF002.Isotropic
noncomputable section
open Set
open scoped Topology BigOperators

theorem exists_actual_diameter_witness {N : ℕ} (hN : 0 < N) (θ : Fin N → ℝ)
    (hne : ∃ i j, θ i ≠ θ j) (ρ : ℝ) :
    ∃ r : ℝ, 0 < r ∧ (∀ i j, |θ i - θ j| ≤ 2 * r) ∧
      (∃ i j, r ≤ |θ i - θ j|) ∧ r ≤ 2 * ‖fun i => θ i - ρ‖ := by
  let : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  obtain ⟨ij, _, hmax⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin N × Fin N))
    (fun p => |θ p.1 - θ p.2|) Finset.univ_nonempty
  let r := |θ ij.1 - θ ij.2|
  have hr : 0 < r := by
    obtain ⟨i, j, hij⟩ := hne
    exact (abs_pos.mpr (sub_ne_zero.mpr hij)).trans_le (hmax (i, j) (Finset.mem_univ _))
  refine ⟨r, hr, fun i j => (hmax (i, j) (Finset.mem_univ _)).trans (by linarith),
    ⟨ij.1, ij.2, le_rfl⟩, ?_⟩
  calc
    r = |(θ ij.1 - ρ) - (θ ij.2 - ρ)| := by dsimp [r]; congr 1; ring
    _ ≤ |θ ij.1 - ρ| + |θ ij.2 - ρ| := abs_sub _ _
    _ ≤ ‖fun i => θ i - ρ‖ + ‖fun i => θ i - ρ‖ :=
      add_le_add (by simpa only [Real.norm_eq_abs] using norm_le_pi_norm (fun i => θ i - ρ) ij.1)
        (by simpa only [Real.norm_eq_abs] using norm_le_pi_norm (fun i => θ i - ρ) ij.2)
    _ = _ := by ring

theorem centeredConstraintAngles_sub_const {d : ℕ} (ρ : ℝ) (x : Fin d → ℝ) :
    (fun i => centeredConstraintAngles ρ x i - ρ) = constrainedTangentMap d x := by
  rw [constrainedTangentMap_apply]
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [centeredConstraintAngles, NegativeHT.Angular.independentChart_last, Fin.snoc_last]
    ring
  · simp only [centeredConstraintAngles, NegativeHT.Angular.independentChart_castSucc, Fin.snoc_castSucc]
    ring

theorem centeredConstraintAngles_nonconstant {d : ℕ} (ρ : ℝ) (x : Fin d → ℝ) (hx : x ≠ 0) :
    ∃ i j, centeredConstraintAngles ρ x i ≠ centeredConstraintAngles ρ x j := by
  by_contra hh
  push Not at hh
  apply hx
  exact centeredConstraintAngles_constant_iff ρ (centeredConstraintAngles ρ x (Fin.last d)) x
    (fun i => hh i (Fin.last d))

theorem centered_actual_diameter_witness {d : ℕ} (ρ : ℝ) (x : Fin d → ℝ) (hx : x ≠ 0) :
    ∃ r : ℝ, 0 < r ∧
      (∀ i j, |centeredConstraintAngles ρ x i - centeredConstraintAngles ρ x j| ≤ 2 * r) ∧
      (∃ i j, r ≤ |centeredConstraintAngles ρ x i - centeredConstraintAngles ρ x j|) ∧
      r ≤ (2 * ‖constrainedTangentMap d‖) * ‖x‖ := by
  obtain ⟨r, hr, hdiam, hlow, hbound⟩ := exists_actual_diameter_witness (by omega)
    (centeredConstraintAngles ρ x) (centeredConstraintAngles_nonconstant ρ x hx) ρ
  refine ⟨r, hr, hdiam, hlow, ?_⟩
  rw [centeredConstraintAngles_sub_const] at hbound
  exact hbound.trans ((mul_le_mul_of_nonneg_left ((constrainedTangentMap d).le_opNorm x)
    (by norm_num : (0 : ℝ) ≤ 2)).trans_eq (by ring))

theorem isotropicShellDelta_le_radial_distance {N : ℕ} (b ε r e : ℝ) (θ : Fin N → ℝ)
    (he : 0 < e) (hε : e ≤ ε) (hr : 0 ≤ r) :
    isotropicShellDelta b ε r θ ≤ r / Real.sqrt e := by
  have hT : e ≤ isotropicShellT b ε r θ := by
    dsimp [isotropicShellT]
    linarith only [abs_nonneg (angularMean (fun i => θ i + b)), hr, hε]
  exact div_le_div_of_nonneg_left hr (Real.sqrt_pos.mpr he) (Real.sqrt_le_sqrt hT)

theorem centered_actual_shell_scale_witness {d : ℕ} (ρ b ε e : ℝ)
    (he : 0 < e) (hε : e ≤ ε) (x : Fin d → ℝ) (hx : x ≠ 0) :
    ∃ r : ℝ, 0 < r ∧
      (∀ i j, |centeredConstraintAngles ρ x i - centeredConstraintAngles ρ x j| ≤ 2 * r) ∧
      (∃ i j, r ≤ |centeredConstraintAngles ρ x i - centeredConstraintAngles ρ x j|) ∧
      isotropicShellDelta b ε r (centeredConstraintAngles ρ x) ≤
        (2 * ‖constrainedTangentMap d‖ / Real.sqrt e) * ‖x‖ := by
  obtain ⟨r, hr, hd, hl, hb⟩ := centered_actual_diameter_witness ρ x hx
  exact ⟨r, hr, hd, hl, (isotropicShellDelta_le_radial_distance b ε r e _ he hε hr.le).trans
    ((div_le_div_of_nonneg_right hb (Real.sqrt_nonneg e)).trans_eq (by ring))⟩

end
end IsingBulk.AnisoF002.Isotropic
