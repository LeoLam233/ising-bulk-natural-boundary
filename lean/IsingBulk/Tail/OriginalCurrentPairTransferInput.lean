import IsingBulk.Tail.CurrentPairTransferInput

/-! Actual coupled current tuple motion on an absolute small parameter disk.
The c epsilon specialization has no particle-count restriction. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch Set Filter
open scoped Topology

theorem actual_deformed_sourceW_small_disk_motion (d : LocalBranchData) {N : ℕ} (hN : 1 ≤ N)
    (f : SelectorFunctions) {eps τ lam c : ℝ} (heps : 0 ≤ eps) (heps1 : eps ≤ 1)
    (hτ : 0 ≤ τ) (hl0 : 0 ≤ lam) (hl1 : lam ≤ 1) (hc : c ≤ 1/4)
    (hp : ∀ x, 0 ≤ f.p x ∧ f.p x ≤ 1) (hm : ∀ x, 0 ≤ f.m x ∧ f.m x ≤ 1)
    (hsmall : d.c₀*eps+2*τ ≤ 1) (θ : Fin N → ℝ) (i : Fin N) {s : ℂ}
    (hs : ‖s-radialParameter d.theta eps‖ ≤ c) :
    ‖sourceW s (deformedPoint f (Real.exp (-d.c₀*eps)) τ lam θ i)-
      (limitingAngularW d.thetaB (θ i):ℂ)‖ ≤ 3*c+(3+2*d.c₀)*eps+4*τ := by
  have hs0 := (selected_disk_parameter_envelope (N := 1) (by norm_num) heps heps1 hc (by simpa using hs)).1
  have hsn : 1 ≤ ‖radialParameter d.theta eps‖ := by rw [radialParameter_norm heps]; linarith
  have hd := sourceS_sub_norm_le hs0 hsn
  have hy := deformedPoint_sourceW_transfer d (by omega) f θ heps hτ hl0 hl1 hp hm hsmall i
  have he : sourceW s (deformedPoint f (Real.exp (-d.c₀*eps)) τ lam θ i)-
      sourceW (radialParameter d.theta eps) (deformedPoint f (Real.exp (-d.c₀*eps)) τ lam θ i)=
      sourceS s-sourceS (radialParameter d.theta eps) := by unfold sourceW; ring
  have ht := norm_sub_le_norm_sub_add_norm_sub
    (sourceW s (deformedPoint f (Real.exp (-d.c₀*eps)) τ lam θ i))
    (sourceW (radialParameter d.theta eps) (deformedPoint f (Real.exp (-d.c₀*eps)) τ lam θ i))
    (limitingAngularW d.thetaB (θ i):ℂ)
  rw [he] at ht
  have hsc : 3*‖s-radialParameter d.theta eps‖ ≤ 3*c := by
    calc
      _ ≤ 3*(c) := mul_le_mul_of_nonneg_left hs (by norm_num)
      _ = _ := by ring
  linarith

/-- Uniform motion for every actual coordinate, including both endpoint
slivers and the lower branch, before N, occupancy or lambda are chosen. -/
theorem original_current_pair_inputs (d : LocalBranchData) {δ : ℝ} (hδ : 0 < δ) :
    ∃ r : ℝ, 0 < r ∧ r ≤ 1/4 ∧
      ∀ (N : ℕ) (eps τ lam α c : ℝ) (f : SelectorFunctions) (θ : Fin N → ℝ) (s : ℂ),
        1 ≤ N → 0 ≤ eps → eps < r → 0 ≤ τ → τ < r → 0 ≤ lam → lam ≤ 1 →
        0 ≤ α → α < r → c ≤ r →
        (∀ x, 0 ≤ f.p x ∧ f.p x ≤ 1) → (∀ x, 0 ≤ f.m x ∧ f.m x ≤ 1) →
        ‖s-radialParameter d.theta eps‖ ≤ c → ∀ i,
        Real.sin (θ i) ≤ 3*α/2 →
        ‖deformedPoint f (Real.exp (-d.c₀*eps)) τ lam θ i-
          ((Real.cos (θ i):ℂ)-((|Real.sin (θ i)|:ℝ):ℂ)*Complex.I)‖ < δ ∧
        ‖selectedContinuedRoot s (deformedPoint f (Real.exp (-d.c₀*eps)) τ lam θ i)-
          continuedRoot (limitingAngularW d.thetaB (θ i):ℂ)‖ < δ := by
  have hcos : -1 < Real.cos d.thetaB := by
    have hh := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos,d.theta_pos],d.theta_lt⟩
    linarith [d.angle_relation]
  obtain ⟨rW,hrW,hroot⟩ := continuedRoot_real_segment_uniform (hi := 2+Real.cos d.thetaB) hcos hδ
  let v := min δ rW
  let r := min (1/(4*(d.c₀+1))) (v/(20*(d.c₀+1)))
  have hv : 0 < v := lt_min hδ hrW
  have hcp : 0 < d.c₀+1 := by linarith [d.c₀_pos]
  have hr : 0 < r := lt_min (by positivity) (by positivity)
  have hrbase : 4*(d.c₀+1)*r ≤ 1 := by
    have hh := (le_div_iff₀ (by positivity : 0<4*(d.c₀+1))).mp (min_le_left (1/(4*(d.c₀+1))) (v/(20*(d.c₀+1))))
    nlinarith only [hh]
  have hrsmall : 20*(d.c₀+1)*r ≤ v := by
    have hh := (le_div_iff₀ (by positivity : 0<20*(d.c₀+1))).mp (min_le_right (1/(4*(d.c₀+1))) (v/(20*(d.c₀+1))))
    nlinarith only [hh]
  have hrquarter : r ≤ 1/4 := by nlinarith [mul_nonneg d.c₀_pos.le hr.le]
  refine ⟨r,hr,hrquarter,?_⟩
  intro N eps τ lam α c f θ s hN heps hepsr hτ hτr hl0 hl1 hα hαr hc hp hm hs i hsin
  have hsmall : d.c₀*eps+2*τ ≤ 1 := by nlinarith [mul_nonneg d.c₀_pos.le hr.le]
  have heps1 : eps ≤ 1 := by linarith
  have hcN : c ≤ r := hc
  constructor
  · have hh := actual_deformedPoint_motion (by omega) f d.c₀_pos.le heps hτ hl0 hl1 hα hp hm hsmall θ i hsin
    apply hh.trans_lt
    have hvδ : v ≤ δ := min_le_left _ _
    nlinarith [mul_nonneg d.c₀_pos.le (sub_nonneg.mpr hepsr.le),mul_nonneg d.c₀_pos.le hr.le]
  · apply hroot (limitingAngularW d.thetaB (θ i))
      ⟨by unfold limitingAngularW; linarith [Real.cos_le_one (θ i)],
       by unfold limitingAngularW; linarith [Real.neg_one_le_cos (θ i)]⟩
    have hh := actual_deformed_sourceW_small_disk_motion d hN f heps heps1 hτ hl0 hl1 (hc.trans hrquarter) hp hm hsmall θ i hs
    apply hh.trans_lt
    have hvW : v ≤ rW := min_le_right _ _
    have hdiv : 3*c ≤ 3*r := mul_le_mul_of_nonneg_left hcN (by norm_num)
    nlinarith [mul_nonneg d.c₀_pos.le (sub_nonneg.mpr hepsr.le),mul_nonneg d.c₀_pos.le hr.le]



end
end IsingBulk.Tail
