import IsingBulk.Tail.AllBranchExteriorFiniteOrders
import IsingBulk.Tail.SelectedFAsymptotic

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.Branch Filter Asymptotics
open scoped Topology

theorem radial_log_polynomial_littleO :
    (fun ε : ℝ => (Real.log (1/ε)+1)^2) =o[𝓝[>] 0]
      (fun ε : ℝ => (Real.sqrt ε)⁻¹) := by
  have hshift : (fun H : ℝ => (H+1)^2) =O[atTop] (fun H : ℝ => H^2) := by
    apply IsBigO.of_bound 4
    filter_upwards [eventually_ge_atTop (1:ℝ)] with H hH
    simp only [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg (H+1)),abs_of_nonneg (sq_nonneg H)]
    nlinarith
  have hpow := isLittleO_pow_exp_pos_mul_atTop 2 (b := (1/2:ℝ)) (by norm_num)
  have h := (hshift.trans_isLittleO hpow).comp_tendsto log_inverse_tendsto_atTop
  apply h.congr' (Eventually.of_forall (fun _ => rfl))
  filter_upwards [self_mem_nhdsWithin] with ε hε
  simpa only [Function.comp_def,div_eq_mul_inv,one_mul,mul_comm] using exp_half_log_inverse hε

def allBranchExteriorWindowTerm (p : ℕ) (d : LocalBranchData) (η δ : ℝ)
    (hδ : 0 < δ) (A c β D : ℝ) (j : ℕ) (ε : ℝ) (N : ℕ) : ℝ :=
  if 2*p+2 ≤ N ∧ (N:ℝ) ≤ D*Real.sqrt (Real.log (1/ε)) then
    allBranchExteriorAngularNorm N d η δ ε (allBranchMicroRadius A c N)
      (allBranchEqualityRadius β N) hδ j else 0

theorem allBranchExteriorWindowTerm_nonneg (p : ℕ) (d : LocalBranchData) (η δ : ℝ)
    (hδ : 0 < δ) (A c β D : ℝ) (j : ℕ) (ε : ℝ) (N : ℕ) :
    0 ≤ allBranchExteriorWindowTerm p d η δ hδ A c β D j ε N := by
  unfold allBranchExteriorWindowTerm
  split_ifs
  · exact allBranchExteriorAngularNorm_nonneg ..
  · exact le_rfl

theorem allBranchExterior_window_littleO {d : LocalBranchData}
    (B : BranchEstimates d) (hcsmall : d.c₀ < Real.sin d.theta/2)
    (hα : d.alpha < Real.sin d.thetaB/4) (p : ℕ) (hp : 1 ≤ p) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ η δ : ℝ, ∀ hδ : 0 < δ, δ ≤ δ₀ →
      ∀ A c : ℝ, 0 ≤ A → 0 < c → c ≤ 1 →
      ∃ β₀ : ℝ, 0 < β₀ ∧ ∀ β : ℝ, β₀ ≤ β →
      ∀ D : ℝ, 0 ≤ D → ∀ j : ℕ, j ≤ (2*p)^2/2-1 →
      (∀ᶠ ε : ℝ in 𝓝[>] 0, Summable (allBranchExteriorWindowTerm p d η δ hδ A c β D j ε)) ∧
      (fun ε : ℝ => ∑' N : ℕ, allBranchExteriorWindowTerm p d η δ hδ A c β D j ε N)
        =o[𝓝[>] 0] (fun ε : ℝ => (Real.sqrt ε)⁻¹) := by
  obtain ⟨δ₀,hδ₀,hfinite⟩ := allBranchExterior_angular_window_finite B hcsmall hα ((2*p)^2/2-1)
  refine ⟨δ₀,hδ₀,?_⟩
  intro η δ hδ hδsmall A c hA hc hc1
  obtain ⟨β₀,hβ₀,hβall⟩ := hfinite η δ hδ hδsmall A c hA hc hc1
  refine ⟨β₀,hβ₀,?_⟩
  intro β hβ D hD j hj
  obtain ⟨S,hS,hSn,hbound⟩ := hβall β hβ j hj
  have hmajor : ∀ᶠ ε : ℝ in 𝓝[>] 0, ∀ N : ℕ,
      allBranchExteriorWindowTerm p d η δ hδ A c β D j ε N ≤ S N*(Real.log (1/ε)+1)^2 := by
    filter_upwards [log_inverse_tendsto_atTop.eventually (hbound D hD),self_mem_nhdsWithin] with ε he hε
    intro N
    unfold allBranchExteriorWindowTerm
    split_ifs with hwindow
    · have hN : 1 ≤ N := by omega
      have hpred : N-1+1=N := Nat.sub_add_cancel hN
      have hpreal : ((N-1:ℕ):ℝ)+1=N := by exact_mod_cast hpred
      have horder := allBranchExterior_source_degree hp hwindow.1 hj
      have ho : 2*j+1 ≤ (N-1+1)*(N-1) := by rw [hpred]; omega
      have hh := he (N-1) (by rw [hpreal]; exact hwindow.2) ho
      have heq : Real.exp (-Real.log (1/ε))=ε := by
        rw [one_div,Real.log_inv,neg_neg,Real.exp_log hε]
      simpa only [hpred,heq] using hh
    · exact mul_nonneg (hSn N) (sq_nonneg _)
  have hn := allBranchExteriorWindowTerm_nonneg p d η δ hδ A c β D j
  have hsum : ∀ᶠ ε : ℝ in 𝓝[>] 0,
      Summable (allBranchExteriorWindowTerm p d η δ hδ A c β D j ε) := by
    filter_upwards [hmajor] with ε he
    exact Summable.of_nonneg_of_le (hn ε) he (hS.mul_right _)
  refine ⟨hsum,?_⟩
  have hO : (fun ε : ℝ => ∑' N : ℕ, allBranchExteriorWindowTerm p d η δ hδ A c β D j ε N)
      =O[𝓝[>] 0] (fun ε : ℝ => (Real.log (1/ε)+1)^2) := by
    apply IsBigO.of_bound (∑' N, S N)
    filter_upwards [hmajor,hsum] with ε he hsε
    have hh := Summable.tsum_le_tsum he hsε (hS.mul_right _)
    rw [tsum_mul_right] at hh
    simpa only [Real.norm_eq_abs,abs_of_nonneg (tsum_nonneg (hn ε)),
      abs_of_nonneg (sq_nonneg (Real.log (1/ε)+1))] using hh
  exact hO.trans_isLittleO radial_log_polynomial_littleO

end
end IsingBulk.Tail
