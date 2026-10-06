import IsingBulk.Tail.UltraHighRadialTail
import IsingBulk.Tail.UltraHighSourceEstimate
import IsingBulk.Tail.SelectedBranchData

/-! Actual ultra-high even derivative tail. The shifted sum enumerates
precisely all even orders N=2n with n at least the quadratic threshold. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch Filter Asymptotics Set
open scoped Topology
set_option maxHeartbeats 800000

def ultraHighActualTail (theta L : ℝ) (j : ℕ) (e : ℝ) : ℝ :=
  ∑' m : ℕ, ‖iteratedDeriv j
    (upperFormFactor (2*(ultraHighFactorialThreshold L (Real.log (1/e))+m)))
    (radialParameter theta e)‖

theorem ultrahigh_actual_tail_littleO (d : LocalBranchData)
    (hcsmall : d.c₀ < Real.sin d.theta/2) :
    ∃ L : ℝ, 1 ≤ L ∧ ∀ j : ℕ, ∀ A : ℝ,
      ultraHighActualTail d.theta L j =o[𝓝[>] 0] (fun e : ℝ => e^A) := by
  obtain ⟨C₀,D,delta,e0,hC,hD,hd,he0,he01,hbound⟩ :=
    ultrahigh_derivative_factorial_bound d hcsmall
  let L := max 1 (2*D*Real.exp 1)
  have hL : 1 ≤ L := le_max_left _ _
  have hLD : 2*D*Real.exp 1 ≤ L := le_max_right _ _
  refine ⟨L,hL,?_⟩
  intro j A
  let K : ℝ := (j.factorial:ℝ)*C₀/delta^j
  have hK : 0 < K := by dsimp only [K]; positivity
  have hb : ultraHighActualTail d.theta L j =O[𝓝[>] 0]
      (fun e : ℝ => Real.exp (((j:ℝ)+2)*Real.log (1/e))*
        ultraHighFactorialTail D L (Real.log (1/e))) := by
    apply IsBigO.of_bound K
    filter_upwards [self_mem_nhdsWithin,
      (show ∀ᶠ e : ℝ in 𝓝[>] 0, e < e0 from
        mem_nhdsWithin_of_mem_nhds (eventually_lt_nhds he0))] with e he heSmall
    have hepos : 0 < e := he
    have he1 : e ≤ 1 := heSmall.le.trans he01
    have hH : 0 ≤ Real.log (1/e) := Real.log_nonneg (by
      apply (le_div_iff₀ he).mpr
      simpa using he1)
    let H := Real.log (1/e)
    let t := ultraHighFactorialThreshold L H
    have htpos : 0 < t := by
      have hh : L*(H+1)^2 ≤ (t:ℝ) := Nat.le_ceil _
      have hp : (0:ℝ) < t := by nlinarith
      exact_mod_cast hp
    let P := (j.factorial:ℝ)*C₀*(e⁻¹)^2/(delta*e)^j
    have hP : 0 ≤ P := by dsimp only [P]; positivity
    have hp (m : ℕ) : ‖iteratedDeriv j (upperFormFactor (2*(t+m)))
        (radialParameter d.theta e)‖ ≤ P*((D*(H+1)^2)^(t+m)/((t+m).factorial:ℝ)) :=
      hbound (t+m) (by omega) j e he heSmall
    have hg : Summable (fun m : ℕ => (D*(H+1)^2)^(t+m)/((t+m).factorial:ℝ)) :=
      (Real.summable_pow_div_factorial _).comp_injective (fun _ _ h => by omega)
    have hs := (hg.mul_left P).of_nonneg_of_le (fun _ => norm_nonneg _) hp
    have hi := hs.tsum_le_tsum hp (hg.mul_left P)
    rw [tsum_mul_left] at hi
    have hpeq : P=K*Real.exp (((j:ℝ)+2)*H) := by
      have heq : Real.exp H=e⁻¹ := by
        dsimp only [H]
        rw [Real.exp_log (by positivity)]
        simp only [one_div]
      have hexp : Real.exp (((j:ℝ)+2)*H)=(e⁻¹)^(j+2) := by
        rw [show (j:ℝ)+2=((j+2:ℕ):ℝ) by push_cast; ring,Real.exp_nat_mul,heq]
      rw [hexp]
      dsimp only [P,K]
      simp only [pow_add,mul_pow,div_eq_mul_inv,mul_inv_rev,inv_pow]
      ring
    have hi' : ultraHighActualTail d.theta L j e ≤
        K*(Real.exp (((j:ℝ)+2)*H)*ultraHighFactorialTail D L H) := by
      change _ ≤ _ at hi
      rw [hpeq] at hi
      simpa only [ultraHighActualTail,ultraHighFactorialTail,t,H,mul_assoc] using hi
    have htail : 0 ≤ ultraHighActualTail d.theta L j e := tsum_nonneg (fun _ => norm_nonneg _)
    have hmajor : 0 ≤ Real.exp (((j:ℝ)+2)*H)*ultraHighFactorialTail D L H := by
      apply mul_nonneg (Real.exp_pos _).le
      exact tsum_nonneg (fun m => by positivity)
    change ‖ultraHighActualTail d.theta L j e‖ ≤
      K*‖Real.exp (((j:ℝ)+2)*H)*ultraHighFactorialTail D L H‖
    simpa only [Real.norm_eq_abs,abs_of_nonneg htail,abs_of_nonneg hmajor] using hi'
  exact hb.trans_isLittleO (ultraHighFactorialTail_radial_littleO hD.le hL hLD ((j:ℝ)+2) A)


theorem ultraHigh_cutoff_exact (L H : ℝ) (n : ℕ) :
    ultraHighFactorialThreshold L H ≤ n ↔ 2*L*(H+1)^2 ≤ (2*n:ℕ) := by
  rw [ultraHighFactorialThreshold,Nat.ceil_le]
  push_cast
  constructor <;> intro h <;> nlinarith

/-- Both clauses of the source proposition for the literal selected family.
The common cutoff is C_H=2L in the source even order N. -/
theorem proposition_ultrahigh {p : ℕ} {a b : ℤ}
    (ha : PrimeFamily.Admissible p a) (hb : PrimeFamily.Admissible p b) :
    ∃ C₀ C delta e0 L : ℝ, 0 < C₀ ∧ 0 < C ∧ 0 < delta ∧ 0 < e0 ∧ e0 ≤ 1 ∧ 1 ≤ L ∧
      (∀ n : ℕ, 0 < n → ∀ j : ℕ, ∀ e : ℝ, 0 < e → e < e0 →
        ‖iteratedDeriv j (upperFormFactor (2*n))
          (radialParameter (selectedOrderedChart ha hb).theta e)‖ ≤
          ((j.factorial:ℝ)*C₀/delta^j)*(e⁻¹)^(j+2)*
            (C*(Real.log (1/e)+1)/Real.sqrt (2*n))^(2*n)) ∧
      (∀ j : ℕ, ∀ A : ℝ,
        ultraHighActualTail (selectedOrderedChart ha hb).theta L j =o[𝓝[>] 0]
          (fun e : ℝ => e^A)) := by
  let d := selectedLocalBranchData ha hb 1 1 (by norm_num) (by norm_num)
  have hc : d.c₀ < Real.sin d.theta/2 :=
    selectedLocalBranchData_c0_small ha hb 1 1 (by norm_num) (by norm_num)
  obtain ⟨C₀,C,delta,e0,hC₀,hC,hd,he0,he01,hbound⟩ := ultrahigh_source_estimate d hc
  obtain ⟨L,hL,htail⟩ := ultrahigh_actual_tail_littleO d hc
  exact ⟨C₀,C,delta,e0,L,hC₀,hC,hd,he0,he01,hL,hbound,htail⟩

end
end IsingBulk.Tail
