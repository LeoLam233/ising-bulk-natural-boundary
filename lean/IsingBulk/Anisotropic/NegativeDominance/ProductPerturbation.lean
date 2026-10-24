import IsingBulk.Anisotropic.NegativeDominance.QuantitativeOddMomentum

namespace IsingBulk.Anisotropic.NegativeDominance
noncomputable section
open scoped BigOperators

theorem norm_prod_sub_prod_le_card {ι : Type*} (s : Finset ι) (z w : ι → ℂ)
    {R d : ℝ} (hR : 1≤R) (hd : 0≤d)
    (hz : ∀ i∈s, ‖z i‖≤R) (hw : ∀ i∈s, ‖w i‖≤R)
    (hdiff : ∀ i∈s, ‖z i-w i‖≤d) :
    ‖(∏ i∈s,z i)-(∏ i∈s,w i)‖≤(s.card : ℝ)*d*R^s.card := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have hzs := fun i hi => hz i (Finset.mem_insert_of_mem hi)
    have hws := fun i hi => hw i (Finset.mem_insert_of_mem hi)
    have hds := fun i hi => hdiff i (Finset.mem_insert_of_mem hi)
    have hs := ih hzs hws hds
    have hza := hz a (Finset.mem_insert_self a s)
    have hda := hdiff a (Finset.mem_insert_self a s)
    have hR0 : 0≤R := le_trans zero_le_one hR
    have hwp : ‖∏ i∈s,w i‖≤R^s.card := by
      rw [norm_prod]
      calc
        ∏ i∈s,‖w i‖ ≤ ∏ _i∈s,R := Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) hws
        _ = R^s.card := by simp
    rw [Finset.prod_insert ha,Finset.prod_insert ha,Finset.card_insert_of_notMem ha,Nat.cast_add,Nat.cast_one]
    calc
      ‖z a*(∏ i∈s,z i)-w a*(∏ i∈s,w i)‖ =
          ‖z a*((∏ i∈s,z i)-(∏ i∈s,w i))+(z a-w a)*(∏ i∈s,w i)‖ := by congr 1; ring
      _ ≤ ‖z a‖*‖(∏ i∈s,z i)-(∏ i∈s,w i)‖+‖z a-w a‖*‖∏ i∈s,w i‖ := by
        simpa only [norm_mul] using norm_add_le
          (z a*((∏ i∈s,z i)-(∏ i∈s,w i))) ((z a-w a)*(∏ i∈s,w i))
      _ ≤ R*((s.card : ℝ)*d*R^s.card)+d*R^s.card :=
        add_le_add (mul_le_mul hza hs (norm_nonneg _) hR0) (mul_le_mul hda hwp (norm_nonneg _) hd)
      _ = (s.card : ℝ)*d*R^(s.card+1)+d*R^s.card := by rw [pow_succ]; ring
      _ ≤ (s.card : ℝ)*d*R^(s.card+1)+d*R^(s.card+1) := by
        gcongr
        omega
      _ = ((s.card : ℝ)+1)*d*R^(s.card+1) := by ring

/-- Product perturbation is linear in N on the scale N*d≤1. -/
theorem norm_prod_perturbation_linear {N : ℕ} (z w : Fin N → ℂ) {d : ℝ}
    (hd : 0≤d) (hNd : (N : ℝ)*d≤1)
    (hw : ∀ i, ‖w i‖≤1) (hdiff : ∀ i, ‖z i-w i‖≤d) :
    ‖(∏ i,z i)-(∏ i,w i)‖≤Real.exp 1*(N : ℝ)*d := by
  have hz (i : Fin N) : ‖z i‖≤1+d := by
    have hh := norm_add_le (z i-w i) (w i)
    rw [sub_add_cancel] at hh
    linarith [hw i,hdiff i]
  have hh := norm_prod_sub_prod_le_card Finset.univ z w (show 1≤1+d by linarith) hd
    (fun i _ => hz i) (fun i _ => (hw i).trans (by linarith)) (fun i _ => hdiff i)
  simp only [Finset.card_univ,Fintype.card_fin] at hh
  have hpow : (1+d)^N≤Real.exp 1 := by
    calc
      (1+d)^N ≤ (Real.exp d)^N := pow_le_pow_left₀ (by positivity)
        (by simpa only [add_comm] using Real.add_one_le_exp d) N
      _ = Real.exp ((N : ℝ)*d) := (Real.exp_nat_mul d N).symm
      _ ≤ Real.exp 1 := Real.exp_le_exp.mpr hNd
  have hm := mul_le_mul_of_nonneg_left hpow (show 0≤(N : ℝ)*d by positivity)
  nlinarith

end
end IsingBulk.Anisotropic.NegativeDominance
