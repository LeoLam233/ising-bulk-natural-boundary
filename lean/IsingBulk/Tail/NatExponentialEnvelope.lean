import IsingBulk.Tail.IntermediateWindow

namespace IsingBulk.Tail
noncomputable section

/-- A scalar envelope with its constant chosen before particle number. -/
def NatExponentialEnvelope (k : ℕ) (f : ℕ → ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 1 ≤ N → |f N| ≤ Real.exp (C*(N:ℝ)^k)

namespace NatExponentialEnvelope

theorem const (k : ℕ) (a : ℝ) : NatExponentialEnvelope k (fun _ => a) := by
  refine ⟨|a|,abs_nonneg _,?_⟩
  intro N hN
  have hn : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hp : 1 ≤ (N:ℝ)^k := one_le_pow₀ hn
  exact (by linarith [Real.add_one_le_exp |a|] : |a| ≤ Real.exp |a|).trans
    (Real.exp_le_exp.mpr (le_mul_of_one_le_right (abs_nonneg _) hp))

theorem id : NatExponentialEnvelope 1 (fun N => (N:ℝ)) := by
  refine ⟨1,by norm_num,?_⟩
  intro N _
  simp only [pow_one,one_mul,abs_of_nonneg (Nat.cast_nonneg N (α := ℝ))]
  linarith [Real.add_one_le_exp (N:ℝ)]

theorem mono_degree {k l : ℕ} {f : ℕ → ℝ} (hf : NatExponentialEnvelope k f) (hkl : k ≤ l) :
    NatExponentialEnvelope l f := by
  obtain ⟨C,hC,hf⟩ := hf
  refine ⟨C,hC,?_⟩
  intro N hN
  apply (hf N hN).trans
  exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left
    (pow_le_pow_right₀ (by exact_mod_cast hN : (1:ℝ) ≤ N) hkl) hC)

theorem mono_abs {k : ℕ} {f g : ℕ → ℝ} (hg : NatExponentialEnvelope k g)
    (hfg : ∀ N : ℕ, 1 ≤ N → |f N| ≤ |g N|) : NatExponentialEnvelope k f := by
  obtain ⟨C,hC,hg⟩ := hg
  exact ⟨C,hC,fun N hN => (hfg N hN).trans (hg N hN)⟩

theorem mul {k : ℕ} {f g : ℕ → ℝ} (hf : NatExponentialEnvelope k f)
    (hg : NatExponentialEnvelope k g) : NatExponentialEnvelope k (fun N => f N*g N) := by
  obtain ⟨C,hC,hf⟩ := hf
  obtain ⟨D,hD,hg⟩ := hg
  refine ⟨C+D,add_nonneg hC hD,?_⟩
  intro N hN
  rw [abs_mul]
  have hh := mul_le_mul (hf N hN) (hg N hN) (abs_nonneg _) (Real.exp_nonneg _)
  simpa only [← Real.exp_add,← add_mul] using hh

theorem add {k : ℕ} {f g : ℕ → ℝ} (hf : NatExponentialEnvelope k f)
    (hg : NatExponentialEnvelope k g) : NatExponentialEnvelope k (fun N => f N+g N) := by
  obtain ⟨C,hC,hf⟩ := hf
  obtain ⟨D,hD,hg⟩ := hg
  refine ⟨C+D+1,by positivity,?_⟩
  intro N hN
  have hn : 1 ≤ (N:ℝ)^k := one_le_pow₀ (by exact_mod_cast hN)
  have hp : 0 ≤ (N:ℝ)^k := pow_nonneg (Nat.cast_nonneg _) _
  have h₁ : C*(N:ℝ)^k ≤ (C+D)*(N:ℝ)^k := by nlinarith
  have h₂ : D*(N:ℝ)^k ≤ (C+D)*(N:ℝ)^k := by nlinarith
  have htwo : 2 ≤ Real.exp ((N:ℝ)^k) := by linarith [Real.add_one_le_exp ((N:ℝ)^k)]
  calc
    _ ≤ |f N|+|g N| := abs_add_le _ _
    _ ≤ Real.exp (C*(N:ℝ)^k)+Real.exp (D*(N:ℝ)^k) := add_le_add (hf N hN) (hg N hN)
    _ ≤ 2*Real.exp ((C+D)*(N:ℝ)^k) := by nlinarith [Real.exp_le_exp.mpr h₁,Real.exp_le_exp.mpr h₂]
    _ ≤ Real.exp ((N:ℝ)^k)*Real.exp ((C+D)*(N:ℝ)^k) := mul_le_mul_of_nonneg_right htwo (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem pow {k : ℕ} {f : ℕ → ℝ} (hf : NatExponentialEnvelope k f) (m : ℕ) :
    NatExponentialEnvelope k (fun N => f N^m) := by
  obtain ⟨C,hC,hf⟩ := hf
  refine ⟨(m:ℝ)*C,by positivity,?_⟩
  intro N hN
  rw [abs_pow]
  have hh := pow_le_pow_left₀ (abs_nonneg _) (hf N hN) m
  simpa only [← Real.exp_nat_mul,mul_assoc] using hh

theorem pow_particle {k : ℕ} {f : ℕ → ℝ} (hf : NatExponentialEnvelope k f) :
    NatExponentialEnvelope (k+1) (fun N => f N^N) := by
  obtain ⟨C,hC,hf⟩ := hf
  refine ⟨C,hC,?_⟩
  intro N hN
  rw [abs_pow]
  apply (pow_le_pow_left₀ (abs_nonneg _) (hf N hN) N).trans_eq
  rw [← Real.exp_nat_mul,pow_succ]
  congr 1
  ring

theorem exp_monomial (k : ℕ) (C : ℝ) :
    NatExponentialEnvelope k (fun N => Real.exp (C*(N:ℝ)^k)) := by
  refine ⟨max 0 C,le_max_left _ _,?_⟩
  intro N _
  rw [abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_max_right _ _) (pow_nonneg (Nat.cast_nonneg _) _))

theorem const_pow {k : ℕ} (a : ℝ) (m : ℕ → ℕ) (hm : ∀ N : ℕ, 1 ≤ N → m N ≤ N^k) :
    NatExponentialEnvelope k (fun N => a^(m N)) := by
  refine ⟨|a|,abs_nonneg _,?_⟩
  intro N hN
  rw [abs_pow]
  have ha : |a| ≤ Real.exp |a| := by linarith [Real.add_one_le_exp |a|]
  apply (pow_le_pow_left₀ (abs_nonneg _) ha (m N)).trans
  rw [← Real.exp_nat_mul]
  apply Real.exp_le_exp.mpr
  have he : ((m N:ℕ):ℝ) ≤ (N:ℝ)^k := by exact_mod_cast hm N hN
  nlinarith [abs_nonneg a]

end NatExponentialEnvelope
end
end IsingBulk.Tail
