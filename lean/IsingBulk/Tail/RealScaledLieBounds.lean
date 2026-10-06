import IsingBulk.Tail.RealScaledJetBounds

/-! Exact loss of two scale degrees for a Lie step with a simple-pole
vector field. All jets are real joint jets; only the source parameter is
required to be holomorphic. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.Lie Set Filter
open scoped Topology ContDiff BigOperators
set_option maxHeartbeats 1500000

theorem parameterSmooth_lieStep_real {n : ℕ} {Ω : Set (ℂ × AngularSpace n)}
    (V : ℂ → AngularSpace n → Fin (n+1) → ℂ) (A : ℂ → AngularSpace n → ℂ)
    (hV : ∀ i, ParameterSmoothOn Ω (fun s x => V s x i))
    (hA : ParameterSmoothOn Ω A) {p : ℂ × AngularSpace n} (hp : p ∈ Ω) :
    lieStep V A p.1 p.2 =
      realDirection (Function.uncurry A) (1,0) p -
        ∑ i, realDirection (fun q => V q.1 q.2 i*A q.1 q.2) (0,Pi.single i 1) p := by
  unfold lieStep
  congr 1
  · have hCR := differentiableAt_complex_iff_differentiableAt_real.mp (hA p hp).2
    rw [complexOfReal_deriv hCR.1 hCR.2]
    exact parameterSlice_fderiv (Function.uncurry A) p
      ((hA p hp).1.differentiableAt (by simp)) 1
  · apply Finset.sum_congr rfl
    intro i _
    exact angularSlice_fderiv (fun q => V q.1 q.2 i*A q.1 q.2) p
      (((hV i).mul hA p hp).1.differentiableAt (by simp)) (Pi.single i 1)

theorem realScaledJetBound_lieStep {n : ℕ} {Ω : Set (ℂ × AngularSpace n)}
    (hΩ : IsOpen Ω) (V : ℂ → AngularSpace n → Fin (n+1) → ℂ)
    (A : ℂ → AngularSpace n → ℂ)
    (hV : ∀ i, ParameterSmoothOn Ω (fun s x => V s x i))
    (hA : ParameterSmoothOn Ω A) {p : ℂ × AngularSpace n} (hp : p ∈ Ω)
    {J : ℕ} {ρ B C : ℝ} {a : ℤ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hB : 0 ≤ B)
    (hVb : ∀ i, RealScaledJetBound (fun q => V q.1 q.2 i) p (J+1) ρ B (-1))
    (hAb : RealScaledJetBound (Function.uncurry A) p (J+1) ρ C a) :
    RealScaledJetBound (Function.uncurry (lieStep V A)) p J ρ
      (C*(1+(n+1:ℕ)*2^(J+1)*B)) (a-2) := by
  have hparam := (hAb.direction hρ (1,0) (by simp [Prod.norm_def])).lower_degree hρ hρ1
  have hang (i : Fin (n+1)) := ((hVb i).mul hAb hρ).direction hρ
    (0,Pi.single i 1) (by simp [Prod.norm_def,Pi.norm_single])
  have hs := RealScaledJetBound.sum hang
    (show 0 ≤ (2:ℝ)^(J+1)*B*C by have := hAb.nonneg; positivity)
  have hc : C+(n+1:ℕ)*(2^(J+1)*B*C)=C*(1+(n+1:ℕ)*2^(J+1)*B) := by ring
  have ha : a-1-1=a-2 := by ring
  have hva : (-1:ℤ)+a-1=a-2 := by ring
  rw [hva] at hs
  rw [ha] at hparam
  have hb := hparam.sub hs
  rw [hc] at hb
  apply hb.congr
  filter_upwards [hΩ.mem_nhds hp] with q hq
  exact parameterSmooth_lieStep_real V A hV hA hq

theorem realScaledJetBound_iterate_lieStep {n : ℕ} {Ω : Set (ℂ × AngularSpace n)}
    (hΩ : IsOpen Ω) (V : ℂ → AngularSpace n → Fin (n+1) → ℂ)
    (A : ℂ → AngularSpace n → ℂ)
    (hV : ∀ i, ParameterSmoothOn Ω (fun s x => V s x i))
    (hA : ParameterSmoothOn Ω A) {p : ℂ × AngularSpace n} (hp : p ∈ Ω)
    {L : ℕ} {ρ B C K : ℝ} {a : ℤ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hB : 0 ≤ B)
    (hK : 1+(n+1:ℕ)*2^L*B ≤ K)
    (hVb : ∀ i, RealScaledJetBound (fun q => V q.1 q.2 i) p L ρ B (-1))
    (hAb : RealScaledJetBound (Function.uncurry A) p L ρ C a) :
    ∀ k ≤ L, RealScaledJetBound (Function.uncurry ((lieStep V)^[k] A)) p (L-k)
      ρ (C*K^k) (a-2*(k:ℤ)) := by
  have hK0 : 0 ≤ K := by
    have : 0 ≤ (n+1:ℕ)*(2:ℝ)^L*B := by positivity
    linarith
  intro k
  induction k with
  | zero => intro _; simpa using hAb
  | succ k ih =>
    intro hk
    have hprev := ih (by omega)
    have hord : L-k=(L-(k+1))+1 := by omega
    rw [hord] at hprev
    have hv' (i : Fin (n+1)) := (hVb i).mono hρ
      (show L-(k+1)+1 ≤ L by omega) le_rfl
    have hstep := realScaledJetBound_lieStep hΩ V ((lieStep V)^[k] A) hV
      (hA.iterate_lieStep hΩ V A hV k) hp hρ hρ1 hB hv' hprev
    have he : a-2*(k:ℤ)-2=a-2*((k+1:ℕ):ℤ) := by push_cast; ring
    rw [he] at hstep
    rw [Function.iterate_succ_apply']
    apply hstep.mono hρ le_rfl
    have hcoef : 1+(n+1:ℕ)*(2:ℝ)^(L-(k+1)+1)*B ≤ K := by
      have hpow : (2:ℝ)^(L-(k+1)+1) ≤ 2^L :=
        pow_le_pow_right₀ (by norm_num) (by omega)
      have hmul := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hpow (Nat.cast_nonneg (α := ℝ) (n+1))) hB
      linarith
    calc
      _ ≤ (C*K^k)*K := mul_le_mul_of_nonneg_left hcoef
        (mul_nonneg hAb.nonneg (pow_nonneg hK0 _))
      _ = C*K^(k+1) := by rw [pow_succ]; ring

end
end IsingBulk.Tail
