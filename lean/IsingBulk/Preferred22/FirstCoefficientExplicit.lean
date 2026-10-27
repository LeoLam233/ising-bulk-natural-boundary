import IsingBulk.Preferred22.ActualFirstSingularity

/-! The explicit coefficient and radial phase in LT22 Theorem 10.4.
The coefficient is the literal complete physical coefficient, with both
reflected charts, the normalized shape period and the principal beta branch. -/
namespace IsingBulk.Preferred22
noncomputable section
open Complex Filter Set
open scoped Topology BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

def preferredLocalDenominatorDerivative (n : ℕ) (α : ℝ) : ℂ :=
  2*(n+1:ℂ)*Complex.exp (-Complex.I*(α:ℂ))

/-- Exactly 2 A_alpha (-1)^k k! D_s^k J_alpha.  The first factor two
counts the reflected charts; localAmplitude includes the separate 1+Z=2. -/
def preferredLeadingCoefficient (n : ℕ) (α : ℝ) : ℂ :=
  let k := (n+1)^2/2-1
  2*(localAmplitude (n+1) α:ℂ)*(-1:ℂ)^k*(k.factorial:ℂ)*
    preferredLocalDenominatorDerivative n α^k*sourceShapePeriod n α

theorem preferred_local_amplitude_formula (n : ℕ) (α : ℝ) :
    localAmplitude (n+1) α =
      2/(((n+1).factorial:ℝ)*(2*Real.pi)^n*2^((n+1)*n)*(Real.sin α)^((n+1)^2)) := by
  simp only [localAmplitude,Nat.add_sub_cancel_right,zpow_neg,zpow_natCast,
    div_eq_mul_inv,mul_inv_rev]
  ring

theorem preferred_equal_amplitude (n : ℕ) (α : ℝ) (hα : 0<α) (hαπ : α<Real.pi/2) :
    (2*Real.pi)*(equalAngleData α hα hαπ).K (n+1)=localAmplitude (n+1) α := by
  rw [preferred_local_amplitude_formula]
  simp only [IsingBulk.First.OrderedChartData.K,equalAngleData,Nat.add_sub_cancel_right]
  rw [pow_succ (2*Real.pi) n]
  have hpi : (2*Real.pi:ℝ)≠0 := by positivity
  field_simp

theorem preferred_equal_Ds (n : ℕ) (α : ℝ) (hα : 0<α) (hαπ : α<Real.pi/2) :
    (equalAngleData α hα hαπ).Ds (n+1)=preferredLocalDenominatorDerivative n α := by
  have hs : (Real.sin α:ℂ)≠0 := by
    exact_mod_cast (Real.sin_pos_of_pos_of_lt_pi hα (by linarith [Real.pi_pos])).ne'
  simp only [IsingBulk.First.OrderedChartData.Ds,equalAngleData,
    preferredLocalDenominatorDerivative,Nat.cast_add,Nat.cast_one]
  field_simp

theorem preferredLeadingCoefficient_eq_local (n : ℕ) (α : ℝ)
    (hα : 0<α) (hαπ : α<Real.pi/2) :
    preferredLeadingCoefficient n α =
      2*IsingBulk.First.localLeadingCoefficient (equalAngleData α hα hαπ)
        n ((n+1)^2/2-1) := by
  have hA := congrArg (fun r : ℝ => (r:ℂ)) (preferred_equal_amplitude n α hα hαπ)
  push_cast at hA
  rw [IsingBulk.First.localLeadingCoefficient,preferred_equal_Ds,
    equalAngleData_d,equalAngleData_Q]
  dsimp only [preferredLeadingCoefficient,sourceShapePeriod]
  push_cast
  rw [← hA]
  ring

theorem preferredLeadingCoefficient_ne_zero {n : ℕ} (hn : 1≤n) (he : Even (n+1))
    {α : ℝ} (hα : 0<α) (hαπ : α<Real.pi/2) :
    preferredLeadingCoefficient n α≠0 := by
  rw [preferredLeadingCoefficient_eq_local n α hα hαπ]
  exact mul_ne_zero (by norm_num)
    (IsingBulk.First.localLeadingCoefficient_ne_zero (equalAngleData α hα hαπ) hn he)

/-- Positivity of the actual beta factor, proved from its exact integration
recurrence and beta(1/2,1/2)=pi. -/
theorem preferred_beta_half_positive (k : ℕ) :
    ∃ b : ℝ,0<b ∧ Complex.betaIntegral ((k:ℂ)+1/2) (1/2)=(b:ℂ) := by
  induction k with
  | zero =>
      refine ⟨Real.pi,Real.pi_pos,?_⟩
      simpa only [Nat.cast_zero,zero_add] using IsingBulk.First.scalarBetaHalf_zero
  | succ k ih =>
      obtain ⟨b,hb,he⟩ := ih
      let c : ℝ := (2*(k:ℝ)+1)/(2*(k:ℝ)+2)*b
      refine ⟨c,by dsimp [c]; positivity,?_⟩
      have hz : (2*(k:ℂ)+2)≠0 := by
        apply Complex.ne_zero_of_re_pos
        simp
        positivity
      apply mul_left_cancel₀ hz
      rw [IsingBulk.First.scalarBetaHalf_recurrence,he]
      dsimp [c]
      push_cast
      field_simp

theorem preferred_imaginary_cpow (k : ℕ) {d : ℝ} (hd : 0<d) :
    (-Complex.I*(d:ℂ))^(-(k:ℂ)-1/2)=
      (Real.exp (-((k:ℝ)+1/2)*Real.log d):ℂ)*
        Complex.exp (((k:ℂ)+1/2)*((Real.pi:ℂ)/2)*Complex.I) := by
  have hz : -Complex.I*(d:ℂ)≠0 :=
    mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) (Complex.ofReal_ne_zero.mpr hd.ne')
  rw [Complex.cpow_def_of_ne_zero hz,
    Complex.log_mul_ofReal d hd (-Complex.I) (neg_ne_zero.mpr Complex.I_ne_zero),
    Complex.log_neg_I]
  have he : ((Real.log d:ℂ)+-((Real.pi:ℂ)/2)*Complex.I)*(-(k:ℂ)-1/2)=
      ((-((k:ℝ)+1/2)*Real.log d:ℝ):ℂ)+
        ((k:ℂ)+1/2)*((Real.pi:ℂ)/2)*Complex.I := by push_cast; ring
  rw [he,Complex.exp_add,← Complex.ofReal_exp]

theorem preferred_half_phase (k : ℕ) (hk : k%4=1) :
    (-1:ℂ)^k*Complex.exp (((k:ℂ)+1/2)*((Real.pi:ℂ)/2)*Complex.I)=
      Complex.exp (-((Real.pi:ℂ)/4)*Complex.I) := by
  have he : k=4*(k/4)+1 := by omega
  have hs : (-1:ℂ)^k= -1 := by
    rw [he,pow_add,pow_mul]
    norm_num
  rw [hs]
  have hx : ((k:ℂ)+1/2)*((Real.pi:ℂ)/2)*Complex.I=
      ((k/4:ℕ):ℂ)*(2*(Real.pi:ℂ)*Complex.I)+
        3*(Real.pi:ℂ)/4*Complex.I := by
    have hc : (k:ℂ)=4*((k/4:ℕ):ℂ)+1 := by exact_mod_cast he
    rw [hc]
    ring
  rw [hx,Complex.exp_add,Complex.exp_nat_mul,Complex.exp_two_pi_mul_I,one_pow,one_mul,
    ← Complex.exp_neg_pi_mul_I,← Complex.exp_add]
  congr 1
  ring

theorem preferred_prime_critical_mod_four {p : ℕ} (hp : p.Prime) (hp5 : 5≤p) :
    ((2*p)^2/2-1)%4=1 := by
  obtain ⟨m,hm⟩ := hp.odd_of_ne_two (by omega)
  have hk := preferred_prime_critical_derivative hp.pos
  have hpoly : (2*p)^2=2*(4*(2*m*(m+1))+1)+2 := by rw [hm]; ring
  omega

/-- The full principal-branch shape period, after the derivative sign, has
exact phase exp(-i*pi/4) at the manuscript's k congruent to one modulo four. -/
theorem preferred_shape_period_phase {n : ℕ} (hn : 1≤n) (he : Even (n+1))
    {α : ℝ} (hα : 0<α) (hαπ : α<Real.pi/2)
    (hk : ((n+1)^2/2-1)%4=1) :
    ∃ c : ℝ,0<c ∧ (-1:ℂ)^((n+1)^2/2-1)*sourceShapePeriod n α=
      (c:ℂ)*Complex.exp (-((Real.pi:ℂ)/4)*Complex.I) := by
  let k := (n+1)^2/2-1
  let Q : ℝ := 2*(n+1)
  let d := sourceCotangent α
  have hQ : 0<Q := by dsimp [Q]; positivity
  have hd : 0<d := sourceCotangent_pos hα hαπ
  obtain ⟨b,hb,hbeta⟩ := preferred_beta_half_positive k
  let c := IsingBulk.First.shapeAngularConstant n/2*(Real.sqrt Q)⁻¹*
    Real.exp (-((k:ℝ)+1/2)*Real.log d)*b
  refine ⟨c,by dsimp [c]; exact mul_pos (mul_pos (mul_pos
    (div_pos (IsingBulk.First.shapeAngularConstant_pos hn) (by norm_num))
    (inv_pos.mpr (Real.sqrt_pos.mpr hQ))) (Real.exp_pos _)) hb,?_⟩
  have hperiod := IsingBulk.First.shapePeriod_eq_beta hn
    (IsingBulk.First.source_shape_radial_exponent hn he) hQ hd
  have hQhalf : (Q:ℂ)^(-1/2:ℂ)=(Real.sqrt Q:ℂ)⁻¹ := by
    rw [show (-1/2:ℂ)= -(1/2) by ring,Complex.cpow_neg,
      IsingBulk.First.scalarPositive_cpow_half hQ]
  change (-1:ℂ)^k*IsingBulk.First.shapePeriod n k Q (-Complex.I*d)=_
  rw [hperiod,hQhalf,preferred_imaginary_cpow k hd,hbeta]
  have hphase := preferred_half_phase k hk
  have hm := congrArg (fun z : ℂ => (IsingBulk.First.shapeAngularConstant n:ℂ)/2*
    (Real.sqrt Q:ℂ)⁻¹*(Real.exp (-((k:ℝ)+1/2)*Real.log d):ℂ)*(b:ℂ)*z) hphase
  dsimp [c]
  push_cast at hm ⊢
  linear_combination hm

/-- The angular derivative D_s has the opposite phase to the radial ray. -/
theorem preferred_radial_Ds (n : ℕ) (α : ℝ) :
    Complex.exp ((α:ℂ)*Complex.I)*preferredLocalDenominatorDerivative n α=2*(n+1:ℂ) := by
  unfold preferredLocalDenominatorDerivative
  have he : Complex.exp ((α:ℂ)*Complex.I)*Complex.exp (-Complex.I*(α:ℂ))=1 := by
    rw [← Complex.exp_add,show (α:ℂ)*Complex.I+-Complex.I*(α:ℂ)=0 by ring,Complex.exp_zero]
  linear_combination 2*(n+1:ℂ)*he

/-- The precise radial phase stated after Theorem 10.4, including its
strictly positive real multiplier. -/
theorem preferred_leading_radial_phase {p : ℕ} (hp : p.Prime) (hp5 : 5≤p)
    {a : ℤ} (ha : IsingBulk.PrimeFamily.Admissible p a) :
    ∃ c : ℝ,0<c ∧
      (IsingBulk.PrimeFamily.angleRoot p a)^((2*p)^2/2-1)*
        preferredLeadingCoefficient (2*p-1) (IsingBulk.PrimeFamily.angle p a)=
      (c:ℂ)*Complex.exp (-((Real.pi:ℂ)/4)*Complex.I) := by
  let n := 2*p-1
  let α := IsingBulk.PrimeFamily.angle p a
  let k := (2*p)^2/2-1
  have hN : n+1=2*p := by dsimp [n]; omega
  have hn : 1≤n := by dsimp [n]; omega
  have he : Even (n+1) := by rw [hN]; exact ⟨p,by omega⟩
  have hk : ((n+1)^2/2-1)%4=1 := by rw [hN]; exact preferred_prime_critical_mod_four hp hp5
  obtain ⟨b,hb,hbphase⟩ := preferred_shape_period_phase hn he ha.1 ha.2 hk
  let c : ℝ := 2*localAmplitude (n+1) α*(k.factorial:ℝ)*(2*(n+1):ℝ)^k*b
  have hA : 0<localAmplitude (n+1) α := localAmplitude_pos _ ha.1 (by linarith [ha.2,Real.pi_pos])
  refine ⟨c,by dsimp [c]; positivity,?_⟩
  have hpow := congrArg (fun z : ℂ => z^k) (preferred_radial_Ds n α)
  rw [mul_pow] at hpow
  have hkN : (n+1)^2/2-1=k := by rw [hN]
  change (Complex.exp ((α:ℂ)*Complex.I))^k*preferredLeadingCoefficient n α=_
  unfold preferredLeadingCoefficient
  rw [hkN]
  have hbphase' : (-1:ℂ)^k*sourceShapePeriod n α=(b:ℂ)*
      Complex.exp (-((Real.pi:ℂ)/4)*Complex.I) := by simpa only [hkN] using hbphase
  calc
    _ = 2*(localAmplitude (n+1) α:ℂ)*(k.factorial:ℂ)*
        ((Complex.exp ((α:ℂ)*Complex.I))^k*preferredLocalDenominatorDerivative n α^k)*
        ((-1:ℂ)^k*sourceShapePeriod n α) := by ring
    _ = _ := by rw [hpow,hbphase']; dsimp [c]; push_cast; ring

/-- The exact explicit coefficient is the limit of the kth derivative of
the complete coefficient. The actual complete remainder has already been
proved and its logarithmic bound is lower order after multiplication by sqrt eps. -/
theorem preferred_actual_first_explicit_limit (d : PreferredBranchData)
    {p : ℕ} (hp : p.Prime) (hp5 : 5≤p) {a : ℤ}
    (ha : IsingBulk.PrimeFamily.Admissible p a)
    (hα : d.alpha=IsingBulk.PrimeFamily.angle p a) (n : ℕ) (hN : n+1=2*p) :
    preferredLeadingCoefficient n d.alpha≠0 ∧
      Tendsto (fun ε : ℝ => Real.sqrt ε • iteratedDeriv ((n+1)^2/2-1)
        (coefficient (n+1)) ((1+(ε:ℂ))*Complex.exp ((d.alpha:ℂ)*Complex.I)))
        (𝓝[>] 0) (𝓝 (preferredLeadingCoefficient n d.alpha)) := by
  have hn : 1≤n := by omega
  have he : Even (n+1) := ⟨p,by omega⟩
  have hres : Complex.exp (-(n+1:ℂ)*(d.alpha:ℂ)*Complex.I)=1 := by
    have hc : (n+1:ℂ)=((2*p:ℕ):ℂ) := by exact_mod_cast hN
    rw [hc,hα]
    exact preferred_prime_first_resonance hp.pos a
  obtain ⟨_hΛ,R,hR,hasym⟩ :=
    localizedPhysical_source_asymptotic hn he d.alpha d.alpha_pos d.alpha_lt hres
  obtain ⟨ρ,ε₀,hρ,hρR,hε₀,hlog⟩ :=
    preferred_actual_first_remainder_log d hp hp5 ha hα n hN R hR
  let k := (n+1)^2/2-1
  let Λ := IsingBulk.First.localLeadingCoefficient
    (equalAngleData d.alpha d.alpha_pos d.alpha_lt) n k
  let path := fun ε : ℝ => (1+(ε:ℂ))*Complex.exp ((d.alpha:ℂ)*Complex.I)
  let f := fun ε : ℝ => iteratedDeriv k
    (localizedPhysicalIntegral d.alpha (preferredShapeCutoff (n := n) ρ)) (path ε)
  let g := fun ε : ℝ => iteratedDeriv k (coefficient (n+1)) (path ε)-2*f ε
  have hf : Tendsto (fun ε : ℝ => Real.sqrt ε • f ε) (𝓝[>] 0) (𝓝 Λ) := by
    apply preferred_local_asymptotic_limit
    exact hasym (preferredShapeCutoff ρ) (preferredShapeCutoff_smooth ρ).continuous
      (preferredShapeCutoff_zero ρ) (preferredShapeCutoff_bound ρ)
      (fun x hx => (preferredShapeCutoff_support hρ x hx).trans_le hρR)
  obtain ⟨C,_hC,hbound⟩ := hlog k
  have hg : Tendsto (fun ε : ℝ => Real.sqrt ε • g ε) (𝓝[>] 0) (𝓝 0) := by
    apply sqrt_log_bound_tendsto_zero (C := 0) (D := C) hε₀
    intro ε hε hεr
    simpa only [zero_add,g,f,path,IsingBulk.Branch.radialParameter,
      Complex.ofReal_add,Complex.ofReal_one] using hbound ε hε hεr
  refine ⟨preferredLeadingCoefficient_ne_zero hn he d.alpha_pos d.alpha_lt,?_⟩
  rw [preferredLeadingCoefficient_eq_local n d.alpha d.alpha_pos d.alpha_lt]
  have hh := (hf.const_mul (2:ℂ)).add hg
  simp only [add_zero] at hh
  convert hh using 1
  funext ε
  simp only [Complex.real_smul,g,f,path,k]
  ring

/-- The source-facing explicit first singular coefficient at every
admissible prime root, including p=5 and p=7. -/
theorem preferred_prime_first_explicit_limit {p : ℕ} (hp : p.Prime) (hp5 : 5≤p)
    {a : ℤ} (ha : IsingBulk.PrimeFamily.Admissible p a) :
    preferredLeadingCoefficient (2*p-1) (IsingBulk.PrimeFamily.angle p a)≠0 ∧
      Tendsto (fun ε : ℝ => Real.sqrt ε • iteratedDeriv ((2*p)^2/2-1)
        (coefficient (2*p)) ((1+(ε:ℂ))*IsingBulk.PrimeFamily.angleRoot p a))
        (𝓝[>] 0) (𝓝 (preferredLeadingCoefficient (2*p-1) (IsingBulk.PrimeFamily.angle p a))) := by
  have hN : 2*p-1+1=2*p := by omega
  have hh := preferred_actual_first_explicit_limit (preferredPrimeBranchData ha)
    hp hp5 ha rfl (2*p-1) hN
  simpa only [hN,preferredPrimeBranchData,preferredBranchAt,IsingBulk.PrimeFamily.angleRoot] using hh

end
end IsingBulk.Preferred22
