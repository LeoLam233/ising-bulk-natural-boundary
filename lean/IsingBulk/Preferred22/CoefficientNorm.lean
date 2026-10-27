import IsingBulk.Preferred22.CoefficientTermCount

/-! Quantitative monomial estimates with the exact physical normalizer on
the unique seed. The only analytic premises are bounds for the original
seed, collective field and regular kernel frame jets. -/
namespace IsingBulk.Preferred22
noncomputable section
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

theorem preferredTermValue_normalized_bound {N : ℕ} (τ : ℝ) (η p m r : ℝ → ℝ)
    (s : ℂ) (θ : Fin N → ℝ) (Z : ℂ) (R d : ℝ) (hR : 0≤R) (hd : 0<d)
    (L M : ℕ) (T : PreferredCoefficientTerm N)
    (hA : ∀ a∈T,
      ‖Z^preferredAtomSeedCount a*preferredAtomValue τ η p m r a s θ‖≤
        R^(N*preferredAtomSeedCount a+1)*(N:ℝ)^(L*preferredAtomSeedCount a+M)/d^preferredAtomLoss a) :
    ‖Z^preferredTermSeedCount T*preferredTermValue τ η p m r T s θ‖≤
      R^(N*preferredTermSeedCount T+T.length)*(N:ℝ)^(L*preferredTermSeedCount T+M*T.length)/
        d^preferredTermLoss T := by
  induction T with
  | nil => simp [preferredTermSeedCount,preferredTermValue,preferredTermLoss]
  | cons a T ih =>
    have hh := hA a (List.mem_cons_self ..)
    have ht := ih (fun b hb => hA b (List.mem_cons_of_mem _ hb))
    have he : Z^preferredTermSeedCount (a::T)*preferredTermValue τ η p m r (a::T) s θ=
        (Z^preferredAtomSeedCount a*preferredAtomValue τ η p m r a s θ)*
          (Z^preferredTermSeedCount T*preferredTermValue τ η p m r T s θ) := by
      simp only [preferredTermSeedCount,preferredTermValue,List.map_cons,List.sum_cons,List.prod_cons,pow_add]
      ring
    rw [he,norm_mul]
    apply (mul_le_mul hh ht (norm_nonneg _) (by positivity)).trans
    have hpow₁ : (N*preferredAtomSeedCount a+1)+(N*preferredTermSeedCount T+T.length)=
        N*preferredTermSeedCount (a::T)+(a::T).length := by
      simp only [preferredTermSeedCount,List.map_cons,List.sum_cons,List.length_cons]
      ring
    have hpow₂ : (L*preferredAtomSeedCount a+M)+(L*preferredTermSeedCount T+M*T.length)=
        L*preferredTermSeedCount (a::T)+M*(a::T).length := by
      simp only [preferredTermSeedCount,List.map_cons,List.sum_cons,List.length_cons]
      ring
    have hpow₃ : preferredAtomLoss a+preferredTermLoss T=preferredTermLoss (a::T) := rfl
    apply le_of_eq
    rw [←hpow₁,←hpow₂,←hpow₃,pow_add,pow_add,pow_add]
    ring

theorem inverse_power_loss_bound (d D : ℝ) (hd : 0<d) (hdD : d≤D) (hD : 1≤D)
    (a h k : ℕ) (hah : a≤h) (hhk : h≤k) : 1/d^a≤D^k/d^h := by
  have he : a+(h-a)=h := Nat.add_sub_of_le hah
  have hp : d^(h-a)≤D^k := (pow_le_pow_left₀ hd.le hdD _).trans
    (pow_le_pow_right₀ hD ((Nat.sub_le _ _).trans hhk))
  calc
    1/d^a = d^(h-a)/d^h := by
      have hpw : d^h=d^a*d^(h-a) := by rw [←pow_add,he]
      rw [hpw]
      field_simp [hd.ne']
    _ ≤ _ := div_le_div_of_nonneg_right hp (pow_nonneg hd.le _)

theorem norm_list_sum_map_bound {α : Type*} (L : List α) (f : α → ℂ) (C : ℝ)
    (h : ∀ a∈L, ‖f a‖≤C) : ‖(L.map f).sum‖≤(L.length:ℝ)*C := by
  induction L with
  | nil => simp
  | cons a L ih =>
    have ha := h a (List.mem_cons_self ..)
    have ht := ih (fun b hb => h b (List.mem_cons_of_mem _ hb))
    simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.cast_add,Nat.cast_one]
    exact (norm_add_le _ _).trans (by nlinarith)

/-- The normalizer stays on the unique seed atom. All other atoms have
only fixed-order polynomial particle-count bounds. -/
theorem preferredAtomValue_bound_of_frame_bounds {N : ℕ} (hN : 0<N)
    (τ : ℝ) (η p m r : ℝ → ℝ) (s : ℂ) (θ : Fin N → ℝ)
    (Z : ℂ) (R d : ℝ) (hR : 1≤R) (_hd : 0<d) (L M j : ℕ)
    (hseed : ∀ xs : List (Option (Fin N)), xs.length≤j →
      ‖Z*preferredFrameJet τ p m (preferredRegularSeedCoefficient τ η p m r) xs s θ‖≤R^N*(N:ℝ)^L)
    (hB : ∀ i (xs : List (Option (Fin N))), xs.length≤j →
      ‖preferredFrameJet τ p m
        (fun t x => preferredResidualCollective t (preferredSourceCoordinate τ p m t x) i) xs s θ‖≤
          R*(N:ℝ)^M/d^(1+preferredCoordinateJetOrder xs))
    (hK : ∀ (ij : Fin N × Fin N) (xs : List (Option (Fin N))), xs.length≤j →
      ‖preferredFrameJet τ p m
        (fun t x => preferredSourceRegularKernel τ p m t x ij.1 ij.2) xs s θ‖≤R)
    (a : PreferredCoefficientAtom N) (ha : preferredAtomJetOrder a≤j) :
    ‖Z^preferredAtomSeedCount a*preferredAtomValue τ η p m r a s θ‖≤
      R^(N*preferredAtomSeedCount a+1)*(N:ℝ)^(L*preferredAtomSeedCount a+M)/d^preferredAtomLoss a := by
  have hn : (1:ℝ)≤N := by exact_mod_cast Nat.succ_le_iff.mpr hN
  have hRn : 0≤R := le_trans (by norm_num) hR
  have hNM : 1≤(N:ℝ)^M := one_le_pow₀ hn
  cases a with
  | seed xs =>
    simp only [preferredAtomSeedCount,preferredAtomValue,preferredAtomLoss,Nat.mul_one,
      pow_one,pow_zero,div_one]
    apply (hseed xs ha).trans
    exact mul_le_mul (pow_le_pow_right₀ hR (Nat.le_succ N))
      (pow_le_pow_right₀ hn (Nat.le_add_right L M)) (by positivity) (by positivity)
  | collective i xs =>
    simpa only [preferredAtomSeedCount,preferredAtomValue,preferredAtomLoss,Nat.mul_zero,
      zero_add,pow_zero,pow_one,one_mul] using hB i xs ha
  | kernel ij xs =>
    simp only [preferredAtomSeedCount,preferredAtomValue,preferredAtomLoss,Nat.mul_zero,
      zero_add,pow_zero,pow_one,one_mul,div_one]
    exact (hK ij xs ha).trans (le_mul_of_one_le_right hRn hNM)

/-- Every explicit actual coefficient term has the manuscript loss. This
is a proved norm estimate from original-factor frame bounds, not an assumed
bound on recursively generated coefficients. -/
theorem preferredCoefficientTerm_bound {N : ℕ} (hN : 0<N)
    (τ : ℝ) (η p m r : ℝ → ℝ) (s : ℂ) (θ : Fin N → ℝ) (Z : ℂ)
    (R d D : ℝ) (hR : 1≤R) (hd : 0<d) (hdD : d≤D) (hD : 1≤D)
    (L M j : ℕ) (w : PreferredMarkedWord N j) (T : PreferredCoefficientTerm N)
    (hT : T∈preferredCoefficientTerms j w)
    (hA : ∀ a∈T,
      ‖Z^preferredAtomSeedCount a*preferredAtomValue τ η p m r a s θ‖≤
        R^(N*preferredAtomSeedCount a+1)*(N:ℝ)^(L*preferredAtomSeedCount a+M)/d^preferredAtomLoss a) :
    ‖Z*preferredTermValue τ η p m r T s θ‖≤
      R^(N+2*j+1)*(N:ℝ)^(L+M*(2*j+1))*D^(2*j)/d^(preferredWordLoss j w) := by
  have hwell := preferredCoefficientTerms_wellFormed j w T hT
  have hn : (1:ℝ)≤N := by exact_mod_cast Nat.succ_le_iff.mpr hN
  have hRn : 0≤R := le_trans (by norm_num) hR
  have hbase := preferredTermValue_normalized_bound τ η p m r s θ Z R d hRn hd L M T hA
  simp only [hwell.seed,pow_one,Nat.mul_one] at hbase
  have hloss : preferredWordLoss j w≤2*j := by have := preferredWordLoss_budget j w; omega
  have hdeg := inverse_power_loss_bound d D hd hdD hD _ _ (2*j) hwell.loss hloss
  have hRp : R^(N+T.length)≤R^(N+2*j+1) := pow_le_pow_right₀ hR (by have := hwell.length; omega)
  have hNp : (N:ℝ)^(L+M*T.length)≤(N:ℝ)^(L+M*(2*j+1)) :=
    pow_le_pow_right₀ hn (Nat.add_le_add_left (Nat.mul_le_mul_left M hwell.length) L)
  calc
    _ ≤ R^(N+T.length)*(N:ℝ)^(L+M*T.length)/d^preferredTermLoss T := hbase
    _ ≤ R^(N+2*j+1)*(N:ℝ)^(L+M*(2*j+1)) * (D^(2*j)/d^preferredWordLoss j w) := by
      rw [div_eq_mul_inv,←one_div]
      exact mul_le_mul (mul_le_mul hRp hNp (by positivity) (by positivity)) hdeg
        (by positivity) (by positivity)
    _ = _ := by ring

/-- Summing the explicit coefficient terms preserves an exponential base
independent of N and only a fixed-order polynomial in N. The exact loss is
the actual word loss, whose sum with its marked-minor size is 2j. -/
theorem preferredCoefficientTerms_sum_bound {N : ℕ} (hN : 0<N)
    (τ : ℝ) (η p m r : ℝ → ℝ) (s : ℂ) (θ : Fin N → ℝ) (Z : ℂ)
    (R d D : ℝ) (hR : 1≤R) (hd : 0<d) (hdD : d≤D) (hD : 1≤D)
    (L M j : ℕ) (w : PreferredMarkedWord N j)
    (hseed : ∀ xs : List (Option (Fin N)), xs.length≤j →
      ‖Z*preferredFrameJet τ p m (preferredRegularSeedCoefficient τ η p m r) xs s θ‖≤R^N*(N:ℝ)^L)
    (hB : ∀ i (xs : List (Option (Fin N))), xs.length≤j →
      ‖preferredFrameJet τ p m
        (fun t x => preferredResidualCollective t (preferredSourceCoordinate τ p m t x) i) xs s θ‖≤
          R*(N:ℝ)^M/d^(1+preferredCoordinateJetOrder xs))
    (hK : ∀ (ij : Fin N × Fin N) (xs : List (Option (Fin N))), xs.length≤j →
      ‖preferredFrameJet τ p m
        (fun t x => preferredSourceRegularKernel τ p m t x ij.1 ij.2) xs s θ‖≤R) :
    ‖Z*((preferredCoefficientTerms j w).map
      (fun T => preferredTermValue τ η p m r T s θ)).sum‖≤
        ((preferredCoefficientCountConstant j:ℝ)*R^(2*j+2)*D^(2*j))^N *
          (N:ℝ)^(L+M*(2*j+1)+j)/d^(preferredWordLoss j w) := by
  let A := (preferredCoefficientCountConstant j:ℝ)
  have hA : 1≤A := by
    dsimp only [A]
    exact_mod_cast Nat.succ_le_iff.mpr (preferredCoefficientCountConstant_pos j)
  have hRn : 0≤R := le_trans (by norm_num) hR
  have hDn : 0≤D := le_trans (by norm_num) hD
  have hn : (1:ℝ)≤N := by exact_mod_cast Nat.succ_le_iff.mpr hN
  let H := R^(N+2*j+1)*(N:ℝ)^(L+M*(2*j+1))*D^(2*j)/d^(preferredWordLoss j w)
  have hH : 0≤H := by dsimp [H]; positivity
  have hterm (T : PreferredCoefficientTerm N) (hT : T∈preferredCoefficientTerms j w) :
      ‖Z*preferredTermValue τ η p m r T s θ‖≤H := by
    apply preferredCoefficientTerm_bound hN τ η p m r s θ Z R d D hR hd hdD hD L M j w T hT
    intro a ha
    exact preferredAtomValue_bound_of_frame_bounds hN τ η p m r s θ Z R d hR hd L M j
      hseed hB hK a ((preferredCoefficientTerms_wellFormed j w T hT).order a ha)
  have hcount : ((preferredCoefficientTerms j w).length:ℝ)≤A*(N:ℝ)^j := by
    dsimp only [A]
    exact_mod_cast preferredCoefficientTerms_count hN j w
  have hconst : A*R^(N+2*j+1)*D^(2*j)≤(A*R^(2*j+2)*D^(2*j))^N := by
    have hAp : A≤A^N := by simpa only [pow_one] using pow_le_pow_right₀ hA (Nat.succ_le_iff.mpr hN)
    have hRp : R^(N+2*j+1)≤(R^(2*j+2))^N := by
      rw [←pow_mul]
      apply pow_le_pow_right₀ hR
      nlinarith
    have hDp : D^(2*j)≤(D^(2*j))^N := by
      simpa only [pow_one] using pow_le_pow_right₀ (one_le_pow₀ hD) (Nat.succ_le_iff.mpr hN)
    rw [mul_pow,mul_pow]
    exact mul_le_mul (mul_le_mul hAp hRp (by positivity) (by positivity)) hDp
      (by positivity) (by positivity)
  calc
    _ = ‖((preferredCoefficientTerms j w).map
        (fun T => Z*preferredTermValue τ η p m r T s θ)).sum‖ := by rw [List.sum_map_mul_left]
    _ ≤ ((preferredCoefficientTerms j w).length:ℝ)*H := norm_list_sum_map_bound _ _ H hterm
    _ ≤ (A*(N:ℝ)^j)*H := mul_le_mul_of_nonneg_right hcount hH
    _ = (A*R^(N+2*j+1)*D^(2*j))*(N:ℝ)^(L+M*(2*j+1)+j)/d^(preferredWordLoss j w) := by
      dsimp only [H]
      rw [pow_add]
      ring
    _ ≤ _ := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hconst (by positivity)) (by positivity)

end
end IsingBulk.Preferred22
