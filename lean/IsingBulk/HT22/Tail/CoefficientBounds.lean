import IsingBulk.HT22.Tail.TotalJetLoss
import IsingBulk.HT22.Tail.CoefficientCalculus
import IsingBulk.Preferred22.CoefficientNorm

/-! # Quantitative HT22 coefficient induction from original frame jets

The abstract polynomial estimate is parameterized by its atom evaluator;
it does not mention either physical field. The final theorem instantiates
it with the actual HT22 fixed-v frame jets. Uniform bounds for those
original factors remain explicit, not replaced by a final-tail premise.
-/
namespace IsingBulk.HT22.Tail
noncomputable section
open IsingBulk.Preferred22 Set
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise
set_option backward.isDefEq.respectTransparency false

def evaluatedTerm {N : ℕ} (A : PreferredCoefficientAtom N → ℂ)
    (T : PreferredCoefficientTerm N) : ℂ := (T.map A).prod

theorem evaluatedTerm_normalized_bound {N : ℕ} (A : PreferredCoefficientAtom N → ℂ) (Z : ℂ) (R d : ℝ) (hR : 0≤R) (hd : 0<d)
    (L M : ℕ) (T : PreferredCoefficientTerm N)
    (hA : ∀ a∈T,
      ‖Z^preferredAtomSeedCount a*A a‖≤
        R^(N*preferredAtomSeedCount a+1)*(N:ℝ)^(L*preferredAtomSeedCount a+M)/d^totalAtomLoss a) :
    ‖Z^preferredTermSeedCount T*evaluatedTerm A T‖≤
      R^(N*preferredTermSeedCount T+T.length)*(N:ℝ)^(L*preferredTermSeedCount T+M*T.length)/
        d^totalTermLoss T := by
  induction T with
  | nil => simp [preferredTermSeedCount,evaluatedTerm,totalTermLoss]
  | cons a T ih =>
    have hh := hA a (List.mem_cons_self ..)
    have ht := ih (fun b hb => hA b (List.mem_cons_of_mem _ hb))
    have he : Z^preferredTermSeedCount (a::T)*evaluatedTerm A (a::T)=
        (Z^preferredAtomSeedCount a*A a)*
          (Z^preferredTermSeedCount T*evaluatedTerm A T) := by
      simp only [preferredTermSeedCount,evaluatedTerm,List.map_cons,List.sum_cons,List.prod_cons,pow_add]
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
    have hpow₃ : totalAtomLoss a+totalTermLoss T=totalTermLoss (a::T) := rfl
    apply le_of_eq
    rw [←hpow₁,←hpow₂,←hpow₃,pow_add,pow_add,pow_add]
    ring

theorem evaluatedCoefficientTerm_bound {N : ℕ} (hN : 0<N)
    (A : PreferredCoefficientAtom N → ℂ) (Z : ℂ)
    (R d D : ℝ) (hR : 1≤R) (hd : 0<d) (hdD : d≤D) (hD : 1≤D)
    (L M j : ℕ) (w : PreferredMarkedWord N j) (T : PreferredCoefficientTerm N)
    (hT : T∈preferredCoefficientTerms j w)
    (hA : ∀ a∈T,
      ‖Z^preferredAtomSeedCount a*A a‖≤
        R^(N*preferredAtomSeedCount a+1)*(N:ℝ)^(L*preferredAtomSeedCount a+M)/d^totalAtomLoss a) :
    ‖Z*evaluatedTerm A T‖≤
      R^(N+2*j+1)*(N:ℝ)^(L+M*(2*j+1))*D^(2*j)/d^(preferredWordLoss j w) := by
  have hwell := totalCoefficientTerms_wellFormed j w T hT
  have hn : (1:ℝ)≤N := by exact_mod_cast Nat.succ_le_iff.mpr hN
  have hRn : 0≤R := le_trans (by norm_num) hR
  have hbase := evaluatedTerm_normalized_bound A Z R d hRn hd L M T hA
  simp only [hwell.seed,pow_one,Nat.mul_one] at hbase
  have hloss : preferredWordLoss j w≤2*j := by have := preferredWordLoss_budget j w; omega
  have hdeg := inverse_power_loss_bound d D hd hdD hD _ _ (2*j) hwell.loss hloss
  have hRp : R^(N+T.length)≤R^(N+2*j+1) := pow_le_pow_right₀ hR (by have := hwell.length; omega)
  have hNp : (N:ℝ)^(L+M*T.length)≤(N:ℝ)^(L+M*(2*j+1)) :=
    pow_le_pow_right₀ hn (Nat.add_le_add_left (Nat.mul_le_mul_left M hwell.length) L)
  calc
    _ ≤ R^(N+T.length)*(N:ℝ)^(L+M*T.length)/d^totalTermLoss T := hbase
    _ ≤ R^(N+2*j+1)*(N:ℝ)^(L+M*(2*j+1)) * (D^(2*j)/d^preferredWordLoss j w) := by
      rw [div_eq_mul_inv,←one_div]
      exact mul_le_mul (mul_le_mul hRp hNp (by positivity) (by positivity)) hdeg
        (by positivity) (by positivity)
    _ = _ := by ring

theorem atomValue_bound_of_frame_bounds {N : ℕ} (hN : 0<N)
    (τ : ℝ) (η p m r : ℝ → ℝ) (s : ℂ) (θ : Fin N → ℝ)
    (Z : ℂ) (R d : ℝ) (hR : 1≤R) (_hd : 0<d) (L M j : ℕ)
    (hseed : ∀ xs : List (Option (Fin N)), xs.length≤j →
      ‖Z*frameJet τ p m (regularSeedCoefficient τ η p m r) xs s θ‖≤R^N*(N:ℝ)^L)
    (hB : ∀ i (xs : List (Option (Fin N))), xs.length≤j →
      ‖frameJet τ p m
        (fun t x => residualField t (sourceCoordinate τ p m t x) i) xs s θ‖≤
          R*(N:ℝ)^M/d^(1+xs.length))
    (hK : ∀ (ij : Fin N × Fin N) (xs : List (Option (Fin N))), xs.length≤j →
      ‖frameJet τ p m
        (fun t x => sourceOrdinaryKernel τ p m t x ij.1 ij.2) xs s θ‖≤R)
    (a : PreferredCoefficientAtom N) (ha : preferredAtomJetOrder a≤j) :
    ‖Z^preferredAtomSeedCount a*atomValue τ η p m r a s θ‖≤
      R^(N*preferredAtomSeedCount a+1)*(N:ℝ)^(L*preferredAtomSeedCount a+M)/d^totalAtomLoss a := by
  have hn : (1:ℝ)≤N := by exact_mod_cast Nat.succ_le_iff.mpr hN
  have hRn : 0≤R := le_trans (by norm_num) hR
  have hNM : 1≤(N:ℝ)^M := one_le_pow₀ hn
  cases a with
  | seed xs =>
    simp only [preferredAtomSeedCount,atomValue,totalAtomLoss,Nat.mul_one,
      pow_one,pow_zero,div_one]
    apply (hseed xs ha).trans
    exact mul_le_mul (pow_le_pow_right₀ hR (Nat.le_succ N))
      (pow_le_pow_right₀ hn (Nat.le_add_right L M)) (by positivity) (by positivity)
  | collective i xs =>
    simpa only [preferredAtomSeedCount,atomValue,totalAtomLoss,Nat.mul_zero,
      zero_add,pow_zero,pow_one,one_mul] using hB i xs ha
  | kernel ij xs =>
    simp only [preferredAtomSeedCount,atomValue,totalAtomLoss,Nat.mul_zero,
      zero_add,pow_zero,pow_one,one_mul,div_one]
    exact (hK ij xs ha).trans (le_mul_of_one_le_right hRn hNM)

theorem coefficientTerms_sum_bound {N : ℕ} (hN : 0<N)
    (τ : ℝ) (η p m r : ℝ → ℝ) (s : ℂ) (θ : Fin N → ℝ) (Z : ℂ)
    (R d D : ℝ) (hR : 1≤R) (hd : 0<d) (hdD : d≤D) (hD : 1≤D)
    (L M j : ℕ) (w : PreferredMarkedWord N j)
    (hseed : ∀ xs : List (Option (Fin N)), xs.length≤j →
      ‖Z*frameJet τ p m (regularSeedCoefficient τ η p m r) xs s θ‖≤R^N*(N:ℝ)^L)
    (hB : ∀ i (xs : List (Option (Fin N))), xs.length≤j →
      ‖frameJet τ p m
        (fun t x => residualField t (sourceCoordinate τ p m t x) i) xs s θ‖≤
          R*(N:ℝ)^M/d^(1+xs.length))
    (hK : ∀ (ij : Fin N × Fin N) (xs : List (Option (Fin N))), xs.length≤j →
      ‖frameJet τ p m
        (fun t x => sourceOrdinaryKernel τ p m t x ij.1 ij.2) xs s θ‖≤R) :
    ‖Z*((preferredCoefficientTerms j w).map
      (fun T => termValue τ η p m r T s θ)).sum‖≤
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
      ‖Z*termValue τ η p m r T s θ‖≤H := by
    apply evaluatedCoefficientTerm_bound hN (fun a => atomValue τ η p m r a s θ) Z R d D hR hd hdD hD L M j w T hT
    intro a ha
    exact atomValue_bound_of_frame_bounds hN τ η p m r s θ Z R d hR hd L M j
      hseed hB hK a ((totalCoefficientTerms_wellFormed j w T hT).order a ha)
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
        (fun T => Z*termValue τ η p m r T s θ)).sum‖ := by rw [List.sum_map_mul_left]
    _ ≤ ((preferredCoefficientTerms j w).length:ℝ)*H := norm_list_sum_map_bound _ _ H hterm
    _ ≤ (A*(N:ℝ)^j)*H := mul_le_mul_of_nonneg_right hcount hH
    _ = (A*R^(N+2*j+1)*D^(2*j))*(N:ℝ)^(L+M*(2*j+1)+j)/d^(preferredWordLoss j w) := by
      dsimp only [H]
      rw [pow_add]
      ring
    _ ≤ _ := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hconst (by positivity)) (by positivity)

/-- Proved quantitative induction for the actual fixed-v word coefficient.
The only norm inputs concern the original seed, new field, and ordinary
kernel jets; no generated-word estimate is assumed. -/
theorem wordCoefficient_bound_of_source_frames {N : ℕ} (hN : 0<N)
    (τ δ : ℝ) (η p m r : ℝ → ℝ)
    (hη : ContDiff ℝ ∞ η) (hp : ContDiff ℝ ∞ p)
    (hm : ContDiff ℝ ∞ m) (hr : ContDiff ℝ ∞ r)
    (Ω : Set (ℂ × (Fin N → ℝ))) (hΩ : IsOpen Ω)
    (hpoint : ∀ z∈Ω, PreferredFramePoint τ δ p m z.1 z.2)
    (hRcov : ∀ z∈Ω, sourceCovariance z.1 (sourceCoordinate τ p m z.1 z.2)≠0)
    (s : ℂ) (θ : Fin N → ℝ) (hz : (s,θ)∈Ω)
    (R d D : ℝ) (hR : 1≤R) (hd : 0<d) (hdD : d≤D) (hD : 1≤D)
    (L M j : ℕ)
    (hseed : ∀ xs : List (Option (Fin N)), xs.length≤j →
      ‖((N.factorial:ℂ)*(2*Real.pi:ℂ)^(N-1))*
        frameJet τ p m (regularSeedCoefficient τ η p m r) xs s θ‖≤R^N*(N:ℝ)^L)
    (hB : ∀ i (xs : List (Option (Fin N))), xs.length≤j →
      ‖frameJet τ p m
        (fun t x => residualField t (sourceCoordinate τ p m t x) i) xs s θ‖≤
          R*(N:ℝ)^M/d^(1+xs.length))
    (hK : ∀ (ij : Fin N × Fin N) (xs : List (Option (Fin N))), xs.length≤j →
      ‖frameJet τ p m
        (fun t x => sourceOrdinaryKernel τ p m t x ij.1 ij.2) xs s θ‖≤R)
    (w : MarkedWord N j) :
    ‖((N.factorial:ℂ)*(2*Real.pi:ℂ)^(N-1))*wordCoefficient τ η p m r j w s θ‖≤
      ((preferredCoefficientCountConstant j:ℝ)*R^(2*j+2)*D^(2*j))^N *
        (N:ℝ)^(L+M*(2*j+1)+j)/d^(wordLoss j w) := by
  rw [wordCoefficient_eq_terms τ η p m r Ω hΩ
    (atomValue_mixed τ δ η p m r hη hp hm hr Ω hΩ hpoint hRcov) j w s θ hz]
  exact coefficientTerms_sum_bound hN τ η p m r s θ
    ((N.factorial:ℂ)*(2*Real.pi:ℂ)^(N-1)) R d D hR hd hdD hD L M j w hseed hB hK

end
end IsingBulk.HT22.Tail
