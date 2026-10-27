import IsingBulk.Preferred22.InverseFrameJets
import IsingBulk.Preferred22.CutoffJets

/-! Quantitative bounds for the explicit separated frame expansion.
All angular derivatives remain real, and all complex factors are evaluated
on their genuine regular chart. -/
namespace IsingBulk.Preferred22
noncomputable section
open Set Filter
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise
set_option backward.isDefEq.respectTransparency false

/-- A fixed directional derivative raises the genuine Fréchet jet order by
one and costs exactly the norm of its direction. -/
theorem preferred_directional_jet_le {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (f : E → F) (x v : E) (hf : ContDiffAt 𝕜 ∞ f x) (j : ℕ) :
    ‖iteratedFDeriv 𝕜 j (fun y => fderiv 𝕜 f y v) x‖≤
      ‖v‖*‖iteratedFDeriv 𝕜 (j+1) f x‖ := by
  have hh := norm_iteratedFDeriv_clm_apply_const (c := v)
    (hf.fderiv_right (by simp : (∞:ℕ∞ω)+1≤∞)) (by simp : (j:ℕ∞ω)≤∞)
  simpa only [norm_iteratedFDeriv_fderiv] using hh

theorem preferredComplexFrameDirection_norm_le {N : ℕ} (a : Option (Fin N)) :
    ‖preferredComplexFrameDirection a‖≤1 := by
  cases a <;> simp [preferredComplexFrameDirection,Prod.norm_def,Pi.norm_single]

/-- Local analyticity is sufficient for the standard finite Leibniz jet
bound. Global analyticity outside the physical chart is not assumed. -/
theorem preferred_analytic_product_jet_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f g : E → ℂ) (x : E) (hf : AnalyticAt ℂ f x) (hg : AnalyticAt ℂ g x)
    (J j : ℕ) (hj : j≤J) {A B : ℝ} (hA : 0≤A) (hB : 0≤B)
    (ha : ∀ k≤J, ‖iteratedFDeriv ℂ k f x‖≤A)
    (hb : ∀ k≤J, ‖iteratedFDeriv ℂ k g x‖≤B) :
    ‖iteratedFDeriv ℂ j (fun y => f y*g y) x‖≤2^J*A*B := by
  let S := {y | AnalyticAt ℂ f y} ∩ {y | AnalyticAt ℂ g y}
  have hS : IsOpen S := (isOpen_analyticAt ℂ f).inter (isOpen_analyticAt ℂ g)
  have hx : x∈S := ⟨hf,hg⟩
  have hfc : ContDiffOn ℂ ∞ f S := fun _ hy => hy.1.contDiffAt.contDiffWithinAt
  have hgc : ContDiffOn ℂ ∞ g S := fun _ hy => hy.2.contDiffAt.contDiffWithinAt
  have hh := norm_iteratedFDerivWithin_mul_le hfc hgc hS.uniqueDiffOn hx (by simp : (j:ℕ∞ω)≤∞)
  simp_rw [iteratedFDerivWithin_of_isOpen _ hS hx] at hh
  apply hh.trans
  calc
    _ ≤ ∑ k∈Finset.range (j+1), (j.choose k:ℝ)*A*B := by
      apply Finset.sum_le_sum
      intro k hk
      have hkj : k≤j := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
      exact mul_le_mul (mul_le_mul_of_nonneg_left (ha k (hkj.trans hj)) (Nat.cast_nonneg _))
        (hb (j-k) ((Nat.sub_le _ _).trans hj)) (norm_nonneg _) (by positivity)
    _ = 2^j*A*B := by
      rw [←Finset.sum_mul,←Finset.sum_mul]
      congr 2
      exact_mod_cast Nat.sum_range_choose j
    _ ≤ _ := by gcongr; norm_num

theorem preferred_real_complex_product_jet_le {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f g : E → ℂ) (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (x : E) (J j : ℕ) (hj : j≤J) {A B : ℝ} (hA : 0≤A) (hB : 0≤B)
    (ha : ∀ k≤J, ‖iteratedFDeriv ℝ k f x‖≤A)
    (hb : ∀ k≤J, ‖iteratedFDeriv ℝ k g x‖≤B) :
    ‖iteratedFDeriv ℝ j (fun y => f y*g y) x‖≤2^J*A*B := by
  apply (norm_iteratedFDeriv_mul_le hf hg x (by simp : (j:ℕ∞ω)≤∞)).trans
  calc
    _ ≤ ∑ k∈Finset.range (j+1), (j.choose k:ℝ)*A*B := by
      apply Finset.sum_le_sum
      intro k hk
      have hkj : k≤j := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
      exact mul_le_mul (mul_le_mul_of_nonneg_left (ha k (hkj.trans hj)) (Nat.cast_nonneg _))
        (hb (j-k) ((Nat.sub_le _ _).trans hj)) (norm_nonneg _) (by positivity)
    _ = 2^j*A*B := by
      rw [←Finset.sum_mul,←Finset.sum_mul]
      congr 2
      exact_mod_cast Nat.sum_range_choose j
    _ ≤ _ := by gcongr; norm_num

/-- Every analytic separated branch has a finite-jet bound built only from
the actual Uq/Udot jets and the initial analytic factor. -/
theorem preferredSeparatedAnalytic_jet_le {N : ℕ}
    (F : ℂ × (Fin N → ℂ) → ℂ) (z : ℂ × (Fin N → ℂ))
    (hF : AnalyticAt ℂ F z)
    (hU : ∀ i, AnalyticAt ℂ (fun y : ℂ × ℂ => preferredMovingInverse y.1 y.2) (z.1,z.2 i))
    (J : ℕ) {A U : ℝ} (hA : 0≤A) (hU1 : 1≤U)
    (hFjet : ∀ k≤J, ‖iteratedFDeriv ℂ k F z‖≤A)
    (hUjet : ∀ a b, ∀ k≤J,
      ‖iteratedFDeriv ℂ k (preferredSeparatedInverseFactor (N:=N) a b) z‖≤U)
    (xs : List (Option (Fin N))) (w : PreferredMarkedWord N xs.length)
    (k : ℕ) (hbudget : xs.length+k≤J) :
    ‖iteratedFDeriv ℂ k (preferredSeparatedAnalytic F xs w) z‖≤(2^J*U)^xs.length*A := by
  have hD : 1≤2^J*U := one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) hU1
  induction xs generalizing k with
  | nil => simpa only [preferredSeparatedAnalytic,List.length_nil,pow_zero,one_mul] using hFjet k (by simpa using hbudget)
  | cons a xs ih =>
    have htail := preferredSeparatedAnalytic_analyticAt F xs (Fin.tail w) z hF hU
    cases hw : w 0 with
    | none =>
      simp only [preferredSeparatedAnalytic,hw,preferredComplexFrameJet,List.length_cons]
      have hh := preferred_directional_jet_le (preferredSeparatedAnalytic F xs (Fin.tail w)) z
        (preferredComplexFrameDirection a) htail.contDiffAt k
      apply hh.trans
      calc
        _ ≤ ‖iteratedFDeriv ℂ (k+1) (preferredSeparatedAnalytic F xs (Fin.tail w)) z‖ :=
          mul_le_of_le_one_left (norm_nonneg _) (preferredComplexFrameDirection_norm_le a)
        _ ≤ (2^J*U)^xs.length*A := ih (Fin.tail w) (k+1) (by simp only [List.length_cons] at hbudget; omega)
        _ ≤ (2^J*U)^(xs.length+1)*A := mul_le_mul_of_nonneg_right
          (pow_le_pow_right₀ hD (Nat.le_succ _)) hA
    | some ib =>
      simp only [preferredSeparatedAnalytic,hw,List.length_cons]
      have hbound := preferred_analytic_product_jet_le
        (preferredSeparatedAnalytic F xs (Fin.tail w)) (preferredSeparatedInverseFactor a ib.2) z
        htail (preferredSeparatedInverseFactor_analyticAt a ib.2 z hU) k k le_rfl
        (by positivity : 0≤(2^J*U)^xs.length*A) (zero_le_one.trans hU1)
        (fun r hr => ih (Fin.tail w) r (by simp only [List.length_cons] at hbudget; omega))
        (fun r hr => hUjet a ib.2 r (by simp only [List.length_cons] at hbudget; omega))
      apply hbound.trans
      calc
        _ ≤ 2^J*((2^J*U)^xs.length*A)*U := by
          apply mul_le_mul_of_nonneg_right _ (zero_le_one.trans hU1)
          exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2)
            (by simp only [List.length_cons] at hbudget; omega)) (by positivity)
        _ = _ := by rw [pow_succ]; ring

/-- The real angular branches are controlled by the actual inverse matrix's
real jets. There is no inverse-coordinate singularity in this bound. -/
theorem preferredSeparatedAngular_jet_le {N : ℕ} (τ : ℝ) (p m : ℝ → ℝ)
    (hp : ContDiff ℝ ∞ p) (hm : ContDiff ℝ ∞ m)
    (hM : ∀ θ : Fin N → ℝ, (preferredContourMatrix τ p m θ).det≠0)
    (G : (Fin N → ℝ) → ℂ) (hG : ContDiff ℝ ∞ G) (θ : Fin N → ℝ)
    (J : ℕ) {A M : ℝ} (hA : 0≤A) (hM1 : 1≤M)
    (hGjet : ∀ k≤J, ‖iteratedFDeriv ℝ k G θ‖≤A)
    (hMjet : ∀ i b, ∀ k≤J,
      ‖iteratedFDeriv ℝ k (fun x : Fin N → ℝ => (preferredContourMatrix τ p m x)⁻¹ i b) θ‖≤M)
    (xs : List (Option (Fin N))) (w : PreferredMarkedWord N xs.length)
    (k : ℕ) (hbudget : xs.length+k≤J) :
    ‖iteratedFDeriv ℝ k (preferredSeparatedAngular τ p m G xs w) θ‖≤(2^J*M)^xs.length*A := by
  have hD : 1≤2^J*M := one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) hM1
  have hMi (i b : Fin N) : ContDiff ℝ ∞ (fun x : Fin N → ℝ => (preferredContourMatrix τ p m x)⁻¹ i b) := by
    apply contDiff_iff_contDiffAt.mpr
    intro x
    exact contDiffAt_pi.mp (contDiffAt_pi.mp
      (preferredContourMatrix_inverse_contDiffAt τ p m hp hm x (hM x)) i) b
  induction xs generalizing k with
  | nil => simpa only [preferredSeparatedAngular,List.length_nil,pow_zero,one_mul] using hGjet k (by simpa using hbudget)
  | cons a xs ih =>
    have htail := preferredSeparatedAngular_contDiff τ p m hp hm hM G hG xs (Fin.tail w)
    cases hw : w 0 with
    | none =>
      simp only [preferredSeparatedAngular,hw,List.length_cons]
      exact (ih (Fin.tail w) k (by simp only [List.length_cons] at hbudget; omega)).trans
        (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hD (Nat.le_succ _)) hA)
    | some ib =>
      simp only [preferredSeparatedAngular,hw,List.length_cons]
      have hdir : ContDiff ℝ ∞ (fun y => fderiv ℝ (preferredSeparatedAngular τ p m G xs (Fin.tail w)) y (Pi.single ib.1 1)) :=
        (ContinuousLinearMap.apply ℝ ℂ (Pi.single ib.1 1)).contDiff.comp (htail.fderiv_right (by simp))
      have hdjet (r : ℕ) (hr : r≤k) :
          ‖iteratedFDeriv ℝ r (fun y => fderiv ℝ (preferredSeparatedAngular τ p m G xs (Fin.tail w)) y (Pi.single ib.1 1)) θ‖≤
            (2^J*M)^xs.length*A := by
        have hh := preferred_directional_jet_le _ θ (Pi.single ib.1 1) htail.contDiffAt r
        simp only [Pi.norm_single,norm_one,one_mul] at hh
        exact hh.trans (ih (Fin.tail w) (r+1) (by simp only [List.length_cons] at hbudget; omega))
      have hbound := preferred_real_complex_product_jet_le _ _ (hMi ib.1 ib.2) hdir θ k k le_rfl
        (zero_le_one.trans hM1) (by positivity : 0≤(2^J*M)^xs.length*A)
        (fun r hr => hMjet ib.1 ib.2 r (by simp only [List.length_cons] at hbudget; omega)) hdjet
      apply hbound.trans
      calc
        _ ≤ 2^J*M*((2^J*M)^xs.length*A) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2)
            (by simp only [List.length_cons] at hbudget; omega)) (zero_le_one.trans hM1)
        _ = _ := by rw [pow_succ]; ring

/-- Quantitative exact separated expansion. The only norm premises are
finite jets of the initial two factors and actual U/M coefficients. -/
theorem preferredFrameJet_separated_norm {N : ℕ} (τ δ : ℝ) (p m : ℝ → ℝ)
    (hp : ContDiff ℝ ∞ p) (hm : ContDiff ℝ ∞ m)
    (hM : ∀ θ : Fin N → ℝ, (preferredContourMatrix τ p m θ).det≠0)
    (Ω : Set (ℂ × (Fin N → ℝ))) (hΩ : IsOpen Ω)
    (hpoint : ∀ z∈Ω, PreferredFramePoint τ δ p m z.1 z.2)
    (F : ℂ × (Fin N → ℂ) → ℂ) (G : (Fin N → ℝ) → ℂ)
    (hF : ∀ z∈Ω, AnalyticAt ℂ F (z.1,preferredSourceCoordinate τ p m z.1 z.2))
    (hG : ContDiff ℝ ∞ G) (s : ℂ) (θ : Fin N → ℝ) (hz : (s,θ)∈Ω)
    (J : ℕ) {A B U M : ℝ} (hA : 0≤A) (hB : 0≤B) (hU1 : 1≤U) (hM1 : 1≤M)
    (hFjet : ∀ k≤J, ‖iteratedFDeriv ℂ k F (s,preferredSourceCoordinate τ p m s θ)‖≤A)
    (hGjet : ∀ k≤J, ‖iteratedFDeriv ℝ k G θ‖≤B)
    (hUjet : ∀ a b, ∀ k≤J, ‖iteratedFDeriv ℂ k
      (preferredSeparatedInverseFactor (N:=N) a b) (s,preferredSourceCoordinate τ p m s θ)‖≤U)
    (hMjet : ∀ i b, ∀ k≤J,
      ‖iteratedFDeriv ℝ k (fun x : Fin N → ℝ => (preferredContourMatrix τ p m x)⁻¹ i b) θ‖≤M)
    (xs : List (Option (Fin N))) (hxs : xs.length≤J) :
    ‖preferredFrameJet τ p m (fun t x => F (t,preferredSourceCoordinate τ p m t x)*G x) xs s θ‖≤
      ((N:ℝ)^2+1)^xs.length * ((2^J*U)*(2^J*M))^xs.length*A*B := by
  rw [preferredFrameJet_separated_expansion τ δ p m hp hm hM Ω hΩ hpoint F G hF hG xs s θ hz]
  unfold preferredSeparatedSum
  have hterm (w : PreferredMarkedWord N xs.length) :
      ‖preferredSeparatedAnalytic F xs w (s,preferredSourceCoordinate τ p m s θ)*
        preferredSeparatedAngular τ p m G xs w θ‖≤
      ((2^J*U)*(2^J*M))^xs.length*A*B := by
    have ha := preferredSeparatedAnalytic_jet_le F _ (hF (s,θ) hz) (hpoint (s,θ) hz).inverse_analytic
      J hA hU1 hFjet hUjet xs w 0 (by simpa only [add_zero] using hxs)
    have hb := preferredSeparatedAngular_jet_le τ p m hp hm hM G hG θ J hB hM1 hGjet hMjet xs w 0
      (by simpa only [add_zero] using hxs)
    simp only [norm_iteratedFDeriv_zero] at ha hb
    rw [norm_mul]
    exact (mul_le_mul ha hb (norm_nonneg _) (by positivity)).trans_eq (by rw [mul_pow]; ring)
  apply (norm_sum_le _ _).trans
  apply (Finset.sum_le_sum (fun w (_ : w∈Finset.univ) => hterm w)).trans_eq
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,preferredWord_card]
  push_cast
  ring

/-- Real angular factors have only a polynomial N cost under the true
frames. All initial real jets and the actual inverse-matrix jets are visible. -/
theorem preferredFrameJet_angular_norm_on_chart {N : ℕ} (hN : 0<N)
    (τ δ : ℝ) (p m : ℝ → ℝ) (hp : ContDiff ℝ ∞ p) (hm : ContDiff ℝ ∞ m)
    (hM : ∀ θ : Fin N → ℝ, (preferredContourMatrix τ p m θ).det≠0)
    (Ω : Set (ℂ × (Fin N → ℝ))) (hΩ : IsOpen Ω)
    (hpoint : ∀ z∈Ω, PreferredFramePoint τ δ p m z.1 z.2)
    (G : (Fin N → ℝ) → ℂ) (hG : ContDiff ℝ ∞ G)
    (s : ℂ) (θ : Fin N → ℝ) (hz : (s,θ)∈Ω)
    (J : ℕ) {A U M : ℝ} (hA : 0≤A) (hU1 : 1≤U) (hM1 : 1≤M)
    (hGjet : ∀ k≤J, ‖iteratedFDeriv ℝ k G θ‖≤A)
    (hUjet : ∀ a b, ∀ k≤J, ‖iteratedFDeriv ℂ k
      (preferredSeparatedInverseFactor (N:=N) a b) (s,preferredSourceCoordinate τ p m s θ)‖≤U)
    (hMjet : ∀ i b, ∀ k≤J,
      ‖iteratedFDeriv ℝ k (fun x : Fin N → ℝ => (preferredContourMatrix τ p m x)⁻¹ i b) θ‖≤M*(N:ℝ)^J)
    (xs : List (Option (Fin N))) (hxs : xs.length≤J) :
    ‖preferredFrameJet τ p m (fun _ x => G x) xs s θ‖≤
      (2*((2^J*U)*(2^J*M)))^J*(N:ℝ)^(J*J+2*J)*A := by
  have hn : (1:ℝ)≤N := by exact_mod_cast hN
  have hnJ : 1≤(N:ℝ)^J := one_le_pow₀ hn
  have hMN : 1≤M*(N:ℝ)^J := one_le_mul_of_one_le_of_one_le hM1 hnJ
  have hFjet (k : ℕ) (_hk : k≤J) :
      ‖iteratedFDeriv ℂ k (fun _ : ℂ × (Fin N → ℂ) => (1:ℂ))
        (s,preferredSourceCoordinate τ p m s θ)‖≤1 := by
    cases k with
    | zero => simp
    | succ k => simp only [iteratedFDeriv_succ_const,Pi.zero_apply,norm_zero]; norm_num
  have hh := preferredFrameJet_separated_norm τ δ p m hp hm hM Ω hΩ hpoint
    (fun _ : ℂ × (Fin N → ℂ) => (1:ℂ)) G (fun _ _ => analyticAt_const) hG s θ hz J
    (by norm_num : (0:ℝ)≤1) hA hU1 hMN hFjet hGjet hUjet hMjet xs hxs
  simp only [one_mul,mul_one] at hh
  apply hh.trans
  let Q := (2^J*U)*(2^J*M)
  have htwo : (1:ℝ)≤2^J := one_le_pow₀ (by norm_num)
  have hQ : 1≤Q := one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le htwo hU1) (one_le_mul_of_one_le_of_one_le htwo hM1)
  have hQN : 1≤Q*(N:ℝ)^J := one_le_mul_of_one_le_of_one_le hQ hnJ
  have hcount : (N:ℝ)^2+1≤2*(N:ℝ)^2 := by nlinarith [sq_nonneg ((N:ℝ)-1)]
  have hcount1 : (1:ℝ)≤2*(N:ℝ)^2 := by nlinarith
  have he : (2^J*U)*(2^J*(M*(N:ℝ)^J))=Q*(N:ℝ)^J := by dsimp [Q]; ring
  rw [he]
  calc
    _ ≤ (2*(N:ℝ)^2)^J*(Q*(N:ℝ)^J)^J*A := by
      apply mul_le_mul_of_nonneg_right _ hA
      exact mul_le_mul
        ((pow_le_pow_left₀ (by positivity) hcount _).trans (pow_le_pow_right₀ hcount1 hxs))
        (pow_le_pow_right₀ hQN hxs) (by positivity) (by positivity)
    _ = _ := by
      rw [mul_pow,mul_pow,mul_pow,←pow_mul,←pow_mul]
      rw [pow_add]
      ring

end
end IsingBulk.Preferred22
