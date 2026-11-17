import IsingBulk.AnisoF002.C03.RegularQuadraticContinuation
import IsingBulk.AnisoF002.C03.RegularSpectralMatching
import IsingBulk.AnisoF002.C03.RegularIsotropicWeightedMatching

/-!
# The filled matching identity for arbitrary continued reciprocal roots

Every reciprocal angular collision is retained. A local continuation of
each prescribed simple root gives a dense family with ordinary Schur
denominators; the finite, division-free matched expression has a genuine
continuous limit. This identity applies to the actual contour and to its
protected complex parameter neighborhoods, without changing root signs.
-/

namespace IsingBulk.AnisoF002.RegularTail.C03
noncomputable section
open Filter Set
open scoped Topology BigOperators

theorem continuousAt_pairProductOn {X α : Type*} [TopologicalSpace X]
    (K : X → α → α → ℂ) {x : X} (hK : ∀ a b, ContinuousAt (fun t => K t a b) x)
    (xs : List α) : ContinuousAt (fun t => pairProductOn (K t) xs) x := by
  induction xs with
  | nil => exact continuousAt_const
  | cons a xs ih =>
      exact (tendsto_list_prod xs (fun b _ => hK a b)).mul ih

theorem continuousAt_matchedExpansion {X α : Type*} [TopologicalSpace X]
    (K P : X → α → α → ℂ) {x : X}
    (hK : ∀ a b, ContinuousAt (fun t => K t a b) x)
    (hP : ∀ a b, ContinuousAt (fun t => P t a b) x)
    (n : ℕ) (xs : List α) : ContinuousAt (fun t => matchedExpansion (K t) (P t) n xs) x := by
  induction n generalizing xs with
  | zero => exact continuousAt_const
  | succ n ih =>
      cases xs with
      | nil => exact continuousAt_const
      | cons a xs =>
          apply tendsto_list_sum xs.zipIdx
          intro bj _
          exact ((hP a bj.1).mul (tendsto_list_prod (xs.eraseIdx bj.2)
            (fun c _ => (hK a c).mul (hK bj.1 c)))).mul (ih _)

theorem canceledPair_continuousAt_family {X : Type*} [TopologicalSpace X]
    {B : ℂ} {r s y v : X → ℂ} {x : X}
    (hr : ContinuousAt r x) (hs : ContinuousAt s x)
    (hy : ContinuousAt y x) (hv : ContinuousAt v x)
    (hy0 : y x ≠ 0) (hv0 : v x ≠ 0) (hd : 1 - r x * s x ≠ 0) :
    ContinuousAt (fun t => canceledPair B (r t) (s t) (y t) (v t)) x :=
  (((continuousAt_const.mul ((hy.sub hv).pow 2)).mul hr).mul hs).div
    ((hy.mul hv).mul ((continuousAt_const.sub (hr.mul hs)).pow 2))
    (mul_ne_zero (mul_ne_zero hy0 hv0) (pow_ne_zero _ hd))

theorem reciprocal_polynomial_exp_form {A B r y : ℂ} (hy : y ≠ 0)
    (hp : r ^ 2 - 2 * (A - B * (y + y⁻¹) / 2) * r + 1 = 0) :
    y * (r ^ 2 + 1) - 2 * A * y * r + B * (y ^ 2 + 1) * r = 0 := by
  have hi := mul_inv_cancel₀ hy
  linear_combination y * hp - B * r * hi

theorem dense_good_complex_radial_shift {N : ℕ} (y : Fin N → ℂ)
    (hy : ∀ i, y i ≠ 0) :
    Dense {t : ℝ | ∀ i j, 1 - (y i * Complex.exp (t : ℂ)) *
      (y j * Complex.exp (t : ℂ)) ≠ 0} := by
  have hcount (i j : Fin N) : Set.Countable {t : ℝ | 1 -
      (y i * Complex.exp (t : ℂ)) * (y j * Complex.exp (t : ℂ)) = 0} := by
    let f : ℝ → ℂ := fun t => 2 * (t : ℂ)
    have hf : Function.Injective f := by
      intro s t h
      have hr := congrArg Complex.re h
      simp only [f, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.re_ofNat, Complex.im_ofNat, mul_zero, sub_zero] at hr
      linarith
    have hc := (Set.countable_singleton ((y i * y j)⁻¹)).preimage_cexp.preimage hf
    have hprod (t : ℝ) : (y i * Complex.exp (t : ℂ)) * (y j * Complex.exp (t : ℂ)) =
        (y i * y j) * Complex.exp (f t) := by
      have he : Complex.exp (f t) = Complex.exp (t : ℂ) * Complex.exp (t : ℂ) := by
        rw [← Complex.exp_add]
        congr 1
        dsimp [f]
        ring
      rw [he]
      ring
    convert hc using 1
    ext t
    change (1 - (y i * Complex.exp (t : ℂ)) * (y j * Complex.exp (t : ℂ)) = 0) ↔
      Complex.exp (f t) = (y i * y j)⁻¹
    rw [hprod, sub_eq_zero]
    constructor
    · intro h
      apply mul_left_cancel₀ (mul_ne_zero (hy i) (hy j))
      rw [← h, mul_inv_cancel₀ (mul_ne_zero (hy i) (hy j))]
    · intro h
      rw [h, mul_inv_cancel₀ (mul_ne_zero (hy i) (hy j))]
  have hc : Set.Countable (⋃ i : Fin N, ⋃ j : Fin N,
      {t : ℝ | 1 - (y i * Complex.exp (t : ℂ)) * (y j * Complex.exp (t : ℂ)) = 0}) :=
    Set.countable_iUnion fun i => Set.countable_iUnion fun j => hcount i j
  convert hc.dense_compl ℝ using 1
  ext t
  simp

theorem exists_prescribed_root_radial_family {N : ℕ} (A B : ℂ) (r y : Fin N → ℂ)
    (hy : ∀ i, y i ≠ 0)
    (hp : ∀ i, r i ^ 2 - 2 * (A - B * (y i + (y i)⁻¹) / 2) * r i + 1 = 0)
    (hd : ∀ i j, 1 - r i * r j ≠ 0) :
    ∃ R : ℝ → Fin N → ℂ,
      (∀ i, R 0 i = r i) ∧ (∀ i, ContinuousAt (fun t => R t i) 0) ∧
      (∀ t i, R t i ^ 2 - 2 * (A - B *
        ((y i * Complex.exp (t : ℂ)) + (y i * Complex.exp (t : ℂ))⁻¹) / 2) * R t i + 1 = 0) ∧
      ∀ᶠ t in 𝓝 (0 : ℝ), ∀ i j, 1 - R t i * R t j ≠ 0 := by
  let W : ℝ → Fin N → ℂ := fun t i => A - B *
    ((y i * Complex.exp (t : ℂ)) + (y i * Complex.exp (t : ℂ))⁻¹) / 2
  let R : ℝ → Fin N → ℂ := fun t i => reciprocalRootContinuation (W 0 i) (r i) (W t i)
  have hW0 (i : Fin N) : W 0 i = A - B * (y i + (y i)⁻¹) / 2 := by simp [W]
  have hp0 (i : Fin N) : r i ^ 2 - 2 * W 0 i * r i + 1 = 0 := by rw [hW0]; exact hp i
  have hR0 (i : Fin N) : R 0 i = r i := reciprocalRootContinuation_center _ _
  have hRc (i : Fin N) : ContinuousAt (fun t => R t i) 0 := by
    have hyc : ContinuousAt (fun t : ℝ => y i * Complex.exp (t : ℂ)) 0 := by fun_prop
    have hyz : y i * Complex.exp ((0 : ℝ) : ℂ) ≠ 0 :=
      mul_ne_zero (hy i) (Complex.exp_ne_zero _)
    have hWc : ContinuousAt (fun t => W t i) 0 :=
      continuousAt_const.sub ((continuousAt_const.mul (hyc.add (hyc.inv₀ hyz))).div_const 2)
    exact ContinuousAt.comp (f := fun t : ℝ => W t i) (x := 0)
      (reciprocalRootContinuation_analyticAt (W 0 i) (r i)).continuousAt hWc
  refine ⟨R, hR0, hRc, ?_, ?_⟩
  · intro t i
    exact reciprocalRootContinuation_polynomial (hp0 i)
      (reciprocalRootContinuation_simple (hp0 i) (hd i i)) (W t i)
  · apply (Filter.eventually_all.mpr fun i => Filter.eventually_all.mpr fun j => ?_)
    have hc : ContinuousAt (fun t => 1 - R t i * R t j) 0 :=
      continuousAt_const.sub ((hRc i).mul (hRc j))
    exact hc.eventually_ne (by simpa only [hR0] using hd i j)

theorem filled_pairs_even_matched_identity {N : ℕ} (A B : ℂ) (r y : Fin N → ℂ)
    (hy : ∀ i, y i ≠ 0)
    (hp : ∀ i, r i ^ 2 - 2 * (A - B * (y i + (y i)⁻¹) / 2) * r i + 1 = 0)
    (hd : ∀ i j, 1 - r i * r j ≠ 0)
    (n : ℕ) (xs : List (Fin N)) (hlen : xs.length = 2 * n) :
    pairProductOn (fun i j => canceledPair B (r i) (r j) (y i) (y j)) xs =
      matchedExpansion (fun i j => schur (r i) (r j))
        (fun i j => canceledPair B (r i) (r j) (y i) (y j)) n xs := by
  obtain ⟨R, hR0, hRc, hRp, hRd⟩ := exists_prescribed_root_radial_family A B r y hy hp hd
  let Y : ℝ → Fin N → ℂ := fun t i => y i * Complex.exp (t : ℂ)
  let K : ℝ → Fin N → Fin N → ℂ := fun t i j => schur (R t i) (R t j)
  let P : ℝ → Fin N → Fin N → ℂ := fun t i j => canceledPair B (R t i) (R t j) (Y t i) (Y t j)
  let G : Set ℝ := {t | ∀ i j, 1 - Y t i * Y t j ≠ 0}
  have hYc (i : Fin N) : ContinuousAt (fun t => Y t i) 0 := by dsimp [Y]; fun_prop
  have hY0 (i : Fin N) : Y 0 i = y i := by simp [Y]
  have hYn (t : ℝ) (i : Fin N) : Y t i ≠ 0 := mul_ne_zero (hy i) (Complex.exp_ne_zero _)
  have hKc (i j : Fin N) : ContinuousAt (fun t => K t i j) 0 :=
    ((hRc i).sub (hRc j)).div (continuousAt_const.sub ((hRc i).mul (hRc j)))
      (by simpa only [hR0] using hd i j)
  have hPc (i j : Fin N) : ContinuousAt (fun t => P t i j) 0 :=
    canceledPair_continuousAt_family (hRc i) (hRc j) (hYc i) (hYc j)
      (hYn 0 i) (hYn 0 j) (by simpa only [hR0] using hd i j)
  have hG : Dense G := dense_good_complex_radial_shift y hy
  have : NeBot (𝓝[G] (0 : ℝ)) := mem_closure_iff_nhdsWithin_neBot.mp (hG 0)
  have he : ∀ᶠ t in 𝓝[G] (0 : ℝ), pairProductOn (P t) xs = matchedExpansion (K t) (P t) n xs := by
    filter_upwards [hRd.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with t hdt hgt
    have hf : (fun i j => K t i j * schur (Y t i) (Y t j)) = P t := by
      funext i j
      have h := schur_pair_eq_canceled (S := (1 : ℂ)) (T := B) (A := A)
        (by norm_num) (hYn t i) (hYn t j) (hdt i j) (hgt i j)
        (by simpa only [one_mul] using reciprocal_polynomial_exp_form (hYn t i) (hRp t i))
        (by simpa only [one_mul] using reciprocal_polynomial_exp_form (hYn t j) (hRp t j))
      simpa only [div_one] using h
    rw [← hf, pairProductOn_mul, ← schur_even_pfaffianOn (Y t) n xs hlen hgt]
    exact pairProduct_mul_pfaffian_eq_matched (K t) _ (fun i j => schur_skew _ _) n xs hlen
  have hl := (continuousAt_pairProductOn P hPc xs).tendsto.mono_left
    (nhdsWithin_le_nhds (s := G))
  have hr := (continuousAt_matchedExpansion K P hKc hPc n xs).tendsto.mono_left
    (nhdsWithin_le_nhds (s := G))
  have hh := tendsto_nhds_unique (Filter.Tendsto.congr' he hl) hr
  simpa only [K, P, hR0, hY0] using hh

def ghostCompletePair {α : Type*} (P : α → α → ℂ) : Option α → Option α → ℂ
  | some a, some b => P a b
  | none, none => 0
  | _, _ => 1

theorem ghostCompletePair_mul {α : Type*} (K Y : α → α → ℂ) :
    ghostCompletePair (fun a b => K a b * Y a b) =
      fun a b => ghostKernel K 1 a b * ghostKernel Y 1 a b := by
  funext a b
  cases a <;> cases b <;> simp [ghostCompletePair, ghostKernel]

theorem filled_pairs_odd_matched_identity {N : ℕ} (A B : ℂ) (r y : Fin N → ℂ)
    (hy : ∀ i, y i ≠ 0)
    (hp : ∀ i, r i ^ 2 - 2 * (A - B * (y i + (y i)⁻¹) / 2) * r i + 1 = 0)
    (hd : ∀ i j, 1 - r i * r j ≠ 0)
    (n : ℕ) (xs : List (Fin N)) (hlen : xs.length = 2 * n + 1) :
    pairProductOn (fun i j => canceledPair B (r i) (r j) (y i) (y j)) xs =
      matchedExpansion (ghostKernel (fun i j => schur (r i) (r j)) 1)
        (ghostCompletePair (fun i j => canceledPair B (r i) (r j) (y i) (y j)))
        (n + 1) (xs.map some ++ [none]) := by
  obtain ⟨R, hR0, hRc, hRp, hRd⟩ := exists_prescribed_root_radial_family A B r y hy hp hd
  let Y : ℝ → Fin N → ℂ := fun t i => y i * Complex.exp (t : ℂ)
  let K : ℝ → Fin N → Fin N → ℂ := fun t i j => schur (R t i) (R t j)
  let P : ℝ → Fin N → Fin N → ℂ := fun t i j => canceledPair B (R t i) (R t j) (Y t i) (Y t j)
  let G : Set ℝ := {t | ∀ i j, 1 - Y t i * Y t j ≠ 0}
  let ys := xs.map some ++ [none]
  have hlen' : ys.length = 2 * (n + 1) := by simp [ys, hlen]; omega
  have hYc (i : Fin N) : ContinuousAt (fun t => Y t i) 0 := by dsimp [Y]; fun_prop
  have hY0 (i : Fin N) : Y 0 i = y i := by simp [Y]
  have hYn (t : ℝ) (i : Fin N) : Y t i ≠ 0 := mul_ne_zero (hy i) (Complex.exp_ne_zero _)
  have hKc (i j : Fin N) : ContinuousAt (fun t => K t i j) 0 :=
    ((hRc i).sub (hRc j)).div (continuousAt_const.sub ((hRc i).mul (hRc j)))
      (by simpa only [hR0] using hd i j)
  have hPc (i j : Fin N) : ContinuousAt (fun t => P t i j) 0 :=
    canceledPair_continuousAt_family (hRc i) (hRc j) (hYc i) (hYc j)
      (hYn 0 i) (hYn 0 j) (by simpa only [hR0] using hd i j)
  have hKgc (i j : Option (Fin N)) : ContinuousAt (fun t => ghostKernel (K t) 1 i j) 0 := by
    cases i <;> cases j
    · exact continuousAt_const
    · exact continuousAt_const
    · exact continuousAt_const
    · exact hKc _ _
  have hPgc (i j : Option (Fin N)) : ContinuousAt (fun t => ghostCompletePair (P t) i j) 0 := by
    cases i <;> cases j
    · exact continuousAt_const
    · exact continuousAt_const
    · exact continuousAt_const
    · exact hPc _ _
  have hG : Dense G := dense_good_complex_radial_shift y hy
  have : NeBot (𝓝[G] (0 : ℝ)) := mem_closure_iff_nhdsWithin_neBot.mp (hG 0)
  have he : ∀ᶠ t in 𝓝[G] (0 : ℝ), pairProductOn (P t) xs =
      matchedExpansion (ghostKernel (K t) 1) (ghostCompletePair (P t)) (n + 1) ys := by
    filter_upwards [hRd.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with t hdt hgt
    let YK : Fin N → Fin N → ℂ := fun i j => schur (Y t i) (Y t j)
    have hf : (fun i j => K t i j * YK i j) = P t := by
      funext i j
      have h := schur_pair_eq_canceled (S := (1 : ℂ)) (T := B) (A := A)
        (by norm_num) (hYn t i) (hYn t j) (hdt i j) (hgt i j)
        (by simpa only [one_mul] using reciprocal_polynomial_exp_form (hYn t i) (hRp t i))
        (by simpa only [one_mul] using reciprocal_polynomial_exp_form (hYn t j) (hRp t j))
      simpa only [div_one] using h
    have hg (i : Fin N) : Y t i ≠ -1 := by
      intro h
      exact hgt i i (by simp only [h, neg_mul_neg, one_mul, sub_self])
    have hpk : pairProductOn (ghostKernel (K t) 1) ys = pairProductOn (K t) xs := by
      simpa only [one_pow, one_mul] using pairProductOn_ghost (K t) (1 : ℂ) xs
    have hpf : pfaffianOn (ghostKernel YK 1) (n + 1) ys = pairProductOn YK xs :=
      schur_odd_pfaffianOn (Y t) n xs hlen hgt hg
    rw [← hf, pairProductOn_mul, ← hpk, ← hpf, ghostCompletePair_mul]
    exact pairProduct_mul_pfaffian_eq_matched _ _
      (ghostKernel_skew (K t) 1 (fun i j => schur_skew _ _)) (n + 1) ys hlen'
  have hl := (continuousAt_pairProductOn P hPc xs).tendsto.mono_left
    (nhdsWithin_le_nhds (s := G))
  have hr := (continuousAt_matchedExpansion (fun t => ghostKernel (K t) 1)
    (fun t => ghostCompletePair (P t)) hKgc hPgc (n + 1) ys).tendsto.mono_left
    (nhdsWithin_le_nhds (s := G))
  have hh := tendsto_nhds_unique (Filter.Tendsto.congr' he hl) hr
  simpa only [K, P, hR0, hY0, ys] using hh

end
end IsingBulk.AnisoF002.RegularTail.C03
