/-
Copyright (c) 2024 Pjotr Buys. All rights reserved.
Authors: Pjotr Buys
-/

import Mathlib

/-!
# Convexity of the Shearer function.

This file analyzes the function `F : ℝ → ℝ` defined by
```
F(x) = (x * log x - x + 1) / (x - 1)²  for x > 0, x ≠ 1
F(1) = 1/2
```

The main result is that `F` is convex on `(0, ∞)`.

## Main definitions

* `F` : The function under study, with explicit handling of the singularity at `x = 1`.
* `F'`, `F''` : The first and second derivatives of `F`, also with explicit singularity handling.
* `S` : The domain `{x | 0 < x ∧ x ≠ 1}` where `F` has the standard rational form.

## Main results

* `F_convex` : The function `F` is convex on `(0, ∞)`
* `F_convex_inequality` : For `0 ≤ x` and `0 < y`, we have `F x ≥ F y + F' y * (x - y)`
* `F'_nonpositive` : For `0 < x`, we have `F' x ≤ 0`
* `F_diff_equation` : The funxtion `F` satisfies `1 + (x - x^2) * F' x - (x + 1) * F x = 0`.

## Implementation notes

The proof goes by defining `F'` and `F''` explicitly, showing that they are the first and second
derivative of `F`, and proving (using the explicit form of `F''`) that `F''` is nonnegative and thus
`F` convex.

## Technical notes

* The section `General` contains auxiliary lemmas, most importantly `ContinuousAt.lhopital_iterated`
  which generalizes L'Hôpital's rule to higher-order singularities
* The section `Calculations` handles derivatives: we use `HasDerivAt.div` for `x ≠ 1` and
  the custom lemma `HasDerivAt.extend_to_singularity` for extending to `x = 1`.
-/

open Set Filter

variable {x y : ℝ} {f f' g g' : ℝ → ℝ} {U : Set ℝ}

section General

/-!
### Derivative extension lemmas
-/

-- Extension lemma for HasDerivAt
lemma HasDerivAt.congr_on_open {f'x : ℝ} (hU_open : IsOpen U) (hx : x ∈ U)
    (hf : HasDerivAt f f'x x) (heq : U.EqOn f g) : HasDerivAt g f'x x :=
  HasDerivWithinAt.hasDerivAt (HasDerivWithinAt.congr (HasDerivAt.hasDerivWithinAt hf)
    (fun _ a ↦ (heq a).symm) (heq hx).symm) (IsOpen.mem_nhds hU_open hx)

-- Main extension theorem for derivatives
theorem HasDerivAt.extend_to_singularity (hU_open : IsOpen U) (hx : x ∈ U)
    (g_diff : ∀ y ≠ x, y ∈ U → HasDerivAt g (g' y) y)
    (hg : ContinuousAt g x) (hg' : ContinuousAt g' x) :
    HasDerivAt g (g' x) x := by
  have hInterval : ∃ a b, x ∈ Ioo a b ∧ Icc a b ⊆ U := by
    have ⟨δ, hδ, hy⟩ :=
    Metric.eventually_nhds_iff_ball.1 (eventually_closedBall_subset (IsOpen.mem_nhds hU_open hx))
    simp_rw [Real.ball_eq_Ioo, Real.closedBall_eq_Icc] at hy
    refine ⟨_, _, ⟨mem_Ioo.mpr ⟨?_, ?_⟩, hy (δ/2) (mem_Ioo.mpr ⟨?_, ?_⟩)⟩⟩ <;> linarith
  have ⟨a,b, hxI ,hIU⟩ := hInterval
  have h_diff_right : ∀ {y}, y ∈ Ioo x b → HasDerivAt g (g' y) y :=
    fun hyI ↦ (g_diff _ ((ne_of_lt hyI.1).symm)
      (hIU (mem_Icc_of_Ioo ((Ioo_subset_Ioo_left (le_of_lt hxI.1)) hyI))))
  have h_diff_left : ∀ {y}, y ∈ Ioo a x → HasDerivAt g (g' y) y :=
    fun hyI ↦ (g_diff _ (ne_of_lt hyI.2)
      (hIU (mem_Icc_of_Ioo ((Ioo_subset_Ioo_right (le_of_lt hxI.2)) hyI))))
  have h_right : HasDerivWithinAt g (g' x) (Icc x b) x := by
    rw [hasDerivWithinAt_iff_hasFDerivWithinAt]
    convert hasFDerivWithinAt_closure_of_tendsto_fderiv ?_ (convex_Ioo x b) isOpen_Ioo ?_ ?_ using 1
    · exact (closure_Ioo (ne_of_lt hxI.2)).symm
    · exact fun y hyI ↦ DifferentiableAt.differentiableWithinAt
        (HasFDerivAt.differentiableAt (h_diff_right hyI))
    · rw [closure_Ioo (ne_of_lt hxI.2)]
      intro y hy
      apply ContinuousAt.continuousWithinAt
      by_cases hxy : y = x
      · rwa [hxy]
      · exact HasFDerivAt.continuousAt
          (g_diff y hxy (hIU (Icc_subset_Icc_left (le_of_lt hxI.1) hy)))
    · simp_rw [toSpanSingleton_deriv.symm]
      let cle := ContinuousLinearMap.toSpanSingletonCLE (𝕜 := ℝ) (E := ℝ)
      exact Tendsto.comp (cle.continuous.continuousAt)
        (Tendsto.congr' (eventuallyEq_nhdsWithin_of_eqOn
          (fun _ hyI ↦ (HasDerivAt.deriv (h_diff_right hyI)).symm))
        (Tendsto.mono_left (y := nhdsWithin x (Ioo x b)) hg' nhdsWithin_le_nhds))
  have h_left : HasDerivWithinAt g (g' x) (Icc a x) x := by
    rw [hasDerivWithinAt_iff_hasFDerivWithinAt]
    convert hasFDerivWithinAt_closure_of_tendsto_fderiv ?_ (convex_Ioo a x) isOpen_Ioo ?_ ?_ using 1
    · exact (closure_Ioo (ne_of_lt hxI.1)).symm
    · exact fun y hyI ↦ DifferentiableAt.differentiableWithinAt
        (HasFDerivAt.differentiableAt (h_diff_left hyI))
    · rw [closure_Ioo (ne_of_lt hxI.1)]
      intro y hy
      apply ContinuousAt.continuousWithinAt
      by_cases hxy : y = x
      · rwa [hxy]
      · exact HasFDerivAt.continuousAt (g_diff y hxy
          (hIU (Icc_subset_Icc_right (le_of_lt hxI.2) hy)))
    · simp_rw [toSpanSingleton_deriv.symm]
      let cle := ContinuousLinearMap.toSpanSingletonCLE (𝕜 := ℝ) (E := ℝ)
      exact Tendsto.comp (cle.continuous.continuousAt)
        (Tendsto.congr' (eventuallyEq_nhdsWithin_of_eqOn
          (fun _ hyI ↦ (HasDerivAt.deriv (h_diff_left hyI)).symm))
        (Tendsto.mono_left (y := nhdsWithin x (Ioo a x)) hg' nhdsWithin_le_nhds))
  convert HasDerivWithinAt.hasDerivAt (HasDerivWithinAt.mono (h_left.union h_right) ?_)
    (Ioo_mem_nhds hxI.1 hxI.2)
  exact fun y hy ↦ (le_or_gt x y).elim (fun hxy => Or.inr ⟨hxy, hy.2.le⟩)
    (fun hxy => Or.inl ⟨hy.1.le, hxy.le⟩)


/-!
### Auxiliary analysis lemmas
-/

lemma pos_of_dist_one_lt_one (hx : dist x 1 < 1) : 0 < x := by
  rw [Real.dist_eq, abs_sub_lt_iff] at hx
  linarith

-- Extract property from neighborhood
lemma eventually_nhds_self {p : ℝ → Prop} (h : ∀ᶠ (y : ℝ) in nhds x, p y) : p x := by
  have ⟨_, hε, hall⟩ := (Metric.eventually_nhds_iff_ball.1 h)
  exact hall _ (Metric.mem_ball_self hε)

-- Propagate zeros to derivatives
lemma frequently_deriv_eq_zero_of_frequently_eq_zero
    (hx : g x = 0)
    (hDer : ∀ᶠ (y : ℝ) in nhds x, HasDerivAt g (g' y) y)
    (hgZero : ∃ᶠ (y : ℝ) in nhdsWithin x {x}ᶜ, g y = 0) :
    ∃ᶠ (y : ℝ) in nhdsWithin x {x}ᶜ, g' y = 0 := by
  rw [frequently_nhdsWithin_iff, frequently_nhds_iff]
  intro U hxU hUopen
  rw [eventually_nhds_iff] at hDer
  have ⟨V, hVder, hVopen, hxV⟩ := hDer
  have ⟨ε, hε, hBall⟩ := Metric.isOpen_iff.1 (hUopen.inter hVopen) _ ⟨hxU, hxV⟩
  rw [frequently_nhdsWithin_iff, frequently_nhds_iff] at hgZero
  have ⟨y, hUy, hy, hynx⟩ :=  hgZero (Metric.ball x ε) (Metric.mem_ball_self hε) Metric.isOpen_ball
  rw [Set.mem_compl_singleton_iff] at hynx
  let a := min x y; let b := max x y
  have rw_cases : a = x ∧ b = y ∨ a = y ∧ b = x := by
    rcases (lt_or_gt_of_ne hynx) with hyx | hxy
    · right; exact ⟨min_eq_right_of_lt hyx, max_eq_left_of_lt hyx⟩
    · left; exact ⟨min_eq_left_of_lt hxy, max_eq_right_of_lt hxy⟩
  have hab : a < b := min_lt_max.2 hynx.symm
  have hsub : Set.Icc a b ⊆ U ∩ V := by
    refine subset_trans ?_ hBall
    refine IsConnected.Icc_subset (Metric.isConnected_ball hε) ?_ ?_
    · rcases rw_cases with h | h <;> rw[h.1]
      · exact Metric.mem_ball_self hε
      · exact hUy
    · rcases rw_cases with h | h <;> rw[h.2]
      · exact hUy
      · exact Metric.mem_ball_self hε
  have hgab : g a = 0 ∧ g b = 0 := by
    rcases rw_cases with h | h <;> rw[h.1, h.2]
    · exact ⟨hx, hy⟩
    · exact ⟨hy, hx⟩
  have hxnot : x ∉ Set.Ioo a b := by
    intro hcontra; rw [Set.mem_Ioo] at hcontra
    rcases rw_cases with h | h <;> (rw[h.1, h.2] at hcontra; linarith)
  have ⟨z,hz,hg'z⟩ := exists_hasDerivAt_eq_slope g g' hab ?_ ?_
  · rw [hgab.1, hgab.2, sub_self, zero_div] at hg'z
    use z, (hsub (Set.Ioo_subset_Icc_self hz)).1, hg'z
    intro hcontra
    rw [Set.mem_singleton_iff.1 hcontra] at hz
    exact hxnot hz
  · exact HasDerivAt.continuousOn (fun w hw  ↦ hVder _ (hsub hw).2)
  · exact (fun w hw  ↦ hVder _ (hsub (Set.Ioo_subset_Icc_self hw)).2)

lemma ContinuousAt.eq_of_frequently_eq {g : ℝ → ℝ} {a x : ℝ}
    (hZero : ∃ᶠ y in nhdsWithin x {x}ᶜ, g y = a)
    (hCont : ContinuousAt g x) :
    g x = a :=
    (tendsto_nhds_unique_of_frequently_eq
      (tendsto_nhdsWithin_of_tendsto_nhds hCont)
      tendsto_const_nhds hZero)



lemma ConvexOn.tangent_line_le (hgc : ConvexOn ℝ U g) (hx : x ∈ U) (hy : y ∈ U)
  (hg' : HasDerivAt g (g' y) y) : g y + g' y * (x - y) ≤ g x := by
  rcases lt_trichotomy x y with hxy | hxy | hxy
  · rw [←le_sub_iff_add_le', ←neg_le_neg_iff, neg_sub, mul_comm, neg_mul_eq_neg_mul, neg_sub,
          ←div_le_iff₀' (by linarith), div_eq_inv_mul]
    convert ConvexOn.slope_le_of_hasDerivAt hgc hx hy hxy hg' using 1
  · simp only [hxy, sub_self, mul_zero, add_zero, le_refl]
  · let φ : ℝ → ℝ   := fun x ↦ -x
    have hgmc   : ConvexOn ℝ (φ '' U) (g ∘ φ) := by
      refine ⟨Convex.is_linear_image hgc.1 (IsLinearMap.isLinearMap_neg), ?_⟩
      intro mv ⟨v, hvS, hv⟩ mw ⟨w, hwS, hw⟩ a b hap hbp hab
      rw [←hv, ←hw]
      convert hgc.2 hvS hwS hap hbp hab using 1 <;> unfold φ
      · simp only [Function.comp_apply, smul_eq_mul, mul_neg, neg_add, neg_neg]
      · simp only [Function.comp_apply, neg_neg, smul_eq_mul]
    have hgm'c  : HasDerivAt (g ∘ φ) (φ (g' y)) (φ y) := by
      convert HasDerivAt.scomp (φ y) (h := φ) (h' := -1) (g₁ := g) (g₁' := g' y) ?_ ?_ using 1
      · simp only [smul_eq_mul, neg_mul, one_mul, φ]
      · convert hg'
        simp [φ]
      · exact hasDerivAt_neg' _
    rw [←le_sub_iff_add_le]
    apply (tsub_le_iff_left (c := - (g' y * (x - y)))).1
    rw [neg_mul_eq_neg_mul, ←mul_inv_le_iff₀ (by linarith), mul_comm]
    convert ConvexOn.slope_le_of_hasDerivAt (x := -x) hgmc ?_ ?_ ?_ hgm'c using 1
    · rw [slope, sub_neg_eq_add, add_comm]
      congr 1
      simp [φ]
    · exact (Set.mem_image _ _ _).2 ⟨x, hx, rfl⟩
    · exact (Set.mem_image _ _ _).2 ⟨y, hy, rfl⟩
    · exact neg_lt_neg_iff.mpr hxy

/-!
### L'Hôpital's rule
-/

-- General iterated L'Hôpital's rule
lemma ContinuousAt.lhopital_iterated (n : ℕ) (ns ds : List (ℝ → ℝ))
    (hnslen : ns.length = n + 1) (hdslen : ds.length = n + 1)
    (hnDer : ∀ k (hk : k < n), ∀ᶠ (y : ℝ) in nhds x, HasDerivAt ns[k] (ns[k + 1] y) y)
    (hdDer : ∀ k (hk : k < n), ∀ᶠ (y : ℝ) in nhds x, HasDerivAt ds[k] (ds[k + 1] y) y)
    (hnZero : ∀ k (hk : k < n), ns[k] x = 0)
    (hdZero : ∀ k (hk : k < n), ds[k] x = 0)
    (hnCont : ContinuousAt ns[n] x)
    (hdCont : ContinuousAt ds[n] x)
    (hdFinal : ds[n] x ≠ 0) :
    ContinuousAt
        (fun y ↦ if y = x
          then (ns[n] x) / (ds[n] x)
          else (ns[0] y) / (ds[0] y))
        x := by
  revert ns ds n; intro n
  induction n with
  | zero =>
    intro ns ds _ _ _ _ _ _  hnC hdC hnZ
    refine ContinuousAt.congr (ContinuousAt.div₀ hnC hdC hnZ) (Eq.eventuallyEq ?_)
    ext; split <;> simp_all only [ne_eq]
  | succ n ih =>
    intro ns ds len_ns len_ds hnDer hdDer hnZero hdZero hnC hdC hnZ
    rw [←continuousWithinAt_compl_self, ContinuousWithinAt, if_pos rfl]
    apply Filter.Tendsto.congr' (f₁ := fun y ↦ (ns[0] y) / (ds[0] y) )
      (eventually_nhdsWithin_of_forall fun y hy ↦ (if_neg hy).symm)
    have hn : 0 < n + 1 := Nat.zero_lt_succ _
    have hn_tail : ns.tail.length = n + 1 := by
      rw [List.length_tail, len_ns, add_tsub_cancel_right, Nat.add_left_cancel_iff]
    have hd_tail : ds.tail.length = n + 1 := by
      rw [List.length_tail, len_ds, add_tsub_cancel_right, Nat.add_left_cancel_iff]
    refine HasDerivAt.lhopital_zero_nhdsNE (f' := ns[1]) (g' := ds[1]) ?_ ?_ ?_ ?_ ?_ ?_
    · exact eventually_nhdsWithin_of_eventually_nhds (hnDer 0 hn)
    · exact eventually_nhdsWithin_of_eventually_nhds (hdDer 0 hn)
    · by_contra hcontra
      simp_rw [Filter.not_eventually, not_ne_iff] at hcontra
      have hInd : ∀ k (hk : k < n + 1), ∃ᶠ (x : ℝ) in nhdsWithin x {x}ᶜ, ds[k+1] x = 0 := by
        intro k
        induction k with
        | zero => exact fun _ ↦ hcontra
        | succ _ ih =>
          exact fun _ ↦ frequently_deriv_eq_zero_of_frequently_eq_zero (hdZero _ (by linarith))
            (hdDer _ (by linarith)) (ih (by linarith))
      specialize hInd n (by linarith)
      exact hnZ (ContinuousAt.eq_of_frequently_eq hInd hdC)
    · rw [←(hnZero 0 hn)]
      refine continuousWithinAt_compl_self.2 ?_
      have this := (eventually_nhds_self (hnDer 0 hn))
      exact HasDerivAt.continuousAt this
    · rw [←(hdZero 0 hn)]
      refine continuousWithinAt_compl_self.2 ?_
      have this := (eventually_nhds_self (hdDer 0 hn))
      exact HasDerivAt.continuousAt this
    · specialize ih ns.tail ds.tail hn_tail hd_tail ?_ ?_ ?_ ?_ ?_ ?_ ?_
      · intro k hk
        convert hnDer (k+1) (by linarith) using 3
        · refine List.getElem_tail (by linarith)
        · simp
      · intro k hk
        convert hdDer (k+1) (by linarith) using 3
        · refine List.getElem_tail (by linarith)
        · simp
      · exact fun k hk ↦ by convert hnZero (k + 1) (by linarith) using 1; simp
      · exact fun k hk ↦ by convert hdZero (k + 1) (by linarith) using 1; simp
      · convert hnC using 1; simp
      · convert hdC using 1; simp
      · convert hnZ using 1; simp
      · rw [←continuousWithinAt_compl_self, ContinuousWithinAt, if_pos rfl] at ih
        convert Filter.Tendsto.congr' ?_ ih using 2
        · simp
        · refine eventually_nhdsWithin_of_forall ?_
          intro _ hy
          convert if_neg hy using 1
          simp

end General


/-!
### Function analysis and calculations
-/

noncomputable section Calculations

open Polynomial

/-!
### Main definitions
-/

-- Domain
def S : Set ℝ := {x | 0 < x ∧ x ≠ 1}

-- Main function `F` and its derivatives.
def F : ℝ → ℝ := fun x ↦
  if x = 1 then 1/2
  else          (x * Real.log x - x + 1) / (x - 1)^2

def F' : ℝ → ℝ := fun x ↦
  if x = 1 then -1/6
  else          (-2 + 2*x - Real.log x - x * Real.log x) / (x - 1)^3

def F'' : ℝ → ℝ := fun x ↦
  if x = 1 then 1/6
  else          (1 + 4*x - 5*x^2 + 4 * x * Real.log x + 2 * x^2 * Real.log x) / ((x - 1)^4 * x)

/-!
### Numerators and denominators of F, F', and F''.
-/
-- `F`
def nF₀ : ℝ → ℝ := fun x ↦ x * Real.log x - x + 1
def nF₁ : ℝ → ℝ := fun x ↦ Real.log x
def nF₂ : ℝ → ℝ := fun x ↦ 1/x

def dF₀ : ℝ → ℝ := fun x ↦ (x - 1)^2
def dF₁ : ℝ → ℝ := fun x ↦ 2 * (x - 1)
def dF₂ : ℝ → ℝ := fun _ ↦ 2

-- `F'`
def nF'₀ : ℝ → ℝ := fun x ↦ -2 + 2*x - Real.log x - x * Real.log x
def nF'₁ : ℝ → ℝ := fun x ↦ 1 - 1/x - Real.log x
def nF'₂ : ℝ → ℝ := fun x ↦ 1 / x^2 - 1 / x
def nF'₃ : ℝ → ℝ := fun x ↦ -2 / x^3 + 1 / x^2

def dF'₀ : ℝ → ℝ := fun x ↦ (x - 1)^3
def dF'₁ : ℝ → ℝ := fun x ↦ 3 * (x - 1)^2
def dF'₂ : ℝ → ℝ := fun x ↦ 6 * (x - 1)
def dF'₃ : ℝ → ℝ := fun _ ↦ 6

-- `F''`
def nF''₀ : ℝ → ℝ := fun x ↦ 1 + 4*x - 5*x^2 + 4 * x * Real.log x + 2 * x^2 * Real.log x
def nF''₁ : ℝ → ℝ := fun x ↦ 8 - 8 * x + 4 * Real.log x  + 4 * x * Real.log x
def nF''₂ : ℝ → ℝ := fun x ↦ -4 + 4/x + 4 * Real.log x
def nF''₃ : ℝ → ℝ := fun x ↦ -4 / x^2 + 4 / x
def nF''₄ : ℝ → ℝ := fun x ↦ 8 / x^3 - 4 / x^2

def dF''₀ : ℝ → ℝ := fun x ↦ (x - 1)^4 * x
def dF''₁ : ℝ → ℝ := fun x ↦ 1 - 8 * x + 18 * x^2 - 16 * x^3 + 5 * x^4
def dF''₂ : ℝ → ℝ := fun x ↦ -8 + 36 * x - 48 * x^2 + 20 * x^3
def dF''₃ : ℝ → ℝ := fun x ↦ 36 - 96 * x + 60 * x^2
def dF''₄ : ℝ → ℝ := fun x ↦ -96 + 120 * x

/-!
### Lemmas about S
-/

lemma S_open : IsOpen S := IsOpen.and (isOpen_lt' 0) (isOpen_ne)

lemma pos_not_in_S_eq_one (hx_pos : 0 < x) (hx_not_in_S : x ∉ S) : x = 1 := by
  by_contra hxn1
  exact hx_not_in_S ⟨hx_pos, hxn1⟩

/-!
### F, F', and F'' equal to rational functions on S
-/


lemma F_not_one (hx : x ≠ 1) : F x   = nF₀ x / dF₀ x       := if_neg hx
lemma F'_not_one (hx : x ≠ 1) : F' x  = nF'₀ x / dF'₀ x     := if_neg hx
lemma F''_not_one (hx : x ≠ 1) : F'' x = nF''₀ x / dF''₀ x   := if_neg hx

lemma F_at_zero : F 0    = 1  := by simp [F]
lemma F_at_one : F 1    = 1/2  := if_pos rfl
lemma F'_at_one : F' 1   = -1/6 := if_pos rfl
lemma F''_at_one : F'' 1  = 1/6  := if_pos rfl

lemma F_on_S : S.EqOn F    (fun x ↦ nF₀ x    / dF₀ x)    := fun _ hx ↦ if_neg hx.2
lemma F'_on_S : S.EqOn F'   (fun x ↦ nF'₀ x   / dF'₀ x)   := fun _ hx ↦ if_neg hx.2
lemma F''_on_S : S.EqOn F''  (fun x ↦ nF''₀ x  / dF''₀ x)  := fun _ hx ↦ if_neg hx.2

/-!
### Derivatives of the numerators and denominators of F, F' and F''
-/

/-!
  Two helpful rewrite lemmas about the derivatives of `x ↦ 1/x` and `x ↦ 1/x^2`.
-/

lemma hasDerivAtInv (hx : 0 < x) : HasDerivAt (fun y ↦ 1 / y) (- 1 / x^2) x := by
  convert hasDerivAt_inv (ne_of_lt hx).symm using 1
  · ext _; ring
  · ring

lemma hasDerivAtInvSq (hx : 0 < x) : HasDerivAt (fun y ↦ 1 / y^2) (- 2 / x^3) x := by
  convert HasDerivAt.inv (c := fun y ↦ y^2) (c' := 2 * x) ?_ ?_ using 1
  · ext _; simp
  · field_simp
  · convert Polynomial.hasDerivAt (X (R := ℝ) ^ 2) _ <;> norm_num
  · positivity

-- `F`

lemma hasDerivAt_nF₀ (hx : 0 < x) : HasDerivAt nF₀ (nF₁ x) x := by
  unfold nF₀ nF₁
  convert HasDerivAt.add_const 1 (HasDerivAt.sub (f := fun x ↦ x * Real.log x)
    (f' := Real.log x + 1) ?_ (hasDerivAt_id' x)) using 1
  · ring
  · convert HasDerivAt.mul (hasDerivAt_id' x) (Real.hasDerivAt_log (ne_of_lt hx).symm) using 1
    field_simp

lemma hasDerivAt_nF₁ (hx : 0 < x) : HasDerivAt nF₁ (nF₂ x) x := by
  unfold nF₂
  convert Real.hasDerivAt_log (ne_of_lt hx).symm using 1
  exact one_div x

lemma hasDerivAt_dF₀ : HasDerivAt dF₀ (dF₁ x) x := by
  convert Polynomial.hasDerivAt (1 - 2 * X (R := ℝ) + X^2) _ <;> norm_num
  · unfold dF₀; ring
  · unfold dF₁; ring

lemma hasDerivAt_dF₁ : HasDerivAt dF₁ (dF₂ x) x := by
  convert Polynomial.hasDerivAt (-2 + 2 * X (R := ℝ)) _ <;> norm_num
  · unfold dF₁; ring
  · rfl

-- `F'`

lemma hasDerivAt_nF'₀ (hx : 0 < x) : HasDerivAt nF'₀ (nF'₁ x) x := by
  unfold nF'₀ nF'₁
  convert HasDerivAt.sub (f := fun x ↦ 2*x - 2) (f' := 2)
    (g := fun x ↦ (1 + x) * Real.log x) (g' := 1 + 1/x + Real.log x) ?_ ?_ using 1
  · ext _; rw [Pi.sub_apply]; ring
  · ring
  · convert Polynomial.hasDerivAt (- 2 + 2 * X (R := ℝ)) _ <;> norm_num
    ring
  · convert HasDerivAt.mul (c := fun x ↦ 1 + x) (c' := 1) ?_
      (Real.hasDerivAt_log (ne_of_lt hx).symm) using 1
    · field_simp; ring
    · convert Polynomial.hasDerivAt (1 + X (R := ℝ)) _ <;> norm_num

lemma hasDerivAt_nF'₁ (hx : 0 < x) : HasDerivAt nF'₁ (nF'₂ x) x := by
  unfold nF'₁ nF'₂
  convert HasDerivAt.sub (f := fun x ↦ 1 - 1/x) (f' := 1 / x^2) ?_
    (Real.hasDerivAt_log (ne_of_lt hx).symm) using 1
  · field_simp
  · convert HasDerivAt.sub (g := fun x ↦ 1 / x) (g' := - 1 / x^2)
      (hasDerivAt_const x 1) (hasDerivAtInv hx) using 1
    ring

lemma hasDerivAt_nF'₂ (hx : 0 < x) : HasDerivAt nF'₂ (nF'₃ x) x := by
  unfold nF'₂ nF'₃
  convert HasDerivAt.sub (hasDerivAtInvSq hx) (hasDerivAtInv hx) using 1
  field_simp; ring

lemma hasDerivAt_dF'₀ : HasDerivAt dF'₀ (dF'₁ x) x := by
  convert Polynomial.hasDerivAt (- 1 + 3 * X (R := ℝ) - 3 * X^2 + X^3) _ <;> norm_num
  · unfold dF'₀; ring
  · unfold dF'₁; ring

lemma hasDerivAt_dF'₁ : HasDerivAt dF'₁ (dF'₂ x) x := by
  convert Polynomial.hasDerivAt (3 - 6 * X (R := ℝ) + 3 * X^2) _ <;> norm_num
  · unfold dF'₁; ring
  · unfold dF'₂; ring

lemma hasDerivAt_dF'₂ : HasDerivAt dF'₂ (dF'₃ x) x := by
  convert Polynomial.hasDerivAt (-6 + 6 * X (R := ℝ)) _ <;> norm_num
  · unfold dF'₂; ring
  · unfold dF'₃; ring

-- `F''`

lemma hasDerivAt_nF''₀ (hx : 0 < x) : HasDerivAt nF''₀ (nF''₁ x) x := by
  unfold nF''₀ nF''₁
  convert HasDerivAt.add
    (f := fun x ↦ 1 + 4 * x - 5 * x^2) (f' := 4 - 10*x)
    (g := fun x ↦ (4 * x + 2 * x^2) * Real.log x)
    (g' := 4 + 2 * x + 4 * Real.log x + 4 * x * Real.log x) ?_ ?_ using 1
  · ext _; rw [Pi.add_apply]; ring
  · ring
  · convert Polynomial.hasDerivAt (1 + 4 * X (R := ℝ) - 5 * X^2) _ <;> norm_num; ring
  · convert HasDerivAt.mul (c := fun x ↦ 4 * x + 2 * x^2) (c' := 4 + 4 * x) ?_
      (Real.hasDerivAt_log (ne_of_lt hx).symm) using 1
    · field_simp; ring
    · convert Polynomial.hasDerivAt (4 * X (R := ℝ) + 2 * X^2) _ <;> norm_num; ring

lemma hasDerivAt_nF''₁ (hx : 0 < x) : HasDerivAt nF''₁ (nF''₂ x) x := by
  unfold nF''₁ nF''₂
  convert HasDerivAt.add
    (f := fun x ↦ 8 - 8 * x) (f' := - 8)
    (g := fun x ↦ (4 + 4 * x) * Real.log x) (g' := 4 + 4 / x + 4 * Real.log x) ?_ ?_ using 1
  · ext _; rw [Pi.add_apply]; ring
  · ring
  · convert Polynomial.hasDerivAt (8 - 8 * X (R := ℝ)) _ <;> norm_num
  · convert HasDerivAt.mul (c := fun x ↦ 4 + 4 * x) (c' := 4) ?_
      (Real.hasDerivAt_log (ne_of_lt hx).symm) using 1
    · field_simp; ring
    · convert Polynomial.hasDerivAt (4 + 4 * X (R := ℝ)) _ <;> norm_num

lemma hasDerivAt_nF''₂ (hx : 0 < x) : HasDerivAt nF''₂ (nF''₃ x) x := by
  unfold nF''₂ nF''₃
  convert HasDerivAt.add
    (f := fun x ↦ -4 + 4/x) (f' := -4 / x^2) ?_
    (HasDerivAt.const_mul _ (Real.hasDerivAt_log (ne_of_lt hx).symm)) using 1
  convert HasDerivAt.add (hasDerivAt_const x (-4))
    (HasDerivAt.const_mul 4 (hasDerivAtInv hx)) using 1
  · ext _; rw [Pi.add_apply]; ring
  · ring

lemma hasDerivAt_nF''₃ (hx : 0 < x) : HasDerivAt nF''₃ (nF''₄ x) x := by
  unfold nF''₃ nF''₄
  convert HasDerivAt.add (HasDerivAt.const_mul (-4) (hasDerivAtInvSq hx))
    (HasDerivAt.const_mul 4 (hasDerivAtInv hx)) using 1
  · ext _; rw [Pi.add_apply]; ring
  · ring

lemma hasDerivAt_dF''₀ : HasDerivAt dF''₀ (dF''₁ x) x := by
  convert Polynomial.hasDerivAt (X - 4 * X^2 + 6 * X^3 - 4 * X^4 + X^5 : ℝ[X]) _ <;> norm_num
  · unfold dF''₀; ring
  · unfold dF''₁; ring

lemma hasDerivAt_dF''₁ : HasDerivAt dF''₁ (dF''₂ x) x := by
  convert Polynomial.hasDerivAt (1 - 8 * X (R := ℝ) + 18 * X^2 - 16 * X^3 + 5 * X^4) _ <;> norm_num
  · unfold dF''₁; ring
  · unfold dF''₂; ring

lemma hasDerivAt_dF''₂ : HasDerivAt dF''₂ (dF''₃ x) x := by
  convert Polynomial.hasDerivAt (-8 + 36 * X (R := ℝ) - 48 * X^2 + 20 * X^3 ) _ <;> norm_num
  · unfold dF''₂; ring
  · unfold dF''₃; ring

lemma hasDerivAt_dF''₃ : HasDerivAt dF''₃ (dF''₄ x) x := by
  convert Polynomial.hasDerivAt (36 - 96 * X (R := ℝ) + 60 * X^2) _ <;> norm_num
  · unfold dF''₃; ring
  · unfold dF''₄; ring




/-!
### Continuity of (derivatives of) denominators and numerators
-/

lemma ContinuousAt_dF₀ : ContinuousAt dF₀ x := by
  unfold dF₀
  exact ContinuousAt.pow (ContinuousAt.sub (by exact fun ⦃U⦄ a ↦ a) continuousAt_const) _

lemma ContinuousAt_nF₀ : ContinuousAt nF₀ x  :=
  ContinuousAt.add (ContinuousAt.sub (Continuous.continuousAt Real.continuous_mul_log ) fun _ a ↦ a)
    continuousAt_const

lemma ContinuousAt_nF₂ (hx : 0 < x) : ContinuousAt nF₂ x := by unfold nF₂; continuity

lemma ContinuousAt_dF₂ : ContinuousAt dF₂ x := continuousAt_const

lemma ContinuousAt_nF'₃ (hx : 0 < x) : ContinuousAt nF'₃ x := by
  refine ContinuousAt.add ?_ ?_ <;>
  exact ContinuousAt.div₀ continuousAt_const
    (ContinuousAt.pow (by exact fun _ a ↦ a) _) (by positivity)

lemma ContinuousAt_dF'₃ : ContinuousAt dF'₃ x := continuousAt_const

lemma ContinuousAt_nF''₄ (hx : 0 < x) : ContinuousAt nF''₄ x := by
  refine ContinuousAt.add ?_ (ContinuousAt.neg ?_) <;>
  exact ContinuousAt.div₀ continuousAt_const
    (ContinuousAt.pow (by exact fun _ a ↦ a) _) (by positivity)

lemma ContinuousAt_dF''₄ : ContinuousAt dF''₄ x := by
  unfold dF''₄
  exact Continuous.continuousAt (by continuity)


/-!
### Useful (in)equalities involving the denominators and numerators
-/



lemma dF₀_ne_zero (hx : x ≠ 1) : dF₀ x ≠ 0      := pow_ne_zero 2 (sub_ne_zero_of_ne hx)
lemma dF₀_ne_zero_on_S (hx : x ∈ S) : dF₀ x ≠ 0 := dF₀_ne_zero hx.2

lemma dF'₀_ne_zero (hx : x ≠ 1) : dF'₀ x ≠ 0      := pow_ne_zero 3 (sub_ne_zero_of_ne hx)
lemma dF'₀_ne_zero_on_S (hx : x ∈ S) : dF'₀ x ≠ 0 := dF'₀_ne_zero hx.2
lemma dF'₀_nonneg (hx : 1 < x) : 0 ≤ dF'₀ x       := pow_nonneg (by linarith) 3

lemma dF''₀_nonneg (hx : 0 < x) : 0 ≤ dF''₀ x  := by unfold dF''₀; positivity

lemma dF''₀_ne_zero_on_S (hx : x ∈ S) : dF''₀ x ≠ 0   :=
  (mul_ne_zero_iff_right (ne_of_lt hx.1).symm).mpr (pow_ne_zero 4 (sub_ne_zero_of_ne hx.2))


/-!
  To prove that `nF''₀` is nonnegative we define two types of functions:
  `isType1`: Nonincreasing on (0,1], nondecreasing on [1,∞) and zero at x = 1.
  `isType2`: Nonpositive on (0,1] and nonnegative on [1,∞).
  We prove that a function `l` with `l 1 = 0` whose derivative is one type is itself the other type.
-/

def isType1 (l : ℝ → ℝ) :=  AntitoneOn l (Ioc 0 1) ∧ MonotoneOn l (Ici 1) ∧ (l 1 = 0)
def isType2 (l : ℝ → ℝ) :=  (∀ {x}, x ∈ Ioc 0 1 → l x ≤ 0) ∧ (∀ {x}, x ∈ Ici 1 → 0 ≤ l x)

lemma Type1_nonneg {l : ℝ → ℝ} (hType : isType1 l) (hx : 0 < x) : 0 ≤ l x := by
  rw [←hType.2.2]
  rcases le_or_gt x 1 with hx1 | hx1
  · exact hType.1 ⟨hx,hx1⟩ ⟨Real.zero_lt_one, le_refl 1⟩ hx1
  · exact hType.2.1 self_mem_Ici (mem_Ici_of_Ioi hx1) (le_of_lt hx1)

lemma Type2_mul_nonneg {l m : ℝ → ℝ} (hType : isType2 l) (hm : ∀ {x}, 0 < x → 0 ≤ m x) :
  isType2 (fun x ↦ l x * m x) :=
  ⟨ fun hx ↦ mul_nonpos_of_nonpos_of_nonneg (hType.1 hx) (hm hx.1),
    fun hx ↦ Left.mul_nonneg (hType.2 hx) (hm (by linarith [mem_Ici.1 hx]))⟩

lemma DerivAt_Type1_imp_Type2 {l l' : ℝ → ℝ} (hType : isType1 l')
    (hDer : ∀ {x}, 0 < x → HasDerivAt l (l' x) x)
    (h : l 1 = 0) : isType2 l := by
  have h_mon : MonotoneOn l (Ioi 0) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (f' := l')
    · exact fun _ hx ↦ ContinuousAt.continuousWithinAt (HasDerivAt.continuousAt (hDer hx))
    · rw [interior_Ioi]
      exact fun y hy ↦ HasDerivAt.hasDerivWithinAt (hDer hy)
    · rw [interior_Ioi]
      exact fun x hx ↦ Type1_nonneg hType hx
    · exact convex_Ioi 0
  refine ⟨?_,?_⟩ <;> (intro x hx; rw [←h])
  · exact h_mon (mem_of_mem_inter_left hx) (by norm_num) (by exact hx.2)
  · refine h_mon (by norm_num) ?_ (by exact hx)
    rw [mem_Ioi]; rw [mem_Ici] at hx; linarith

lemma DerivAt_Type2_imp_Type1 {l l' : ℝ → ℝ} (hType : isType2 l')
    (hDer : ∀ {x}, 0 < x → HasDerivAt l (l' x) x)
    (h : l 1 = 0) : isType1 l := by
  refine ⟨?_, ⟨?_, h⟩⟩
  · apply antitoneOn_of_hasDerivWithinAt_nonpos (f' := l')
    · exact fun _ hx ↦ ContinuousAt.continuousWithinAt (HasDerivAt.continuousAt (hDer hx.1))
    · rw [interior_Ioc]
      exact fun y hy ↦ HasDerivAt.hasDerivWithinAt (hDer hy.1)
    · rw [interior_Ioc]
      exact fun x hx ↦ (hType.1 (mem_Ioc_of_Ioo hx))
    · exact convex_Ioc 0 1
  · apply monotoneOn_of_hasDerivWithinAt_nonneg (f' := l')
    · exact fun _ hx ↦ ContinuousAt.continuousWithinAt
        (HasDerivAt.continuousAt (hDer (by linarith [mem_Ici.1 hx])))
    · rw [interior_Ici]
      exact fun y hy ↦ HasDerivAt.hasDerivWithinAt (hDer (by linarith [mem_Ioi.1 hy]))
    · rw [interior_Ici]
      exact fun x hx ↦ (hType.2 (mem_Ici_of_Ioi hx))
    · exact convex_Ici 1


/-!
  We prove that the first few derivatives of `nF''₀` alternate between these two types.
-/

lemma isType2_nF''₃ : isType2 nF''₃ := by
  convert Type2_mul_nonneg (l := fun x ↦ -4 + 4*x) (m := fun x ↦ 1 / x^2) ?_ ?_ using 1
  · unfold nF''₃; ext x;
    by_cases hx : x = 0
    · rw [hx]; simp
    · field_simp
  · refine ⟨?_,?_⟩ <;> (intro _ _; simp_all)
  · intro _ _; simp [sq_nonneg]

lemma isType1_nF''₂ : isType1 nF''₂ :=
  DerivAt_Type2_imp_Type1 isType2_nF''₃ hasDerivAt_nF''₂ (by norm_num [nF''₂])

lemma isType2_nF''₁ : isType2 nF''₁ :=
  DerivAt_Type1_imp_Type2 isType1_nF''₂ hasDerivAt_nF''₁ (by norm_num [nF''₁])

lemma isType1_nF''₀ : isType1 nF''₀ :=
  DerivAt_Type2_imp_Type1 isType2_nF''₁ hasDerivAt_nF''₀ (by norm_num [nF''₀])

lemma nF''₀_nonneg (hx : 0 < x) : 0 ≤ nF''₀ x  := Type1_nonneg (isType1_nF''₀) hx

/-!
  As a convenient corollary we find that nF'₀ is nonpositive.
-/

lemma nF'₀_nonpos (hx : 1 ≤ x) : nF'₀ x ≤ 0  := by
  have h₁ : -4 * nF'₀ x = nF''₁ x := by unfold nF'₀ nF''₁; ring
  have h₂ : 0 ≤ nF''₁ x           := isType2_nF''₁.2 hx
  linarith


/-!
### Continuity of F, F' and F'' at x = 1.
-/

lemma F_continuousAt_one : ContinuousAt F 1 := by
  convert ContinuousAt.lhopital_iterated 2
    [nF₀, nF₁, nF₂] [dF₀, dF₁, dF₂] rfl rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ using 1
  · unfold F nF₂ dF₂; congr! 2; norm_num
  · intro k _
    interval_cases k <;> (rw [Metric.eventually_nhds_iff]; use 1, Real.zero_lt_one; intro _ hy)
    · exact hasDerivAt_nF₀ (pos_of_dist_one_lt_one hy)
    · exact hasDerivAt_nF₁ (pos_of_dist_one_lt_one hy)
  · intro k _
    interval_cases k <;> refine Filter.Eventually.of_forall ?_
    · exact (fun x ↦ hasDerivAt_dF₀)
    · exact (fun x ↦ hasDerivAt_dF₁)
  · intro k _
    interval_cases k <;> norm_num [nF₀, nF₁]
  · intro k _
    interval_cases k <;> norm_num [dF₀, dF₁]
  · exact ContinuousAt_nF₂ (by norm_num)
  · exact ContinuousAt_dF₂
  · simp [dF₂]

lemma F'_continuousAt_one : ContinuousAt F' 1 := by
  convert ContinuousAt.lhopital_iterated 3
    [nF'₀, nF'₁, nF'₂, nF'₃] [dF'₀, dF'₁, dF'₂, dF'₃] rfl rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ using 1
  · unfold F' nF'₃ dF'₃; congr! 2; norm_num
  · intro k _
    interval_cases k <;> (rw [Metric.eventually_nhds_iff]; use 1, Real.zero_lt_one; intro _ hy)
    · exact hasDerivAt_nF'₀ (pos_of_dist_one_lt_one hy)
    · exact hasDerivAt_nF'₁ (pos_of_dist_one_lt_one hy)
    · exact hasDerivAt_nF'₂ (pos_of_dist_one_lt_one hy)
  · intro k _
    interval_cases k <;> refine Filter.Eventually.of_forall ?_
    · exact (fun x ↦ hasDerivAt_dF'₀)
    · exact (fun x ↦ hasDerivAt_dF'₁)
    · exact (fun x ↦ hasDerivAt_dF'₂)
  · intro k _
    interval_cases k <;> norm_num [nF'₀, nF'₁, nF'₂]
  · intro k _
    interval_cases k <;> norm_num [dF'₀, dF'₁, dF'₂]
  · exact ContinuousAt_nF'₃ (by norm_num)
  · exact ContinuousAt_dF'₃
  · simp [dF'₃]

lemma F''_continuousAt_one : ContinuousAt F'' 1 := by
  convert ContinuousAt.lhopital_iterated 4
    [nF''₀, nF''₁, nF''₂, nF''₃, nF''₄] [dF''₀, dF''₁, dF''₂, dF''₃, dF''₄]
      rfl rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ using 1
  · unfold F'' nF''₄ dF''₄; congr! 2; norm_num
  · intro k _
    interval_cases k <;> (rw [Metric.eventually_nhds_iff]; use 1, Real.zero_lt_one; intro _ hy)
    · exact hasDerivAt_nF''₀ (pos_of_dist_one_lt_one hy)
    · exact hasDerivAt_nF''₁ (pos_of_dist_one_lt_one hy)
    · exact hasDerivAt_nF''₂ (pos_of_dist_one_lt_one hy)
    · exact hasDerivAt_nF''₃ (pos_of_dist_one_lt_one hy)
  · intro k _
    interval_cases k <;> refine Filter.Eventually.of_forall ?_
    · exact (fun x ↦ hasDerivAt_dF''₀)
    · exact (fun x ↦ hasDerivAt_dF''₁)
    · exact (fun x ↦ hasDerivAt_dF''₂)
    · exact (fun x ↦ hasDerivAt_dF''₃)
  · intro k _
    interval_cases k <;> norm_num [nF''₀, nF''₁, nF''₂, nF''₃]
  · intro k _
    interval_cases k <;> norm_num [dF''₀, dF''₁, dF''₂, dF''₃]
  · exact ContinuousAt_nF''₄ (by norm_num)
  · exact ContinuousAt_dF''₄
  · norm_num [dF''₄]


/-!
### Derivatives of F, F'.
-/

/-!
  First two auxilliary lemmas giving the derivatives on S.
-/

lemma hasDerivAt_F_on_S (hx : x ∈ S) : HasDerivAt F (F' x) x := by
  refine HasDerivAt.congr_on_open S_open hx ?_ F_on_S.symm
  convert HasDerivAt.div (hasDerivAt_nF₀ hx.1) hasDerivAt_dF₀ (dF₀_ne_zero_on_S hx) using 1
  rw [F'_on_S hx]
  field_simp [dF₀_ne_zero_on_S hx, dF'₀_ne_zero_on_S hx]
  unfold dF₀ nF₀ dF'₀ nF'₀ nF₁ dF₁
  ring

lemma hasDerivAt_F'_on_S (hx : x ∈ S) : HasDerivAt F' (F'' x) x := by
  refine HasDerivAt.congr_on_open S_open hx ?_ F'_on_S.symm
  convert HasDerivAt.div (hasDerivAt_nF'₀ hx.1) hasDerivAt_dF'₀ (dF'₀_ne_zero_on_S hx) using 1
  rw [F''_on_S hx]
  field_simp [dF'₀_ne_zero_on_S hx, dF''₀_ne_zero_on_S hx]
  unfold dF'₀ nF'₀ dF''₀ nF''₀ nF'₁ dF'₁
  field_simp [(ne_of_lt hx.1).symm]
  ring

/-!
  Then the derivatives on (0,∞).
-/

lemma hasDerivAt_F (hx : 0 < x) : HasDerivAt F (F' x) x := by
  by_cases hxS : x ∈ S
  · exact hasDerivAt_F_on_S hxS
  · rw [pos_not_in_S_eq_one hx hxS]
    exact HasDerivAt.extend_to_singularity (isOpen_Ioi (a := 0)) (by norm_num)
      (fun y hyn1 hy ↦ hasDerivAt_F_on_S ⟨hy,hyn1⟩) (F_continuousAt_one) (F'_continuousAt_one)

lemma hasDerivAt_F' (hx : 0 < x) : HasDerivAt F' (F'' x) x := by
  by_cases hxS : x ∈ S
  · exact hasDerivAt_F'_on_S hxS
  · rw [pos_not_in_S_eq_one hx hxS]
    exact HasDerivAt.extend_to_singularity (isOpen_Ioi (a := 0)) (by norm_num)
      (fun y hyn1 hy ↦ hasDerivAt_F'_on_S ⟨hy,hyn1⟩) (F'_continuousAt_one) (F''_continuousAt_one)

/-!
### Continuity of F, F'.
-/

lemma F_Continuous : Continuous F  := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x = 1
  · rw [hx]
    exact HasDerivAt.continuousAt (hasDerivAt_F (by norm_num))
  · rw [←continuousWithinAt_iff_continuousAt (mem_nhds_iff.2 ⟨_, ⟨fun _ a ↦ a, isOpen_ne, hx⟩⟩)]
    exact ContinuousWithinAt.congr (f := fun x ↦ nF₀ x / dF₀ x) (
      ContinuousWithinAt.div (ContinuousAt.continuousWithinAt ContinuousAt_nF₀)
        (ContinuousAt.continuousWithinAt ContinuousAt_dF₀ ) (pow_ne_zero 2 (sub_ne_zero_of_ne hx)))
        (fun _ hy ↦ by simp only [F, if_neg hy, nF₀, dF₀]) (by simp only [F, if_neg hx, nF₀, dF₀])

lemma F_ContinuousAt (hx : 0 < x) : ContinuousAt F x   := HasDerivAt.continuousAt (hasDerivAt_F hx)
lemma F'_ContinuousAt (hx : 0 < x) : ContinuousAt F' x := HasDerivAt.continuousAt (hasDerivAt_F' hx)

/-
### Convexity of F, nonpositivity of F' and F is at most 1.
-/

lemma F''_nonnegative (hx : 0 < x) : 0 ≤ F'' x := by
  · by_cases hxS : x ∈ S
    · rw [F''_on_S hxS]
      exact div_nonneg (nF''₀_nonneg hxS.1) (dF''₀_nonneg hxS.1)
    · rw [F'', pos_not_in_S_eq_one hx hxS]
      norm_num

lemma F_convex : ConvexOn ℝ (Set.Ioi 0) F := by
  refine convexOn_of_hasDerivWithinAt2_nonneg (f := F) (f' := F') (f'' := F'') (convex_Ioi 0)
    (fun x hx ↦ ContinuousAt.continuousWithinAt (F_ContinuousAt hx))
    ?_ ?_ ?_ <;> (intro x hx; rw [interior_Ioi] at hx;)
  · exact HasDerivAt.hasDerivWithinAt (hasDerivAt_F hx)
  · exact HasDerivAt.hasDerivWithinAt (hasDerivAt_F' hx)
  · exact F''_nonnegative hx

lemma F_convex_inequality {x y : ℝ} (hx : 0 ≤ x) (hy : 0 < y)
    : F x ≥ F y + F' y * (x - y) := by
  rcases (LE.le.lt_or_eq' hx) with hx | hx
  · exact ConvexOn.tangent_line_le F_convex hx hy (hasDerivAt_F hy)
  · rw [ge_iff_le, hx]
    refine ContinuousWithinAt.closure_le (s := Ioo 0 1)
      (f := fun x ↦ F y + F' y * (x - y)) ?_ ?_ ?_ ?_
    · rw [closure_Ioo (by norm_num)]
      exact unitInterval.zero_mem
    · exact Continuous.continuousWithinAt (by continuity)
    · refine ContinuousWithinAt.congr ?_ (fun _ hy ↦ F_on_S ⟨hy.1, (ne_of_gt hy.2).symm⟩) ?_
      · refine ContinuousWithinAt.div ?_ ?_ (by simp [dF₀])
        · exact ContinuousAt.continuousWithinAt ContinuousAt_nF₀
        · exact ContinuousAt.continuousWithinAt ContinuousAt_dF₀
      · simp [F,nF₀,dF₀]
    · exact fun _ hx ↦ ConvexOn.tangent_line_le F_convex hx.1 hy (hasDerivAt_F hy)

lemma F'_nonpositive (hx : 0 < x) : F' x ≤ 0 := by
  have h_mon : MonotoneOn F' (Ioi 0) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (f' := F'') (convex_Ioi 0) ?_ ?_ ?_
    · exact fun y hy ↦ ContinuousAt.continuousWithinAt (F'_ContinuousAt hy)
    · rw [interior_Ioi]
      exact fun y hy ↦ HasDerivAt.hasDerivWithinAt (hasDerivAt_F' hy)
    · rw [interior_Ioi]
      exact fun y hy ↦ F''_nonnegative hy
  rcases (le_or_gt x 1) with hx1 | hx1
  · exact le_trans (h_mon hx (by norm_num) hx1) (by norm_num [F'])
  · rw [F'_on_S ⟨by linarith,(ne_of_lt hx1).symm⟩]
    exact div_nonpos_of_nonpos_of_nonneg (nF'₀_nonpos (le_of_lt hx1)) (dF'₀_nonneg hx1)

lemma F_at_most_one (hx : 0 ≤ x) : 1 ≥ F x := by
  have h_mon : AntitoneOn F (Ici 0) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (f' := F')
    · exact Continuous.continuousOn F_Continuous
    · rw [interior_Ici]
      exact fun y hy ↦ HasDerivAt.hasDerivWithinAt (hasDerivAt_F hy)
    · rw [interior_Ici]
      exact fun y hy ↦ F'_nonpositive hy
    · exact convex_Ici 0
  rw [←(by simp[F] : F 0 = 1)]
  exact h_mon self_mem_Ici hx hx


/-
### Finally the differential equation that F satisfies.
-/

lemma F_diff_equation : (x - x^2) * F' x - (x + 1) * F x + 1 = 0 := by
  by_cases hx : x = 1
  · rw [hx, F_at_one, F'_at_one]; norm_num
  · rw [F_not_one hx, F'_not_one hx, ←mul_right_inj' (dF₀_ne_zero hx),
        ←mul_right_inj' (dF'₀_ne_zero hx), mul_zero, mul_zero]
    field_simp [(dF₀_ne_zero hx), (dF'₀_ne_zero hx)]
    unfold dF₀ dF'₀ nF₀ nF'₀
    ring
