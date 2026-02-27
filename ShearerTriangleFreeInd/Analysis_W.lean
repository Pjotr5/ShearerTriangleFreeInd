import Mathlib
import ShearerTriangleFreeInd.Analysis




/-
## Definition of LambertW
-/

open Real

variable {x y : ℝ}

noncomputable def xexp : ℝ → ℝ := fun x ↦ x * exp x

lemma xexp_zero : xexp 0 = 0 := zero_mul _

lemma xexp_pos (hx : 0 < x) : 0 < xexp x := mul_pos hx (exp_pos _)

lemma xexp_neg (hx : x < 0) : xexp x < 0 := mul_neg_of_neg_of_pos hx (exp_pos _)

lemma hasDerivAt_xexp : HasDerivAt xexp ((1 + x) * exp x) x := by
  convert HasDerivAt.mul (hasDerivAt_id' x) (Real.hasDerivAt_exp x) using 1
  ring

lemma continuous_xexp : Continuous xexp := Continuous.mul continuous_id' continuous_exp

-- Stronger version of log_mul_self_monotoneOn
lemma StrictMonoOn_xexp : StrictMonoOn xexp (Set.Ici (-1)) :=
  strictMonoOn_of_hasDerivWithinAt_pos (convex_Ici _) (Continuous.continuousOn continuous_xexp)
    (fun _ _ ↦ HasDerivAt.hasDerivWithinAt hasDerivAt_xexp)
    (fun _ hx ↦ mul_pos (by rw [interior_Ici] at hx; exact neg_lt_iff_pos_add'.mp hx) (exp_pos _))

lemma xexp_le (hx : -1 ≤ x) : xexp (-1) ≤ xexp x :=
  StrictMonoOn.monotoneOn StrictMonoOn_xexp Set.self_mem_Ici hx hx

lemma xexp_lt (hx : -1 < x) : xexp (-1) < xexp x :=
  StrictMonoOn_xexp Set.self_mem_Ici (le_of_lt hx) hx

lemma xexp_neg_one_neg : xexp (-1) < 0 := by
  rw [←xexp_zero]
  exact xexp_lt (neg_one_lt_zero)

lemma log_xexp (hx : 0 < x) : log (xexp x) = x + log x := by
  rw [xexp, log_mul (ne_of_lt hx).symm (exp_ne_zero _) , log_exp, add_comm]

lemma self_le_xexp : x ≤ xexp x := by
  rw [←sub_nonneg, xexp, ←mul_sub_one]
  rcases lt_or_ge 0 x with (hx | hx)
  · exact le_of_lt (mul_pos hx (sub_pos.2 (one_lt_exp_iff.2 hx)))
  · exact mul_nonneg_of_nonpos_of_nonpos hx (sub_nonpos.2 (exp_le_one_iff.2 hx))

lemma xexp_surjective (hx : xexp (-1) ≤ x) : ∃ y, -1 ≤ y ∧ xexp y = x :=
  IsPreconnected.intermediate_value₂ isPreconnected_Ici (Set.self_mem_Ici)
    (le_trans self_le_xexp hx) (Continuous.continuousOn continuous_xexp)
    (continuousOn_const (c := x)) hx self_le_xexp

lemma xexp_InjOn : Set.InjOn xexp (Set.Ici (-1)) := StrictMonoOn.injOn StrictMonoOn_xexp

--StrictMonoOn.orderIso

-- noncomputable def xexpOrderIso' : Set.Ici (-1 : ℝ) ≃o Set.Ici (xexp (-1)) := by
--   convert StrictMonoOn.orderIso _ _ StrictMonoOn_xexp
--   sorry

noncomputable def xexpOrderIso : Set.Ici (-1 : ℝ) ≃o Set.Ici (xexp (-1)) := by
  refine StrictMono.orderIsoOfSurjective (fun x ↦ ⟨xexp x, xexp_le x.2⟩) ?_ ?_
  · apply StrictMono.codRestrict
    exact (Set.strictMonoOn_iff_strictMono.mp StrictMonoOn_xexp)
  · intro x
    have ⟨y, hyb, hyx⟩ := xexp_surjective x.2
    use ⟨y, hyb⟩
    simp_all

lemma coe_xexpOrderIso_apply (hx : -1 ≤ x) : xexpOrderIso ⟨x, hx⟩ = xexp x :=
  rfl



lemma coe_Ici {x : Set.Ici y} : y ≤ x := x.2

noncomputable def W : ℝ → ℝ := fun x ↦ if hx : xexp (-1) ≤ x then xexpOrderIso.symm ⟨x, hx⟩ else 0

lemma W_rw (hx : xexp (-1) ≤ x) : W x = xexpOrderIso.symm ⟨x, hx⟩ := dif_pos hx

lemma W_EqOn : Set.EqOn (α := Set.Ici (xexp (-1))) (fun x ↦ W x.1) (fun x ↦ xexpOrderIso.symm x)
  Set.univ := by
  intro x _
  simp [W_rw x.2]

lemma neg_one_le_W (hx : xexp (-1) ≤ x) : -1 ≤ W x := by
  rw [W_rw hx]
  exact coe_Ici

lemma W_coe (a : Set.Ici (xexp (-1))) : W a.1 = xexpOrderIso.symm a := dif_pos a.2

lemma xexp_W (hx : xexp (-1) ≤ x) : xexp (W x) = x := by
  rw [W_rw hx, ←(coe_xexpOrderIso_apply ?_), OrderIso.apply_symm_apply, Subtype.coe_mk]
  exact coe_Ici

lemma StrictMonoOn_W : StrictMonoOn W (Set.Ici (xexp (-1))) := by
  intro _ hx _ hy hxy
  refine ((StrictMonoOn.congr ?_ W_EqOn.symm) (a := ⟨_, hx⟩) trivial (b := ⟨_, hy⟩) trivial hxy)
  exact strictMonoOn_univ.2 (OrderIso.strictMono (xexpOrderIso.symm))

lemma StrictMonoOn_W' (hx : xexp (-1) ≤ x) (hxy : x < y) : W x < W y :=
  StrictMonoOn_W hx (Set.mem_Ici.2 (by linarith)) hxy

lemma W_InjOn : Set.InjOn W (Set.Ici (xexp (-1))) := StrictMonoOn.injOn StrictMonoOn_W

lemma W_xexp (hx : -1 ≤ x) : W (xexp x) = x :=
  xexp_InjOn (neg_one_le_W (xexp_le hx)) hx (xexp_W (xexp_le hx))

lemma W_xexp_neg_one : W (xexp (-1)) = -1 := W_xexp le_rfl

lemma W_zero : W 0 = 0 := by
  convert W_xexp (le_of_lt neg_one_lt_zero)
  exact xexp_zero.symm

lemma neg_one_lt_W (hx : xexp (-1) < x) : -1 < W x := by
  rw [←W_xexp_neg_one]
  apply StrictMonoOn_W' le_rfl hx

lemma one_add_W_pos (hx : xexp (-1) < x) : 0 < 1 + W x :=
  neg_lt_iff_pos_add'.mp (neg_one_lt_W hx)

lemma W_add_one_pos (hx : xexp (-1) < x) : 0 < W x + 1 := by
  linarith [one_add_W_pos hx ]

lemma W_add_one_nonzero (hx : xexp (-1) < x) : W x + 1 ≠ 0 :=
  (ne_of_lt (W_add_one_pos hx)).symm

lemma W_affine_combo_pos {a b : ℝ} (hx : xexp (-1) < x) (ha : 0 < a)
    (hb : a ≤ b) : 0 < a * W x + b := by
  convert Right.add_pos_of_pos_of_nonneg
    (mul_pos ha (W_add_one_pos hx)) (sub_nonneg_of_le hb) using 1
  ring

lemma W_neg_at_neg (hx : xexp (-1) ≤ x) (hx_neg : x < 0) : W x < 0 := by
  rw [←W_zero]
  exact StrictMonoOn_W' hx hx_neg

lemma W_pos_at_pos (hx_pos : 0 < x) : 0 < W x  := by
  rw [←W_zero]
  exact StrictMonoOn_W' (le_of_lt xexp_neg_one_neg) hx_pos

lemma W_nonzero_of_nonzero (hx : xexp (-1) ≤ x) (hx_nonzero : x ≠ 0) : W x ≠ 0 := by
  rcases lt_or_gt_of_ne hx_nonzero with (h | h)
  · exact (ne_of_gt (W_neg_at_neg hx h)).symm
  · exact (ne_of_lt (W_pos_at_pos h)).symm

lemma W_eq_x_mul_exp_neg_W (hx : xexp (-1) ≤ x) : W x = x * exp (- W x) := by
  nth_rewrite 2 [←xexp_W hx]
  rw [xexp, mul_assoc, ←exp_add, ←sub_eq_add_neg, sub_self, exp_zero, mul_one]

lemma lt_of_xexp_lt_xexp (hx : -1 ≤ x) (hy : -1 ≤ y) (hxy : xexp x < xexp y) :
    x < y := by
  have this := StrictMonoOn_W' (xexp_le hx) hxy
  rwa [W_xexp hx, W_xexp hy] at this

lemma exp_W (hx : xexp (-1) ≤ x) (hx₀ : x ≠ 0) : exp (W x) = x / W x := by
  nth_rw 2 [←xexp_W hx]; rw [xexp]
  field_simp [W_nonzero_of_nonzero hx hx₀]

lemma W_lt_log (hx : xexp 1 < x) : W x < log x := by
  have hx1 := lt_of_le_of_lt self_le_xexp hx
  have hx2 := (le_of_lt (lt_of_le_of_lt (xexp_le (by linarith)) hx))
  rw [←exp_lt_exp, exp_log (by linarith), exp_W hx2 (by linarith)]
  apply div_lt_self (by linarith)
  convert StrictMonoOn_W' (xexp_le (by linarith)) hx
  rw [W_xexp (by linarith)]

lemma log_sub_loglog_lt_W (hx : xexp 1 < x) : log x - log (log x) < W x := by
  have hx1 := lt_of_le_of_lt self_le_xexp hx
  have hx2 := (le_of_lt (lt_of_le_of_lt (xexp_le (by linarith)) hx))
  rw [←exp_lt_exp, exp_sub, exp_log (by linarith), exp_log (log_pos hx1), exp_W hx2 (by linarith)]
  refine div_lt_div_of_pos_left (by linarith) (W_pos_at_pos (by linarith)) (W_lt_log hx)

lemma continuousOn_W : ContinuousOn W (Set.Ici (xexp (-1))) := by
  simp +unfoldPartialApp only [continuousOn_iff_continuous_restrict, Set.restrict, W_coe]
  exact Continuous.subtype_val (OrderIso.continuous _)

lemma hasDerivAt_W (hx : xexp (-1) < x) : HasDerivAt W (exp (-W x) / (1 + W x)) x := by
  convert HasDerivAt.of_local_left_inverse
    (ContinuousOn.continuousAt continuousOn_W (Ici_mem_nhds hx)) hasDerivAt_xexp
    (mul_ne_zero_iff.2 ⟨(ne_of_lt (one_add_W_pos hx)).symm, exp_ne_zero _⟩)
    (Filter.eventually_iff_exists_mem.2 ⟨_, Ici_mem_nhds hx, fun _ hy ↦ xexp_W hy⟩) using 1
  rw [mul_inv, exp_neg, inv_mul_eq_div]

lemma continuousAt_W (hx : xexp (-1) < x) : ContinuousAt W x :=
  HasDerivAt.continuousAt (hasDerivAt_W hx)


noncomputable section Calculations

variable {x y : ℝ}

def D : Set ℝ := Set.Ici (xexp (-1))
def Di : Set ℝ := Set.Ioi (xexp (-1))

lemma D_interior : interior D = Di := interior_Ici
lemma Di_interior : interior Di = Di := interior_Ioi

lemma Di_sub_D : Di ⊆ D := Set.Ioi_subset_Ici_self

lemma Di_open : IsOpen Di := isOpen_Ioi

lemma nonneg_mem_domain_interior (hx : 0 ≤ x) : x ∈ Di :=
  lt_of_le_of_lt' hx xexp_neg_one_neg

lemma zero_mem_domain_interior : 0 ∈ Di :=
  nonneg_mem_domain_interior (le_refl _)

lemma two_mem_domain_interior : 2 ∈ Di :=
  nonneg_mem_domain_interior (zero_le_two)

lemma zero_mem_domain : 0 ∈ D :=
  Di_sub_D zero_mem_domain_interior

lemma two_mem_domain : 2 ∈ D :=
  Di_sub_D two_mem_domain_interior




/-
## The function P := W(x)/x makes things more convenient.
-/

noncomputable def P : ℝ → ℝ := fun x ↦ exp (- W x)

noncomputable def W' : ℝ → ℝ := fun x ↦ P x / (W x + 1)
noncomputable def W'' : ℝ → ℝ := fun x ↦ -(W' x)^2 * (W x + 2) / (W x + 1)

noncomputable def P' : ℝ → ℝ  := fun x ↦ (- W' x) * P x
noncomputable def P'' : ℝ → ℝ := fun x ↦ (W' x)^3 * (2 * W x + 3)

lemma hasDerivAt_W₀ {x : ℝ} (hx : x ∈ Di) : HasDerivAt W (W' x) x := by
  convert hasDerivAt_W hx using 1
  unfold W' P; congr 1; exact add_comm _ _

lemma W_eq_self_mul_P (hx : x ∈ D) : W x = x * P x := W_eq_x_mul_exp_neg_W hx

-- lemma P_eq_on_nonzero (hx : x ∈ D) (hx₀ : x ≠ 0) : P x = W x / x := by
--   rw [W_eq_self_mul_P hx]
--   exact (mul_div_cancel_left₀ _ hx₀).symm

lemma continuousOn_P : ContinuousOn P D := by
  unfold P
  exact Continuous.comp_continuousOn' continuous_exp (ContinuousOn.neg (continuousOn_W))

lemma hasDerivAt_P (hx : x ∈ Di) : HasDerivAt P (P' x) x := by
  convert HasDerivAt.comp x (Real.hasDerivAt_exp (-W x))
    (HasDerivAt.fun_neg (hasDerivAt_W₀ hx)) using 1
  rw [mul_comm]; rfl

lemma continuousAt_P (hx : x ∈ Di) : ContinuousAt P x :=
  HasDerivAt.continuousAt (hasDerivAt_P hx)

-- lemma P'_continuousAt (hx : x ∈ Di) : ContinuousAt P' x := by
--   refine ContinuousAt.mul (ContinuousAt.neg (ContinuousAt.div₀ ?_ ?_ ?_)) (continuousAt_P hx)
--   · exact continuousAt_P hx
--   · exact ContinuousAt.add (continuousAt_W hx) continuousAt_const
--   · exact W_add_one_nonzero hx

lemma hasDerivAt_W' (hx : x ∈ Di) : HasDerivAt W' (W'' x) x := by
  convert HasDerivAt.div (hasDerivAt_P hx) (HasDerivAt.add_const 1 (hasDerivAt_W₀ hx))
    (W_add_one_nonzero hx) using 1
  unfold W'' P' W'
  field_simp [W_add_one_nonzero hx]
  ring

lemma continuousAt_W' (hx : x ∈ Di) : ContinuousAt W' x :=
  HasDerivAt.continuousAt (hasDerivAt_W' hx)

lemma hasDerivAt_P' (hx : x ∈ Di) : HasDerivAt P' (P'' x) x := by
  convert HasDerivAt.mul (HasDerivAt.fun_neg (hasDerivAt_W' hx)) (hasDerivAt_P hx) using 1
  unfold P'' W'' P' W'
  field_simp [W_add_one_nonzero hx]
  ring

lemma continuousAt_P' (hx : x ∈ Di) : ContinuousAt P' x :=
  HasDerivAt.continuousAt (hasDerivAt_P' hx)

lemma continuousAt_P'' (hx : x ∈ Di) : ContinuousAt P'' x :=
  ContinuousAt.mul (ContinuousAt.pow (continuousAt_W' hx) 3)
  (ContinuousAt.add (ContinuousAt.mul continuousAt_const (continuousAt_W hx)) continuousAt_const)

lemma P_pos : 0 < P x := exp_pos (-W x)

lemma W'_pos (hx : x ∈ Di) : 0 < W' x := div_pos P_pos (W_add_one_pos hx)

lemma P'_neg (hx : x ∈ Di) : P' x < 0 :=
  mul_neg_of_neg_of_pos (neg_neg_iff_pos.mpr (W'_pos hx)) P_pos

lemma P''_pos (hx : x ∈ Di) : 0 < P'' x :=
  mul_pos (pow_pos (W'_pos hx) 3) (W_affine_combo_pos hx (by norm_num) (by norm_num))

lemma ConvexOn_P : ConvexOn ℝ D P := by
  refine convexOn_of_hasDerivWithinAt2_nonneg (f' := P') (f'' := P'')
    (convex_Ici _) (continuousOn_P) ?_ ?_ ?_ <;> (rw [interior_Ici]; intro _ hx)
  · exact HasDerivAt.hasDerivWithinAt (hasDerivAt_P hx)
  · exact HasDerivAt.hasDerivWithinAt (hasDerivAt_P' hx)
  · exact le_of_lt (P''_pos hx)






/-!
## Integral running average.
-/

def IntAverage (a b : ℝ) (g : ℝ → ℝ) : ℝ :=
  if b = a then g a
  else          (⨍ y in a..b, g y)


lemma image_affine_uIcc (a b c d : ℝ) :
    (a * · + b) '' Set.uIcc c d = Set.uIcc (a * c + b) (a * d + b) := by
  suffices (· + b) '' ((a * ·) '' Set.uIcc c d) = Set.uIcc (a * c + b) (a * d + b) by
    rwa [Set.image_image] at this
  rw [Set.image_const_mul_uIcc, Set.image_add_const_uIcc]

lemma affine_continuous (a b : ℝ) : Continuous (a * · + b) :=
  Continuous.add (continuous_mul_left _) continuous_const

-- Probably not necessary.
lemma uIcc_convexHull (a b : ℝ) : convexHull ℝ {a, b} = Set.uIcc a b :=
  Set.Subset.antisymm (convexHull_min
    (Set.pair_subset (Set.left_mem_uIcc) (Set.right_mem_uIcc)) (convex_uIcc _ _))
    (Set.OrdConnected.uIcc_subset (Convex.ordConnected (convex_convexHull _ _))
    (mem_convexHull_iff.mpr (fun _ h _ ↦ h (Set.mem_insert _ _)))
    (mem_convexHull_iff.mpr (fun _ h _ ↦ h (Set.mem_insert_of_mem _ rfl))))

lemma uIcc_sub_connected {a b : ℝ} {U : Set ℝ} (hU : IsConnected U) (ha : a ∈ U) (hb : b ∈ U) :
    Set.uIcc a b ⊆ U :=
  Set.OrdConnected.uIcc_subset (IsPreconnected.ordConnected (IsConnected.isPreconnected hU)) ha hb

lemma lt_mem_uIcc {a b c d : ℝ} (ha : d < a) (hb : d < b) (hc : c ∈ Set.uIcc a b) :
    d < c := by
  rw [Set.uIcc_eq_union] at hc
  rcases hc with (hc | hc) <;> linarith [hc.1]

lemma IntAverage_eq (a b : ℝ) (g : ℝ → ℝ) (hCont : ContinuousOn g (Set.uIcc a b))
    : IntAverage a b g = ∫ y in 0..1, g ((b-a) * y + a) := by
  rw [IntAverage]
  split_ifs
  · simp_all
  · rw [interval_average_eq_div]
    refine div_eq_of_eq_mul ?_ ?_
    · (expose_names; exact sub_ne_zero_of_ne h)
    · rw [←intervalIntegral.integral_mul_const]
      symm
      convert intervalIntegral.integral_comp_mul_deriv'
        (f := fun t ↦ (b - a)*t + a) ?_ ?_ ?_ using 1
      · simp
      · intro _ _
        rw [hasDerivAt_add_const_iff]
        convert hasDerivAt_mul_const (b-a) using 1;
        ext; ring
      · exact continuousOn_const
      · convert hCont
        rw [image_affine_uIcc]
        congr! <;> ring


/- To do: This lemma contains duplicated code.-/
lemma IntAverage_ConvexOn {g : ℝ → ℝ} {a : ℝ} {U : Set ℝ}
    (hConvex : ConvexOn ℝ U g) (hCont : ContinuousOn g U)
    (ha : a ∈ U) : ConvexOn ℝ U (fun t ↦ IntAverage a t g) := by
  rw [convexOn_iff_pairwise_pos] at *
  have hCon := Convex.isConnected hConvex.1 (Set.nonempty_of_mem ha)
  have hAux : Set.Ioo (0 : ℝ) 1 ⊆ Set.uIcc 0 1 := by
            simp only [zero_le_one, Set.uIcc_of_le, Set.Ioo_subset_Icc_self]
  simp only [smul_eq_mul] at *
  refine ⟨hConvex.1,?_⟩
  intro x hx y hy hneq a₁ a₂ ha₁ ha₂ ha₁₂
  rw [IntAverage_eq, IntAverage_eq, IntAverage_eq]
  · rw [←intervalIntegral.integral_const_mul, ←intervalIntegral.integral_const_mul,
      ←intervalIntegral.integral_add]
    · apply intervalIntegral.integral_mono_on_of_le_Ioo (by norm_num)
      · refine ContinuousOn.intervalIntegrable (ContinuousOn.comp' hCont ?_ ?_)
        · exact Continuous.continuousOn (affine_continuous _ _)
        · rw [Set.mapsTo_iff_image_subset, image_affine_uIcc]
          refine uIcc_sub_connected hCon ?_ ?_
          · convert ha; ring
          · convert (convex_iff_add_mem.1 hConvex.1) hx hy (le_of_lt ha₁)
              (le_of_lt ha₂) ha₁₂ using 1
            simp [smul_eq_mul]
      · apply ContinuousOn.intervalIntegrable (ContinuousOn.add ?_ ?_)
        · refine ContinuousOn.const_smul (ContinuousOn.comp' hCont ?_ ?_) a₁
          · exact Continuous.continuousOn (affine_continuous _ _)
          · rw [Set.mapsTo_iff_image_subset, image_affine_uIcc]
            refine uIcc_sub_connected hCon ?_ ?_
            · convert ha; ring
            · convert hx; ring
        · refine ContinuousOn.const_smul (ContinuousOn.comp' hCont ?_ ?_) a₂
          · exact Continuous.continuousOn (affine_continuous _ _)
          · rw [Set.mapsTo_iff_image_subset, image_affine_uIcc]
            refine uIcc_sub_connected hCon ?_ ?_
            · convert ha; ring
            · convert hy; ring
      · intro t ht
        convert hConvex.2 ?_ ?_ ?_ ha₁ ha₂ ha₁₂ using 2
        · rw [eq_sub_of_add_eq ha₁₂]; ring
        · refine uIcc_sub_connected hCon ha hx ?_
          have this := image_affine_uIcc (x-a) a 0 1
          ring_nf at this
          rw [←this]
          exact (Set.mem_image _ _ _).mpr ⟨t, ⟨hAux ht, by ring⟩⟩
        · refine uIcc_sub_connected hCon ha hy ?_
          have this := image_affine_uIcc (y-a) a 0 1
          ring_nf at this
          rw [←this]
          exact (Set.mem_image _ _ _).mpr ⟨t, ⟨hAux ht, by ring⟩⟩
        · simp_all [(ne_of_lt ht.1).symm]
    · apply ContinuousOn.intervalIntegrable
      refine ContinuousOn.const_smul (ContinuousOn.comp' hCont ?_ ?_) a₁
      · exact Continuous.continuousOn (affine_continuous _ _)
      · rw [Set.mapsTo_iff_image_subset, image_affine_uIcc]
        refine uIcc_sub_connected hCon ?_ ?_
        · convert ha; ring
        · convert hx; ring
    · apply ContinuousOn.intervalIntegrable
      refine ContinuousOn.const_smul (ContinuousOn.comp' hCont ?_ ?_) a₂
      · exact Continuous.continuousOn (affine_continuous _ _)
      · rw [Set.mapsTo_iff_image_subset, image_affine_uIcc]
        refine uIcc_sub_connected hCon ?_ ?_
        · convert ha; ring
        · convert hy; ring
  · exact ContinuousOn.mono hCont (uIcc_sub_connected hCon ha hy)
  · exact ContinuousOn.mono hCont (uIcc_sub_connected hCon ha hx)
  · refine ContinuousOn.mono hCont (uIcc_sub_connected hCon ha ?_)
    convert (convex_iff_add_mem.1 hConvex.1) hx hy (le_of_lt ha₁)
              (le_of_lt ha₂) ha₁₂ using 1



/-
  ## Definitions of the main functions.
-/


noncomputable def P_prim : ℝ → ℝ  := fun x ↦ (1 / 2) * (W x)^2 + W x
def nG : ℝ → ℝ                    := fun x ↦ P_prim x - P_prim 2

-- Main function `G` and its derivative.
def G : ℝ → ℝ := fun x ↦
  if x = 2 then rexp (-W 2)
  else          ((1 / 2) * (W x)^2 + W x - ((1 / 2) * (W 2)^2 + W 2)) / (x - 2)

def G' : ℝ → ℝ := fun x ↦
  if x = 2 then P' 2 / 2
  else          (P x * (x - 2) - nG x) / (x - 2)^2

def nG' : ℝ → ℝ := fun x ↦ P x * (x - 2) - nG x
def dnG' : ℝ → ℝ := fun x ↦ P' x * (x - 2)
def ddnG' : ℝ → ℝ := fun x ↦ P'' x * (x - 2) + P' x

lemma ddnG'_at_two : ddnG' 2 = P' 2 := by rw [ddnG', sub_self, mul_zero, zero_add]

lemma G_rw (hx : x ≠ 2) : G x = nG x / (x - 2) := if_neg hx
lemma G_two_rw : G 2 = P 2 := if_pos rfl

lemma G'_rw (hx : x ≠ 2) : G' x = (P x - G x) / (x - 2) := by
  field_simp [(sub_ne_zero_of_ne hx)]
  rw [G', if_neg hx, G_rw hx]
  field_simp [(sub_ne_zero_of_ne hx)]

lemma G'_rw' (hx : x ≠ 2) : G' x = nG' x / (x - 2)^2 := if_neg hx

lemma G'_two_rw : G' 2 = P' 2 / 2 := if_pos rfl

lemma G_diff_equation : G x + (x - 2) * G' x = P x := by
  by_cases hx : x = 2
  · rw [hx, sub_self, zero_mul, add_zero, G, if_pos rfl]
    rfl
  · rw [G'_rw hx, mul_div_cancel₀ _ (sub_ne_zero_of_ne hx)]
    ring


lemma HasDerivAt_P_prim (hx : x ∈ Di) : HasDerivAt P_prim (P x) x := by
  unfold P_prim
  convert HasDerivAt.add (f := fun x ↦ (1 / 2) * (W x)^2) (f' := W x * W' x)
    ?_ (hasDerivAt_W₀ hx) using 1
  · unfold W'
    field_simp [W_add_one_nonzero hx]
  · convert HasDerivAt.const_mul (1/2)
      (HasDerivAt.mul (hasDerivAt_W₀ hx) (hasDerivAt_W₀ hx)) using 1
    · ext _
      simp only [one_div, Pi.mul_apply, mul_eq_mul_left_iff, inv_eq_zero,
      OfNat.ofNat_ne_zero, or_false]
      ring
    · ring


def G_int : ℝ → ℝ := fun t ↦ IntAverage 2 t P

lemma G_int_eq_G : Set.EqOn G_int G Di := by
  intro _ hx
  unfold G G_int IntAverage
  split_ifs
  · simp [P]
  · rw [interval_average_eq_div]
    congr 1
    convert intervalIntegral.integral_eq_sub_of_hasDerivAt (f := P_prim) (f' := P) ?_ ?_ using 1
    · intro _ ht
      apply HasDerivAt_P_prim
      exact lt_mem_uIcc two_mem_domain_interior hx ht
    · apply ContinuousOn.intervalIntegrable
      intro _ hy
      refine ContinuousAt.continuousWithinAt (continuousAt_P ?_)
      exact lt_mem_uIcc two_mem_domain_interior hx hy

lemma G_convexOn : ConvexOn ℝ Di G :=
  ConvexOn.congr (IntAverage_ConvexOn (ConvexOn.subset ConvexOn_P Di_sub_D (convex_Ioi _))
    (ContinuousOn.mono continuousOn_P Di_sub_D) two_mem_domain_interior) G_int_eq_G

-- G is continuous on D, but we will not use it.
lemma G_continuousOn : ContinuousOn G Di :=
  ConvexOn.continuousOn isOpen_Ioi G_convexOn


lemma nG_hasDerivAt (hx : x ∈ Di) : HasDerivAt nG (P x) x :=
  HasDerivAt.add_const _ (HasDerivAt_P_prim hx)

lemma nG'_hasDerivAt (hx : x ∈ Di) : HasDerivAt nG' (dnG' x) x := by
  have h₁ : HasDerivAt (fun t ↦ P t * (t - 2)) (P' x * (x - 2) + P x) x := by
    convert HasDerivAt.mul (hasDerivAt_P hx) (HasDerivAt.add_const (-2) (hasDerivAt_id' x)) using 1
    ring
  convert HasDerivAt.sub h₁ (nG_hasDerivAt hx) using 1
  unfold dnG'
  ring

lemma nG'_continuousOn : ContinuousOn nG' Di :=
  fun _ hx ↦ ContinuousAt.continuousWithinAt (HasDerivAt.continuousAt (nG'_hasDerivAt hx))

lemma dnG'_hasDerivAt (hx : x ∈ Di) : HasDerivAt dnG' (ddnG' x) x := by
  convert HasDerivAt.mul (hasDerivAt_P' hx) (HasDerivAt.add_const (-2) (hasDerivAt_id' x)) using 1
  unfold ddnG'
  ring


lemma ddnG'_continuousAt (hx : x ∈ Di) : ContinuousAt ddnG' x :=
  ContinuousAt.add (ContinuousAt.mul (continuousAt_P'' hx)
  (Continuous.continuousAt (continuous_add_right (-2)))) (continuousAt_P' hx)


lemma pos_of_dist_two_lt_two {x : ℝ} (hx : dist x 2 < 2) : 0 < x := by
  rw [Real.dist_eq, abs_sub_lt_iff] at hx
  linarith

lemma G_hasDerivAt_aux (hx : x ∈ Di \ {2}) : HasDerivAt G (G' x) x := by
  refine HasDerivAt.congr_on_open (IsOpen.and (isOpen_lt' _) isOpen_ne) hx
      ?_ (fun _ hy ↦ (if_neg hy.2).symm)
  convert HasDerivAt.div (nG_hasDerivAt hx.1)
    (HasDerivAt.add_const (-2) (hasDerivAt_id' x)) (sub_ne_zero_of_ne hx.2 ) using 1
  rw [mul_one];
  exact if_neg hx.2

open Polynomial

lemma G'_continuousAt_two : ContinuousAt G' 2 := by
  convert ContinuousAt.lhopital_iterated 2
    [nG', dnG', ddnG'] [fun x ↦ (x-2)^2, fun x ↦ 2*(x-2), fun x ↦ 2] rfl rfl
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ using 1
  · unfold G' nG'; simp [ddnG'_at_two]
  · intro k _
    interval_cases k <;> (rw [Metric.eventually_nhds_iff]; use 2, (by norm_num); intro _ hy)
    · exact nG'_hasDerivAt (nonneg_mem_domain_interior (le_of_lt (pos_of_dist_two_lt_two hy)))
    · exact dnG'_hasDerivAt (nonneg_mem_domain_interior (le_of_lt (pos_of_dist_two_lt_two hy)))
  · intro k _
    interval_cases k <;> refine Filter.Eventually.of_forall ?_
    · intro x
      convert Polynomial.hasDerivAt (X^2 - 4*X + 4 : ℝ[X]) _ <;> (norm_num; ring)
    · intro x
      convert Polynomial.hasDerivAt (2*X - 4 : ℝ[X]) _ <;> norm_num
      ring
  · intro k _
    interval_cases k
    · simp [nG, nG']
    · simp [dnG']
  · intro k _
    interval_cases k <;> simp
  · exact ddnG'_continuousAt two_mem_domain_interior
  · exact continuousAt_const
  · simp

lemma G_hasDerivAt (hx : x ∈ Di) : HasDerivAt G (G' x) x := by
  by_cases hx2 : x = 2
  · rw [hx2]
    exact HasDerivAt.extend_to_singularity Di_open two_mem_domain_interior
      (fun _ hy hyD ↦ G_hasDerivAt_aux ⟨hyD, hy⟩ )
      (ContinuousWithinAt.continuousAt (G_continuousOn 2 two_mem_domain_interior)
        (IsOpen.mem_nhds Di_open two_mem_domain_interior))
      G'_continuousAt_two
  · exact G_hasDerivAt_aux ⟨hx, hx2⟩


lemma G_convex_inequality {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    : G x ≥ G y + G' y * (x - y) :=
  ConvexOn.tangent_line_le G_convexOn (nonneg_mem_domain_interior hx)
    (nonneg_mem_domain_interior hy) (G_hasDerivAt (nonneg_mem_domain_interior hy))


/-
## G' is nonpositive
-/

lemma dnG'_nonnegative (hx : x ∈ Di) (hx' : x ≤ 2) : dnG' x ≥ 0 :=
  mul_nonneg_of_nonpos_of_nonpos (le_of_lt (P'_neg hx)) (tsub_nonpos.2 hx')

lemma dnG'_nonpositive (hx : x ∈ Di) (hx' : 2 ≤ x) : dnG' x ≤ 0 :=
  mul_nonpos_of_nonpos_of_nonneg (le_of_lt (P'_neg hx)) (sub_nonneg_of_le hx')

lemma nG'_nonpositive (hx : 0 ≤ x) : nG' x ≤ 0 := by
  have hsub₁ : Set.Icc 0 2 ⊆ Di := (IsConnected.Icc_subset
        (isConnected_Ioi) (zero_mem_domain_interior) (two_mem_domain_interior))
  have hsub₂ : Set.Ici 2 ⊆ Di := (Set.Ici_subset_Ioi.mpr two_mem_domain_interior)
  have h₁ : MonotoneOn nG' (Set.Icc 0 2) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (f' := dnG')
    · exact nG'_continuousOn.mono hsub₁
    · rw [interior_Icc]
      exact fun y hy ↦ HasDerivAt.hasDerivWithinAt (nG'_hasDerivAt (hsub₁ (Set.mem_Icc_of_Ioo hy)))
    · rw [interior_Icc]
      intro x hx
      apply dnG'_nonnegative (hsub₁ (Set.mem_Icc_of_Ioo hx)) (le_of_lt hx.2)
    · exact convex_Icc _ _
  have h₂ : AntitoneOn nG' (Set.Ici 2) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (f' := dnG')
    · exact nG'_continuousOn.mono hsub₂
    · rw [interior_Ici]
      refine fun y hy ↦ HasDerivAt.hasDerivWithinAt (nG'_hasDerivAt (hsub₂ (Set.mem_Ici_of_Ioi hy)))
    · rw [interior_Ici]
      intro x hx
      exact dnG'_nonpositive (hsub₂ (Set.mem_Ici_of_Ioi hx)) (le_of_lt hx)
    · exact convex_Ici _
  have h₃ : nG' 2 = 0 := by simp [nG', nG]
  rw [←h₃]
  rcases le_total x 2 with (hx' | hx')
  · exact h₁ ⟨hx, hx'⟩ (Set.right_mem_Icc.2 (zero_le_two)) hx'
  · exact h₂ Set.self_mem_Ici hx' hx'

lemma G'_nonpositive (hx : 0 ≤ x) : G' x ≤ 0 := by
  by_cases hx' : x = 2
  · rw [hx', G'_two_rw]
    exact div_nonpos_of_nonpos_of_nonneg (le_of_lt (P'_neg two_mem_domain_interior)) zero_le_two
  · rw [G'_rw' hx']
    exact div_nonpos_of_nonpos_of_nonneg (nG'_nonpositive hx) (sq_nonneg _)

/-
## The expression we want to show is positive.
-/

def goal : ℝ → ℝ := fun x ↦ rexp (-x * G' x - G x) + rexp ((x - x^2) * G' x - (x + 1) * G x)

lemma goal_pos :  0 < goal x := by
  rw [goal]
  positivity

lemma goal_rewrite (hx : x ∈ D) : goal x = rexp (-x * G' x - G x) * (1 + P x) := by
  rw [goal, mul_add, mul_one, P, ←exp_add, W_eq_self_mul_P hx]
  congr 2
  rw [←G_diff_equation]
  ring

def bound : ℝ → ℝ := fun x ↦ -x * G' x - G x + (2 * P x)/ (P x + 2)

def term₁ : ℝ → ℝ := fun x ↦ 2 * nG x - ((x - 2) * P x * (4 + W x)) / (P x + 2)

def term₂ : ℝ → ℝ := fun x ↦ ((P' x) * (-4 + 2 * P x + W x * P x)) / (P x + 2)^2

lemma bound_is_sufficient (hx : x ∈ D) (hB : 0 < bound x) : 1 < goal x := by
  rw [←log_lt_log_iff zero_lt_one goal_pos, log_one, goal_rewrite hx,
    log_mul (exp_ne_zero _) (by linarith [@P_pos x]), log_exp]
  refine lt_trans hB ?_
  rw [bound]
  gcongr
  exact Real.lt_log_one_add_of_pos P_pos

lemma bound_two : bound 2 = term₂ 2 / 2 := by
  rw [bound, term₂, G'_two_rw, G_two_rw, P', W', W_eq_self_mul_P two_mem_domain]
  have _ : P 2 + 2      ≠ 0 := (ne_of_lt (add_pos P_pos zero_lt_two)).symm
  have _ : 2 * P 2 + 1  ≠ 0 := (ne_of_lt (add_pos (by linarith [@P_pos 2]) zero_lt_one)).symm
  field_simp
  ring

lemma bound_at_not_two (hxD : x ∈ D) (hx : x ≠ 2) : bound x = term₁ x / (x - 2)^2 := by
  have _ : P x + 2  ≠ 0     := (ne_of_lt (add_pos P_pos zero_lt_two)).symm
  rw [bound, term₁, G'_rw hx, G_rw hx, W_eq_self_mul_P hxD]
  field_simp [sub_ne_zero_of_ne hx]
  ring

lemma term₁_hasDerivAt (hxD : x ∈ Di)
    : HasDerivAt term₁ ((x - 2) * (term₂ x)) x := by
  have hP : P x + 2 ≠ 0 := (ne_of_lt (add_pos P_pos zero_lt_two)).symm
  have _  := W_add_one_nonzero hxD
  unfold term₁
  have h₁ : HasDerivAt (fun x ↦ 2 * nG x) (2 * P x) x := HasDerivAt.const_mul 2 (nG_hasDerivAt hxD)
  have h₂ : HasDerivAt (fun x ↦ x - 2) 1 x            := HasDerivAt.add_const _ (hasDerivAt_id' _)
  have h₃ : HasDerivAt (fun x ↦ (x - 2) * P x) (P x + (x - 2) * P' x) x := by
    convert HasDerivAt.mul h₂ (hasDerivAt_P hxD) using 1
    rw [one_mul]
  have h₄ : HasDerivAt (fun x ↦ 4 + W x) (W' x) x     := HasDerivAt.const_add 4 (hasDerivAt_W₀ hxD)
  have h₅ : HasDerivAt (fun x ↦ (x - 2) * P x * (4 + W x))
      (P x * (4 + W x) + (x - 2) * (4 + W x) * P' x + (x - 2) * P x * W' x) x := by
    convert HasDerivAt.mul h₃ h₄ using 1
    ring
  have h₆ : HasDerivAt (fun x ↦ P x + 2) (P' x) x := HasDerivAt.add_const _ (hasDerivAt_P hxD)
  convert HasDerivAt.sub h₁ (HasDerivAt.div h₅ h₆ hP) using 1
  rw [term₂, P', W']
  field_simp
  rw [W_eq_self_mul_P (Di_sub_D hxD)]
  ring


lemma term₂_pos_aux (hx : 0 ≤ x) : (-4 + 2 * P x + W x * P x) < 0 := by
  let f   : ℝ → ℝ := fun x ↦ (-4 + 2 * P x + W x * P x)
  let f'  : ℝ → ℝ := fun x ↦ -(P x)^2
  change f x < 0
  have hxD := (nonneg_mem_domain_interior hx)
  have h₁ {y : ℝ} (hy : y ∈ Di) : HasDerivAt (fun x ↦ -4 + 2 * P x) (2 * P' y) y  := by
    convert HasDerivAt.add (hasDerivAt_const y (-4))
      (HasDerivAt.const_mul ?_ (hasDerivAt_P hy)) using 1
    · ring
  have h₂ {y : ℝ} (hy : y ∈ Di) : HasDerivAt (fun x ↦ W x * P x) (W' y * P y + W y * P' y) y :=
    HasDerivAt.mul (hasDerivAt_W₀ hy) (hasDerivAt_P hy)
  have h₃ {y : ℝ} (hy : y ∈ Di) : HasDerivAt f (f' y) y := by
    convert HasDerivAt.add (h₁ hy) (h₂ hy) using 1
    rw [P', W']
    have _ := W_add_one_pos hy
    field_simp
    rw [W_eq_self_mul_P (Di_sub_D hy)]
    ring
  refine lt_of_le_of_lt (a := f x) (b := f 0) ?_ ?_
  · suffices AntitoneOn f (Set.Ici 0) from this (Set.self_mem_Ici) hx hx
    refine antitoneOn_of_hasDerivWithinAt_nonpos (f' := f') ?_ ?_ ?_ ?_
    · exact convex_Ici _
    · intro y hy
      exact ContinuousAt.continuousWithinAt
        (HasDerivAt.continuousAt (h₃ (nonneg_mem_domain_interior hy) ))
    · rw [interior_Ici]
      exact fun _ hx ↦ HasDerivAt.hasDerivWithinAt (h₃ (nonneg_mem_domain_interior (le_of_lt hx)))
    · intro _ _
      rw [neg_nonpos]
      positivity
  · unfold f
    rw [P, W_zero]
    norm_num


lemma term₂_pos (hx : 0 ≤ x) : 0 < term₂ x :=
  div_pos (mul_pos_of_neg_of_neg (P'_neg (nonneg_mem_domain_interior hx)) (term₂_pos_aux hx))
    (sq_pos_of_pos (add_pos P_pos zero_lt_two ))


lemma term₁_pos (hx : 0 ≤ x) (hxn : x ≠ 2) : 0 < term₁ x := by
  have h₁ : StrictAntiOn term₁ (Set.Icc 0 2) := by
    refine strictAntiOn_of_hasDerivWithinAt_neg (f' := fun x ↦ (x - 2) * term₂ x) ?_ ?_ ?_ ?_
    · exact convex_Icc 0 2
    · intro _ hy
      exact ContinuousAt.continuousWithinAt
        (HasDerivAt.continuousAt (term₁_hasDerivAt (nonneg_mem_domain_interior hy.1)))
    · rw [interior_Icc]
      exact fun _ hy ↦
        HasDerivAt.hasDerivWithinAt (term₁_hasDerivAt (nonneg_mem_domain_interior (le_of_lt hy.1)))
    · rw [interior_Icc]
      intro _ hy
      exact mul_neg_of_neg_of_pos (by linarith [hy.2]) (term₂_pos (le_of_lt hy.1))
  have h₂ : StrictMonoOn term₁ (Set.Ici 2) := by
    refine strictMonoOn_of_hasDerivWithinAt_pos (f' := fun x ↦ (x - 2) * term₂ x) ?_ ?_ ?_ ?_
    · exact convex_Ici 2
    · intro _ hy
      exact ContinuousAt.continuousWithinAt (HasDerivAt.continuousAt
        (term₁_hasDerivAt (nonneg_mem_domain_interior (le_trans zero_le_two hy))))
    · rw [interior_Ici]
      exact fun _ hy ↦ HasDerivAt.hasDerivWithinAt
        (term₁_hasDerivAt (nonneg_mem_domain_interior (le_of_lt (lt_trans zero_lt_two hy))))
    · rw [interior_Ici]
      refine fun _ hy ↦ mul_pos (sub_pos.mpr hy) (term₂_pos (le_trans zero_le_two (le_of_lt hy)))
  rw [←(by simp [term₁, nG] : term₁ 2 = 0)]
  rcases ne_iff_lt_or_gt.1 hxn with (hx_lt_two | htwo_lt_x)
  · exact h₁ ⟨hx, le_of_lt hx_lt_two⟩ ⟨zero_le_two, le_rfl⟩ hx_lt_two
  · exact h₂ Set.self_mem_Ici (le_of_lt htwo_lt_x) htwo_lt_x

lemma bound_pos (hx : 0 ≤ x) : 0 < bound x := by
  by_cases hx₂ : x = 2
  · rw [hx₂, bound_two]
    exact div_pos (term₂_pos zero_le_two) zero_lt_two
  · rw [bound_at_not_two (Di_sub_D (nonneg_mem_domain_interior hx)) hx₂]
    exact div_pos (term₁_pos hx hx₂) (pow_two_pos_of_ne_zero (sub_ne_zero_of_ne hx₂))


theorem goal_bound (hx : 0 ≤ x) : 1 < goal x :=
  bound_is_sufficient (Di_sub_D (nonneg_mem_domain_interior hx)) (bound_pos hx)


























end Calculations
