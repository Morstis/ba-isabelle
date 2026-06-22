theory prob_to_hol_prob
  imports Main "HOL-Probability.Probability" probability definitions theorems 
begin

(* Dieses Theorem ist teilweise mit Unterstützung von Claude entstanden.
Auch wenn die Arbeit mit Claude eine große Katastrophe ist... *)

consts dds :: "ds" where "satisfiable ds"

definition dds :: "ds"
  where "dds = (SOME x. satisfiable x)"

locale prob_DoJ = 
  fixes ds :: "ds"
  assumes sat: "satisfiable ds"

context prob_DoJ
begin

(* Die gleiche Definition, wie Pr, aber mit ennreal. Außerdem werden alle A \<notin> Pow (\<Omega> ds) zu 0 *)
definition \<mu> where "\<mu> A = 
            (if A \<in> Pow (\<Omega> ds) 
             then ennreal ((card A) / (card (\<Omega> ds)))
             else 0)"

(* Für eine Measure braucht man ein Tripel aus: (Grundraum, Sigma-Raum, Mess-Funktion *)
definition ds_measure :: "position measure" where
  "ds_measure =  Abs_measure (\<Omega> ds, Pow (\<Omega> ds), \<mu>)"    

(* Unsere Definition ist tatsächlich ein measure-soace *)
lemma mes_space: 
  shows "measure_space (\<Omega> ds) (Pow (\<Omega> ds)) (\<mu>)"
proof (unfold measure_space_def, intro conjI)
  show "sigma_algebra (\<Omega> ds) (Pow (\<Omega> ds))"
    by (simp add: sigma_algebra_Pow) 
next
  show "positive (Pow (\<Omega> ds)) (\<mu>)" unfolding positive_def \<mu>_def using Pr_def by simp 
next 
  show "countably_additive (Pow (\<Omega> ds)) (\<mu>)" 
  proof (unfold countably_additive_def, intro allI impI)
    fix A :: "nat \<Rightarrow> position set"
    assume range_sub:  "range A \<subseteq> Pow (\<Omega> ds)"
    assume disjoint:   "disjoint_family A"
    assume union_in:   "\<Union> (range A) \<in> Pow (\<Omega> ds)"

    have fin: "finite (range A)" using range_sub \<Omega>_def fin_mods
      by (simp add: finite_subset) 

    have "\<forall>i . A i \<in> Pow (\<Omega> ds)" 
      using union_in by fastforce
    hence simp_l:"(\<Sum>i . \<mu> (A i)) = (\<Sum>i . ennreal (real (card (A i)) / real (card (\<Omega> ds))))" 
      unfolding \<mu>_def by simp

    have simp_r: "\<mu> (\<Union> (range A)) = (ennreal (real (card (\<Union> (range A)))) / real (card (\<Omega> ds)))"
      unfolding \<mu>_def using union_in
      using divide_ennreal not_empty sat by auto

    have "(\<Sum>i . (ennreal (card (A i)))) = (ennreal (card (\<Union> (range A))))" 
    proof -
           have dis: "\<forall>i j. i \<noteq> j \<longrightarrow> A i \<inter> A j = {}" using disjoint by (simp add: disjoint_family_onD)
           hence fin_all: "\<forall>i . finite (A i)" using fin_mods \<Omega>_def
              by (meson Finite_Set.finite_set finite_positions finite_subset subset_UNIV) 
           obtain I :: "nat set" where fin_I: "finite I" and range_I: "range A = image A I"
             by (meson fin finite_subset_image subset_refl)
           hence "(\<Sum>i . (ennreal (card (A i)))) = (\<Sum>i \<in> I. ennreal (card (A i)))"
           proof (intro antisym)   
             show "(\<Sum>i\<in>I. ennreal (real (card (A i)))) \<le> (\<Sum>i. ennreal (real (card (A i))))"
               using fin_I sum_le_suminf by (metis summableI zero_order(1))
             next
               show "(\<Sum>i . ennreal (real (card (A i)))) \<le> (\<Sum>i \<in> I. ennreal (real (card (A i))))" 
               proof -
                 have "\<forall>x \<in> -I . ennreal (real (card (A x))) = 0" 
                 proof
                   fix x
                   assume "x \<in> -I"
                   hence "A x = {}" using range_I 
                     by (metis (no_types, opaque_lifting) ComplD all_not_in_conv bex_imageD dis disjoint_iff
                         rangeI)
                   thus "ennreal (real (card (A x))) = 0" by simp
                 qed
                 thus ?thesis 
                   by (metis (no_types, lifting) Compl_iff fin_I order_refl suminf_finite)
               qed
           qed
           also have "... = ennreal (\<Sum>i \<in> I. (card (A i)))"
             using sum_ennreal by auto
           also have "... = ennreal (card (\<Union>i \<in> I . (A i)))" using card_UN_disjoint fin dis fin_I fin_all
               by (metis (lifting) sum.cong)
           also have "... = ennreal (card (\<Union>(range A)))"  by (metis range_I)
           finally show ?thesis by auto
    qed
       
    hence "(\<Sum>i . ennreal (real (card (A i)) / real (card (\<Omega> ds)))) = (ennreal (real (card (\<Union> (range A)))) / real (card (\<Omega> ds)))" 
        by (metis (mono_tags, lifting) divide_ennreal ennreal_suminf_divide not_empty of_nat_0_le_iff
                        of_nat_0_less_iff sat suminf_cong)
     thus "(\<Sum>i . \<mu> (A i)) = (\<mu> (\<Union> (range A)))"  using simp_l simp_r
           by order
   qed
 qed

(* Elemente außerhalb des Sigma-Raums sind null per Definition.*)
lemma compl_0:
  shows "(\<forall>a \<in> -(Pow (\<Omega> ds)) . \<mu> a = 0)"
proof 
  fix a :: "position set"
  assume "a \<in> -(Pow (\<Omega> ds))"
  thus "\<mu> a = 0" using \<mu>_def by simp
  qed

(* Es gibt einen Isomorphismus zwischen unserem Raum und dem allgemeinen mes_space *)
lemma inv: 
"Rep_measure (Abs_measure (\<Omega> ds, Pow (\<Omega> ds), \<mu>)) = (\<Omega> ds, Pow (\<Omega> ds), \<mu>)"
  using Abs_measure_inverse mes_space compl_0 by auto

(* Die Summe des Grundraums ist 1 *)
lemma sum1:
  shows "emeasure ds_measure (space ds_measure) = 1"
proof -
  have "emeasure ds_measure = \<mu>" using inv ds_measure_def emeasure_def
    by (metis sndI)

  moreover have "(space ds_measure) = \<Omega> ds" using inv ds_measure_def space_def
    by (metis fstI)

  moreover have "\<mu> (\<Omega> ds) = 1" 
    using Pr_def \<Omega>_def \<Omega>_one sat not_empty by (simp add: \<mu>_def)
  ultimately show ?thesis by simp
qed


(* Hier die Brücke zu HOL-Probability. Damit ist unsere Definition ein prob_space *)
interpretation model_space: prob_space "ds_measure"
proof (unfold_locales)
  show "emeasure (ds_measure) (space (ds_measure)) = 1" 
    by (simp add: sum1)
next
  show "emeasure (ds_measure) (space (ds_measure)) \<noteq> \<top>" 
    by (simp add: sum1)
next
  show " \<exists>A. countable A \<and> A \<subseteq> sets (ds_measure) \<and> \<Union> A = space (ds_measure) \<and> (\<forall>a\<in>A. emeasure (ds_measure) a \<noteq> \<infinity>)" 
      proof (intro exI[of _ "{\<Omega> ds}"] conjI)
        show "countable {\<Omega> ds}"
          by simp
      next
        show "{\<Omega> ds} \<subseteq> sets ds_measure"
          unfolding ds_measure_def sets_def using inv
          by simp
      next
        show "\<Union> {\<Omega> ds} = space ds_measure"
          unfolding ds_measure_def space_def using inv
          by simp
      next
        show "\<forall>a \<in> {\<Omega> ds}. emeasure ds_measure a \<noteq> \<infinity>" 
          by (simp add: \<mu>_def ds_measure_def emeasure_def inv)
  qed
qed


(* Unsere Pr Definition ist die Dichte unseres prob_spaces, definiert über HOL-Probability *)
lemma pr_prob_eq: "Pr A ds = model_space.prob A" 
proof -
  let ?M = "ds_measure"
  have "model_space.prob A =  enn2real (emeasure ?M A)" using measure_def by metis
  also have "... = \<mu> A" using emeasure_def inv ds_measure_def
    by (metis calculation model_space.emeasure_eq_measure prod.sel(2))
  finally show ?thesis unfolding  \<mu>_def Pr_def
    by (smt (verit, del_insts)
        \<open>model_space.prob A = enn2real (emeasure ds_measure A)\<close> divide_ennreal
        divide_eq_0_iff enn2real_ennreal enn2real_top ennreal_divide_eq_0_iff
        ennreal_neg model_space.emeasure_eq_measure of_nat_0 of_nat_le_0_iff
        of_rat_divide of_rat_of_nat_eq of_real_divide of_real_of_nat_eq)
qed
abbreviation prob where "prob \<equiv> model_space.prob"

end


lemma total_prob:
  assumes sat: "satisfiable ds"
  assumes disjoint: "\<forall>i j. i \<noteq> j \<longrightarrow> (B i) \<inter> (B j) = {}"
  assumes fin: "finite I"
  assumes complete: "(\<Union>n \<in> I. (B n)) = \<Omega> ds"
  shows "Pr A ds = (\<Sum>n \<in> I . (Pr_cond A (B n) ds) * (Pr (B n) ds))"
(*<*)
proof -
  interpret prob_DoJ ds using sat by unfold_locales
  (* Das hier möche ich machen können *)
  have "Pr A ds = prob A" using pr_prob_eq 
    by presburger
  show ?thesis sorry
qed
end