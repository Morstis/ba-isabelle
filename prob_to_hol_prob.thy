theory prob_to_hol_prob
  imports Main   "HOL-Probability.Probability" probability definitions theorems 
begin

(* Dieses Theorem ist Teilweise mit Unterstützung von Claude entstanden *)

definition \<mu> where "\<mu> ds Ps = 
            (if Ps \<in> Pow (\<Omega> ds) 
             then ennreal ((card Ps) / (card (\<Omega> ds)))
             else 0)"

definition ds_measure :: "ds \<Rightarrow> position measure" where
  "ds_measure ds =  Abs_measure (\<Omega> ds, Pow (\<Omega> ds), (\<mu> ds))"    


locale prob_DoJ = 
  fixes ds :: "ds"
  assumes sat: "satisfiable ds"

context prob_DoJ
begin

lemma mes_space: 
  shows "measure_space (\<Omega> ds) (Pow (\<Omega> ds)) (\<mu> ds)"
proof (unfold measure_space_def, intro conjI)
  show "sigma_algebra (\<Omega> ds) (Pow (\<Omega> ds))"
    by (simp add: sigma_algebra_Pow) 
next
  show "positive (Pow (\<Omega> ds)) (\<mu> ds)" 
  proof (unfold positive_def)
    show "\<mu> ds {} = 0" unfolding \<mu>_def using Pr_def by simp 
  qed
next 
  show "countably_additive (Pow (\<Omega> ds)) (\<mu> ds)" 
  proof (unfold countably_additive_def, intro allI impI)
    fix A :: "nat \<Rightarrow> position set"
    assume range_sub:  "range A \<subseteq> Pow (\<Omega> ds)"
    assume disjoint:   "disjoint_family A"
    assume union_in:   "\<Union> (range A) \<in> Pow (\<Omega> ds)"


    have fin: "finite (range A)" using range_sub \<Omega>_def fin_mods
      by (simp add: finite_subset) 


    have fst_if: "\<forall>i . A i \<in> Pow (\<Omega> ds)" 
      using union_in by fastforce
    hence s:"(\<Sum>i . \<mu> ds (A i)) = (\<Sum>i . ennreal (real (card (A i)) / real (card (\<Omega> ds))))" 
      unfolding \<mu>_def by simp

    have u: "\<mu> ds (\<Union> (range A)) = (ennreal (real (card (\<Union> (range A)))) / real (card (\<Omega> ds)))"
      unfolding \<mu>_def using union_in
      using divide_ennreal not_empty sat by auto

     have "(\<Sum>i . ennreal (real (card (A i)) / real (card (\<Omega> ds)))) 
        = (ennreal (real (card (\<Union> (range A)))) / real (card (\<Omega> ds)))" 
     proof -
       have "(\<Sum>i . (ennreal (card (A i)))) = (ennreal (card (\<Union> (range A))))" 
       proof -
           obtain I :: "nat set" where fin_I: "finite I" and range_I: "range A = image A I"
             by (meson fin finite_subset_image subset_refl)

           have dis: "\<forall>i j. i \<noteq> j \<longrightarrow> A i \<inter> A j = {}" using disjoint by (simp add: disjoint_family_onD)
           have  "finite (\<Union> (range A))"
              by (metis Pow_iff \<Omega>_def fin_mods finite_subset union_in)
           hence fin_all: "\<forall>i . finite (A i)" using fin_mods \<Omega>_def
              by (meson Finite_Set.finite_set finite_positions finite_subset
                  subset_UNIV) 

            have r: "(\<Sum>i. ennreal (real (card (A i)))) = (ennreal (real (\<Sum>i. card (A i))))" 
              using ennreal_suminf_neq_top sorry
            
             have s_eq:  "(\<Sum>i. (card (A i))) = (\<Sum>i \<in> I . card ((A i)))"
               using ennreal_suminf_neq_top suminf_finite sorry
             also have "... = card (\<Union>i \<in> I . (A i))" using card_UN_disjoint fin dis fin_I fin_all
               by (metis (lifting) sum.cong)
             also have "... = (card (\<Union>(range A)))"  by (metis range_I)
             finally have "(\<Sum>i. (card (A i))) = (card (\<Union>(range A)))" by auto
             thus ?thesis  
               using ennreal_of_nat_eq_real_of_nat r by metis
       qed
        thus ?thesis
          by (metis (mono_tags, lifting) divide_ennreal ennreal_suminf_divide not_empty of_nat_0_le_iff
              of_nat_0_less_iff sat suminf_cong)
     qed
     thus "(\<Sum>i . \<mu> ds (A i)) = (\<mu> ds (\<Union> (range A)))"  using u s
           by order
   qed
 qed


lemma compl_0:
  shows "(\<forall>a \<in> -(Pow (\<Omega> ds)) . \<mu> ds a = 0)"
proof 
  fix a :: "position set"
  assume "a \<in> -(Pow (\<Omega> ds))"
  thus "\<mu> ds a = 0" using \<mu>_def by simp
  qed

lemma inv: "Rep_measure (Abs_measure (\<Omega> ds, Pow (\<Omega> ds), \<mu> ds)) = 
        (\<Omega> ds, Pow (\<Omega> ds), \<mu> ds)" using Abs_measure_inverse mes_space compl_0  by auto

lemma sum1:
  shows "emeasure (ds_measure ds) (space (ds_measure ds)) = 1"
proof -
  have "emeasure (ds_measure ds) = \<mu> ds" using inv ds_measure_def emeasure_def
    by (metis sndI)

  moreover have "(space (ds_measure ds)) = \<Omega> ds" using inv ds_measure_def space_def
    by (metis fstI)

  moreover have "(\<mu> ds) (\<Omega> ds) = 1" 
    using Pr_def \<Omega>_def \<Omega>_one sat not_empty by (simp add: \<mu>_def)
  ultimately show ?thesis by simp
qed


interpretation x: prob_space "ds_measure ds"
proof -
  have "emeasure (ds_measure ds) (space (ds_measure ds)) = 1" 
    using sum1 by auto
  moreover have "emeasure (ds_measure ds) (space (ds_measure ds)) \<noteq> \<top>" 
    using calculation by simp
  moreover have " \<exists>A. countable A \<and>
        A \<subseteq> sets (ds_measure ds) \<and>
        \<Union> A = space (ds_measure ds) \<and> (\<forall>a\<in>A. emeasure (ds_measure ds) a \<noteq> \<infinity>)" 
proof -
  show ?thesis
  proof (intro exI[of _ "{\<Omega> ds}"] conjI)
    show "countable {\<Omega> ds}"
      by simp
  next
    show "{\<Omega> ds} \<subseteq> sets (ds_measure ds)"
      unfolding ds_measure_def sets_def using inv
      by simp
  next
    show "\<Union> {\<Omega> ds} = space (ds_measure ds)"
      unfolding ds_measure_def space_def using inv
      by simp
  next
    show "\<forall>a \<in> {\<Omega> ds}. emeasure (ds_measure ds) a \<noteq> \<infinity>" 
      by (simp add: \<mu>_def ds_measure_def emeasure_def inv)
  qed
qed

  ultimately show "prob_space (ds_measure ds)" by unfold_locales
qed
end
end