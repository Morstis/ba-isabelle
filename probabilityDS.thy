theory probabilityDS
  imports Main  "HOL.Rat" defDS theoremsDS
begin

definition \<Omega> :: "ds \<Rightarrow> position set" where
  "\<Omega> ds = mods {} ds"

axiomatization where
  not_empty: "card (\<Omega> ds) > 0"

definition Pr :: "position set \<Rightarrow> ds \<Rightarrow> rat"
  where "Pr Ps ds = rat_of_nat (card (Ps \<inter> \<Omega> ds)) / (rat_of_nat (card (\<Omega> ds)))"

definition Pr_cond 
  where "Pr_cond P B ds =  Pr (P \<inter> B) ds / Pr B ds"

lemma bet0_1:
  shows "0 \<le> Pr Ps ds \<and> Pr Ps ds \<le> 1"
proof -
  have "0 \<le> Pr Ps ds" by (simp add: Pr_def)
  also have "Pr Ps ds \<le> 1"
    proof -
        have "Ps \<inter> \<Omega> ds \<subseteq> \<Omega> ds" by simp
        hence "card (Ps \<inter> \<Omega> ds) \<le> card (\<Omega> ds)"
        by (simp add: \<Omega>_def card_mono fin_mods)
        thus ?thesis
        by (metis Pr_def less_divide_eq_1 linorder_not_le of_nat_le_iff
            of_nat_less_0_iff)
    qed

  ultimately show ?thesis by simp
qed

lemma \<Omega>_one:
  shows "Pr (\<Omega> ds) ds = 1"
  using not_empty by (simp add: Pr_def)

lemma sigma_subadd:
  assumes subsets: "\<forall>n. (A n :: position set) \<subseteq> \<Omega> ds"
  assumes "finite I"
  shows "Pr (\<Union>n \<in> I . A n ) ds \<le> (\<Sum>n \<in> I . (Pr (A n) ds))"
proof -
  have  "(card (\<Union>n \<in> I . (A n) \<inter> \<Omega> ds)) \<le> (\<Sum>n \<in> I . card ((A n) \<inter> \<Omega> ds))"
    using card_UN_le assms(2) by blast
  thus ?thesis unfolding  Pr_def
  proof -
    show "rat_of_nat (card (\<Union> (A ` I) \<inter> \<Omega> ds)) / rat_of_nat (card (\<Omega> ds)) \<le> (\<Sum>a\<in>I. rat_of_nat (card (A a \<inter> \<Omega> ds)) / rat_of_nat (card (\<Omega> ds)))"
      by (metis (no_types) SUP_inf \<open>card (\<Union>n\<in>I. A n \<inter> \<Omega> ds) \<le> (\<Sum>n\<in>I. card (A n \<inter> \<Omega> ds))\<close> divide_right_mono of_nat_0_le_iff of_nat_le_iff of_nat_sum sum_divide_distrib)
  qed
qed

lemma sigma_add:
  assumes subsets: "\<forall>n. (A n :: position set) \<subseteq> \<Omega> ds"
  assumes disjoint: "\<forall>i j. i \<noteq> j \<longrightarrow> (A i) \<inter> (A j) = {}"
  assumes fin: "finite I"
  shows "Pr (\<Union>n \<in> I . A n ) ds = (\<Sum>n \<in> I . (Pr (A n) ds))"
proof -
  have "\<forall>i \<in> I. finite (A i)" using fin_mods \<Omega>_def 
    by (metis infinite_super subsets)
  hence  "(card (\<Union>n \<in> I . (A n) \<inter> \<Omega> ds)) = (\<Sum>n \<in> I . card ((A n) \<inter> \<Omega> ds))"
    using card_UN_disjoint fin disjoint 
    by (smt (verit, ccfv_SIG) inf.idem inf_le2 le_inf_iff subset_antisym subsets sum.cong)


  thus ?thesis unfolding Pr_def
    by (simp add: sum_divide_distrib)
qed


theorem doj_pr:
  shows "doj P ds = Pr (mods P ds) ds"
proof -
  have "mods P ds \<inter> \<Omega> ds = mods P ds" using mods_def \<Omega>_def by auto
  thus ?thesis unfolding doj_def doj_cond_def Pr_def \<sigma>_def \<Omega>_def
    by simp
qed


theorem doj_cond_pr_cond:
  shows "doj_cond P B ds = Pr_cond (mods P ds) (mods B ds) ds"
proof -
  have mods_sub: "\<forall>p . mods p ds \<subseteq> \<Omega> ds" using \<Omega>_def mods_def by auto
  have cap_union: "\<forall>A B . (mods (A \<union> B) ds) = (mods A ds \<inter> mods B ds)" unfolding mods_def 
    by blast

  have "Pr (mods P ds \<inter> mods B ds) ds / Pr (mods B ds) ds 
    = rat_of_nat (card (mods P ds \<inter> mods B ds \<inter> \<Omega> ds)) / rat_of_nat (card (mods B ds \<inter> \<Omega> ds))"
    unfolding Pr_def
    using not_empty by auto
  also have "... = rat_of_nat (card (mods P ds \<inter> mods B ds)) / rat_of_nat (card (mods B ds))" 
    using mods_sub  by (simp add: inf_absorb1 inf_assoc)
  also have "... = rat_of_nat (card (mods (P \<union> B) ds)) / rat_of_nat (card (mods B ds))"
    using cap_union by auto
  finally show ?thesis unfolding doj_cond_def \<sigma>_def Pr_cond_def by simp
qed

(* Der Satz gilt *)
lemma total_prob:
  assumes disjoint: "\<forall>i j. i \<noteq> j \<longrightarrow> (B i) \<inter> (B j) = {}"
  assumes fin: "finite I"
  assumes complete: "(\<Union>n \<in> I. (B n)) = \<Omega> ds"
  shows "Pr A ds = (\<Sum>n \<in> I . (Pr_cond A (B n) ds) * (Pr (B n) ds))"

proof -
  show ?thesis sorry 
qed

(* Das ist eine Anwendung des Satzes der totalen Wahrscheinlichkeit.
Das müsste technisch in Isabelle auch schöner gehen.*)
lemma simp_total:
  shows "Pr A ds = Pr_cond A (mods {Pos s} ds) ds * Pr (mods {Pos s} ds) ds + Pr_cond A (mods {Neg s} ds) ds * Pr (mods {Neg s} ds) ds"
  unfolding \<Omega>_def Pr_def Pr_cond_def total_prob compl_sen_union compl_sen_inter try
  by (smt (verit) Int_Un_distrib Int_Un_distrib2 Int_Un_eq(1,2,3,4)
      Un_Int_crazy add_divide_distrib boolean_algebra.conj_zero_right
      card_Un_disjoint card_mono compl_sen_inter compl_sen_union
      divide_eq_0_iff fin_mods finite_Int gr0I inf.assoc inf.commute
      inf.left_commute inf_idem inf_le2 inf_right_idem less_numeral_extra(3)
      nat_0_less_mult_iff nonzero_eq_divide_eq of_nat_0_eq_iff of_nat_add
      of_nat_le_0_iff of_nat_mono of_nat_mult)



end





