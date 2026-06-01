theory probabilityDS
  imports Main  "HOL.Rat" defDS theoremsDS
begin

definition \<Omega> :: "ds \<Rightarrow> position set" where
  "\<Omega> ds = mods {} ds"

axiomatization where
  not_empty: "card (\<Omega> ds) > 0"

definition Pr :: "position set \<Rightarrow> ds \<Rightarrow> rat"
  where "Pr Ps ds = rat_of_nat (card (Ps \<inter> \<Omega> ds)) / (rat_of_nat (card (\<Omega> ds)))"

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
  assumes disjoint: "\<forall>i j. i \<noteq> j \<longrightarrow>  (A i) \<inter> (A j) = {}"
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
end
