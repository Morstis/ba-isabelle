(*<*)
theory Doj
  imports Main "HOL.Rat" "HOL-Library.LaTeXsugar"  "HOL-Probability.Probability"  base
begin
(*>*)
declare [[quick_and_dirty = true]]

(* Isar Ref. S. 277 *)
text \<open>Wir definieren den Typen ccPosition als eine Position, die complete und konsistent ist.\<close>
typedef \<Omega> = "{P :: position. consistent P \<and> complete P}"
   using consistent_def complete_def literal.sel(1) 
   by (metis literal.disc(1) literal.disc_eq_case(2) literal.simps(6) mem_Collect_eq)
definition \<Omega> where "\<Omega> = (UNIV :: \<Omega> set)"

text \<open>Ein Argument hat die Form einer Implikation. Wenn die Prämissen in der Position enthalten sind,
erfüllt die Position das Argument, wenn die Konklusion ebenfalls entfalten ist. Wenn die Position
das Komplement einer Prämisse enthält, erfüllt die Position ebenfalls das Argument.
\#Info Wenn die Position dem Argument erfüllt, dann modelliert die Interpretation P das Argument\<close>
fun models_arg :: "position \<Rightarrow> argument \<Rightarrow> bool" (infix "\<Turnstile>\<^sub>a" 65)
  where "models_arg P (ps,c) = (ps \<subseteq>  P \<longrightarrow> c \<in>  P)"

text \<open>Eine vollständig und konsistente Position ist kohärent, wenn sie alle Argumente
der Debatte erfüllt.\<close>
definition coherent :: "\<Omega> \<Rightarrow> ds \<Rightarrow> bool"  (infix "\<Turnstile>" 65)
  where "coherent P ds = (\<forall>A \<in> ds . models_arg (Rep_\<Omega> P) A)"

definition satisfiable :: "ds \<Rightarrow> bool"
  where "satisfiable ds = (\<exists>P . P \<Turnstile> ds)"

text \<open>Die Positionen sind endlich\<close>
lemma finite_positions:  "finite (UNIV :: position)"
(*<*)
proof -
  have "((UNIV :: literal set) = range Pos \<union> range Neg)"
    by (metis literal.exhaust UNIV_eq_I Un_iff rangeI)
  thus ?thesis
    using finsen by (metis finite_Un finite_imageI)
qed
(*>*)

text \<open>Der Grundraum ist endlich => Wir befinden uns im diskreten Fall\<close>
lemma \<Omega>_fin: "finite \<Omega>"
(*<*)
  using finite_positions \<Omega>_def
  by (metis (full_types) Finite_Set.finite_set Rep_\<Omega>_inverse UNIV_I
      ex_new_if_finite finite_imageI image_eqI)
(*>*)

text \<open>Wir definieren @{term "\<Omega>_mods"} als Untermenge von @{term "\<Omega>"}, sodass alle @{term "p \<in> \<Omega>_mods"} zusätzlich die Debatte erfüllen.
Das sind alle Modelle der Debatte.\<close>
definition \<Omega>_mods where "\<Omega>_mods ds = {p \<in> \<Omega> . p \<Turnstile> ds}"

(*<*)
lemma \<Omega>_mods_fin: "finite (\<Omega>_mods ds)" using \<Omega>_fin 
  using \<Omega>_def rev_finite_subset by auto
(*>*)

text \<open>Wir definieren die Wahrscheinlichkeitsfunkion bzw. Dichte als Gleichverteilung.
Dabei werden alle nicht kohärenten Positionen nicht betrachtet. (of\_bool ist definiert als @{term "if P \<Turnstile> ds then 1 else 0"})\<close>


definition f :: "ds \<Rightarrow> \<Omega> \<Rightarrow> real"
  where "f ds P =  (1 / card (\<Omega>_mods ds)) * (indicator (\<Omega>_mods ds) P)"

text \<open>Damit ist Pr ganz kanonisch genau das diskrete Wahrscheinlichkeitsmaß bzgl. f\<close>
definition Pr :: "ds \<Rightarrow> \<Omega> set \<Rightarrow> real"
  where "Pr ds Ps = (\<Sum> p \<in> Ps. f ds p)"

text \<open>Die bedingte Wahrscheinlichkeit ist folgendermaßen definiert.\<close>
definition Pr_cond 
  where "Pr_cond ds H E = Pr ds (H \<inter> E)  / Pr ds E"

definition propo :: "position \<Rightarrow> \<Omega> set" 
  where "propo p = {x \<in> \<Omega> . p \<subseteq> Rep_\<Omega> x}"

text \<open>doj lässt sich damit sehr einfach über Pr definieren.\<close>
definition doj :: "ds \<Rightarrow> position \<Rightarrow> real"
  where "doj ds P = Pr ds (propo P)"

text \<open>Bedingte doj lassen sich über Pr_cond definieren.\<close>
definition doj_cond :: "ds \<Rightarrow> position \<Rightarrow> position \<Rightarrow> real"
  where "doj_cond ds P B = Pr_cond ds (propo P) (propo B)"



locale fix_ds =
  fixes ds :: "ds"
  assumes sat: "satisfiable ds"

context fix_ds begin
  abbreviation carrier where "carrier \<equiv> \<Omega>_mods ds"
  definition \<mu> where "\<mu> \<equiv> pmf_of_set carrier"
end

sublocale fix_ds \<subseteq> model_space: prob_space "measure_pmf \<mu>"
  by (simp add: prob_space_measure_pmf)

context fix_ds begin
  abbreviation prob where "prob \<equiv> model_space.prob"
  abbreviation prob_cond where "prob_cond A B \<equiv> prob (A \<inter> B) / prob B"

  lemma pr_prob_eq [simp]: "Pr ds P = prob P" 
  proof -
  have "\<forall>x . (pmf \<mu>) x = f ds x"
  using pmf_of_set \<mu>_def f_def \<Omega>_mods_fin sat \<Omega>_mods_def satisfiable_def \<Omega>_def 
    by auto

  thus ?thesis using \<mu>_def 
    by (metis Pr_def \<Omega>_def \<Omega>_fin infinite_super measure_measure_pmf_finite subset_UNIV sum.cong)
  qed


lemma bayes: 
assumes "prob B > 0" "prob A > 0"
shows "prob_cond A B = (prob_cond B A * prob A) / prob B"
using assms by (simp add: inf.commute)

end

lemma bayes:
  assumes "satisfiable ds1"
  assumes "Pr ds1 A > 0" "Pr ds1 B > 0"
  shows "Pr_cond ds1 A B = Pr_cond ds1 B A * Pr ds1 A / Pr ds1 B"
proof -
  interpret fix_ds ds1 using assms(1) by unfold_locales
  show ?thesis using bayes assms Pr_cond_def pr_prob_eq by simp
qed

lemma sat_impl_card_nn: "satisfiable ds \<Longrightarrow> card (\<Omega>_mods ds) > 0"
  using \<Omega>_mods_def satisfiable_def \<Omega>_mods_fin \<Omega>_def card_gt_0_iff by fastforce

lemma sat_un:
assumes "satisfiable (ds1 \<union> ds2)"
shows "satisfiable ds1" and "satisfiable ds2"
using assms satisfiable_def by (meson UnCI coherent_def)+

lemma \<Omega>_mods_inter: "\<Omega>_mods (ds1 \<union> ds2) = (\<Omega>_mods ds1) \<inter> (\<Omega>_mods ds2)" using \<Omega>_mods_def coherent_def by auto

lemma Pr_to_cond:
assumes "satisfiable ds1"
shows "Pr (ds1 \<union> ds2) Ps = Pr_cond ds1 Ps (\<Omega>_mods ds2)"
proof -

let ?H = "(\<Omega>_mods ds2)"

have "Pr_cond ds1 Ps ?H = Pr ds1 (Ps \<inter> ?H) / Pr ds1 ?H" using Pr_cond_def by simp
also have "... = (1 / real (card (\<Omega>_mods ds1)) * (\<Sum> P \<in> (Ps \<inter> ?H) .indicator (\<Omega>_mods ds1) P))
                /(1 / real (card (\<Omega>_mods ds1)) * (\<Sum> P \<in> ?H .indicator (\<Omega>_mods ds1) P))"  
  unfolding Pr_def f_def by (simp add: sum_distrib_left)
also have "... = (\<Sum> P \<in> (Ps \<inter> ?H) .indicator (\<Omega>_mods ds1) P) / (\<Sum> P \<in> ?H .indicator (\<Omega>_mods ds1) P)"
  using sat_impl_card_nn assms by simp
also have "... =  (\<Sum> P \<in> (Ps \<inter> ?H) .indicator (\<Omega>_mods ds1) P) / card (\<Omega>_mods (ds1 \<union> ds2))"
  proof - 
    have "(\<Sum> P \<in> ?H .indicator (\<Omega>_mods ds1) P) = card ((\<Omega>_mods ds1) \<inter> ?H)"
      using \<Omega>_mods_def by (metis \<Omega>_def \<Omega>_fin finite_subset inf_sup_aci(1) sum_indicator_eq_card top.extremum) 
    thus  ?thesis using \<Omega>_mods_inter by (metis (mono_tags, lifting) of_nat_sum real_of_nat_indicator sum.cong)
  qed
also have "... = (1 / card (\<Omega>_mods (ds1 \<union> ds2))) * (\<Sum> P \<in> (Ps \<inter> ?H) .indicator (\<Omega>_mods ds1) P)" by algebra
also have "... = (1 / card (\<Omega>_mods (ds1 \<union> ds2))) * (\<Sum> P \<in> Ps  .indicator (\<Omega>_mods (ds1 \<union> ds2)) P)"
  proof - 
    have "\<Omega>_mods (ds1 \<union> ds2) = (\<Omega>_mods ds1) \<inter> ?H" using \<Omega>_mods_def coherent_def by auto
    hence "(\<Sum> P \<in> (Ps \<inter> ?H) .indicator (\<Omega>_mods ds1) P) = (\<Sum> P \<in> Ps  .indicator (\<Omega>_mods (ds1 \<union> ds2)) P)"
        using \<Omega>_mods_def \<Omega>_def \<Omega>_fin finite_subset
    by (smt (verit, best) Diff_iff Int_iff indicator_simps(1,2) subset_eq sum.mono_neutral_cong_right top.extremum)  
    thus ?thesis by auto
  qed
also have "... = Pr (ds1 \<union> ds2) Ps" unfolding Pr_def f_def by (rule sum_distrib_left)
finally show ?thesis by auto
qed


lemma move_norm [simp]: "Pr ds P =  (1 / (card (\<Omega>_mods ds))) * sum (indicator (\<Omega>_mods ds)) P" 
  unfolding Pr_def f_def by (simp add: sum_distrib_left)

lemma pr_card [simp]: "Pr ds P = (1 / (card (\<Omega>_mods ds))) * card (\<Omega>_mods ds \<inter> P)" 
proof -
  have "finite P" using  \<Omega>_fin \<Omega>_def using rev_finite_subset by auto
  hence "sum (indicator (\<Omega>_mods ds)) P = card (\<Omega>_mods ds \<inter> P)" using sum_indicator_eq_card 
    by (metis inf_sup_aci(1))
  thus ?thesis using move_norm by (metis of_nat_sum real_of_nat_indicator sum.cong)
qed


lemma extended_subset: "\<Omega>_mods (ds1 \<union> ds2) \<subseteq> \<Omega>_mods ds1" 
proof 
  fix x
  assume "x \<in> \<Omega>_mods (ds1 \<union> ds2)"
  thus "x \<in>  \<Omega>_mods ds1" 
    using \<Omega>_mods_def coherent_def consistent_def complete_def by simp
qed

lemma normal_subset_if_fullfills:
  assumes "\<forall>Q \<in> \<Omega>_mods ds1 . Q \<Turnstile> ds2"
  shows "\<Omega>_mods ds1 \<subseteq> \<Omega>_mods (ds1 \<union> ds2)"
(*<*)
proof
  fix x 
  assume "x \<in> \<Omega>_mods ds1"
  thus "x \<in>  \<Omega>_mods (ds1 \<union> ds2)" using \<Omega>_mods_def coherent_def 
complete_def consistent_def assms by fastforce
qed


lemma sat_union_deb_impl_Pr_gt0:
  assumes "satisfiable (ds1 \<union> ds2)"
  shows "Pr ds1 (\<Omega>_mods ds2) > 0" 
  using assms sat_un
    by (metis Pr_cond_def Pr_to_cond div_by_0 fix_ds.intro fix_ds.pr_prob_eq measure_pmf.prob_space_axioms one_neq_zero prob_space.prob_space zero_less_measure_iff)

lemma independence_eq [simp]: 
  assumes "Pr ds B > 0"
  shows "Pr_cond ds A B = Pr ds A \<longleftrightarrow> Pr ds (A \<inter> B) = Pr ds A * Pr ds B"
  using Pr_cond_def assms divide_eq_eq by (metis rel_simps(70))


text \<open>Monotonie für erweiterte Debatten ist probabilistische Relevanz der neuen Debatte für eine Position in der alten Debatte\<close>
theorem extends_prob_relevency_iff:
  assumes "satisfiable ds1"
  shows "doj (ds1 \<union> ds2) P - doj ds1 P = Pr_cond ds1 (propo P) (\<Omega>_mods ds2) - Pr ds1 (propo P)"
  using doj_def  Pr_to_cond assms by simp

definition propto :: "real \<Rightarrow> real \<Rightarrow> bool" (infix "\<propto>" 50) where
  "x \<propto> y \<longleftrightarrow> (\<exists> c > 0. x = c * y)"

lemma subset_args:  "\<forall>Ai \<in> ds . (\<Inter> A \<in> ds . \<Omega>_mods {A}) \<subseteq> \<Omega>_mods {Ai}"
  using \<Omega>_mods_inter by blast

lemma pr_to_args:
  assumes "satisfiable ds"
  shows "Pr ds P = Pr {} (P \<inter> (\<Inter> A \<in> ds . \<Omega>_mods {A})) / Pr {}  (\<Inter> A \<in> ds .  \<Omega>_mods {A})"
proof -
  have "\<forall>A \<in> ds . satisfiable {A}" using coherent_def satisfiable_def assms by auto
  hence "\<forall>A \<in> ds. \<Omega>_mods {A} \<noteq> {}" using \<Omega>_mods_def satisfiable_def by (metis card_gt_0_iff sat_impl_card_nn)
  hence "\<Omega>_mods ds = (\<Inter> A \<in> ds . \<Omega>_mods {A})" using \<Omega>_mods_def coherent_def 
    using \<Omega>_def by auto
  moreover have  "Pr ds P = Pr_cond {} P (\<Omega>_mods ds)" using Pr_to_cond 
    by (metis Un_empty_left assms sat_un(1))
  ultimately show ?thesis using Pr_cond_def by presburger
qed

lemma 
  assumes "satisfiable ds"
  assumes "ds \<noteq> {}"
  assumes "finite ds"
  shows "card (P \<inter> (\<Inter> A \<in> ds . \<Omega>_mods {A})) \<le> Min {card (P \<inter> \<Omega>_mods {A}) | A. A \<in> ds}"
proof -

  let ?A = "{card (\<Omega>_mods {A} \<inter> P) | A. A \<in> ds}"
  have "\<forall>Ai \<in> ?A . card (P \<inter> (\<Inter> A \<in> ds . \<Omega>_mods {A})) \<le> Ai" 
    using subset_args \<Omega>_mods_fin card_mono 
      by (smt (verit) Int_iff Set.basic_monos(7) finite_Int mem_Collect_eq subsetI)
  moreover have "?A \<noteq> {}" using assms by blast
  moreover have "finite ?A" using assms 
    by (smt (verit, del_insts) \<Omega>_def \<Omega>_fin card_mono finite_nat_set_iff_bounded_le mem_Collect_eq
        top_greatest)
  ultimately show ?thesis using Min_ge_iff 
    by (metis (no_types, lifting) ext inf_sup_aci(1))
qed

lemma Pr_cond_eq1:
  assumes "\<forall>x \<in> (propo P \<inter> \<Omega>_mods ds1) . x \<Turnstile> ds2"
  assumes "satisfiable ds1"
  assumes "Pr ds1 (propo P) > 0"
  shows "Pr_cond ds1 (\<Omega>_mods ds2) (propo P) = 1"
proof -
  have nn_gt0: "card ((\<Omega>_mods ds1) \<inter> (propo P)) > 0" using assms by (metis Num.of_nat_simps(1) of_nat_less_0_iff pr_card zero_less_mult_iff zero_order(5))

  have "(\<Omega>_mods (ds1 \<union> ds2)) \<inter> (propo P) = (\<Omega>_mods ds1) \<inter> (propo P)" 
  proof (intro antisym)
    show "\<Omega>_mods (ds1 \<union> ds2) \<inter> propo P \<subseteq> \<Omega>_mods ds1 \<inter> propo P" using extended_subset by blast
    show "\<Omega>_mods ds1 \<inter> propo P \<subseteq> \<Omega>_mods (ds1 \<union> ds2) \<inter> propo P" using normal_subset_if_fullfills assms try
      using \<Omega>_mods_def \<Omega>_mods_inter by auto
  qed
  hence "card ((\<Omega>_mods (ds1 \<union> ds2)) \<inter> (propo P)) = card ((\<Omega>_mods ds1) \<inter> (propo P))" by presburger
  hence "1 = (card ((\<Omega>_mods (ds1 \<union> ds2)) \<inter> (propo P)) / card ((\<Omega>_mods ds1) \<inter> (propo P)))" using nn_gt0 by simp
  thus ?thesis using pr_card 
    by (metis Pr_cond_def \<Omega>_mods_inter assms(3) divide_eq_eq_1 inf_sup_aci(2) order.strict_implies_not_eq)
qed

lemma Pr_cond_e0:
  assumes "\<forall>x \<in> (propo P \<inter> \<Omega>_mods ds1) . \<not>(x \<Turnstile> ds2)"
  assumes "satisfiable ds1"
  shows "Pr_cond ds1 (\<Omega>_mods ds2) (propo P) = 0"
proof -
  have "\<Omega>_mods (ds1 \<union> ds2) \<inter> (propo P) = {}" using assms 
    using \<Omega>_mods_def \<Omega>_mods_inter by auto
  hence "card ((\<Omega>_mods (ds1 \<union> ds2)) \<inter> (propo P)) = 0" by simp
  thus ?thesis using pr_card assms 
    by (metis (lifting) Multiseries_Expansion.intyness_0 Pr_cond_def
        \<Omega>_mods_inter divide_divide_eq_right division_ring_divide_zero inf_aci(3)
        inf_sup_aci(1))
qed
lemma 
  assumes "satisfiable ds1"
  assumes "Pr ds1 (propo P) > 0"
  assumes "Pr ds1 (\<Omega>_mods ds2) > 0"
  shows "doj (ds1 \<union> ds2) P - doj ds1 P \<propto>
        card (\<Omega>_mods ds1) * card ((\<Omega>_mods (ds1 \<union> ds2)) \<inter> propo P) - card (\<Omega>_mods (ds1 \<union> ds2)) * card (\<Omega>_mods ds1 \<inter> propo P)"
proof -

  let ?P = "propo P"
  let ?D = "\<Omega>_mods ds2"
  have gt0: "card (\<Omega>_mods ds1) > 0" using assms sat_impl_card_nn by simp

  interpret fix_ds ds1 using assms by unfold_locales
  let ?l1 = "(1 / prob ?D)"
  let ?l2 = "(1 / card (\<Omega>_mods ds1))^2"
  have "doj (ds1 \<union> ds2) P - doj ds1 P = Pr_cond ds1 ?P ?D - Pr ds1 ?P" using extends_prob_relevency_iff assms by presburger
  have "... = prob_cond ?P ?D - prob ?P" using pr_prob_eq unfolding Pr_cond_def by simp
  also have "... = (1 / prob ?D) * prob (?P \<inter> ?D) - prob ?P" by simp
  also have "... = (1 / prob ?D) * (prob (?P \<inter> ?D) - prob ?P * prob ?D)" using assms(3) pr_prob_eq 
    by (simp add: right_diff_distrib)
  also have "... = ?l1 * (prob (?P \<inter> ?D) - prob ?P * prob ?D)" using assms(3) propto_def 
    by simp
  also have "... =?l1 * (1 / card (\<Omega>_mods ds1)) * card (?P \<inter>?D \<inter> \<Omega>_mods ds1) - 
                   (1 / card (\<Omega>_mods ds1)) * card (?D \<inter> \<Omega>_mods ds1) * (1 / card (\<Omega>_mods ds1)) * card (?P \<inter> \<Omega>_mods ds1)" 
    using pr_card pr_prob_eq sorry

  also have "... =?l1 * (1 / card (\<Omega>_mods ds1)) * card (?P \<inter>?D \<inter> \<Omega>_mods ds1) - 
                   (1 / card (\<Omega>_mods ds1))^2 * card (?D \<inter> \<Omega>_mods ds1) * card (?P \<inter> \<Omega>_mods ds1)" by algebra
  also have "... = ?l1 * (1 / card (\<Omega>_mods ds1)) * (card (?P \<inter>?D \<inter> \<Omega>_mods ds1) - (1 / card (\<Omega>_mods ds1)) * card (?D \<inter> \<Omega>_mods ds1) * card (?P \<inter> \<Omega>_mods ds1))"
    using gt0 sorry
  also have "... =?l1 * (1 / card (\<Omega>_mods ds1)) * (card (?P \<inter>?D \<inter> \<Omega>_mods ds1) * card (\<Omega>_mods ds1) * (1 / card (\<Omega>_mods ds1))  - (1 / card (\<Omega>_mods ds1)) * card (?D \<inter> \<Omega>_mods ds1) * card (?P \<inter> \<Omega>_mods ds1))"
    using gt0 by auto
  also have "... = ?l1 * ?l2 * (card (?P \<inter>?D \<inter> \<Omega>_mods ds1) * card (\<Omega>_mods ds1) - card (?D \<inter> \<Omega>_mods ds1) * card (?P \<inter> \<Omega>_mods ds1))"
    sorry
  also have "... = ?l1 * ?l2 * card (\<Omega>_mods ds1) * card ((\<Omega>_mods (ds \<union> ds2)) \<inter> propo P) - card (\<Omega>_mods (ds1 \<union> ds2)) * card (\<Omega>_mods ds1 \<inter> propo P)"
    using \<Omega>_mods_inter propto_def sorry
  finally show ?thesis try
qed



text \<open>Bzw. die probabilisitische Relevanz von Position P für die Debatte.\<close>
theorem weak_mono_bayes:
  assumes "satisfiable ds1"
  assumes "Pr ds1 (propo P) > 0"
  assumes "Pr ds1 (\<Omega>_mods ds2) > 0"
  shows "Pr_cond ds1 (propo P) (\<Omega>_mods ds2) \<ge> Pr ds1 (propo P) \<longleftrightarrow> Pr_cond ds1 (\<Omega>_mods ds2) (propo P) \<ge> Pr ds1 (\<Omega>_mods ds2)"
proof -
have "Pr_cond ds1 (propo P) (\<Omega>_mods ds2) - Pr ds1 (propo P) = 
      Pr_cond ds1 (\<Omega>_mods ds2) (propo P) * Pr ds1 (propo P) / Pr ds1 (\<Omega>_mods ds2) - Pr ds1 (propo P)" using assms bayes by metis
  also have "... =  Pr ds1 (propo P) / Pr ds1 (\<Omega>_mods ds2) * (Pr_cond ds1 (\<Omega>_mods ds2) (propo P) - Pr ds1 (\<Omega>_mods ds2))" using assms
    by (simp add: vector_space_over_itself.scale_right_diff_distrib) 
  finally show ?thesis using assms by (simp add: Groups.mult_ac(2) Pr_cond_def inf_commute pos_le_divide_eq)
qed

theorem mono_bayes:
  assumes "satisfiable ds1"
  assumes "Pr ds1 (propo P) > 0"
  assumes "Pr ds1 (\<Omega>_mods ds2) > 0"
  shows "Pr_cond ds1 (propo P) (\<Omega>_mods ds2) > Pr ds1 (propo P) \<longleftrightarrow> Pr_cond ds1 (\<Omega>_mods ds2) (propo P) > Pr ds1 (\<Omega>_mods ds2)"
proof -
have "Pr_cond ds1 (propo P) (\<Omega>_mods ds2) - Pr ds1 (propo P) = 
      Pr_cond ds1 (\<Omega>_mods ds2) (propo P) * Pr ds1 (propo P) / Pr ds1 (\<Omega>_mods ds2) - Pr ds1 (propo P)" using assms bayes by metis
  also have "... =  Pr ds1 (propo P) / Pr ds1 (\<Omega>_mods ds2) * (Pr_cond ds1 (\<Omega>_mods ds2) (propo P) - Pr ds1 (\<Omega>_mods ds2))" using assms
    by (simp add: vector_space_over_itself.scale_right_diff_distrib) 
  finally show ?thesis using assms by (smt (verit, best) divide_le_0_iff mult_sign_intros(5) zero_less_mult_pos)
qed



text \<open>Debatte ds2 ist unabhängig von einer Debatte ds1, genau dann wenn alle Modelle von ds1 bereits ds2 erfüllen. \<close>
lemma independence:
  assumes "Pr ds1 (\<Omega>_mods ds2) > 0"
  assumes "\<forall>Q \<in> \<Omega>_mods ds1 . Q \<Turnstile> ds2"
  shows "Pr ds1 ((\<Omega>_mods ds2) \<inter> (propo P)) = Pr ds1 (\<Omega>_mods ds2) * Pr ds1 (propo P)"
proof -

  have "Pr ds1 ((\<Omega>_mods ds2) \<inter> (propo P)) - Pr ds1 (\<Omega>_mods ds2) * Pr ds1 (propo P) = 
       (1 / (card (\<Omega>_mods ds1))) * card (\<Omega>_mods ds1 \<inter> (\<Omega>_mods ds2) \<inter> (propo P)) -
       (1 / (card (\<Omega>_mods ds1))) * card (\<Omega>_mods ds1 \<inter> \<Omega>_mods ds2) * (1 / (card (\<Omega>_mods ds1))) * card (\<Omega>_mods ds1 \<inter> (propo P))" 
    using pr_card by (metis inf_assoc more_arith_simps(11))
  hence "?thesis \<longleftrightarrow> card (\<Omega>_mods ds1) * card (\<Omega>_mods ds1 \<inter> \<Omega>_mods ds2 \<inter> propo P) = card (\<Omega>_mods ds1 \<inter> \<Omega>_mods ds2) * card (\<Omega>_mods ds1 \<inter> propo P)"
    by (smt (verit) assms divide_eq_0_iff move_norm mult_cancel_right1 mult_eq_0_iff nonzero_mult_div_cancel_left of_nat_eq_iff
        of_nat_mult times_divide_eq_left times_divide_eq_right)


  moreover have "card (\<Omega>_mods ds1) * card (\<Omega>_mods ds1 \<inter> \<Omega>_mods ds2 \<inter> propo P) = card (\<Omega>_mods ds1 \<inter> \<Omega>_mods ds2) * card (\<Omega>_mods ds1 \<inter> propo P)"
  proof -
    have "\<Omega>_mods (ds1 \<union> ds2) = \<Omega>_mods ds1" using assms normal_subset_if_fullfills extended_subset by blast
    hence  "\<Omega>_mods ds1 \<inter> \<Omega>_mods ds2 = \<Omega>_mods ds1" using \<Omega>_mods_inter by simp
    thus ?thesis by simp
  qed
  ultimately show ?thesis by simp
qed

theorem extended_eq:
  assumes "satisfiable ds1"
  assumes "\<forall>Q \<in> \<Omega>_mods ds1 . Q \<Turnstile> ds2"
  shows "doj (ds1 \<union> ds2) P = doj ds1 P" 
  using extends_prob_relevency_iff independence_eq
  by (metis assms(2) doj_def equalityI extended_subset move_norm normal_subset_if_fullfills)

theorem support:
  assumes "satisfiable (ds1 \<union> ds2)"
  assumes "doj ds1 P > 0"
  shows "doj (ds1 \<union> ds2) P = doj ds1 P"
  proof -
  interpret fix_ds ds1 using assms sat_un by unfold_locales

  have "Pr ds1 (\<Omega>_mods ds2) > 0" using assms sat_un  
    by (metis Pr_cond_def Pr_to_cond div_by_0 fix_ds.intro fix_ds.pr_prob_eq measure_pmf.prob_space_axioms one_neq_zero prob_space.prob_space zero_less_measure_iff)
  hence H_gt0: "prob (\<Omega>_mods ds2) > 0" by simp
  have P_gt0: "prob (propo P) > 0" using assms(2) unfolding doj_def by simp

  (* have "Pr ds1 (propo P) > 0" using assms Pr_def f_def  *)
  have "doj (ds1 \<union> ds2) P = Pr_cond ds1 (propo P) (\<Omega>_mods ds2)" using doj_def Pr_to_cond assms sat_un by metis
  also have "... = prob_cond (propo P) (\<Omega>_mods ds2)" using Pr_cond_def by simp
  also have "... = prob_cond (\<Omega>_mods ds2) (propo P) * prob (propo P) / prob (\<Omega>_mods ds2)" using bayes H_gt0 P_gt0 by simp

  have "Pr_cond ds1 (\<Omega>_mods ds2) (propo P) = 1" using Pr_cond_def assms sat_un try

  show ?thesis sorry
  qed

(*<*)
end
(*>*)