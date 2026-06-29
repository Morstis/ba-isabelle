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
  where "doj ds p = Pr ds (propo p)"

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

lemma sat_impl_card_nn: "satisfiable ds \<Longrightarrow> card (\<Omega>_mods ds) > 0"
  using \<Omega>_mods_def satisfiable_def \<Omega>_mods_fin \<Omega>_def card_gt_0_iff by fastforce

lemma sat_un:
assumes "satisfiable (ds1 \<union> ds2)"
shows "satisfiable ds1" and "satisfiable ds2"
using assms satisfiable_def by (meson UnCI coherent_def)+


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
    moreover have "\<Omega>_mods (ds1 \<union> ds2) = (\<Omega>_mods ds1) \<inter> ?H" using \<Omega>_mods_def coherent_def by auto
    ultimately show ?thesis by (metis (mono_tags, lifting) of_nat_sum real_of_nat_indicator sum.cong)
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