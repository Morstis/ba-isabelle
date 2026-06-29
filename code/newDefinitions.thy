(*<*)
theory newDefinitions
  imports Main "HOL-Probability.Probability" base 
begin

declare [[quick_and_dirty = true]]
(*>*)
(* Ref Isar S. 277 *)
text \<open>Wir definieren den Typen ccPosition als eine Position, die complete und konsistent ist.\<close>
typedef ccPosition  = "{P :: position. consistent P \<and> complete P}"
   using consistent_def complete_def literal.sel(1) 
   by (metis literal.disc(1) literal.disc_eq_case(2) literal.simps(6) mem_Collect_eq)


text \<open>Ein Argument hat die Form einer Implikation. Wenn die Prämissen in der Position enthalten sind,
erfüllt die Position das Argument, wenn die Konklusion ebenfalls entfalten ist. Wenn die Position
das Komplement einer Prämisse enthält, erfüllt die Position ebenfalls das Argument.
\#Info Wenn die Position dem Argument erfüllt, dann modelliert die Interpretation P das Argument\<close>
fun models_arg :: "position \<Rightarrow> argument \<Rightarrow> bool"
  where "models_arg P (ps,c) = (ps \<subseteq>  P \<longrightarrow> c \<in>  P)"

text \<open>Eine vollständig und konsistente Position ist kohärent, wenn sie alle Argumente
der Debatte erfüllt.\<close>
definition coherent :: "ccPosition \<Rightarrow> ds \<Rightarrow> bool"  (infix "\<Turnstile>" 65)
  where "coherent P ds = (\<forall>A \<in> ds . models_arg (Rep_ccPosition P) A)"

definition satisfiable :: "ds \<Rightarrow> bool"
  where "satisfiable ds = (\<exists>P . P \<Turnstile> ds)"


text \<open>Wir wählen den Grundraum als die Menge aller vollständig, konsistenten Positionen\<close>
type_alias \<Omega> = "ccPosition"
definition \<Omega> where "\<Omega> = (UNIV :: \<Omega> set)"


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
  by (metis (full_types) Finite_Set.finite_set Rep_ccPosition_inverse UNIV_I
      ex_new_if_finite finite_imageI image_eqI)
(*>*)

text \<open>Wir definieren @{term "\<Omega>\<^sub>T"} als Untermenge von @{term "\<Omega>"}, sodass alle @{term "p \<in> \<Omega>\<^sub>T"} zusätzlich die Debatte erfüllen.
Das sind alle Modelle der Debatte.\<close>
definition \<Omega>\<^sub>T where "\<Omega>\<^sub>T ds = {p :: \<Omega> . p \<Turnstile> ds}"

(*<*)
lemma \<Omega>\<^sub>T_fin: "finite (\<Omega>\<^sub>T ds)" using \<Omega>_fin 
  using \<Omega>_def rev_finite_subset by auto
(*>*)

text \<open>Wir definieren die Wahrscheinlichkeitsfunkion bzw. Dichte als Gleichverteilung.
Dabei werden alle nicht kohärenten Positionen nicht betrachtet. (of\_bool ist definiert als @{term "if P \<Turnstile> ds then 1 else 0"})\<close>
definition f :: " \<Omega> \<Rightarrow> ds \<Rightarrow> ennreal"
  where "f P ds = (1 / card (\<Omega>\<^sub>T ds)) * (indicator (\<Omega>\<^sub>T ds) P)"

text \<open>Damit ist Pr ganz kanonisch genau das diskrete Wahrscheinlichkeitsmaß bzgl. f\<close>
definition Pr :: "\<Omega> set \<Rightarrow> ds \<Rightarrow> ennreal"
  where "Pr Ps ds = (\<Sum> p \<in> Ps. f p ds)"

text \<open>doj lässt sich damit sehr einfach über Pr definieren.\<close>
definition doj :: "position \<Rightarrow> ds \<Rightarrow> ennreal"
  where "doj p ds = Pr {x \<in> \<Omega> . p \<subseteq> Rep_ccPosition x} ds"


text \<open>@{term "\<Omega>\<^sub>T"} ist der Träger von Pr bzw. f\<close>
lemma "\<Omega>\<^sub>T ds = {p :: \<Omega> . f p ds > 0}" 
(*<*)
proof -
  have "\<forall>p . f p ds > 0 \<longleftrightarrow> p \<Turnstile> ds" using \<Omega>\<^sub>T_def f_def \<Omega>_fin of_bool_def indicator_def
    by (metis \<Omega>\<^sub>T_fin card_gt_0_iff empty_iff ennreal_less_zero_iff
        mem_Collect_eq mult_cancel_left2 mult_eq_0_iff of_nat_0_less_iff
        rel_simps(70) zero_less_divide_1_iff)
  thus ?thesis using \<Omega>\<^sub>T_def by simp
qed
(*>*)

text \<open>Wir fixieren eine ds und nehmen an, dass diese erfüllbar ist\<close>
(*<*)
locale fix_ds = 
(*>*)
  fixes ds :: "ds"
  assumes sat: "satisfiable ds"

(*<*)
context fix_ds
begin
(*>*)
abbreviation \<mu> where "\<mu> p \<equiv> Pr p ds"

(*<*)
abbreviation ds_measure :: "\<Omega> measure" where
  "ds_measure \<equiv> measure_of \<Omega> (Pow \<Omega>) \<mu>"

lemma denom_nn: "card (\<Omega>\<^sub>T ds) > 0" using sat \<Omega>\<^sub>T_def unfolding satisfiable_def 
        using \<Omega>\<^sub>T_fin card_gt_0_iff by blast
(*>*)
text \<open>Offensichtlich ist die Summe des Grundraums 1\<close>
lemma \<mu>_sum: "\<mu> \<Omega> = 1"
(*<*)
proof -
  let ?x = "(\<Omega>\<^sub>T ds)"
    have t_sum: "\<mu> ?x = 1" 
    proof -
      have "\<forall>p \<in> ?x . p \<Turnstile> ds" using \<Omega>\<^sub>T_def by simp
      hence "\<forall>p \<in> ?x . f p ds = (1 / real (card (?x)) )" using f_def of_bool_def by simp
      hence "\<mu> ?x = (\<Sum>p \<in> ?x . (1 / card ?x ))" unfolding Pr_def
        by (smt (verit, best) denom_nn of_nat_0_less_iff sum.cong sum_ennreal
            zero_less_divide_1_iff)
      also have "... = (1 / card ?x) * (\<Sum>p \<in> ?x . 1)" by simp
      also have "... = (1 / card ?x  ) * card ?x " by simp
      finally show ?thesis using denom_nn by auto
    qed

    have "\<forall>x \<in> (\<Omega> - \<Omega>\<^sub>T ds) . \<not>(x \<Turnstile> ds)" using \<Omega>\<^sub>T_def by simp
    hence nt_0: "\<forall>x \<in> (\<Omega> - \<Omega>\<^sub>T ds) . f x ds = 0" using f_def by simp

    have "\<mu> \<Omega> = (\<Sum>i \<in> (\<Omega> - ?x). f i ds) + (\<Sum>y \<in> ?x . f y ds)" using \<Omega>_fin \<Omega>\<^sub>T_fin
      by (metis Pr_def \<Omega>_def subset_UNIV sum.subset_diff)
    also have "... = (\<Sum>y \<in> ?x . f y ds)" using nt_0 by simp
    also have  "... = \<mu> ?x" using Pr_def by simp
    finally show ?thesis using t_sum by simp
  qed
(*>*)

text \<open>Es gilt die @{term "\<sigma>"}-Additivität für @{term "\<mu>"}.\<close>
lemma sigma_sum: "countably_additive (Pow \<Omega>) \<mu>" 
proof (unfold countably_additive_def, intro allI impI)
    fix A :: "nat \<Rightarrow> \<Omega> set"
    assume range_sub:  "range A \<subseteq> Pow \<Omega>"
    assume disjoint:   "disjoint_family A"
    assume union_in:   "\<Union> (range A) \<in> Pow \<Omega>"
(*<*)
    have move_norm: "\<forall>x . \<mu> x = (1 / card (\<Omega>\<^sub>T ds) ) * ennreal (\<Sum>p\<in>x. of_bool (p \<Turnstile> ds))"
    proof 
      fix x
      have "\<mu> x = ennreal (\<Sum>p\<in>x. (1 / (card (\<Omega>\<^sub>T ds)) * of_bool (p \<Turnstile> ds)))" 
        unfolding Pr_def f_def indicator_def \<Omega>\<^sub>T_def by simp
      also have "... = ennreal (1 / card (\<Omega>\<^sub>T ds) ) * (\<Sum>p\<in>x. of_bool (p \<Turnstile> ds))" 
        using ennreal_suminf_cmult 
        by (smt (verit) Num.of_nat_simps(2,5) Pr_def \<Omega>\<^sub>T_def calculation divide_nonneg_nonneg ennreal_0
            ennreal_mult' f_def indicator_def mem_Collect_eq more_arith_simps(6) of_bool_eq(1,2)
            of_nat_0_le_iff sum.cong sum_distrib_left times_divide_eq_left)
      also have "... = (1 / card(\<Omega>\<^sub>T ds) ) * ennreal (\<Sum>p\<in>x. of_bool (p \<Turnstile> ds))" 
        by (smt (verit, ccfv_SIG) ennreal_0 ennreal_1 of_bool_eq(1,2) sum.cong sum_ennreal)
      finally show "\<mu> x = (1 / card (\<Omega>\<^sub>T ds) ) * ennreal (\<Sum>p\<in>x. of_bool (p \<Turnstile> ds))" by auto
  qed

    hence simp_u: "(\<mu> (\<Union> (range A))) = (1 / real (card  (\<Omega>\<^sub>T ds)) * ennreal (\<Sum>p\<in>\<Union> (range A). of_bool (p \<Turnstile> ds)))"
      unfolding Pr_def f_def using ennreal_suminf_cmult by presburger
    have simp_s: "(\<Sum>i . \<mu> (A i)) = (1 / real (card (\<Omega>\<^sub>T ds)) ) * (\<Sum>i. ennreal (\<Sum>p\<in>A i. of_bool (p \<Turnstile> ds)))" 
       using move_norm ennreal_suminf_cmult unfolding Pr_def f_def by presburger



    have "(\<Sum>i. ennreal (\<Sum>p\<in>A i. of_bool (p \<Turnstile> ds))) = ennreal (\<Sum>p\<in>\<Union> (range A). of_bool (p \<Turnstile> ds))"
    proof -
     have t_partition: "\<forall>i . A i = (\<Omega>\<^sub>T ds \<inter> A i) \<union> ((\<Omega> - \<Omega>\<^sub>T ds) \<inter> A i)"
        using \<Omega>\<^sub>T_def \<Omega>_def by auto



    have "(\<Sum>p\<in>\<Union>(range A). of_bool (p \<Turnstile> ds)) = card (\<Union>i. (\<Omega>\<^sub>T ds \<inter> A i))"
    proof -
       have fin_parts: "finite (\<Union> i . (\<Omega>\<^sub>T ds \<inter> A i))"
          using \<Omega>\<^sub>T_fin disjoint disjoint_family_on_def by simp
       have fin_parts2: "finite (\<Union> i . ((\<Omega> - \<Omega>\<^sub>T ds) \<inter> A i))"
         using \<Omega>_fin disjoint disjoint_family_on_def by simp

       have "(\<Sum>p\<in>\<Union>(range A). of_bool (p \<Turnstile> ds)) = (\<Sum>p \<in> (\<Union>i. A i) . of_bool (p \<Turnstile> ds))" by auto
        also have "... = (\<Sum>p \<in> (\<Union>i. (\<Omega>\<^sub>T ds \<inter> A i) \<union> ((\<Omega> - \<Omega>\<^sub>T ds) \<inter> A i)) . of_bool (p \<Turnstile> ds))" 
          using t_partition by simp
        also have "... = (\<Sum>p \<in> ((\<Union>i. (\<Omega>\<^sub>T ds \<inter> A i)) \<union> (\<Union> i. ((\<Omega> - \<Omega>\<^sub>T ds) \<inter> A i))) . of_bool (p \<Turnstile> ds))"
          by (metis Un_Union_image)
        also have  "...
            = (\<Sum>p\<in> (\<Union>i. (\<Omega>\<^sub>T ds \<inter> A i)). of_bool (p \<Turnstile> ds))
            + (\<Sum>p\<in> (\<Union>i. ((\<Omega> - \<Omega>\<^sub>T ds) \<inter> A i)) . of_bool (p \<Turnstile> ds))"
          using fin_parts fin_parts2 sum.union_disjoint t_partition by blast
        also have "... = (\<Sum>p\<in> (\<Union>i. (\<Omega>\<^sub>T ds \<inter> A i)). of_bool (p \<Turnstile> ds))"
          using t_partition \<Omega>\<^sub>T_def by simp
        also have "... = (\<Sum>p\<in> (\<Union>i. (\<Omega>\<^sub>T ds \<inter> A i)). 1)"
          using \<Omega>\<^sub>T_def by auto
        also have "... = card (\<Union>i. (\<Omega>\<^sub>T ds \<inter> A i))" by simp
        finally show ?thesis by auto
      qed
    moreover have  "\<forall>i . (\<Sum>p\<in>A i. of_bool (p \<Turnstile> ds)) = card (\<Omega>\<^sub>T ds \<inter> A i)"
      proof
       fix i
      have "(\<Sum>p\<in>A i. of_bool (p \<Turnstile> ds)) = (\<Sum>p \<in> (\<Omega>\<^sub>T ds \<inter> A i) . of_bool (p \<Turnstile> ds)) + (\<Sum>p \<in> ((\<Omega> - \<Omega>\<^sub>T ds) \<inter> A i) . of_bool (p \<Turnstile> ds))" using t_partition
        by (metis Diff_Int_distrib2 Diff_disjoint \<Omega>_def \<Omega>_fin finite_Int inf_top_right
            sum.union_disjoint)
      also have "... = (\<Sum>p \<in> (\<Omega>\<^sub>T ds \<inter> A i) . of_bool (p \<Turnstile> ds))" using \<Omega>\<^sub>T_def by auto
      also have "... = (\<Sum>p \<in> (\<Omega>\<^sub>T ds \<inter> A i) . 1)" using  \<Omega>\<^sub>T_def by auto
      also have "... = card (\<Omega>\<^sub>T ds \<inter> A i)" using card_def by simp
      finally show "(\<Sum>p\<in>A i. of_bool (p \<Turnstile> ds)) = card (\<Omega>\<^sub>T ds \<inter> A i)" by simp
    qed
    moreover have "(\<Sum>i . ennreal (card (\<Omega>\<^sub>T ds \<inter> A i))) = ennreal (card (\<Union>i. (\<Omega>\<^sub>T ds \<inter> A i)))" 
    proof -
      let ?A = "range (\<lambda>i. \<Omega>\<^sub>T ds \<inter> A i)"
      have "\<forall>x \<in> ?A . finite x" using \<Omega>\<^sub>T_fin by simp
      moreover have "disjoint ?A" using disjoint disjoint_family_on_def sorry
      ultimately have "sum card ?A = card (\<Union> ?A)" using card_Union_disjoint by metis
      hence "(\<Sum>i . (card (\<Omega>\<^sub>T ds \<inter> A i))) = card (\<Union>i . (\<Omega>\<^sub>T ds \<inter> A i))"  sorry
      show ?thesis sorry
    qed
    ultimately show ?thesis
      by (metis (mono_tags, lifting) of_nat_of_bool
          of_nat_sum sum.cong suminf_cong)
    qed
(*>*)

    thus "(\<Sum>i . \<mu> (A i)) = (\<mu> (\<Union> (range A)))" using simp_s simp_u by presburger
  qed
  find_theorems "pmf_of_set"
  find_theorems "density"

definition Pr_measure :: "\<Omega> measure" where
  "Pr_measure = density (count_space (\<Omega>\<^sub>T ds)) (\<lambda>P. f P ds)"

lemma Pr_measure_prob_space:
  shows "prob_space (Pr_measure)"
proof (rule prob_spaceI)
  show "emeasure (Pr_measure) (space (Pr_measure)) = 1"
  proof -
    have "emeasure (Pr_measure) (\<Omega>\<^sub>T ds) = (\<Sum> P \<in> (\<Omega>\<^sub>T ds). f P ds)"
      unfolding Pr_measure_def f_def using emeasure_density nn_integral_count_space_finite
      by (metis (lifting) Set.basic_monos(6) \<Omega>\<^sub>T_def \<Omega>\<^sub>T_fin emeasure_point_measure_finite
          point_measure_def)
    also have "... = card (\<Omega>\<^sub>T ds) * (1 / card (\<Omega>\<^sub>T ds))"
      by (smt (verit, best) divide_nonneg_nonneg f_def indicator_simps(1) mult_cancel_right1
          of_nat_0_le_iff sum.cong sum_constant sum_ennreal times_divide_eq_left)
    also have "... = 1"
      using \<Omega>\<^sub>T_fin denom_nn by auto
    finally show ?thesis by (simp add: Pr_measure_def)
  qed
qed

text \<open>Wenig überraschend ist damit ds\_measure ein Wahrscheinlichkeitsraum. 
Bzw. Pr ist tatsächlich ein Wahrscheinlichkeitsmaß mit Dichte f. Und wir können alle Theoreme von Isabelle HOL-Probability benutzen.\<close>
interpretation model_space: prob_space "ds_measure"
proof (intro prob_spaceI)
  have "\<mu> \<Omega> = 1" using \<mu>_sum by simp
  moreover have "(space ds_measure) = \<Omega>" by simp
  moreover have "emeasure ds_measure \<Omega>  = \<mu> \<Omega>" 
  proof - 
     have  "sigma_algebra \<Omega> (Pow \<Omega>)"by (simp add: sigma_algebra_Pow) 
     moreover have "positive (Pow \<Omega>) \<mu>" unfolding positive_def using Pr_def by simp 
     moreover have "countably_additive (Pow \<Omega>) \<mu>" using sigma_sum by simp
     ultimately show ?thesis using emeasure_measure_of_sigma by auto
  qed
  ultimately show "emeasure ds_measure (space ds_measure) = 1" by auto
qed

(*<*)
end
(*>*)

