(*<*)
theory newDefinitions
  imports Main "HOL.Rat" "HOL-Library.LaTeXsugar" "HOL-Probability.Probability"  base 
begin
(*>*)

notation
   card (\<open>| _ |\<close>)

(* Ref Isar S. 277 *)
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


text \<open>mods gibt bezüglich einer partiellen Position P, die Menge aller vollständigen, kohärenten
Positionen an, in welchen P enthalten ist.
\#Info mods P sind alle Modelle der Debatte, in welchen die Literale von P enthalten sind.\<close>
definition mods :: "position \<Rightarrow> ds \<Rightarrow> ccPosition set" where
"mods P ds = {V :: ccPosition . P \<subseteq> Rep_ccPosition V \<and> V \<Turnstile> ds}"

text \<open>Der Grundraum ist die Menge aller vollständig, konsistenten Positionen\<close>
type_alias \<Omega> = "ccPosition"
definition \<Omega> where "\<Omega> = (UNIV :: \<Omega> set)"

text \<open>Die Positionen sind endlich\<close>
lemma finite_positions:
  shows "finite (UNIV :: position)"
proof -
  have "((UNIV :: literal set) = range Pos \<union> range Neg)"
    by (metis literal.exhaust UNIV_eq_I Un_iff rangeI)
  thus ?thesis
    using finsen by (metis finite_Un finite_imageI) 
qed

text \<open>Der Grundraum ist endlich => Wir befinden uns im diskreten Fall\<close>
lemma \<Omega>_fin: "finite \<Omega>"
  using finite_positions \<Omega>_def
  by (metis (full_types) Finite_Set.finite_set Rep_ccPosition_inverse UNIV_I
      ex_new_if_finite finite_imageI image_eqI)


text \<open>Der Träger von Pr bzw. f ist definiert als\<close>
definition \<Omega>\<^sub>T where "\<Omega>\<^sub>T ds = {p :: \<Omega> . p \<Turnstile> ds}"

lemma \<Omega>\<^sub>T_fin: "finite (\<Omega>\<^sub>T ds)" using \<Omega>_fin 
  using \<Omega>_def rev_finite_subset by auto

text \<open>Wir definieren die Wahrscheinlichkeitsfunkion / Dichte als Gleichverteilung.
Dabei werden alle nicht kohärenten Positionen nicht betrachtet. \<close>
definition f :: " \<Omega> \<Rightarrow> ds \<Rightarrow> ennreal"
  where "f P ds = (if (P \<Turnstile> ds) then  1 / |\<Omega>\<^sub>T ds| else 0)"

text \<open>Damit ist Pr ganz kanonisch das diskrete Wahrscheinlichkeitsmaß\<close>
definition Pr :: "\<Omega> set \<Rightarrow> ds  \<Rightarrow> ennreal"
  where "Pr Ps ds= (\<Sum> p \<in> Ps. f p ds)"


text \<open>Der Trager ist die Menge aller Modelle von ds\<close>
lemma "\<Omega>\<^sub>T ds = {p :: \<Omega> . f p ds > 0}" using mods_def \<Omega>\<^sub>T_def f_def 
proof -
  have "\<forall>p . f p ds > 0 \<longleftrightarrow> p \<Turnstile> ds" using \<Omega>\<^sub>T_def f_def \<Omega>_fin 
    by (metis (mono_tags, lifting) \<Omega>_def card_gt_0_iff empty_iff
        ennreal_less_zero_iff ennreal_of_nat_eq_real_of_nat finite_subset gr_zeroI
        mem_Collect_eq of_nat_0_eq_iff rel_simps(70) subset_UNIV
        zero_less_divide_1_iff)
  thus ?thesis using \<Omega>\<^sub>T_def by simp
qed


locale prob_DoJ = 
  fixes ds :: "ds"
  assumes sat: "satisfiable ds"

context prob_DoJ
begin

abbreviation \<mu> where "\<mu> p \<equiv> Pr p ds"

definition ds_measure :: "\<Omega> measure" where
  "ds_measure =  Abs_measure (\<Omega>, Pow \<Omega>, \<mu>)"    

(* Elemente außerhalb des Sigma-Raums sind null.*)
lemma compl_0:
  shows "(\<forall>a \<in> -(Pow \<Omega>) . \<mu> a = 0)"
proof 
  fix a :: "\<Omega> set"
  assume "a \<in> -(Pow (\<Omega>))"
  hence "\<forall>p \<in> a . \<not>(p \<Turnstile> ds)" using coherent_def by (simp add: \<Omega>_def)
  hence "\<forall>p \<in> a .  f p ds = 0" using f_def by simp 
  thus "\<mu> a = 0" using Pr_def by simp
qed


(* Unsere Definition ist tatsächlich ein measure-soace *)
lemma mes_space: 
  shows "measure_space \<Omega> (Pow \<Omega>) \<mu>"
proof (unfold measure_space_def, intro conjI)
  show "sigma_algebra \<Omega> (Pow \<Omega>)"
    by (simp add: sigma_algebra_Pow) 
next
  show "positive (Pow \<Omega>) \<mu>" unfolding positive_def using Pr_def by simp 
next 
  show "countably_additive (Pow \<Omega>) \<mu>" 
  proof (unfold countably_additive_def, intro allI impI)
    fix A :: "nat \<Rightarrow> \<Omega> set"
    assume range_sub:  "range A \<subseteq> Pow \<Omega>"
    assume disjoint:   "disjoint_family A"
    assume union_in:   "\<Union> (range A) \<in> Pow \<Omega>"
    show "(\<Sum>i . \<mu> (A i)) = (\<mu> (\<Union> (range A)))" sorry
  qed
qed


(* Es gibt einen Isomorphismus zwischen unserem Raum und dem allgemeinen mes_space *)
lemma inv: 
  "Rep_measure (Abs_measure (\<Omega>, Pow \<Omega>, \<mu>)) = (\<Omega>, Pow \<Omega>, \<mu>)"
  using Abs_measure_inverse mes_space compl_0 
  by (smt (verit) case_prod_conv mem_Collect_eq)

lemma \<mu>_sum: "\<mu> \<Omega> = 1"
proof -
  let ?x = "(\<Omega>\<^sub>T ds)"
    have t_sum: "\<mu> ?x = 1" 
    proof -
      have nn: "card ?x > 0" using sat \<Omega>\<^sub>T_def unfolding satisfiable_def 
        using \<Omega>\<^sub>T_fin card_gt_0_iff by blast
      have "\<forall>p \<in> ?x . p \<Turnstile> ds" using \<Omega>\<^sub>T_def by simp
      hence "\<forall>p \<in> ?x . f p ds = (1 / real | ?x | )" using f_def by presburger
      hence "\<mu> ?x = (\<Sum>p \<in> ?x . (1 / card ?x ))" unfolding Pr_def
        by (smt (verit, best) nn of_nat_0_less_iff sum.cong sum_ennreal
            zero_less_divide_1_iff)
      also have "... = (1 / card ?x) * (\<Sum>p \<in> ?x . 1)" by simp
      also have "... = (1 / card ?x  ) * card ?x " by simp
      finally show ?thesis using nn by auto
     qed

    have "\<forall>x \<in> (\<Omega> - \<Omega>\<^sub>T ds) . \<not>(x \<Turnstile> ds)" using \<Omega>\<^sub>T_def by simp
    hence nt_0: "\<forall>x \<in> (\<Omega> - \<Omega>\<^sub>T ds) . f x ds = 0" using f_def by simp

    have "\<mu> \<Omega> = (\<Sum>i \<in> (\<Omega> - ?x). f i ds) + (\<Sum>y \<in> ?x . f y ds)" using \<Omega>_fin \<Omega>\<^sub>T_fin
      by (metis Pr_def \<Omega>_def subset_UNIV sum.subset_diff)
    also have "... = (\<Sum>y \<in> ?x . f y ds)" using nt_0 by simp
    also have  "... = \<mu> ?x" using Pr_def by simp
    finally show ?thesis using t_sum by simp
  qed


(* Hier die Brücke zu HOL-Probability. Damit ist unsere Definition ein prob_space *)
interpretation model_space: prob_space "ds_measure"

proof (intro prob_spaceI)
  have "\<mu> \<Omega> = 1" using \<mu>_sum by simp
  thus "emeasure ds_measure (space ds_measure) = 1" using emeasure_def space_def inv 
    by (metis ds_measure_def fst_conv snd_conv)
qed

end
end

