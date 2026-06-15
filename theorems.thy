(*<*)
theory theorems
  imports Main "HOL.Rat" definitions "HOL-Library.LaTeXsugar"
begin
(*>*)

section "Beobachtungen"
text \<open>Es folgen einige kleine Beobachtungen\<close>

text \<open>Dadruch, dass das Universum der Sätze endlich ist, ist jede Position und die Menge der Modelle endlich.\<close>


(*<*)
lemma finite_positions:
  shows "finite (UNIV :: position)"
proof -
  have "((UNIV :: literal set) = range Pos \<union> range Neg)"
    by (metis literal.exhaust UNIV_eq_I Un_iff rangeI)
  thus ?thesis
    using finsen by (metis finite_Un finite_imageI) 
qed
(*>*)

(*<*)
lemma fin_mods:
"finite (mods P ds)"
proof -
  show ?thesis
    using finite_positions
    using Finite_Set.finite_set infinite_super subset_UNIV
   by blast
qed
(*>*)

text \<open>(informel) Eine Position kann in die Debatte übertragen werden, indem die Literale der Position
als Konklusionen neu hinzugefügter Argumente dargestellt werden\<close>
lemma shift_position_into_debate:
  shows "mods P ds = mods {} (ds \<union> ( \<Union>p \<in> P . {({}, p)}))"
(*<*)
proof (intro antisym)
 show "mods P ds \<subseteq> mods {} (ds \<union> (\<Union>p \<in> P. {({}, p)}))" 
  proof 
    fix x 
    assume "x \<in> mods P ds"
    hence "\<forall>p \<in> P.  models_arg x ({}, p) \<longleftrightarrow> p \<in> x" by auto
    thus "x \<in> mods {} (ds \<union> (\<Union>p \<in> P. {({}, p)}))" 
      using UN_E \<open>x \<in> mods P ds\<close> coherent_def mods_def by auto
  qed
next
  show "mods {} (ds \<union> (\<Union>p \<in> P. {({}, p)})) \<subseteq> mods P ds" 
  proof 
    fix x
    assume "x \<in> mods {} (ds \<union> (\<Union>p \<in> P. {({}, p)}))"
    hence "\<forall>p \<in> P.  models_arg x ({}, p) \<longleftrightarrow> p \<in> x" by auto
    thus "x \<in> mods P ds" 
      using \<open>x \<in> mods {} (ds \<union> (\<Union>p\<in>P. {({}, p)}))\<close> coherent_def mk_disjoint_insert mods_def
      by fastforce
  qed
qed

(*>*)

text \<open>Die Modelle einer erweiterten Debatte sind eine Teilmenge der Modelle der initialen Debatte.\<close>
lemma subset_of_extended:
  shows "mods P (ds1 \<union> ds2) \<subseteq> mods P ds1"
(*<*)
proof 
  fix x
  assume "x \<in> mods P (ds1 \<union> ds2)"
  thus "x \<in> mods P ds1" 
    using mods_def coherent_def consistent_def complete_def by simp
qed
(*>*)

text \<open>Es wäre eine echte Teilmenge, wenn es ein Modell gibt, dass die zweite Debatte nicht erfüllt\<close>
lemma true_subset:
  assumes "\<exists>x \<in> mods P ds1 . \<not>(x \<Turnstile> ds2)"
  shows "mods P (ds1 \<union> ds2) \<subset> mods P ds1"
(*<*)
proof -
  have "mods P (ds1 \<union> ds2) \<subseteq> mods P ds1" using subset_of_extended by auto
  moreover have "\<exists>x \<in> mods P ds1 . x \<notin> mods P (ds1 \<union> ds2)" 
    using assms
    by (metis (lifting) Un_commute subset_of_extended in_mono mem_Collect_eq
        mods_def) 
  ultimately show ?thesis by auto
qed
(*>*)

text \<open>Die Gegenrichtung gilt, wenn alle Modelle der initialen Debatte bereits die zweite Debatte erfüllen.\<close>
lemma fullfills_ds_subset:
  assumes "\<forall>x \<in> mods P ds. x \<Turnstile> A"
  shows "mods P ds \<subseteq> mods P (ds \<union> A)"
(*<*)
proof
  fix x 
  assume "x \<in> mods P ds"
  thus "x \<in>  mods P (ds \<union> A)" using mods_def coherent_def 
complete_def consistent_def assms by fastforce
qed
(*>*)

text \<open>Das ist z.B. der Fall, wenn die neue Konklusion in der Position enthalten ist.\<close>
lemma subset_conclusions:
  shows "mods {l} ds \<subseteq> mods {l} (ds \<union> {(ps, l)})"
(*<*)
proof - 
  have "\<forall>x \<in> mods {l} ds . x \<Turnstile> {(ps, l)}" 
  proof 
    fix x 
    assume i:"x \<in> mods {l} ds"
    hence "l \<in> x" using mods_def by simp
    hence "\<forall>a \<in> {(ps, l)} . models_arg x a" by simp
    thus  "x \<Turnstile> {(ps, l)}"  using i coherent_def 
      complete_def consistent_def mods_def by auto
  qed
  thus ?thesis using fullfills_ds_subset by blast
qed
(*>*)

text \<open>Oder es das Komplement einer Prämisse in der Position gibt\<close>
lemma subset_premisses:
  assumes "\<exists>x \<in> ps . compl_lit x \<in> P"
  shows "mods P ds \<subseteq> mods P (ds \<union> {(ps, c)})"
(*<*)
proof -
  have "\<forall>x \<in> mods P ds . x \<Turnstile> {(ps, c)}" 
  proof
    fix x 
    assume i:"x \<in> mods P ds"
    hence "\<forall>l \<in> P . l \<in> x" using mods_def by auto
    then obtain l where "l \<in> ps" and "compl_lit l \<in> x" using assms by blast
    hence "\<not>(ps \<subseteq> x)" 
    proof -
      have "l \<notin> x" using \<open>compl_lit l \<in> x\<close> consistent_def
        by (metis (lifting) coherent_def compl_lit_def  i literal.exhaust_sel
            mem_Collect_eq mods_def) 
      thus ?thesis using \<open>l \<in> ps\<close> by blast
    qed
    hence "models_arg x (ps, c)" by simp
    thus  "x \<Turnstile> {(ps, c)}" 
      using coherent_def  complete_def consistent_def i mods_def
    by fastforce
  qed
  thus ?thesis using fullfills_ds_subset by blast
qed
(*>*)

text \<open>Die Vereinigung alle Modelle von komplementären Sätzen ist die Menge aller Möglichen Modelle.\<close>
lemma compl_sen_union:
  "mods {Pos s} ds \<union> mods {Neg s} ds = mods {} ds"
(*<*)
proof 
  show "mods {Pos s} ds \<union> mods {Neg s} ds \<subseteq> mods {} ds"
    by (simp add: Collect_mono mods_def)
next 
  show "mods {} ds \<subseteq> mods {Pos s} ds \<union> mods {Neg s} ds"
  proof 
    fix V 
    assume "V \<in> mods {} ds"

    have "V \<in> mods {Pos s} ds \<or> V \<in> mods {Neg s} ds"
      by (metis (lifting) \<open>V \<in> mods {} ds\<close> coherent_def
          mods_def  complete_def insert_subset
          literal.exhaust_sel mem_Collect_eq)
    thus "V \<in> mods {Pos s} ds \<union> mods {Neg s} ds" 
      by auto
  qed
qed
(*>*)


text \<open>Die Modelle komplementären Sätzen überschneiden sich nicht\<close>
lemma compl_sen_inter:
"mods {Pos s} ds \<inter> mods {Neg s} ds = {}"
(*<*)
proof
  show "{} \<subseteq> mods {Pos s} ds \<inter> mods {Neg s} ds"
    by simp
next
  show "mods {Pos s} ds \<inter> mods {Neg s} ds \<subseteq> {}"
  proof
  fix V
  assume "V \<in> mods {Pos s} ds \<inter> mods {Neg s} ds"
  hence hpos: "V \<in> mods {Pos s} ds" 
    and hneg: "V \<in> mods {Neg s} ds" by auto
  have 1: "V \<notin> mods {Neg s} ds" 
    using hpos coherent_def mods_def consistent_def by auto
  thus "V \<in> {}" using hneg by contradiction
    qed
  qed
(*>*)

theorem complement_eq_1:
  assumes "\<sigma> {} ds > 0"
  shows "doj {Pos s} ds + doj {Neg s} ds = 1"
(*<*)
proof - 
  have "1  = doj {} ds"  by (simp add: assms doj_cond_def doj_def)
  also have "... = (((rat_of_nat(\<sigma> {} ds))) / (rat_of_nat (\<sigma> {} ds)))" 
    using doj_cond_def doj_def assms calculation by simp
  also have "... = (((rat_of_nat(\<sigma> {Pos s} ds + \<sigma> {Neg s} ds))) / (rat_of_nat (\<sigma> {} ds)))"
    using compl_sen_inter compl_sen_union by (metis \<sigma>_def card_Un_disjoint fin_mods) 
  also have "... = doj {Pos s} ds + doj {Neg s} ds" 
    by (metis add_divide_distrib doj_cond_def doj_def insert_is_Un of_nat_add)
  finally show ?thesis by simp
qed
(*>*)
(*<*)
end
end
(*>*)
