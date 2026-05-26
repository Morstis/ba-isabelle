(*<*)

theory DOJ
  imports Main HOL.Rat "HOL-Library.LaTeXsugar" 
begin

(* Im folgenden werden Sätz per Konvention immer mit x, y, s dargestellt *)
typedecl sentence


(* Im folgenden werden Literale per Konvention immer mit l, k dargestellt.
Eine Premisse mit p, eine Menge an Premissen mit ps. Eine Konklusion mit c*)
datatype literal = Pos (sen:sentence) | Neg (sen:sentence)


(***** Helper items *****)
lemma witness_nonempty_set: "x \<in> s \<and> finite s \<Longrightarrow> card s \<ge> 1"
  using Suc_le_eq card_gt_0_iff by auto

notation (latex output)
   Fract (\<open>\<^bsup> _ \<^esup> \<^latex>\<open>\hspace{-2ex}\Big/\hspace{-2ex}\<close> \<^bsub> _ \<^esub>\<close>)

notation
   card (\<open>| _ |\<close>)

(*>*)

section \<open>Definitions\<close>

text \<open>Sentences are atomic, have no structure. This justifies 
declaring an uninterpreted type.\<close>


text \<open>A position is a set of literals. Here there are no
  restrictions like in the original publication.\<close>

type_synonym position = "literal set"

text \<open>The following define fundamental properties of positions.\<close>

definition is_coherent :: "position \<Rightarrow> bool"
  where "is_coherent p = (\<forall>s . \<not>(Pos s \<in> p \<and> Neg s \<in> p))"

definition is_on :: "sentence set \<Rightarrow> position \<Rightarrow> bool"
  where "is_on S p = (\<forall>l \<in> p. sen l \<in> S)"

definition is_complete :: "sentence set \<Rightarrow> position \<Rightarrow> bool"
  where "is_complete S p = (is_coherent p \<and> is_on S p \<and> (\<forall>s \<in> S. Pos s \<in> p \<or> Neg s \<in> p))"

text \<open>An argument is a tuple \<open>(ps,c)\<close> consists of premises 
  \<open>ps :: literal set\<close> and a conclusion \<open>c :: literal\<close>.\<close>

type_synonym argument = "literal set \<times> literal"

definition to_fact :: "literal \<Rightarrow> argument"
  where "to_fact l = ({}, l)"

text \<open>The function \<open>to_fact :: literal \<Rightarrow> argument\<close> turns a single literal
  into an argument without premises: @{thm to_fact_def[no_vars]}.

  A debate is a set of arguments. Interpretations are modelled as \<open>sentence set\<close>s.\<close>

type_synonym debate = "argument set"

type_synonym interpr = "sentence set"

text \<open>With these notions,
  we can define when interprations are models. We write \<open>i \<Turnstile> d\<close> to indicate
  that \<open>i\<close> is a model for debate \<open>d\<close>. Similar notions are defined for
  arguments and literals.\<close>

fun models_literal :: "sentence set \<Rightarrow> literal \<Rightarrow> bool"  (infix "\<Turnstile>\<^sub>l" 65)
  where 
    "i \<Turnstile>\<^sub>l Pos s = (s \<in> i)"
  | "i \<Turnstile>\<^sub>l Neg s = (s \<notin> i)"

fun models_argument :: "sentence set \<Rightarrow> argument \<Rightarrow> bool"  (infix "\<Turnstile>\<^sub>a" 65)
  where "i \<Turnstile>\<^sub>a (ps,c) = ((\<forall>l \<in> ps. i \<Turnstile>\<^sub>l l) \<longrightarrow> i \<Turnstile>\<^sub>l c)"

definition models_debate :: "sentence set \<Rightarrow> debate \<Rightarrow> bool"  (infix "\<Turnstile>" 65)
  where "i \<Turnstile> d = (\<forall> a \<in> d. i \<Turnstile>\<^sub>a a)"

text \<open>A debate is \<open>S\<close>-satisfiable if it has a model in \<open>S\<close>.\<close>

definition satisfiable :: "sentence set \<Rightarrow> debate \<Rightarrow> bool"
  where "satisfiable S d = (\<exists>i. i \<subseteq> S \<and> (i \<Turnstile> d))"

text \<open>With \<open>sents\<close>, one can retrieve the setentencs which are mentioned in a
  debate. This is positive or negative, premise or conclusion.\<close>

definition sents :: "debate \<Rightarrow> sentence set"
  where "sents d = \<Union> ((\<lambda>(ps, c). (sen`ps) \<union> {sen c})`d)"

text \<open>Like in the publications: \<open>mods\<close> denotes the number of models of a debate:\<close>

definition mods :: "sentence set \<Rightarrow> debate \<Rightarrow> nat"
  where "mods S debate = | { i . i \<subseteq> S \<and> (i \<Turnstile> debate)} |"

text \<open>The degree of justification is defined as the quotient between 
  two cardinalities.\<close>

definition doj :: "sentence set \<Rightarrow> debate \<Rightarrow> position \<Rightarrow> rat"
  where "doj S d p = Fract (int (mods S (d \<union> (to_fact ` p)))) (int (mods S d))"

lemma empty:
  assumes sat: "satisfiable S ds"
  assumes fin: "finite S"
  shows "doj S ds {} = 1"
proof -
  have gt0: "mods S ds > 0" using sat
    using fin infinite_super mods_def satisfiable_def
    by fastforce

  have "image to_fact {} = {}" by simp
  hence "mods S (ds \<union> (image to_fact {})) = mods S ds" by simp
  hence "int (mods S (ds \<union> (image to_fact {}))) = int (mods S ds)" by simp 
  thus ?thesis using sat fin gt0 unfolding doj_def
    by (metis Fract_less_one_iff Un_empty_right \<open>to_fact ` {} = {}\<close>
        linorder_neq_iff of_nat_0_less_iff
        one_less_Fract_iff) 
qed

text \<open>which is a quotient of natural numbers @{thm doj_def[no_vars]}.
  It is formally also defined for debates that do not have models.\<close>

subsection \<open>Bounds\<close>

text \<open>First some (obvious) boundaries of degrees of justifcation. Upper bound is the value 1.
  The upper bound theorem requires that the debate is satisfiable. I assume it is non-optional
  perhaps due to the way Isabelle defines divison by zero.\<close>

theorem doj_at_most_1:
  assumes sat: "satisfiable S d"
  assumes fin: "finite S"
  shows "doj S d p \<le> 1"
(*<*)
proof -  
  have gt1: "mods S d \<ge> 1" using sat fin  
  proof -
    from sat satisfiable_def obtain i where "i \<Turnstile> d \<and> i \<subseteq> S" by blast
    hence "i \<in> { i . i \<subseteq> S \<and> (i \<Turnstile> d)}" by auto
    hence "card { i . i \<subseteq> S \<and> (i \<Turnstile> d)} \<ge> 1" using fin witness_nonempty_set
      by (smt (verit) Collect_mono_iff finite_Collect_subsets finite_subset)
    thus ?thesis using mods_def by presburger
  qed

  have "{ i . i \<subseteq> S \<and> i \<Turnstile> (d \<union> (to_fact ` p))} \<subseteq> { i . i \<subseteq> S \<and> i \<Turnstile> d }"
    using models_debate_def by force

  hence "(mods S (d \<union> (to_fact ` p))) \<le> (mods S d)"
    by (simp add: card_mono fin mods_def)

  thus ?thesis
    using Fract_le_one_iff doj_def gt1 by auto
qed  
(*>*)

text \<open>And lower bound is the value 0. Here satisfiability is not mandatory.\<close>

lemma doj_at_least_0:
  assumes fin: "finite S"
  shows "doj S d p \<ge> 0"
(*<*)
  by (metis doj_def dual_order.order_iff_strict int_eq_iff rat_number_collapse(6) zero_le_Fract_iff)
(*>*)

subsection \<open>Adding irrelevant new sentences\<close>

(*<*)
lemma sents_union: "sents (a \<union> b) = (sents a) \<union> (sents b)"
  by (simp add: sents_def)


lemma adding_irrelevant3:
  assumes "finite S"
  assumes no_a_in_d: "a \<notin> sents d"
  shows "(i\<union>{a}) \<Turnstile> d \<longleftrightarrow> i \<Turnstile> d"
proof -
  {
    fix i ps c
    assume noa: "a \<notin> sents {(ps,c)}"
    have a1: "c \<noteq> Pos a \<and> c \<noteq> Neg a" using noa sents_def by fastforce
    have a2: "\<forall>p \<in> ps. p \<noteq> Pos a \<and> c \<noteq> Neg a" using noa sents_def mk_disjoint_insert by fastforce 
    hence a3: "\<forall>p \<in> ps. i \<Turnstile>\<^sub>l p \<longrightarrow> (i\<union>{a}) \<Turnstile>\<^sub>l p"
      using mk_disjoint_insert models_literal.elims(3) noa sents_def by fastforce 
    from a2 have a4: "\<forall>p \<in> ps. (i\<union>{a}) \<Turnstile>\<^sub>l p \<longrightarrow> i \<Turnstile>\<^sub>l p"
      by (smt (z3) UnI2 Un_commute Un_empty_right Un_insert_right insertE literal.inject(1) literal.inject(2) literal.simps(4) models_literal.elims(1)) 

    have "i \<Turnstile>\<^sub>a (ps,c) = ((\<forall> p \<in> ps. i \<Turnstile>\<^sub>l p) \<longrightarrow> i \<Turnstile>\<^sub>l c)"
      using models_argument.simps by blast
    also have "... = ((\<forall> p \<in> ps. i \<Turnstile>\<^sub>l p) \<longrightarrow> (i\<union>{a}) \<Turnstile>\<^sub>l c)" using a1
      by (smt (verit) Un_insert_right boolean_algebra.disj_zero_right insertE literal.inject(1) literal.inject(2) literal.simps(4) models_literal.elims(2) models_literal.elims(3) subsetD sup_ge1) 
    also have "... = ((\<forall> p \<in> ps. (i\<union>{a}) \<Turnstile>\<^sub>l p) \<longrightarrow> (i\<union>{a}) \<Turnstile>\<^sub>l c)"
      using a3 a4 by blast
    also have "... = (i\<union>{a}) \<Turnstile>\<^sub>a (ps,c)"
      using models_argument.simps by blast 
    ultimately have "i \<Turnstile>\<^sub>a (ps,c) = (i\<union>{a}) \<Turnstile>\<^sub>a (ps,c)" by blast 
  }
  hence "\<forall>i l. a \<notin> sents {l} \<longrightarrow> i \<Turnstile>\<^sub>a l = (i\<union>{a}) \<Turnstile>\<^sub>a l"
    by (metis models_argument.elims(2)) 
  hence "\<forall>i l. l \<in> d \<longrightarrow> i \<Turnstile>\<^sub>a l = (i\<union>{a}) \<Turnstile>\<^sub>a l" using no_a_in_d
    by (smt (verit, del_insts) Sup_empty Sup_insert Un_iff image_empty image_insert insert_absorb insert_not_empty sents_def)

  thus "((i\<union>{a}) \<Turnstile> d \<longleftrightarrow> i \<Turnstile> d)"
    by (meson models_debate_def) 
qed


lemma adding_irrelevant2:
  assumes fin: "finite S"
  assumes no_a_in_S: "a \<notin> S"
  assumes no_a_in_d: "sents d \<subseteq> S"
  shows "mods (S\<union>{a}) d = 2 * (mods S d)"
proof -
  have a1: "{ i . i \<subseteq> S \<union> {a} \<and> i \<Turnstile> d } = 
     ({ i . i \<subseteq> S \<union> {a} \<and> a\<in>i \<and> i \<Turnstile> d } \<union> { i . i \<subseteq> S \<union> {a} \<and> a\<notin>i \<and> i \<Turnstile> d })" 
    by (rule subset_antisym) auto

  (*have a2: "{ i . i \<subseteq> S \<union> {a} \<and> a\<notin>i \<and> i \<Turnstile> d } = { i . i \<subseteq> S \<and> i \<Turnstile> d }" sorry*)

  have fin1: "finite { i . i \<subseteq> S \<union> {a} \<and> a\<in>i \<and> i \<Turnstile> d }" using fin by simp 
  have fin2: "finite { i . i \<subseteq> S \<union> {a} \<and> a\<notin>i \<and> i \<Turnstile> d }" using fin by simp

  have "mods (S\<union>{a}) d = card { i . i \<subseteq> S \<union> {a} \<and> i \<Turnstile> d }" using fin mods_def by blast
  also have "... = card ({ i . i \<subseteq> S \<union> {a} \<and> a\<in>i \<and> i \<Turnstile> d } \<union> { i . i \<subseteq> S \<union> {a} \<and> a\<notin>i \<and> i \<Turnstile> d })" 
    using a1 by argo
  also have "... = card ({ i . i \<subseteq> S \<union> {a} \<and> a\<in>i \<and> i \<Turnstile> d }) + card({ i . i \<subseteq> S \<union> {a} \<and> a\<notin>i \<and> i \<Turnstile> d })" 
    using fin1 fin2
    by (simp add: card_Un_disjoint subset_antisym subset_iff)
  also have "... = card ({ i . i \<subseteq> S \<union> {a} \<and> a\<in>i \<and> i \<Turnstile> d }) + card({ i . i \<subseteq> S \<and> i \<Turnstile> d })"
    by (metis Un_commute insert_is_Un no_a_in_S subsetD subset_insert) 
  also have "... = card ({ insert a i | i . i \<subseteq> S \<and> insert a i \<Turnstile> d }) + card({ i . i \<subseteq> S \<and> i \<Turnstile> d })" 
  proof -
    have "{ i . i \<subseteq> S \<union> {a} \<and> a\<in>i \<and> i \<Turnstile> d } = { i \<union> {a} | i . i \<subseteq> S \<and> (i\<union>{a}) \<Turnstile> d }"
      by (smt (z3) Collect_cong Un_iff Un_mono insert_subset mk_disjoint_insert 
                   no_a_in_S subset_UnE subset_singleton_iff)
    thus ?thesis by force 
  qed
  also have "... = card ({ i . i \<subseteq> S \<and> (insert a i) \<Turnstile> d }) + card({ i . i \<subseteq> S \<and> i \<Turnstile> d })"
  proof -
    have a1: "inj_on (insert a) {i. i \<subseteq> S \<and> insert a i \<Turnstile> d}"
      using inj_on_def no_a_in_S by fastforce 
    have a2: "insert a ` {i. i \<subseteq> S \<and> insert a i \<Turnstile> d} = {insert a i | i. i \<subseteq> S \<and> insert a i \<Turnstile> d}"
      by blast
    have "bij_betw (insert a) { i . i \<subseteq> S \<and> (insert a i) \<Turnstile> d } { insert a i | i . i \<subseteq> S \<and> (insert a i) \<Turnstile> d }"
      using bij_betw_def a1 a2 by blast
    hence a3: "card ({ i . i \<subseteq> S \<and> (insert a i) \<Turnstile> d }) = card ({ insert a i | i . i \<subseteq> S \<and> (insert a i) \<Turnstile> d })"
      using bij_betw_same_card by blast 
    thus ?thesis by (simp add: bij_betw_same_card)
  qed
  also have "... = card ({ i . i \<subseteq> S \<and> i \<Turnstile> d }) + card({ i . i \<subseteq> S \<and> i \<Turnstile> d })" using adding_irrelevant3
    by (metis Un_insert_right fin no_a_in_S no_a_in_d subset_eq sup_bot.right_neutral)
  ultimately show "mods (S \<union> {a}) d = 2 * (mods S d)"
    using mods_def by simp 
qed
(*>*)

text \<open>The upcoming theorems are consequences that use the following lemmata:
  \<^enum> @{thm adding_irrelevant2[no_vars]}
  \<^enum> @{thm adding_irrelevant3[no_vars]}

The theorem \<open>adding_irrelevant\<close> captures that adding a fresh sentence to \<open>S\<close> does not
change a thing.\<close>

theorem adding_irrelevant:
  assumes fin: "finite S"
  assumes no_a_in_S: "a \<notin> S"
  assumes d_in_S: "sents d \<subseteq> S"
  assumes p_in_S: "sents (to_fact ` p) \<subseteq> S"
  shows "doj S d p = doj (S \<union> {a}) d p"
(*<*)
proof -

  have "sents (d \<union> (to_fact ` p)) \<subseteq> S" using p_in_S d_in_S sents_union
    by blast

  hence rw: "2 * (mods S (d \<union> (to_fact ` p))) = mods (S\<union>{a}) (d \<union> (to_fact ` p))"
    using adding_irrelevant2 fin no_a_in_S d_in_S
    by presburger
 
  have "doj S d p =  Fract (int (mods S (d \<union> (to_fact ` p)))) (int (mods S d))"
    by (simp add: doj_def)
  also have "... = Fract (int (2 * (mods S (d \<union> (to_fact ` p))))) (int (2 * (mods S d)))"
    by (simp add: mult_rat_cancel)   
  also have "...  = Fract (int (2 * (mods S (d \<union> (to_fact ` p))))) (int (mods (S\<union>{a}) d))"
    using adding_irrelevant2 fin no_a_in_S d_in_S by presburger
  also have "...  = Fract (int (mods (S\<union>{a}) (d \<union> (to_fact ` p)))) (int (mods (S\<union>{a}) d))"
    using adding_irrelevant2 fin no_a_in_S rw by argo  
  ultimately show "doj S d p = doj (S \<union> {a}) d p"
    by (simp add: doj_def)    
qed
(*>*)


text \<open>Adding a tautological argument in which the conclusion is contained in
the premises, does never change the degree of justification.\<close>

theorem adding_tautologies:
  assumes fin: "finite S"
  assumes taut: "l \<in> ps"
  shows "doj S d p = doj S (d \<union> {(ps, l)}) p"
(*<*)
proof -

  have "\<forall>d. {i. i \<subseteq> S \<and> i \<Turnstile> d} = {i. i \<subseteq> S \<and> i \<Turnstile> (d \<union> {(ps, l)})}"
    using fin taut models_debate_def by auto
  thus ?thesis using doj_def
    by (simp add: mods_def)
qed
(*>*)

subsection \<open>Monotonicity\<close>

(*<*)
lemma sat_is_pos_mod:
  assumes sat: "satisfiable S d"
  assumes fin: "finite S"
  shows "mods S d \<ge> 1"
proof -
  obtain i where "i \<Turnstile> d \<and> i \<subseteq> S" using sat satisfiable_def by auto 
  hence "i \<in> { i . i \<subseteq> S \<and> (i \<Turnstile> d) }" by blast
  thus ?thesis
    using Pow_def fin mods_def by fastforce 
qed

lemma fracts:
  "0 < b1 \<and> b1 \<le> b2 \<and> 0 \<le> a \<Longrightarrow> Fract a b1 \<ge> Fract a b2" 
proof -
  assume a: "0 < b1 \<and> b1 \<le> b2 \<and> 0 \<le> a"
  hence "b1 \<noteq> 0 \<and> b2 \<noteq> 0" by simp
  hence q:"(a * b1) * (b2 * b1) \<le> (a * b2) * (b2 * b1) = (Fract a b2 \<le> Fract a b1)"
    using le_rat by auto

  from a have nonneg: "(b2 * b1) > 0"
    by simp 

  from a have "b1 \<le> b2" by simp
  hence "a*b1 \<le> a*b2" by (simp add: a mult_left_mono) 
  hence "(a*b1) * (b2*b1) \<le> (a*b2)*(b2*b1)" using a
    by (simp add: mult_right_mono) 

  with q show ?thesis by simp
qed

lemma strict_fracts:
  "0 < b1 \<and> b1 < b2 \<and> 0 < a \<Longrightarrow> Fract a b1 > Fract a b2" 
proof -
  assume a: "0 < b1 \<and> b1 < b2 \<and> 0 < a"
  hence "b1 \<noteq> 0 \<and> b2 \<noteq> 0" by simp
  hence q:"(a * b1) * (b2 * b1) < (a * b2) * (b2 * b1) = (Fract a b2 < Fract a b1)"
    using le_rat by auto

  from a have nonneg: "(b2 * b1) > 0"
    by simp 

  from a have "b1 \<le> b2" by simp
  hence "a*b1 \<le> a*b2" by (simp add: a mult_left_mono) 
  hence "(a*b1) * (b2*b1) \<le> (a*b2)*(b2*b1)" using a
    by (simp add: mult_right_mono) 

  with q a show ?thesis by auto 
qed
(*>*)

text \<open>There are two monotonicity results covered here. The frst is a weak monotoncity result:
If one adds an argument with \<open>l\<close> as conclusion the doj for \<open>l\<close> will not decrease.\<close>

theorem monotonicity:
  assumes fin: "finite S"
  assumes sat: "satisfiable S (d \<union> {(ps, l)})"
  shows "doj S d {l} \<le> doj S (d \<union> {(ps, l)}) {l}"
(*<*)
proof -
  have "\<forall>i . i \<Turnstile>\<^sub>l l \<longrightarrow> (i \<Turnstile> d \<longleftrightarrow> i \<Turnstile> (d \<union> {(ps, l)}))"
    by (simp add: models_debate_def)
  hence "{ i . i \<subseteq> S \<and> i \<Turnstile>\<^sub>l l \<and> i \<Turnstile> d } = { i . i \<subseteq> S \<and> i \<Turnstile>\<^sub>l l \<and> i \<Turnstile> (d \<union> {(ps, l)}) }"
    by blast

  have "{ i . i \<subseteq> S \<and> i \<Turnstile> (d \<union> (to_fact ` {l}) \<union> {(ps, l)}) } = { i . i \<subseteq> S \<and> i \<Turnstile> (d \<union> (to_fact ` {l})) }"
    using models_debate_def to_fact_def by auto
  hence nom: "mods S (d \<union> (to_fact ` {l}) \<union> {(ps, l)}) = mods S (d \<union> (to_fact ` {l}))"
    by (simp add: mods_def)

  have pos: "int (mods S (d \<union> {(ps, l)})) \<ge> 1" using sat sat_is_pos_mod fin
    by fastforce 

  have "{ i . i \<subseteq> S \<and> i \<Turnstile> (d \<union> {(ps, l)}) } \<subseteq> { i . i \<subseteq> S \<and> i \<Turnstile> d }"
    using models_debate_def to_fact_def by auto
  hence "mods S (d \<union> {(ps, l)}) \<le> mods S d"
    by (simp add: card_mono fin mods_def)
  hence denom: "int (mods S (d \<union> {(ps, l)})) \<le> int (mods S d)"
    by auto

  have pos2: "int (mods S (d \<union> {(ps, l)} \<union> {to_fact l})) \<ge> 0"
    by simp 

  have "doj S d {l} = Fract (int (mods S (d \<union> {to_fact l}))) (int (mods S d))"
    by (simp add: doj_def)
  also have "... = Fract (int (mods S (d \<union> {(ps, l)} \<union> {to_fact l}))) (int (mods S d))"
    using nom by (simp add: Un_commute)
  also have "... \<le> Fract (int (mods S (d \<union> {(ps, l)} \<union> {to_fact l}))) 
                           (int (mods S (d \<union> {(ps, l)})))" 
    using denom pos pos2 fracts by auto
  also have "... = doj S (d \<union> {(ps, l)}) {l}"
    by (simp add: doj_def)
  ultimately show "doj S d {l} \<le> doj S (d \<union> {(ps, l)}) {l}"
    by argo
qed



lemma ex_is_lt1:
  assumes fin: "finite S"
  assumes sat: "satisfiable S d"
  assumes lt1: "doj S d {l} < 1"
  shows "\<exists>i. i \<subseteq> S \<and> (i \<Turnstile> d) \<and> \<not>(i \<Turnstile>\<^sub>l l)"
proof -
  have gt0: "mods S d > 0" 
    using sat fin sat_is_pos_mod by fastforce
  from lt1 have "Fract (int (mods S (d \<union> (to_fact ` {l})))) (int (mods S d)) < 1"
    by (simp add: doj_def)
  hence card_lt: "(mods S (d \<union> (to_fact ` {l}))) < (mods S d)" using gt0
    by (simp add: Fract_less_one_iff) 

  have ex: "\<And> a b. finite a \<Longrightarrow> finite b \<Longrightarrow> 
         card a < card b \<Longrightarrow> a \<subseteq> b \<Longrightarrow> a \<subset> b"
    using subset_antisym by fastforce 

  have "{ i . i \<subseteq> S \<and> i \<Turnstile> (d \<union> (to_fact ` {l})) } \<subseteq> { i . i \<subseteq> S \<and> i \<Turnstile> d }"
    using models_debate_def to_fact_def by auto
  hence "{ i . i \<subseteq> S \<and> i \<Turnstile> (d \<union> (to_fact ` {l})) } \<subset> { i . i \<subseteq> S \<and> i \<Turnstile> d }" 
    using ex card_lt mods_def by fastforce 
  hence "\<exists>i. i \<in> { i . i \<subseteq> S \<and> i \<Turnstile> d } \<and> i \<notin> { i . i \<subseteq> S \<and> i \<Turnstile> (d \<union> (to_fact ` {l})) }"
    by blast
  hence "\<exists>i. i \<subseteq> S \<and> i \<Turnstile> d \<and> \<not>(i \<Turnstile> (d \<union> (to_fact ` {l})))"
    by blast
  thus "\<exists>i. i \<subseteq> S \<and> i \<Turnstile> d \<and> \<not>(i \<Turnstile>\<^sub>l l)" using to_fact_def
    using models_debate_def by auto 
qed

lemma ex_is_gt0:
  assumes fin: "finite S"
  assumes sat: "satisfiable S d"
  assumes gt: "doj S d {l} > 0"
  shows "\<exists>i. i \<subseteq> S \<and> (i \<Turnstile> d) \<and> (i \<Turnstile>\<^sub>l l)"
proof -
  have gt0: "mods S d > 0" 
    using sat fin sat_is_pos_mod by fastforce 
  from gt have "Fract (int (mods S (d \<union> (to_fact ` {l})))) (int (mods S d)) > 0"
    by (simp add: doj_def)
  hence card_lt: "(mods S (d \<union> (to_fact ` {l}))) > 0" 
    using gt0 gt zero_less_Fract_iff by auto    
  hence "{ i . i \<subseteq> S \<and> i \<Turnstile> (d \<union> (to_fact ` {l})) } \<noteq> \<emptyset>"
    by (simp add: card_gt_0_iff mods_def)
  thus ?thesis
    using models_debate_def to_fact_def by auto
qed
(*>*)

text \<open>The second theorem on monotinicity is stricter in that it proves that the value actually
 increases if certain contraints are met. I do not know if they were in teh original papers?
 Amongst them are the requirements that \<open>0 < doj S d {l} < 1\<close> (strict comparisons!).

 Thanks to some lemmata this can be expanded to the existence of models for
 derived debates:
 \<^enum> @{thm ex_is_gt0 [no_vars]}
 \<^enum> @{thm ex_is_lt1 [no_vars]}
\<close>

theorem strict_monotonicity:
  assumes fin: "finite S"
  assumes f_in_S: "f \<in> S"
  assumes fresh: "f \<notin> sents d"
  assumes f_not_l: "f \<noteq> sen l"
  assumes sat: "satisfiable S (d \<union> {({Pos f}, l)})"
  assumes lt1: "doj S d {l} < 1"  
  assumes gt0: "doj S d {l} > 0"  
  shows "doj S d {l} < doj S (d \<union> {({Pos f}, l)}) {l}"
(*<*)
proof -
  have sat_d: "satisfiable S d"
    by (meson models_debate_def sat satisfiable_def subset_iff sup.cobounded1) 
  have not_universal: "\<exists>i. i \<subseteq> S \<and> i \<Turnstile> d \<and> \<not>(i \<Turnstile>\<^sub>l l)" using lt1 ex_is_lt1 sat_d
    by (simp add: fin) 
  have not_universal2: "\<exists>i. i \<subseteq> S \<and> i \<Turnstile> d \<and> i \<Turnstile>\<^sub>l l" 
    using gt0 ex_is_gt0 sat_d fin by auto
 
  have "{ i . i \<subseteq> S \<and> i \<Turnstile> (d \<union> (to_fact ` {l}) \<union> {({Pos f}, l)}) } = { i . i \<subseteq> S \<and> i \<Turnstile> (d \<union> (to_fact ` {l})) }"
    using models_debate_def to_fact_def by auto
  hence nom: "mods S (d \<union> (to_fact ` {l}) \<union> {({Pos f}, l)}) = mods S (d \<union> (to_fact ` {l}))"
    by (simp add: mods_def)

  from not_universal obtain j where j: "j \<subseteq> S \<and> (j \<Turnstile> d) \<and> \<not>(j \<Turnstile>\<^sub>l l)" by blast
  then obtain k where k:"k \<subseteq> S \<and> (k \<Turnstile> d) \<and> \<not>(k \<Turnstile>\<^sub>l l) \<and> f \<in> k" 
  proof -
    have a0: "(insert f j) \<subseteq> S" using f_in_S j by simp
    have a1: "(insert f j) \<Turnstile> d"
      using j adding_irrelevant3 fresh by auto 
    have a2: "\<not>((insert f j) \<Turnstile>\<^sub>l l)" 
      using j f_not_l models_literal.elims(3) by fastforce 
    have a3: "f \<in> (insert f j)" by simp

    from a0 a1 a2 a3 show "(\<And>k. k \<subseteq> S \<and> k \<Turnstile> d \<and> \<not> k \<Turnstile>\<^sub>l l \<and> f \<in> k \<Longrightarrow> thesis)
        \<Longrightarrow> thesis" by blast      
  qed

  have subset: "{ i . i \<subseteq> S \<and> i \<Turnstile> (d \<union> {({Pos f}, l)}) } \<subseteq> { i . i \<subseteq> S \<and> i \<Turnstile> d }"
    using models_debate_def to_fact_def by auto

  from k have inside: "k \<in> { i . i \<subseteq> S \<and> i \<Turnstile> d }" by simp
  from k have outside: "k \<notin> { i . i \<subseteq> S \<and> i \<Turnstile> (d \<union> {({Pos f}, l)}) }"
    by (simp add: models_debate_def) 

  from subset inside outside 
  have "{ i . i \<subseteq> S \<and> i \<Turnstile> (d \<union> {({Pos f}, l)}) } \<subset> { i . i \<subseteq> S \<and> i \<Turnstile> d }"
    by blast
  hence "mods S (d \<union> {({Pos f}, l)}) < mods S d" using fin mods_def
    by (simp add: psubset_card_mono)
  hence denom: "int (mods S (d \<union> {({Pos f}, l)})) < int (mods S d)"
    by auto

  have pos: "int (mods S (d \<union> {({Pos f}, l)})) \<ge> 1" using sat sat_is_pos_mod fin
    by fastforce 

  have pos2: "int (mods S (d \<union> {({Pos f}, l)} \<union> {to_fact l})) > 0"
    using not_universal2
    by (smt (verit, ccfv_threshold) Un_insert_right boolean_algebra.disj_zero_right fin 
       insertE models_argument.simps models_debate_def not_one_le_zero of_nat_le_0_iff 
       sat_is_pos_mod satisfiable_def to_fact_def)

  have "doj S d {l} = Fract (int (mods S (d \<union> {to_fact l}))) (int (mods S d))"
    by (simp add: doj_def)
  also have "... = Fract (int (mods S (d \<union> {({Pos f}, l)} \<union> {to_fact l}))) (int (mods S d))"
    using nom by (simp add: Un_commute)
  also have "... < Fract (int (mods S (d \<union> {({Pos f}, l)} \<union> {to_fact l}))) 
                           (int (mods S (d \<union> {({Pos f}, l)})))" 
    using denom pos pos2 strict_fracts by force 
  also have "... = doj S (d \<union> {({Pos f}, l)}) {l}"
    by (simp add: doj_def) 
  ultimately show "doj S d {l} < doj S (d \<union> {({Pos f}, l)}) {l}"
    by argo
qed
(*>*)

end